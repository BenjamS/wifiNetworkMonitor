#include <Arduino.h>
#include <WiFi.h>
#include "esp_wifi.h"
#include <TFT_eSPI.h>
#include <SPI.h>
#include "SdFat.h"
#include <NimBLEDevice.h>
#include <ctype.h>
#include <string.h>
#include <algorithm>
#include <stdint.h>
#include <stdio.h>
#include <stdarg.h>
#include "tag221Lookup.h"
#include "ble_oui.h"
#include "ble_appearance.h"
#include "ble_uuids.h"
#include "UbuntuMono_Regular11pt7b.h"
#include "UbuntuMono_Regular9pt7b.h"
#include "UbuntuMono_Regular8pt7b.h"
#include "UbuntuMono_B9pt7b.h"
#include "UbuntuMono_RI9pt7b.h"
#include <cmath>
#include <atomic> // Add this to your includes
#include "waveHoundSprites.h"

#define COLOR_COLD      0xAEBC  // Light Blue (Far)
//#define COLOR_COLD 0xD511
#define COLOR_WARM      0xFFE0  // Standard Yellow (Medium)
#define COLOR_HOT_CHEST 0xF360  // Light Chestnut (Close)  

#define MAX_BSSID_CACHE 16

struct BssidCacheEntry {
    uint32_t last_seen; // 4 bytes (Largest first)
    uint8_t bssid[6];   // 6 bytes
    char ssid[33];      // 33 bytes
};

BssidCacheEntry bssidCache[MAX_BSSID_CACHE];

// Define the protocols so the math knows how to handle the physics
enum RadioProtocol {
    RADIO_BLE_24GHZ,
    RADIO_WIFI_24GHZ,
    RADIO_WIFI_5GHZ
};
// ==========================================
// OSINT PROBE TRACKER GLOBALS
// ==========================================
enum ProbeSortMode { PROBE_SORT_HITS, PROBE_SORT_DIST, PROBE_SORT_SSIDS, PROBE_SORT_AGE };
ProbeSortMode currentProbeSortMode = PROBE_SORT_HITS;
bool probe_sort_descending = true;

/**
 * Universal Log-Distance Path Loss Calculator
 * * @param rssi        The received signal strength (e.g., -75)
 * @param txPower     The broadcasted TX power in dBm (0 if unknown)
 * @param protocol    The RadioProtocol enum (BLE, Wi-Fi 2.4, Wi-Fi 5)
 * @param customLoss  (Optional) Override the path loss exponent. Default 0.0 uses standard presets.
 * @return            Estimated distance in meters
 */

int ap_current_page = 0;
const int APS_PER_PAGE = 6; // Number of APs that fit safely between the header and footer

int target_rssi = 0;

SdFs sd;

// ==========================================
// WAVE HOUND LAYER 2 & LIVE DUMP GLOBALS
// ==========================================
#define MAX_LEAK_STR_LEN 512
#define MAX_LIVE_CAPTURE 1536
#define LIVE_DUMP_QUEUE_DEPTH 20
#define LEAK_QUEUE_DEPTH 15   
#define MAX_ACTIVE_FLOWS 64
#define MAX_LEAK_SLOTS 20
#define LIVE_DUMP_COOLDOWN_MS 30000 
#define SEC_COOLDOWN_MS 5000 
#define ALERT_CACHE_SIZE 8
// ------------------------------------------
// CORE 0 CACHES
// ------------------------------------------
struct FlowRecord {
    uint32_t flow_hash;       
    uint32_t first_seen_ms;   
    uint32_t last_seen_ms;
    uint32_t last_printed_ms;
    uint16_t count;
};
static FlowRecord flow_cache[MAX_ACTIVE_FLOWS];

struct CryptoAlertCache {
    uint32_t last_alert_ms;
    uint8_t  mac_src[6];
    uint8_t  mac_dst[6];
};
static CryptoAlertCache crypto_cache[ALERT_CACHE_SIZE];
static uint8_t crypto_cache_idx = 0;

uint32_t leak_hash_history[32] = {0};
uint8_t  leak_hash_idx = 0;

// ------------------------------------------
// DUAL-CORE MESSAGE QUEUES & UNIFIED STRUCT
// ------------------------------------------
// Shared metadata — single source of truth
struct Layer2Meta {
    uint32_t timestamp;
    uint32_t flow_hash;
    uint16_t src_port;
    uint16_t dst_port;
    uint16_t frame_length;
    uint16_t ether_type;
    uint8_t  src_ip[16];
    uint8_t  dst_ip[16];
    uint8_t  src_mac[6];
    uint8_t  dst_mac[6];
    uint8_t  ip_version;
    uint8_t  protocol;
    uint8_t  channel;
    uint8_t  direction;
    uint8_t  frame_subtype;
    uint8_t  tcp_flags;
    bool     is_high_value;
    uint8_t bssid[6];
};

struct LiveCaptureEvent {
    Layer2Meta meta;
    uint16_t   raw_len;                 // bytes in raw_payload, up to MAX_LIVE_CAPTURE
    uint8_t    raw_payload[MAX_LIVE_CAPTURE];
};

// --- TRANSIENT HEAP POINTERS ---
LiveCaptureEvent* ptr_isr_evt = nullptr;
LiveCaptureEvent* ptr_core1_evt = nullptr;

struct Layer2Capture {
    Layer2Meta meta;
    uint16_t   retained_len;
    char    text[MAX_LEAK_STR_LEN];
};

struct LeakHistoryEntry {
    Layer2Capture leak;           // Uses the unified struct
    uint32_t first_seen;          // 4 bytes 
    uint32_t flow_hash;           // 4 bytes (Added for tracking Core 1 hits)
    char     src_vendor[16];      // 16 bytes
    char     dst_vendor[16];      // 16 bytes
    uint16_t hitCount;            // 2 bytes
};

/*
struct Layer2Capture {
    // --- 4-Byte Types ---
    uint32_t timestamp;
    uint32_t flow_hash;
    
    // --- 2-Byte Types ---
    uint16_t src_port;
    uint16_t dst_port;
    uint16_t frame_length; // True physical RF size
    uint16_t payload_len;  // Length of raw_payload copied
    uint16_t ether_type;
    
    // --- 1-Byte Types & Arrays ---
    uint8_t  src_ip[16];
    uint8_t  dst_ip[16];
    uint8_t  src_mac[6];
    uint8_t  dst_mac[6];
    uint8_t  ip_version;
    uint8_t  protocol;
    uint8_t  channel;
    uint8_t  direction;
    uint8_t  frame_subtype;
    uint8_t  tcp_flags;
    bool     is_high_value;
    
    // --- UNION 1: BSSID to SSID ---
    // ISR writes 6 bytes. Core 1 resolves it and safely overwrites with an 18-byte string.
    union {
        uint8_t bssid[6];          
        char    network_ssid[18];  
    };

    // --- UNION 2: Raw Binary to ASCII ---
    // ISR writes up to 512 bytes of binary. Core 1 parses it and overwrites with the ASCII translation.
    union {
        uint8_t raw_payload[MAX_RETAINED_PAYLOAD]; 
        char    text[MAX_LEAK_STR_LEN];       
    };
};

struct LiveCaptureEvent {
    uint32_t timestamp;
    uint32_t flow_hash;

    uint16_t src_port;
    uint16_t dst_port;
    uint16_t frame_length;
    uint16_t payload_len;
    uint16_t ether_type;

    uint8_t src_ip[16];
    uint8_t dst_ip[16];
    uint8_t src_mac[6];
    uint8_t dst_mac[6];

    uint8_t ip_version;
    uint8_t protocol;
    uint8_t channel;
    uint8_t direction;
    uint8_t frame_subtype;
    uint8_t tcp_flags;
    bool is_high_value;

    uint8_t bssid[6];

    uint8_t raw_payload[MAX_LIVE_CAPTURE];
};

// ------------------------------------------
// UI MEMORY (SNIFF LIST)
// ------------------------------------------
struct LeakHistoryEntry {
    Layer2Capture leak;           // Uses the unified struct
    uint32_t first_seen;          // 4 bytes 
    uint32_t flow_hash;           // 4 bytes (Added for tracking Core 1 hits)
    char     src_vendor[16];      // 16 bytes
    char     dst_vendor[16];      // 16 bytes
    uint16_t hitCount;            // 2 bytes
};
*/

QueueHandle_t liveDumpQueue = NULL;
QueueHandle_t leakQueue = NULL;
uint8_t leak_current_page = 0;

enum LeakSortMode {
    SORT_LEAK_AGE,
    SORT_LEAK_LENGTH,
    SORT_LEAK_HITS
};
LeakSortMode currentLeakSort = SORT_LEAK_AGE; // Default

// ==========================================
// LAYER 2 WATERFALL GLOBALS
// ==========================================
volatile uint32_t l2_bytes_tick = 0;
uint32_t l2_bytes_render = 0;
#define MAX_TERMINAL_LINES 5
Layer2Capture terminal_history[MAX_TERMINAL_LINES];
uint16_t terminal_hits[MAX_TERMINAL_LINES] = {0};
uint32_t terminal_first_seen[MAX_TERMINAL_LINES] = {0};

volatile uint32_t debug_dropped_packets = 0;
volatile uint32_t ui_total_arrived = 0;
volatile uint32_t ui_dropped_packets = 0;

// ISR-side (Core 0) — deauth + crypto/WEP interceptors
volatile uint32_t leak_isr_attempts = 0;
volatile uint32_t leak_isr_dropped  = 0;
// ISR-side Layer2 funnel diagnostics
volatile uint32_t leak_funnel_seen       = 0;
volatile uint32_t leak_funnel_suppressed = 0;
volatile uint32_t leak_funnel_shipped    = 0;
volatile uint32_t live_dump_dropped      = 0;
// Core 1 — processLiveDumpQueue() repush after parsing
uint32_t leak_core1_attempts = 0;
uint32_t leak_core1_dropped  = 0;
// ------------------------------------------
// FORMATTING HELPERS
// ------------------------------------------
const char* getSubtypeStr(uint8_t subtype) {
    switch (subtype) {
        case 0:  return "Data";
        case 4:  return "Null";
        case 8:  return "QoS Data";
        case 9:  return "QoS+CF-Ack";
        case 10: return "QoS+CF-Poll";
        case 11: return "QoS+Ack+Poll";
        case 12: return "QoS Null";
        case 14: return "QoS CF-Poll";
        case 15: return "QoS Ack+Poll";
        default: return "Mgmt/Ctrl";
    }
}

const char* getDirectionStr(uint8_t dir) {
    switch(dir) {
        case 0: return "STA>STA"; 
        case 1: return "STA>AP";   
        case 2: return "AP>STA";   
        case 3: return "WDS";       
        default: return "???";
    }
}

const char* getProtocolStr(uint8_t proto) {
    if (proto == 17) return "UDP";
    if (proto == 6) return "TCP";
    if (proto == 1) return "ICMP";
    if (proto == 58) return "ICMPv6";
    return "RAW";
}

void getIpString(uint8_t version, const uint8_t* ip_bytes, char* out_str, size_t max_len) {
    if (version == 4) {
        snprintf(out_str, max_len, "%d.%d.%d.%d", 
                 ip_bytes[0], ip_bytes[1], ip_bytes[2], ip_bytes[3]);
    } else if (version == 6) {
        // Now extracting the full 16-byte (128-bit) IPv6 address
        snprintf(out_str, max_len, "%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x:%02x%02x",
                 ip_bytes[0], ip_bytes[1], ip_bytes[2], ip_bytes[3],
                 ip_bytes[4], ip_bytes[5], ip_bytes[6], ip_bytes[7],
                 ip_bytes[8], ip_bytes[9], ip_bytes[10], ip_bytes[11],
                 ip_bytes[12], ip_bytes[13], ip_bytes[14], ip_bytes[15]); 
    } else {
        snprintf(out_str, max_len, "None");
    }
}

// ==========================================
// ABSOLUTE WATERFALL GLOBALS
// ==========================================
uint32_t traffic_history[240] = {0}; // 480 width / 2px increments = 240 columns
uint32_t absolute_max_traffic = 10;  // Seeded to prevent divide-by-zero
// ==========================================
// FOXHUNT STATE GLOBALS
// ==========================================
bool is_selecting_target = false; 
bool is_foxhunting = false;
uint8_t foxhunt_target_mac[6] = {0};
char foxhunt_target_vendor[28] = "Unknown";

// Foxhunt Math & Alert State
float smoothed_rssi = -100.0f;
int baseline_rssi = -100;
int last_displayed_rssi = -999;  // Sentinel: forces redraw on first frame.
                                  // Must differ from -100.0f initial smoothed_rssi
                                  // so updater redraws before first packet arrives.
int last_drawn_min = 0;          // NEW: Sentinel for bounds redraw
int last_drawn_max = 0;          // NEW: Sentinel for bounds redraw

// Cached spatial bounds — written from Core 1 only,
// read from Core 0 ISR via updateFoxhuntSignal. Avoids sessionData
// scan inside ISR callback path.
volatile int8_t foxhunt_rssi_min = -100;
volatile int8_t foxhunt_rssi_max = -100;
volatile bool foxhunt_bounds_seeded = false;

// --- Forward Declarations for OSINT Probe Tracker ---
int addSsidToPool(const char* ssid, int head_idx, bool &already_exists, bool &added, uint8_t current_count);
void processProbeRequestShared(uint8_t* mac, const char* ssid, const char* known_vendor = "", int8_t rssi = -100, uint32_t hw_hash = 0);

enum UIState { SCREEN_CHART, SCREEN_MENU, SCREEN_AP_SCAN,
   SCREEN_DEVICE_LIST, SCREEN_PROBE_TRACKER,
   SCREEN_FOXHUNT, SCREEN_LEAK_LIST };
UIState currentState = SCREEN_CHART;

const int MAX_PROBE_SLOTS = 45;     // Max unique devices tracked
const int TOTAL_SSID_POOL = 150;     // Total unique SSID strings shared among all devices
const int EMERGENCY_CUTOFF = 15;    // Max SSIDs a single device can claim

struct SSIDNode {
  char text[33];
  int next_node_idx = -1;                // Index of the next SSID for this device (-1 if end)
};

struct ProbeRecordShared {
  // --- 8-byte variables ---
  uint64_t pnl_hash;        // <--- NEW: 64-bit SSID Bloom Filter
  
  // --- 4-byte variables ---
  uint32_t hardware_hash;   // <--- NEW: 32-bit IE Tag Fingerprint
  unsigned long first_seen; 
  unsigned long last_seen;
  int first_ssid_idx;               
  float smoothedDistance;   
  
  // --- 2-byte variables ---
  uint16_t hits;
  
  // --- 1-byte arrays and variables ---
  uint8_t mac[6];
  char vendor[25];
  uint8_t ssid_count;
  uint8_t generation = 0;
  bool needs_lookup = false;
  int8_t rssi;              
  uint8_t mac_rotations;  // Tracks how many times this device has spoofed a new MAC
};

// Fixed, static memory blocks
ProbeRecordShared probeList[MAX_PROBE_SLOTS];
SSIDNode ssidPool[TOTAL_SSID_POOL];

int probe_current_page = 0; 
const int PROBES_PER_PAGE = 5;

// ==========================================
// RADIO MODE STATE
// ==========================================
enum RadioMode { RADIO_WIFI, RADIO_BLE, RADIO_AP, RADIO_CHANNELS, RADIO_LAYER2 };
RadioMode currentRadioMode = RADIO_WIFI;

// ==========================================
// BLUETOOTH DATA STRUCTURE
// ==========================================
#define MAX_BLE_DEVICES 150

// 1. Define this enum above the struct so it exists in memory first
enum OsintTrackerType : uint8_t {
    TRACKER_NONE = 0,
    TRACKER_APPLE_FINDMY,
    TRACKER_APPLE_IBEACON,
    TRACKER_GOOGLE_FASTPAIR,
    TRACKER_SAMSUNG_SMARTTAG,
    TRACKER_TILE,
    TRACKER_MS_SWIFTPAIR,
    TRACKER_EDDYSTONE
};

// 2. The perfectly aligned struct
struct BLERecord {
  // --- 4-Byte Types (Grouped at the top) ---
  uint32_t firstSeen;       
  uint32_t lastSeen;
  uint32_t hits;          
  float smoothedDistance; 

  // --- 2-Byte Types (The string replacements) ---
  uint16_t appearanceId;    
  uint16_t serviceId;       

  // --- 1-Byte Types & Arrays (Grouped at the bottom) ---
  uint8_t mac[6];         
  uint8_t trackerType;      
  int8_t rssi;               
  int8_t txPower; 
  uint8_t namePriority;     // <--- ADDED BACK: Protects your Eddystone URLs
  char name[25];            
  char payload[30];
};

// Perfectly aligned with your drawDeviceList() function!
const int BLE_UPDATE_INTERVAL = 2000;         // Refresh rate for BLE waterfall (ms)

// NimBLE Global Scanner Pointer
BLEScan* pBLEScan;

#define MAX_AP_RECORDS 100 // Bumped from 30! Safely fits inside the Union.

struct ApRecord {
  // 8-byte types
  uint64_t sum_bytes;
  uint64_t sum_sq_bytes;

  // 4-byte types
  uint32_t first_seen; 
  uint32_t last_seen;  
  uint32_t packets;
  uint32_t tx_bytes;
  uint32_t rx_bytes;
  float smoothedDistance;

  // 1-byte types & arrays
  uint8_t bssid[6];       
  uint8_t channel;
  uint8_t max_rate;
  int8_t rssi;
  int8_t rssi_min;    
  int8_t rssi_max;    
  bool has_clone;     // NEW: O(1) lookup during UI rendering
  char ssid[25];      // Trimmed from 26 to 25 to maintain exactly 80 bytes
  char country[3];
};
// Still exactly 80 bytes!

#define MAX_CHANNEL_RECORDS 100

struct ChannelRecord {
  uint64_t sum_bytes;
  uint64_t sum_sq_bytes;
  uint32_t first_seen;
  uint32_t last_seen;
  uint32_t packets;
  uint32_t tx_bytes;
  uint32_t rx_bytes;
  uint8_t channel;
  
  // --- The EMA Time-Series Variables ---
  float avg_rssi;     // The moving noise floor
  float ema_variance; // The volatility tracker
  float prev_rssi;    // Memory of the last packet
  float ema_cov;      // The autocorrelation tracker
};

int total_sniffed_probes = 0;
int device_current_page = 0;
const int DEVICES_PER_PAGE = 13; // 9pt font with 18px line spacing fits 13 devices perfectly

std::atomic<bool> pause_sniffing{false};
bool useLogScale = false;

bool sort_descending = true; // Default to loudest devices first

uint16_t calData[5] = { 288, 3501, 301, 3244, 7 };
TFT_eSPI tft = TFT_eSPI();

const int CHANNELS[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13};
const int NUM_CHANNELS = 13;
int current_ch_idx = 0;

const int HOP_INTERVAL = 300;                // Time spent on each channel (ms)
const int LOCKED_UPDATE_INTERVAL = 2000;      // Refresh rate when locked to an AP (ms)
const int MAX_MACS = 185;

// --- TARGET AP LOCK GLOBALS ---
uint8_t target_bssid[6] = {0};
int target_channel = 0;
bool target_locked = false;
char target_ssid[33] = {0}; // Store the name of the targeted network

const int HEADER_HEIGHT = 108; 
const int CHART_BOTTOM = 298;
const int chart_start_y = HEADER_HEIGHT + 53;

int current_x = 0;

struct MacRecord {
    uint64_t sum_bytes;
    uint64_t sum_sq_bytes;
    uint32_t first_seen;
    uint32_t last_seen;
    uint32_t packets;
    uint32_t tx_bytes;
    uint32_t rx_bytes;
    float smoothedDistance;
    uint8_t mac[6];
    char vendor[28];
    int8_t rssi;
    int8_t rssi_min;    // <--- NEW: spatial floor
    int8_t rssi_max;    // <--- NEW: spatial ceiling
    uint8_t rate;
    bool vendorFound;
    bool needs_lookup;
};
//Should be 80 bytes

void resolveMacVendor(MacRecord* record);

struct OUICache {
  uint8_t oui[3];
  char vendor[28]; // <--- Updated to match the new MacRecord limit
};

#define MAX_BEACON_DICT 80 // MAX POSSIBLE IS 255 given uint8_t beaconDictCount
struct BeaconEntry {
    uint32_t last_seen; //  4 bytes — 4-byte type first
    int8_t rssi;        //  1 byte
    uint8_t bssid[6];  //  6 bytes
    char ssid[33];      // 33 bytes
                        // = 44 bytes, no padding needed
};
BeaconEntry beaconDict[MAX_BEACON_DICT];
uint8_t beaconDictCount = 0;

// ==========================================
// OUI RAM CACHE (Ring Buffer)
// ==========================================
#define OUI_CACHE_SIZE 150

OUICache vendorCache[OUI_CACHE_SIZE];
int cacheCount = 0;
int cacheHead = 0;

// ==========================================
// 1. LIVE BUFFER (Shared RAM)
// ==========================================
static union {
  volatile MacRecord liveData[MAX_MACS];
  volatile BLERecord liveBleData[MAX_BLE_DEVICES];
  volatile ApRecord liveApData[MAX_AP_RECORDS];
  volatile ChannelRecord liveChannelData[MAX_CHANNEL_RECORDS];
};
volatile uint16_t liveMacCount = 0;
volatile uint32_t liveOtherBytes = 0;
volatile uint16_t liveBleCount = 0;
volatile uint16_t liveApCount = 0;
volatile uint16_t liveChannelCount = 0;

// ==========================================
// 2. SORT BUFFER (Shared RAM)
// ==========================================
static union {
  MacRecord sortData[MAX_MACS];
  BLERecord sortBleData[MAX_BLE_DEVICES];
  ApRecord sortApData[MAX_AP_RECORDS];
  ChannelRecord sortChannelData[MAX_CHANNEL_RECORDS];
};
uint16_t sortMacCount = 0;
uint32_t sortOtherBytes = 0;
uint16_t sortBleCount = 0;
uint16_t sortApCount = 0;
uint16_t sortChannelCount = 0;

// ==========================================
// 3. SESSION BUFFER (Shared RAM)
// ==========================================
static union {
  MacRecord sessionData[MAX_MACS];
  BLERecord sessionBleData[MAX_BLE_DEVICES];
  ApRecord sessionApData[MAX_AP_RECORDS]; 
  ChannelRecord sessionChannelData[MAX_CHANNEL_RECORDS];
  LeakHistoryEntry leakHistory[MAX_LEAK_SLOTS];
};
uint16_t sessionMacCount = 0;
uint32_t sessionOtherBytes = 0;
uint16_t sessionBleCount = 0;
uint16_t sessionApCount = 0;
uint16_t sessionChannelCount = 0;

// Calculate the memory footprint of each mode
constexpr size_t wifi_size = sizeof(MacRecord) * MAX_MACS;           
constexpr size_t ble_size = sizeof(BLERecord) * MAX_BLE_DEVICES;     
constexpr size_t ap_size = sizeof(ApRecord) * MAX_AP_RECORDS;        
constexpr size_t channel_size = sizeof(ChannelRecord) * MAX_CHANNEL_RECORDS; 
constexpr size_t leak_size = sizeof(LeakHistoryEntry) * MAX_LEAK_SLOTS;

// Dynamically determine the true union boundary
constexpr size_t max_size_1 = (ble_size > wifi_size) ? ble_size : wifi_size;
constexpr size_t max_size_2 = (ap_size > channel_size) ? ap_size : channel_size;
constexpr size_t max_size_3 = (leak_size > max_size_1) ? leak_size : max_size_1; 
constexpr size_t union_size = (max_size_3 > max_size_2) ? max_size_3 : max_size_2;

constexpr size_t static_non_union =
    (union_size * 3) +                                        // live + sort + session
    (sizeof(OUICache)          * OUI_CACHE_SIZE)      +
    (sizeof(ProbeRecordShared) * MAX_PROBE_SLOTS)     +
    (sizeof(SSIDNode)          * TOTAL_SSID_POOL)     +
    (sizeof(BeaconEntry)       * MAX_BEACON_DICT);

constexpr size_t osint_layer_size =
    (sizeof(ProbeRecordShared) * MAX_PROBE_SLOTS) +
    (sizeof(SSIDNode)          * TOTAL_SSID_POOL) +
    (sizeof(BeaconEntry)       * MAX_BEACON_DICT);

// Compile-time safety checks relative to the TRUE union boundary
static_assert(union_size >= wifi_size, "FATAL: Wi-Fi array exceeds union boundary.");
static_assert(union_size >= ble_size, "FATAL: BLE array exceeds union boundary.");
static_assert(union_size >= ap_size, "FATAL: AP array exceeds union boundary.");
static_assert(union_size >= channel_size, "FATAL: Channel array exceeds union boundary.");

// Persistent OSINT layer budget check
static_assert(osint_layer_size < 20480, 
    "FATAL: Persistent OSINT layer exceeds 20KB budget.");

// Total known static allocation
constexpr size_t SRAM_BUDGET = 327680;  // 320KB — conservative application budget
                                         // leaving ~200KB for WiFi/BLE/stack/heap

static_assert(static_non_union <= SRAM_BUDGET,
    "FATAL: Static allocations exceed conservative SRAM budget. "
    "Reduce array sizes.");

bool force_ui_refresh = false;

// Color utility fn
constexpr uint16_t hex24to565(uint32_t hex24) {
  return ((((hex24 >> 16) & 0xFF) & 0xF8) << 8) |
  ((((hex24 >> 8) & 0xFF) & 0xFC) << 3) |
  (((hex24) & 0xFF) >> 3);
}

// 8-color array using standard web hex codes!
uint16_t colors[9] = {
  hex24to565(0x7CD9CA), // [0] Mint Green
  hex24to565(0xFF00FF), // [1] Magenta
  hex24to565(0xD9D680), // [2] Pale Yellow
  hex24to565(0xB75BE2), // [3] Purple
  hex24to565(0x87E370), // [4] Bright Green
  hex24to565(0xD1C9CA), // [5] Light Gray
  hex24to565(0xDA815E), // [6] Rust/Orange  
  hex24to565(0x889FD7), // [7] Periwinkle Blue
  TFT_DARKGREY          // [8] "Other" category (unchanged)
  //hex24to565(0xE07EB6), // [6] Pink
};

// FNV-1a 32-bit Hash
uint32_t hash_flow(const uint8_t* data, size_t len, uint16_t sport, uint16_t dport) {
    uint32_t hash = 2166136261u;
    
    // Hash the ports first
    hash ^= (sport & 0xFF); hash *= 16777619;
    hash ^= (sport >> 8);   hash *= 16777619;
    hash ^= (dport & 0xFF); hash *= 16777619;
    hash ^= (dport >> 8);   hash *= 16777619;

    // Hash the payload
    for (size_t i = 0; i < len; i++) {
        hash ^= data[i];
        hash *= 16777619;
    }
    return hash;
}

// ==========================================
// PHY RATE TO MBPS TRANSLATOR
// ==========================================
uint8_t getBitrateMbps(wifi_promiscuous_pkt_t *pkt) {
  if (pkt->rx_ctrl.sig_mode == 0) { 
    // Legacy 802.11b/g
    switch(pkt->rx_ctrl.rate) {
      case 0x00: return 1;
      case 0x01: return 2;
      case 0x02: return 5; // 5.5 Mbps rounded down
      case 0x03: return 11;
      case 0x0B: return 6;
      case 0x0F: return 9;
      case 0x0A: return 12;
      case 0x0E: return 18;
      case 0x09: return 24;
      case 0x0D: return 36;
      case 0x08: return 48;
      case 0x0C: return 54;
      default: return 0;
    }
  } else { 
    // 802.11n (HT20 / HT40) MCS Index
    switch(pkt->rx_ctrl.mcs) {
      case 0: return 6;  // 6.5 Mbps
      case 1: return 13;
      case 2: return 19; // 19.5 Mbps
      case 3: return 26;
      case 4: return 39;
      case 5: return 52;
      case 6: return 58; // 58.5 Mbps
      case 7: return 65;
      default: return 0;
    }
  }
}

bool isSameDevice(int idxA, int idxB) {
    // GATE 1: HARDWARE (Strict pass/fail)
    if (probeList[idxA].hardware_hash != probeList[idxB].hardware_hash) {
        return false; 
    }

    int confidence_score = 0;

    // GATE 2: BEHAVIORAL (Scoring)
    uint64_t hashA = probeList[idxA].pnl_hash;
    uint64_t hashB = probeList[idxB].pnl_hash;
    
    if (hashA == hashB && hashA != 0) {
        confidence_score += 50; // Exact match of non-empty networks
    } else if ((hashA & hashB) == hashB || (hashA & hashB) == hashA) {
        confidence_score += 30; // Perfect subset match
    }

    // GATE 3: SPATIAL (Scoring)
    int rssi_delta = abs(probeList[idxA].rssi - probeList[idxB].rssi);
    if (rssi_delta <= 5) {
        confidence_score += 40; // Physically occupying the same space
    } else if (rssi_delta > 15) {
        confidence_score -= 50; // Physics dictate these are likely different locations
    }

    // THE VERDICT
    return (confidence_score >= 70);
}

uint8_t getSsidBitIndex(const char* ssid) {
    unsigned long hash = 5381; // Standard djb2 seed
    int c;
    while ((c = *ssid++)) {
        hash = ((hash << 5) + hash) + c; // hash * 33 + c
    }
    return hash % 64; // Constrain to exactly 64 bits
}

void ingestBeacon(uint8_t* bssid, const char* ssid, int8_t rssi) {
    // Skip hidden networks — no useful cross-reference value
    if (ssid == nullptr || strlen(ssid) == 0) return;
    
    // Search for existing entry
    for (int i = 0; i < beaconDictCount; i++) {
        if (memcmp(beaconDict[i].bssid, bssid, 6) == 0) {
            // Update existing
            beaconDict[i].rssi = rssi;
            beaconDict[i].last_seen = millis();
            return;
        }
    }
    
    // New entry
    if (beaconDictCount < MAX_BEACON_DICT) {
        memcpy(beaconDict[beaconDictCount].bssid, bssid, 6);
        strncpy(beaconDict[beaconDictCount].ssid, ssid, 32);
        beaconDict[beaconDictCount].ssid[32] = '\0';
        beaconDict[beaconDictCount].rssi = rssi;
        beaconDict[beaconDictCount].last_seen = millis();
        beaconDictCount++;
    }
    // No eviction needed — beacon SSIDs are stable,
    // so a full dictionary means you've already catalogued
    // everything in the local airspace
}

// Returns the number of SSIDs in a probe record's list
// that have a known beacon in the dictionary
int crossReferenceProbeToBeacons(int probe_idx, 
                                  uint8_t* matched_bssid_out,
                                  int8_t* ap_rssi_out) {
    int matches = 0;
    int best_match_rssi_diff = 999;
    
    // Walk the probe record's SSID linked list
    int node = probeList[probe_idx].first_ssid_idx;
    
    while (node != -1) {
        const char* probed_ssid = ssidPool[node].text;
        
        // Skip wildcard entries
        if (strcmp(probed_ssid, "<Wld>") == 0 || 
            strcmp(probed_ssid, "<Nul>") == 0) {
            node = ssidPool[node].next_node_idx;
            continue;
        }
        
        // Search the beacon dictionary for this SSID
        for (int i = 0; i < beaconDictCount; i++) {
            if (strcmp(beaconDict[i].ssid, probed_ssid) == 0) {
                matches++;
                
                // Find the AP whose RSSI is closest to the probe RSSI
                // (same physical space = similar signal strength)
                int rssi_diff = abs(probeList[probe_idx].rssi - 
                                    beaconDict[i].rssi);
                if (rssi_diff < best_match_rssi_diff) {
                    best_match_rssi_diff = rssi_diff;
                    if (matched_bssid_out) 
                        memcpy(matched_bssid_out, beaconDict[i].bssid, 6);
                    if (ap_rssi_out) 
                        *ap_rssi_out = beaconDict[i].rssi;
                }
            }
        }
        
        node = ssidPool[node].next_node_idx;
    }
    
    return matches;
}

void updateFoxhuntSignal(int packet_rssi) {
  // 1. Set dynamic tuning parameters
  float current_alpha = 0.2; // Default for WiFi/AP

  if (currentRadioMode == RADIO_BLE) {
    current_alpha = 0.55;
  }

  // 2. Initialize or smooth the signal safely
  if (smoothed_rssi == -100.0f) {
    smoothed_rssi = (float)packet_rssi;
  } else {
    smoothed_rssi = (current_alpha * (float)packet_rssi) +
                    ((1.0f - current_alpha) * smoothed_rssi);
  }

  // ==========================================
  // 3. REAL-TIME TACTICAL STRETCHING
  // Mode-agnostic: Works for Wi-Fi, AP, and BLE
  // ==========================================
  
  // Stretch the floor (Triggering on 0 for Wi-Fi and -100 for BLE sentinels)
  if (foxhunt_rssi_min == 0 || foxhunt_rssi_min == -100 || packet_rssi < foxhunt_rssi_min) {
      foxhunt_rssi_min = packet_rssi;
  }
  
  // Stretch the ceiling 
  if (foxhunt_rssi_max == -100 || packet_rssi > foxhunt_rssi_max) {
      foxhunt_rssi_max = packet_rssi;
      foxhunt_bounds_seeded = true;
  }
}

// ==========================================
// CLEARTEXT EXTRACTOR (OSINT UPGRADED)
// ==========================================
bool extract_printable_runs(const uint8_t* data, uint16_t len, char* out, size_t max_len,
                             uint8_t min_run = 4, bool flatten_ws = false,
                             const char* separator = "|") {

    if (!data || !out || max_len < 16 || len == 0) return false;

    uint16_t out_idx = 0;
    uint16_t consecutive = 0;
    uint16_t printable_count = 0;
    size_t sep_len = strlen(separator);

    // --- Phase 1: Raw Extraction ---
    for (uint16_t i = 0; i < len && out_idx < (max_len - 4); i++) {
        char c = (char)data[i];
        bool is_ws = (c == '\n' || c == '\r' || c == '\t');
        bool is_printable = (c >= 32 && c <= 126) || (flatten_ws && is_ws);

        if (is_printable) {
            consecutive++;
            if (consecutive == min_run) {
                for (int back = min_run; back >= 1 && out_idx < max_len - 1; back--) {
                    char rc = (char)data[i - back + 1];
                    if (flatten_ws && (rc == '\n' || rc == '\r' || rc == '\t')) rc = ' ';
                    out[out_idx++] = rc;
                }
                printable_count += min_run;
            } else if (consecutive > min_run && out_idx < max_len - 1) {
                out[out_idx++] = (flatten_ws && is_ws) ? ' ' : c;
                printable_count++;
            }
        } else {
            if (consecutive >= min_run && out_idx + sep_len < max_len - 1) {
                memcpy(out + out_idx, separator, sep_len);
                out_idx += sep_len;
            }
            consecutive = 0;
        }
    }

    out[out_idx] = '\0';
    
    // First line of defense: Must have at least 12 printable characters total
    if (printable_count < 12) return false;

    // --- Phase 2: Signature Classification ---
    const char* tag = nullptr;

    if (strstr(out, "HTTP/1.")) tag = "[HTTP]";
    else if (strstr(out, "<?xml") || (strchr(out, '<') && strchr(out, '>'))) tag = "[XML]";
    else if (strstr(out, "{\"") && strstr(out, "\":")) tag = "[JSON]";
    else if (strstr(out, "ocsp.") || strstr(out, "/ocsp")) tag = "[OCSP]";
    else if (strstr(out, ".crl")) tag = "[CRL]";
    else if (strstr(out, ".crt") || strstr(out, "cacerts.")) tag = "[CERT-URI]";
    else if (strstr(out, "://")) tag = "[URI]";
    else tag = "[TEXT]"; // Semantically precise fallback

    // --- Phase 3: Prepend Tag ---
    size_t tag_len = strlen(tag);
    if (out_idx + tag_len + 1 < max_len) {
        memmove(out + tag_len + 1, out, out_idx + 1);
        memcpy(out, tag, tag_len);
        out[tag_len] = ' '; 
    }

    return true;
}
// ==========================================
// CLEARTEXT EXTRACTOR 
// ==========================================
// Scans raw bytes for runs of printable ASCII, filtering out short noise
// blips below min_run. This is the ONE generic "scrape for cleartext"
// primitive — grammar-aware protocols (SSDP, mDNS, JSON) do NOT use this;
// it's strictly the last-resort fallback for unknown/unstructured payloads.
//
// min_run:     minimum consecutive printable chars before a chunk is kept
// flatten_ws:  if true, \n \r \t count as printable and render as a single
//              space instead of breaking the run (matches old extractCleartext)
// separator:   inserted between chunks on a gap (" | " for Step 13 style,
//              " " for extractCleartext style)
/*
bool extract_printable_runs(const uint8_t* data, uint16_t len, char* out, size_t max_len,
                             uint8_t min_run = 4, bool flatten_ws = false,
                             const char* separator = "|") {
    uint16_t out_idx = 0;
    uint16_t consecutive = 0;
    uint16_t printable_count = 0;
    size_t sep_len = strlen(separator);

    for (uint16_t i = 0; i < len && out_idx < (max_len - 4); i++) {
        char c = (char)data[i];
        bool is_ws = (c == '\n' || c == '\r' || c == '\t');
        bool is_printable = (c >= 32 && c <= 126) || (flatten_ws && is_ws);

        if (is_printable) {
            consecutive++;
            if (consecutive == min_run) {
                for (uint8_t back = min_run; back >= 1 && out_idx < max_len - 1; back--) {
                    char rc = (char)data[i - back + 1];
                    if (flatten_ws && (rc == '\n' || rc == '\r' || rc == '\t')) rc = ' ';
                    out[out_idx++] = rc;
                }
                printable_count += min_run;
            } else if (consecutive > min_run && out_idx < max_len - 1) {
                out[out_idx++] = (flatten_ws && is_ws) ? ' ' : c;
                printable_count++;
            }
        } else {
            if (consecutive >= min_run && out_idx + sep_len < max_len - 1) {
                memcpy(out + out_idx, separator, sep_len);
                out_idx += sep_len;
            }
            consecutive = 0;
        }
    }

    out[out_idx] = '\0';
    return printable_count > 10;
}
*/
// ==========================================
// PROTOCOL TRANSLATORS (NetBIOS, mDNS, Cast)
// ==========================================

// Returns a human-readable label for the NetBIOS suffix byte.
// Shortened slightly from the Python version to prevent text wrapping on the ILI9488 TFT.
const char* getNetbiosSuffixStr(uint8_t suffixCode) {
    switch (suffixCode) {
        case 0x00: return "Workstation/Domain";
        case 0x03: return "Messenger Service";
        case 0x06: return "RAS Server";
        case 0x20: return "File Server";
        case 0x21: return "RAS Client";
        case 0x1B: return "Domain Master";
        case 0x1C: return "Domain Controller";
        case 0x1D: return "Master Browser";
        case 0x1E: return "Browser Election";
        case 0x1F: return "NetDDE Service";
        case 0xBE: return "Network Monitor";
        case 0xFF: return "Parse Error";
        default:   return "Unknown Suffix";
    }
}

// Decodes the A-P string, populates the display name, and returns the suffix byte.
// decodedName buffer should be at least 17 bytes (16 chars + null terminator).
uint8_t decodeNetbiosName(const char* encoded, char* decodedName, size_t maxLen) {
    uint8_t suffix = 0xFF; // Default error/unknown
    int outIdx = 0;
    int len = strlen(encoded);

    // Skip leading dot if your DNS parser accidentally passed one in
    int startIdx = (encoded[0] == '.') ? 1 : 0;

    for (int i = startIdx; i < len - 1 && outIdx < 16; i += 2) {
        char c1 = encoded[i];
        char c2 = encoded[i + 1];

        // Valid NetBIOS encoding uses ASCII 'A' through 'P'
        if (c1 >= 'A' && c1 <= 'P' && c2 >= 'A' && c2 <= 'P') {
            uint8_t high = c1 - 'A';
            uint8_t low  = c2 - 'A';
            decodedName[outIdx++] = (high << 4) | low;
        } else {
            break; // Stop if we hit malformed or non-NetBIOS data
        }
    }

    // A valid NetBIOS name yields exactly 16 bytes
    if (outIdx == 16) {
        suffix = decodedName[15]; // Grab the 16th byte
        
        // NetBIOS pads the name with spaces (0x20). 
        // We trim them off backwards so it looks clean on the TFT screen.
        int trimIdx = 14;
        while (trimIdx >= 0 && decodedName[trimIdx] == ' ') {
            trimIdx--;
        }
        decodedName[trimIdx + 1] = '\0'; // Null-terminate right after the actual name
    } else {
        // If it wasn't 16 bytes, just null-terminate whatever we managed to parse
        decodedName[outIdx < maxLen ? outIdx : maxLen - 1] = '\0';
    }

    return suffix;
}

// ---------------------------------------------------------
// NETBIOS (NBNS) PARSER (Port 137)
// Decodes A-P encoded names and identifies the service type
// ---------------------------------------------------------
bool parse_netbios(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // A standard NetBIOS Name Service (NBNS) query has a 12-byte header.
    // Byte 12 is the length of the name (always 0x20 or 32 bytes).
    // The A-P encoded string starts at Byte 13.
    if (length >= 45 && payload[12] == 0x20) {
        
        // 1. Safely extract the 32-byte A-P encoded string
        char rawEncodedString[33];
        memcpy(rawEncodedString, &payload[13], 32);
        rawEncodedString[32] = '\0'; // Ensure null-termination

        // 2. Decode it using your memory-safe functions
        char cleanName[17]; 
        uint8_t suffixByte = decodeNetbiosName(rawEncodedString, cleanName, sizeof(cleanName));
        const char* serviceType = getNetbiosSuffixStr(suffixByte);

        // 3. Format it (Updated to show both)
        snprintf(out_text, max_len, "NBNS: [%s] -> %s [%s]", 
                 rawEncodedString, cleanName, serviceType);
        return true; 
    }
    return false;
}

// ---------------------------------------------------------
// NETBIOS DATAGRAM (NBDS) PARSER (Port 138)
// Extracts cleartext hostnames, domains, and workgroups 
// from SMB Browser / Mailslot packets
// ---------------------------------------------------------
bool parse_nbds(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    int written = snprintf(out_text, max_len, "NBDS:");
    bool found_any = false;

    int cur_s = 0, cur_l = 0;

    for (int i = 0; i <= length; i++) {
        char c = (i < length) ? payload[i] : 0;

        if (c >= 32 && c <= 126) {
            if (cur_l == 0) cur_s = i;
            cur_l++;
        } else {
            if (cur_l >= 5) {
                // Trim a leading/trailing space — NBT name fields are prefixed with a
                // 0x20 length byte, which is itself printable and merges into the same
                // run as the encoded name that follows it.
                int seg_s = cur_s;
                int seg_l = cur_l;
                while (seg_l > 0 && payload[seg_s] == ' ') { seg_s++; seg_l--; }
                while (seg_l > 0 && payload[seg_s + seg_l - 1] == ' ') { seg_l--; }

                if (seg_l >= 5) {
                    char temp[64] = {0};
                    int copy_len = std::min(seg_l, 63);
                    memcpy(temp, &payload[seg_s], copy_len);

                    if (!strstr(temp, "MAILSLOT") && !strstr(temp, "BROWSE")) {
                        // A real NetBIOS-encoded name is always exactly 32 A-P chars
                        // (16 bytes x 2 nibbles). Requiring the exact length (not just
                        // >=16) avoids misidentifying partial/truncated runs as names.
                        bool is_ap_blob = (seg_l == 32);
                        for (int j = 0; j < copy_len && is_ap_blob; j++) {
                            if (temp[j] < 'A' || temp[j] > 'P') is_ap_blob = false;
                        }

                        if (is_ap_blob) {
                            // Decode it instead of dropping it — this is the actual
                            // "translation" step that was missing.
                            char decoded[17] = {0};
                            uint8_t suffix = decodeNetbiosName(temp, decoded, sizeof(decoded));
                            
                            // ==========================================
                            // NEW "DOUBLE-KEY" PRINTING LOGIC GOES HERE
                            // ==========================================
                            if (decoded[0] != '\0' && !strstr(out_text, decoded) && written < (int)max_len) {
                                written += snprintf(out_text + written, max_len - written,
                                                     " [%s] -> %s [%s]", 
                                                     temp, decoded, getNetbiosSuffixStr(suffix));
                                found_any = true;
                            }
                            // ==========================================
                            
                        } else if (!strstr(out_text, temp)) {
                            if (written < (int)max_len) {
                                written += snprintf(out_text + written, max_len - written, " [%s]", temp);
                                found_any = true;
                            }
                        }
                    }
                }
            }
            cur_l = 0;
        }
    }
    return found_any;
}

void translateProtocolStrings(char* text) {
    char temp_buffer[MAX_LEAK_STR_LEN];
    int len = strlen(text);
    // 0. Global Cleanup: Strip trailing "x V" or "xV" artifacts
    while (len > 0 && text[len-1] == ' ') { text[len-1] = '\0'; len--; } // Trim trailing spaces
    
    if (len >= 3 && text[len-3] == 'x' && text[len-2] == ' ' && text[len-1] == 'V') {
        text[len-3] = '\0';
        len -= 3;
    } else if (len >= 2 && text[len-2] == 'x' && text[len-1] == 'V') {
        text[len-2] = '\0';
        len -= 2;
    }
    
    while (len > 0 && text[len-1] == ' ') { text[len-1] = '\0'; len--; } // Trim again if exposed

    /*
    // ----------------------------------------------------
    // 1. NetBIOS Name Decode (e.g., FCEJEDEPEIFHDCD...)
    // ----------------------------------------------------
    int consec_ap = 0;
    int nb_start = -1;
    
    for (int i = 0; i < len; i++) {
        if (text[i] >= 'A' && text[i] <= 'P') {
            if (consec_ap == 0) nb_start = i;
            consec_ap++;
            
            if (consec_ap == 32) {
                char decoded[17] = {0};
                
                // Decode the 16 bytes from the A-P nibbles
                for (int j = 0; j < 16; j++) {
                    char nibble_high = text[nb_start + j * 2] - 'A';
                    char nibble_low  = text[nb_start + j * 2 + 1] - 'A';
                    decoded[j] = (nibble_high << 4) | nibble_low;
                }
                
                // FIX 1: Ignore the 16th byte (Service Suffix) 
                decoded[15] = '\0';
                
                // FIX 2: Trim trailing spaces from the remaining 15 characters
                for (int j = 14; j >= 0; j--) {
                    if (decoded[j] == ' ') {
                        decoded[j] = '\0';
                    } else if (decoded[j] != '\0') {
                        break;
                    }
                }
                
                char* final_name = decoded;
                
                // FIX 3: Trim leading lowercase letter + space noise (e.g., "a ", "b ")
                if (final_name[0] >= 'a' && final_name[0] <= 'z' && final_name[1] == ' ') {
                    final_name += 2; // Advance pointer past the noise
                }
                
                // FIX 4: Safety pass to strip any remaining non-printable characters 
                for (int j = 0; final_name[j] != '\0'; j++) {
                    if (final_name[j] < 32 || final_name[j] > 126) {
                        final_name[j] = '\0';
                        break;
                    }
                }
                
                snprintf(temp_buffer, MAX_LEAK_STR_LEN, "%s [%s]", text, final_name);
                strncpy(text, temp_buffer, MAX_LEAK_STR_LEN);
                return; 
            }
        } else {
            consec_ap = 0;
        }
    }
*/
    // ----------------------------------------------------
    // 2. mDNS IPv4 Reverse Lookup
    // ----------------------------------------------------
    char* in_addr = strstr(text, "in-addr arpa");
    if (in_addr != NULL) {
        int o1, o2, o3, o4;
        char* ptr = text;
        
        while (ptr < in_addr) {
            if (sscanf(ptr, "%d %d %d %d in-addr", &o4, &o3, &o2, &o1) == 4) {
                snprintf(temp_buffer, MAX_LEAK_STR_LEN, "mDNS Reverse Query: %d.%d.%d.%d", o1, o2, o3, o4);
                strncpy(text, temp_buffer, MAX_LEAK_STR_LEN);
                return;
            }
            ptr++;
        }
    }

    // ----------------------------------------------------
    // 3. mDNS IPv6 Reverse Lookup (Inline Replacement)
    // ----------------------------------------------------
    char* ip6 = strstr(text, "ip6");
    if (ip6 != NULL) {
        char nibbles[32];
        int n_idx = 0;
        char* ptr = ip6 - 1;
        
        while (ptr >= text && n_idx < 32) {
            char c = *ptr;
            if ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f')) {
                nibbles[n_idx++] = c; 
            }
            ptr--;
        }
        
        if (n_idx == 32) {
            char ipv6_str[40];
            int out_idx = 0;
            
            for (int i = 0; i < 32; i++) {
                ipv6_str[out_idx++] = nibbles[i];
                if (i % 4 == 3 && i != 31) {
                    ipv6_str[out_idx++] = ':';
                }
            }
            ipv6_str[out_idx] = '\0';
            
            // ptr is now resting just before the first parsed hex character.
            // We stitch: [Prefix] + [Clean IPv6] + [".ip6" Suffix]
            int prefix_len = (ptr + 1) - text;
            
            snprintf(temp_buffer, MAX_LEAK_STR_LEN, "%.*s%s.%s", prefix_len, text, ipv6_str, ip6);
            strncpy(text, temp_buffer, MAX_LEAK_STR_LEN);
            return;
        }
    }

    // ----------------------------------------------------
    // 4. Google Cast App ID Lookup (Inline Replacement)
    // ----------------------------------------------------
    if (strstr(text, "googlecast") != NULL) {
        struct CastApp {
            const char* id;
            const char* name;
        };
        
        static const CastApp castDictionary[] = {
    {"233637DE", "YouTube"},
    {"CA5E8412", "Netflix"},
    {"CC1AD845", "Default Media Receiver"},
    {"CFE7FEDA", "Default Media Receiver"},
    {"E8C28D3C", "Backdrop"},
    {"674A0243", "Android TV Media Shell"},
    {"8E6C866D", "Android TV Guest Mode"},
    {"CC32E753", "Spotify"},
    {"9AC194DC", "Plex"},
    {"3927FA74", "BubbleUPnP/Spotify"},
    {"84912283", "Dashcast"},
    {"0F5096E8", "Chrome Mirroring"},
    {"85CDB22F", "Cast Streaming Audio"},
    {"B3DCF968", "Twitch"}
};
        
        int numApps = sizeof(castDictionary) / sizeof(castDictionary[0]);
        
        for (int i = 0; i < numApps; i++) {
            // Use a pointer that updates so we can find multiple of the same ID
            char* match = strstr(text, castDictionary[i].id);
            
            while (match != NULL) {
                int prefix_len = match - text;
                char* suffix = match + strlen(castDictionary[i].id);
                
                snprintf(temp_buffer, MAX_LEAK_STR_LEN, "%.*s[%s]%s", prefix_len, text, castDictionary[i].name, suffix);
                strncpy(text, temp_buffer, MAX_LEAK_STR_LEN);
                
                // Re-evaluate on the newly modified string to check for duplicates
                match = strstr(text, castDictionary[i].id);
            }
        }
        // Notice: The return; statement is completely removed.
        
        // Optional fallback: If it's a Cast packet but the App ID isn't in our dictionary, 
        // we can still clean it up slightly to just say it's an unknown Cast App
        // snprintf(temp_buffer, MAX_LEAK_STR_LEN, "Google Cast: Unknown App");
        // strncpy(text, temp_buffer, MAX_LEAK_STR_LEN);
        // return;
    }
}

// ---------------------------------------------------------
// SANITIZED ASCII COPY HELPER
// ---------------------------------------------------------
int copy_printable_ascii(const uint8_t* src, int len, char* dst, int max_len) {
    if (!src || !dst || max_len <= 0) return 0;
    int out_idx = 0;
    for (int i = 0; i < len && out_idx < max_len - 1; i++) {
        char c = src[i];
        dst[out_idx++] = (c >= 32 && c <= 126) ? c : '.';
    }
    dst[out_idx] = '\0';
    return out_idx;
}

// ---------------------------------------------------------
// LIGHTWEIGHT IPv6 FORMATTER (TFT-Friendly Notation)
// ---------------------------------------------------------
void format_ipv6_addr(const uint8_t* ip, char* buf, size_t max_len) {
    snprintf(buf, max_len, "%x:%x:%x:%x:%x:%x:%x:%x",
             (ip[0]<<8)|ip[1], (ip[2]<<8)|ip[3], (ip[4]<<8)|ip[5], (ip[6]<<8)|ip[7],
             (ip[8]<<8)|ip[9], (ip[10]<<8)|ip[11], (ip[12]<<8)|ip[13], (ip[14]<<8)|ip[15]);
}

// ---------------------------------------------------------
// HARDENED DNS NAME DECODER
// ---------------------------------------------------------
int decode_dns_name(const uint8_t* payload, int end_offset, int offset, char* out_name, int max_name_len) {
    if (!payload || !out_name || max_name_len <= 0) return -1;

    out_name[0] = '\0';

    int original_offset = offset;
    int out_idx = 0;
    bool jumped = false;
    int jumps = 0;

    while (offset < end_offset) {
        uint8_t len = payload[offset];

        if (len == 0) {
            if (!jumped) original_offset = offset + 1;
            break;
        }

        if ((len & 0xC0) == 0xC0) {
            if (offset + 1 >= end_offset || jumps >= 16) {
                out_name[out_idx] = '\0';
                return -1;
            }
            if (!jumped) original_offset = offset + 2;

            int ptr = ((len & 0x3F) << 8) | payload[offset + 1];

            if (ptr >= offset) {           // backward-only
                out_name[out_idx] = '\0';
                return -1;
            }

            offset = ptr;
            jumped = true;
            jumps++;
            continue;
        }

        if (len > 63 || offset + 1 > end_offset || len > end_offset - offset - 1) {
            out_name[out_idx] = '\0';
            return -1;
        }

        offset++;
        if (out_idx > 0 && out_idx < max_name_len - 1) out_name[out_idx++] = '.';

        for (int i = 0; i < len; i++) {
            if (out_idx < max_name_len - 1) {
                uint8_t c = payload[offset + i];
                out_name[out_idx++] = (c < 32 || c == 127) ? '.' : (char)c;
            }
        }

        offset += len;
        if (!jumped) original_offset = offset;
    }

    out_name[out_idx] = '\0';
    return original_offset;
}

/*
int decode_dns_name(const uint8_t* payload, int end_offset, int offset, char* out_name, int max_name_len) {
    if (!payload || !out_name || max_name_len <= 0) return -1; 

    int original_offset = offset;
    int out_idx = 0;
    bool jumped = false;
    int jumps = 0;

    while (offset < end_offset) {
        uint8_t len = payload[offset];
        if (len == 0) { 
            if (!jumped) original_offset = offset + 1;
            break;
        }
        
        if ((len & 0xC0) == 0xC0) { 
            if (offset + 1 >= end_offset || jumps > 16) return -1; 
            if (!jumped) original_offset = offset + 2; 
            
            int ptr = ((len & 0x3F) << 8) | payload[offset + 1];
            if (ptr >= end_offset) return -1; 
            
            offset = ptr;
            jumped = true;
            jumps++;
            continue;
        }
        
        if (len > 63 || offset + 1 > end_offset || len > end_offset - offset - 1) return -1;
        
        offset++;
        if (out_idx > 0 && out_idx < max_name_len - 1) out_name[out_idx++] = '.';
        
        for (int i = 0; i < len; i++) {
            if (out_idx < max_name_len - 1) {
                char c = payload[offset + i];
                out_name[out_idx++] = (c >= 32 && c <= 126) ? c : '.';
            }
        }
        
        offset += len;
        if (!jumped) original_offset = offset;
    }

    out_name[out_idx] = '\0';
    return original_offset; 
}

// Helper function to decode length-prefixed DNS/mDNS names and resolve pointers
int decode_dns_name(const uint8_t* payload, uint16_t length, int offset, char* out_name, int max_name_len) {
    int original_offset = offset;
    int out_idx = 0;
    bool jumped = false;
    int jumps = 0;

    while (offset < length) {
        uint8_t len = payload[offset];
        if (len == 0) { // End of name
            if (!jumped) original_offset++;
            break;
        }
        // If the top 2 bits are 11 (0xC0), it's a DNS compression pointer
        if ((len & 0xC0) == 0xC0) { 
            if (offset + 1 >= length || jumps > 5) break; // Prevent infinite loops
            if (!jumped) original_offset += 2; // The pointer is 2 bytes long
            
            // Calculate where the pointer is pointing to
            offset = ((len & 0x3F) << 8) | payload[offset + 1];
            jumped = true;
            jumps++;
            continue;
        }
        
        // Normal text label
        offset++;
        for (int i = 0; i < len; i++) {
            if (offset >= length) break;
            if (out_idx < max_name_len - 1) {
                out_name[out_idx++] = payload[offset];
            }
            offset++;
        }
        if (out_idx < max_name_len - 1) {
            out_name[out_idx++] = '.'; // Add a dot between labels
        }
        if (!jumped) original_offset = offset;
    }

    if (out_idx > 0 && out_name[out_idx - 1] == '.') out_idx--; // Strip trailing dot
    out_name[out_idx] = '\0';
    
    return jumped ? original_offset : offset;
}
*/



// ---------------------------------------------------------
// DHCPv4 (IPv4) PARSER
// Extracts Message Type, Primary DNS, and highest-value text 
// Priority: FQDN > Hostname > Domain > Vendor > Fallback ASCII
// ---------------------------------------------------------

bool parse_dhcp_v4(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (!payload || !out_text || max_len == 0 || length < 240) return false;
    
    if (payload[236] == 0x63 && payload[237] == 0x82 && 
        payload[238] == 0x53 && payload[239] == 0x63) {
        
        int offset = 240;
        char msg_type_str[16] = "UNK";
        
        char best_text[128] = {0};
        char dns_str[96] = {0};
        int current_priority = 99; 

        while (offset < length && payload[offset] != 255) {
            uint8_t opt_type = payload[offset];
            if (opt_type == 0) { offset++; continue; } 
            
            if (offset + 1 >= length) break;
            uint8_t opt_len = payload[offset + 1];
            if (offset + 2 + opt_len > length) break; 
            
            int opt_data = offset + 2;
            int this_priority = 99;
            char temp_buf[128] = {0};

            if (opt_type == 53 && opt_len == 1) {
                switch (payload[opt_data]) {
                    case 1: strlcpy(msg_type_str, "DISCOVER", sizeof(msg_type_str)); break;
                    case 2: strlcpy(msg_type_str, "OFFER", sizeof(msg_type_str)); break;
                    case 3: strlcpy(msg_type_str, "REQUEST", sizeof(msg_type_str)); break;
                    case 4: strlcpy(msg_type_str, "DECLINE", sizeof(msg_type_str)); break;
                    case 5: strlcpy(msg_type_str, "ACK", sizeof(msg_type_str)); break;
                    case 6: strlcpy(msg_type_str, "NAK", sizeof(msg_type_str)); break;
                    case 7: strlcpy(msg_type_str, "RELEASE", sizeof(msg_type_str)); break;
                    case 8: strlcpy(msg_type_str, "INFORM", sizeof(msg_type_str)); break;
                    default: snprintf(msg_type_str, sizeof(msg_type_str), "?%d", payload[opt_data]); break;
                }
            }
            else if (opt_type == 6 && opt_len >= 4 && (opt_len % 4 == 0)) {
                int dns_idx = 0;
                dns_idx += snprintf(dns_str, sizeof(dns_str), "DNS: ");
                for (int i = 0; i < opt_len; i += 4) {
                    if (dns_idx > 5 && dns_idx < (int)sizeof(dns_str) - 2) dns_str[dns_idx++] = ',';
                    if (dns_idx > (int)sizeof(dns_str) - 16) break; // Capacity safety
                    dns_idx += snprintf(dns_str + dns_idx, sizeof(dns_str) - dns_idx, "%d.%d.%d.%d",
                                        payload[opt_data + i], payload[opt_data + i + 1],
                                        payload[opt_data + i + 2], payload[opt_data + i + 3]);
                }
            }
            else if (opt_type == 81 && opt_len > 3) { 
                char fqdn_buf[64] = {0};
                int res = decode_dns_name(payload, opt_data + opt_len, opt_data + 3, fqdn_buf, sizeof(fqdn_buf));
                if (res >= 0 && fqdn_buf[0] != '\0') {
                    this_priority = 1;
                    snprintf(temp_buf, sizeof(temp_buf), "FQDN: %s", fqdn_buf);
                }
            }
            else if (opt_type == 12 && opt_len > 0) { 
                this_priority = 2; 
                snprintf(temp_buf, sizeof(temp_buf), "Host: ");
                copy_printable_ascii(&payload[opt_data], opt_len, temp_buf + 6, sizeof(temp_buf) - 6);
            }
            else if (opt_type == 60 && opt_len > 0) { 
                this_priority = 3; 
                snprintf(temp_buf, sizeof(temp_buf), "Vendor: ");
                copy_printable_ascii(&payload[opt_data], opt_len, temp_buf + 8, sizeof(temp_buf) - 8);
            }
            else if (opt_type == 61 && opt_len > 1) { 
                this_priority = 4;
                snprintf(temp_buf, sizeof(temp_buf), "ClientID: ");
                int out_idx = 10;
                for (int i = 1; i < opt_len && out_idx < (int)sizeof(temp_buf) - 3; i++) {
                    out_idx += snprintf(temp_buf + out_idx, sizeof(temp_buf) - out_idx, "%02X", payload[opt_data + i]);
                }
            }
            else if (opt_type == 55 && opt_len > 0) { 
                this_priority = 5;
                snprintf(temp_buf, sizeof(temp_buf), "PRL: ");
                int out_idx = 5;
                for (int i = 0; i < opt_len && out_idx < (int)sizeof(temp_buf) - 4; i++) {
                    out_idx += snprintf(temp_buf + out_idx, sizeof(temp_buf) - out_idx, "%d,", payload[opt_data + i]);
                }
                if (out_idx > 5) temp_buf[out_idx - 1] = '\0'; 
            }
            
            if (this_priority < current_priority && temp_buf[0] != '\0') {
                current_priority = this_priority;
                strlcpy(best_text, temp_buf, sizeof(best_text));
            }
            offset += 2 + opt_len;
        }

        // Always return true for a valid DHCP packet, even if it lacks text
        int written = snprintf(out_text, max_len, "DHCP [%s]", msg_type_str);
        if (best_text[0] != '\0' && written < (int)max_len) {
            written += snprintf(out_text + written, max_len - written, " %s", best_text);
        }
        if (dns_str[0] != '\0' && written < (int)max_len) {
            written += snprintf(out_text + written, max_len - written, " %s", dns_str);
        }
        return true;
    }
    return false;
}

// ---------------------------------------------------------
// DHCPv6 (IPv6) PARSER
// Extracts Message Type and highest-value text (FQDN > Vendor > ASCII)
// ---------------------------------------------------------
bool parse_dhcp_v6(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (!payload || !out_text || max_len == 0 || length < 4) return false; 
    
    uint8_t msg_type = payload[0];
    char msg_type_str[16] = "UNK";
    
    switch (msg_type) {
        case 1:  strlcpy(msg_type_str, "SOLICIT", sizeof(msg_type_str)); break;
        case 2:  strlcpy(msg_type_str, "ADVERT", sizeof(msg_type_str)); break;
        case 3:  strlcpy(msg_type_str, "REQUEST", sizeof(msg_type_str)); break;
        case 4:  strlcpy(msg_type_str, "CONFIRM", sizeof(msg_type_str)); break;
        case 5:  strlcpy(msg_type_str, "RENEW", sizeof(msg_type_str)); break;
        case 6:  strlcpy(msg_type_str, "REBIND", sizeof(msg_type_str)); break;
        case 7:  strlcpy(msg_type_str, "REPLY", sizeof(msg_type_str)); break;
        case 8:  strlcpy(msg_type_str, "RELEASE", sizeof(msg_type_str)); break;
        case 9:  strlcpy(msg_type_str, "DECLINE", sizeof(msg_type_str)); break;
        case 10: strlcpy(msg_type_str, "RECONFIG", sizeof(msg_type_str)); break;
        case 11: strlcpy(msg_type_str, "INFO-REQ", sizeof(msg_type_str)); break;
        case 12: strlcpy(msg_type_str, "RELAY-FWD", sizeof(msg_type_str)); break;
        case 13: strlcpy(msg_type_str, "RELAY-REP", sizeof(msg_type_str)); break;
        default: snprintf(msg_type_str, sizeof(msg_type_str), "?%d", msg_type); break;
    }

    // Short-circuit Relays: Do not parse outer options to avoid polluting fingerprint
    if (msg_type == 12 || msg_type == 13) {
        snprintf(out_text, max_len, "DHCPv6 [%s]", msg_type_str);
        return true;
    }

    int offset = 4;
    int current_priority = 99;
    char best_text[128] = {0};
    char dns_str[128] = {0};

    while (offset + 4 <= length) {
        uint16_t opt_code = (payload[offset] << 8) | payload[offset + 1];
        uint16_t opt_len = (payload[offset + 2] << 8) | payload[offset + 3];
        offset += 4;
        
        if (offset + opt_len > length) break; 
        
        int opt_data = offset;
        int this_priority = 99;
        char temp_buf[128] = {0};

        if (opt_code == 39 && opt_len > 1) { 
            char fqdn_buf[64] = {0};
            int res = decode_dns_name(payload, opt_data + opt_len, opt_data + 1, fqdn_buf, sizeof(fqdn_buf));
            if (res >= 0 && fqdn_buf[0] != '\0') {
                this_priority = 1;
                snprintf(temp_buf, sizeof(temp_buf), "FQDN: %s", fqdn_buf);
            }
        }
        else if (opt_code == 16 && opt_len > 4) { // Option 16: Structured Vendor Class
            this_priority = 2; 
            snprintf(temp_buf, sizeof(temp_buf), "Vendor: ");
            int out_idx = 8;
            int v_off = 4; // Skip 4-byte enterprise ID
            
            while (v_off + 2 <= opt_len) {
                uint16_t v_len = (payload[opt_data + v_off] << 8) | payload[opt_data + v_off + 1];
                v_off += 2;
                if (v_off + v_len > opt_len) break; // Truncated class data
                
                if (out_idx > 8 && out_idx < (int)sizeof(temp_buf) - 2) temp_buf[out_idx++] = ' ';
                out_idx += copy_printable_ascii(&payload[opt_data + v_off], v_len, temp_buf + out_idx, sizeof(temp_buf) - out_idx);
                v_off += v_len;
            }
        }
        else if (opt_code == 1 && opt_len > 0) { 
            this_priority = 3;
            snprintf(temp_buf, sizeof(temp_buf), "DUID: ");
            int out_idx = 6;
            for (int i = 0; i < opt_len && out_idx < (int)sizeof(temp_buf) - 3; i++) {
                out_idx += snprintf(temp_buf + out_idx, sizeof(temp_buf) - out_idx, "%02X", payload[opt_data + i]);
            }
        }
        else if (opt_code == 23 && opt_len >= 16 && (opt_len % 16 == 0)) { // Option 23: DNS Servers
            int dns_idx = 0;
            dns_idx += snprintf(dns_str, sizeof(dns_str), "DNS: ");
            for (int i = 0; i < opt_len; i += 16) {
                if (dns_idx > 5) dns_str[dns_idx++] = ',';
                if (dns_idx > (int)sizeof(dns_str) - 40) break; // Capacity safety
                
                char ip_buf[40];
                format_ipv6_addr(&payload[opt_data + i], ip_buf, sizeof(ip_buf));
                dns_idx += snprintf(dns_str + dns_idx, sizeof(dns_str) - dns_idx, "%s", ip_buf);
            }
        }

        if (this_priority < current_priority && temp_buf[0] != '\0') {
            current_priority = this_priority;
            strlcpy(best_text, temp_buf, sizeof(best_text));
        }
        offset += opt_len; 
    }

    int written = snprintf(out_text, max_len, "DHCPv6 [%s]", msg_type_str);
    if (best_text[0] != '\0' && written < (int)max_len) {
        written += snprintf(out_text + written, max_len - written, " %s", best_text);
    }
    if (dns_str[0] != '\0' && written < (int)max_len) {
        written += snprintf(out_text + written, max_len - written, " %s", dns_str);
    }
    return true;
}

void format_reverse_lookups(char* text, size_t max_len) {
    // 1. Entry Guard: Match defensive conventions applied everywhere else
    if (text == nullptr || max_len == 0) return;

    // 2. VLA Removal: Use compile-time constant to enforce stack ceiling
    char temp_buffer[MAX_LEAK_STR_LEN];
    
    // Ensure we don't write past our fixed buffer if max_len is somehow larger
    size_t safe_len = (max_len < MAX_LEAK_STR_LEN) ? max_len : MAX_LEAK_STR_LEN;

    // ----------------------------------------------------
    // 1. IPv4 Reverse Lookup (.in-addr.arpa)
    // ----------------------------------------------------
    char* in_addr = strstr(text, "in-addr");
    if (in_addr != nullptr) {
        int o1, o2, o3, o4;
        char* ptr = text;
        
        while (ptr < in_addr) {
            if (sscanf(ptr, "%d.%d.%d.%d.in-addr", &o4, &o3, &o2, &o1) == 4) {
                // 3. Octet Range Validation: Protect against integer overflow/garbage
                if (o1 >= 0 && o1 <= 255 && o2 >= 0 && o2 <= 255 &&
                    o3 >= 0 && o3 <= 255 && o4 >= 0 && o4 <= 255) {
                    
                    int prefix_len = ptr - text;
                    snprintf(temp_buffer, safe_len, "%.*sReverse Query: %d.%d.%d.%d", 
                             prefix_len, text, o1, o2, o3, o4);
                    strncpy(text, temp_buffer, safe_len);
                    return;
                }
            }
            ptr++;
        }
    }

    // ----------------------------------------------------
    // 2. IPv6 Reverse Lookup (.ip6.arpa)
    // ----------------------------------------------------
    char* ip6 = strstr(text, "ip6");
    if (ip6 != nullptr) {
        char nibbles[32];
        int n_idx = 0;
        char* ptr = ip6 - 1;
        
        // Walk backwards to collect exactly 32 hex nibbles
        while (ptr >= text && n_idx < 32) {
            char c = *ptr;
            if ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'F') || (c >= 'a' && c <= 'f')) {
                nibbles[n_idx++] = c; 
            }
            ptr--;
        }
        
        if (n_idx == 32) {
            char ipv6_str[40];
            int out_idx = 0;
            
            // Reconstruct the IPv6 address with colons
            for (int i = 0; i < 32; i++) {
                ipv6_str[out_idx++] = nibbles[i];
                if (i % 4 == 3 && i != 31) {
                    ipv6_str[out_idx++] = ':';
                }
            }
            ipv6_str[out_idx] = '\0';
            
            int prefix_len = (ptr + 1) - text;
            snprintf(temp_buffer, safe_len, "%.*s%s", prefix_len, text, ipv6_str);
            strncpy(text, temp_buffer, safe_len);
            return;
        }
    }
}

static inline uint16_t read_u16(const uint8_t* p, uint16_t len, int offset) {
    if (offset < 0 || offset + 1 >= len) return 0;
    return (p[offset] << 8) | p[offset + 1];
}

// Compresses a fully-expanded IPv6 address string (8 groups, e.g.
// "fe80:0000:0000:0000:1cee:da6a:322a:dd7a") into standard compressed
// form (e.g. "fe80::1cee:da6a:322a:dd7a") per RFC 5952: collapses only
// the single longest run of consecutive all-zero groups (length >= 2),
// and strips leading zeros within each remaining group.
// `full` and `out` must be different buffers.
static void compress_ipv6(const char* full, char* out, size_t out_size) {
    if (out_size == 0) return;
    out[0] = '\0';

    const char* g_start[8];
    int g_len[8];
    int g_count = 0;

    const char* p = full;
    while (*p && g_count < 8) {
        g_start[g_count] = p;
        const char* colon = strchr(p, ':');
        g_len[g_count] = colon ? (int)(colon - p) : (int)strlen(p);
        g_count++;
        if (!colon) break;
        p = colon + 1;
    }

    bool is_zero[8] = {false};
    for (int i = 0; i < g_count; i++) {
        bool z = true;
        for (int j = 0; j < g_len[i]; j++) {
            if (g_start[i][j] != '0') { z = false; break; }
        }
        is_zero[i] = z;
    }

    int best_start = -1, best_len = 0, run_start = -1, run_len = 0;
    for (int i = 0; i < g_count; i++) {
        if (is_zero[i]) {
            if (run_start == -1) run_start = i;
            run_len++;
            if (run_len > best_len) { best_len = run_len; best_start = run_start; }
        } else {
            run_start = -1;
            run_len = 0;
        }
    }
    bool collapse = best_len >= 2;
    int collapse_end = best_start + best_len;

    size_t idx = 0;
    auto put = [&](char c) { if (idx + 1 < out_size) out[idx++] = c; };

    for (int i = 0; i < g_count; ) {
        if (collapse && i == best_start) {
            put(':');
            put(':');
            i = collapse_end;
            continue;
        }
        int j = 0;
        while (j < g_len[i] - 1 && g_start[i][j] == '0') j++;
        for (; j < g_len[i]; j++) put(g_start[i][j]);
        i++;
        if (i < g_count && !(collapse && i == best_start)) put(':');
    }

    out[idx < out_size ? idx : out_size - 1] = '\0';
}

bool parse_dns_mdns(const uint8_t* payload, uint16_t length, bool is_mdns, char* out_text, size_t max_len) {
    if (length < 12) return false; 

    bool is_response = (payload[2] & 0x80) != 0;
    
    uint16_t qdcount = (payload[4] << 8) | payload[5];
    uint16_t ancount = (payload[6] << 8) | payload[7];
    uint16_t nscount = (payload[8] << 8) | payload[9];
    uint16_t arcount = (payload[10] << 8) | payload[11];

    char domains[MAX_LEAK_STR_LEN] = {0};
    int d_idx = 0;
    int valid_labels = 0;

    // CHANGED: process_name() replaced with a thin wrapper around
    // decode_dns_name(). This lambda keeps the same "append to shared
    // domains[] buffer" responsibility process_name used to have, but the
    // actual wire-walking/pointer-following is now in decode_dns_name().
    auto append_dns_name = [&](int start_offset) -> int {
    char name_buf[192];
    int result_offset = decode_dns_name(payload, length, start_offset, name_buf, sizeof(name_buf));

    if (result_offset < 0) {
        return -1;
    }

    int name_len = strlen(name_buf);
    if (name_len > 0 && d_idx + name_len + 3 < (int)sizeof(domains)) {
        if (valid_labels > 0) {
            domains[d_idx++] = ',';
            domains[d_idx++] = ' ';
        }
        memcpy(&domains[d_idx], name_buf, name_len);
        d_idx += name_len;
        valid_labels++;
    }

    return result_offset;
};


    int offset = 12;

    // 1. Process Questions
    for (int i = 0; i < qdcount && offset < length; i++) {
    offset = append_dns_name(offset);
    if (offset < 0) break;

    if (offset + 4 > length) {
        offset = length;
        break;
    }

    offset += 4;
    }

    // 2. Process Answers, Authorities, and Additionals
    int total_answers = ancount + nscount + arcount;
    for (int i = 0; i < total_answers && offset < length; i++) {
        offset = append_dns_name(offset);  // CHANGED
        
        if (offset + 10 <= length) {
            uint16_t rr_type = (payload[offset] << 8) | payload[offset+1];
            uint16_t rdlength = (payload[offset+8] << 8) | payload[offset+9];
            
            offset += 10;
            
            if (offset + rdlength > length) break;
            
            if (rr_type == 16) { // TXT — unchanged
                int txt_off = offset;
                int txt_end = offset + rdlength;
                
                while (txt_off < txt_end) {
                    uint8_t txt_len = payload[txt_off];
                    if (txt_off + 1 + txt_len > txt_end) break;
                    
                    bool is_printable = true;
                    for (int j = 0; j < txt_len; j++) {
                        uint8_t c = payload[txt_off + 1 + j];
                        if (c < 32 || c == 127) {
                            is_printable = false;
                            break;
                        }
                    }
                    
                    if (is_printable && txt_len > 0) {
                        if (d_idx + txt_len + 3 < sizeof(domains)) {
                            if (valid_labels > 0) {
                                domains[d_idx++] = ','; 
                                domains[d_idx++] = ' ';
                            }
                            memcpy(&domains[d_idx], &payload[txt_off+1], txt_len);
                            d_idx += txt_len;
                            valid_labels++;
                        }
                    }
                    txt_off += 1 + txt_len; 
                }
            }
            else if (rr_type == 1 && rdlength == 4) { // A — unchanged
                char ip_str[32];
                snprintf(ip_str, sizeof(ip_str), "[IP: %d.%d.%d.%d]", 
                         payload[offset], payload[offset+1], payload[offset+2], payload[offset+3]);
                int ip_len = strlen(ip_str);
                
                if (d_idx + ip_len + 3 < sizeof(domains)) {
                    if (valid_labels > 0) {
                        domains[d_idx++] = ','; 
                        domains[d_idx++] = ' ';
                    }
                    memcpy(&domains[d_idx], ip_str, ip_len);
                    d_idx += ip_len;
                    valid_labels++;
                }
            }
            // NEW: AAAA / IPv6
            else if (rr_type == 28 && rdlength == 16) {
                char raw_ip6[48];
                getIpString(6, &payload[offset], raw_ip6, sizeof(raw_ip6));

                char compressed_ip6[48];
                compress_ipv6(raw_ip6, compressed_ip6, sizeof(compressed_ip6));

                char out_str[56];
                snprintf(out_str, sizeof(out_str), "[IPv6: %s]", compressed_ip6);
                int out_len = strlen(out_str);

                if (d_idx + out_len + 3 < (int)sizeof(domains)) {
                    if (valid_labels > 0) { domains[d_idx++] = ','; domains[d_idx++] = ' '; }
                    memcpy(&domains[d_idx], out_str, out_len);
                    d_idx += out_len;
                    valid_labels++;
                }
            }
            /*
            else if (rr_type == 28 && rdlength == 16) {
                char ip6_str[48];
                getIpString(6, &payload[offset], ip6_str, sizeof(ip6_str));

                char* p;
                while ((p = strstr(ip6_str, ":0000:0000:")) != NULL) memmove(p + 1, p + 10, strlen(p + 10) + 1);
                while ((p = strstr(ip6_str, ":0000:")) != NULL) memmove(p + 1, p + 5, strlen(p + 5) + 1);

                char out_str[56];
                snprintf(out_str, sizeof(out_str), "[IPv6: %s]", ip6_str);
                int out_len = strlen(out_str);

                if (d_idx + out_len + 3 < (int)sizeof(domains)) {
                    if (valid_labels > 0) { domains[d_idx++] = ','; domains[d_idx++] = ' '; }
                    memcpy(&domains[d_idx], out_str, out_len);
                    d_idx += out_len;
                    valid_labels++;
                }
            }
            */
            else if (rr_type == 12 || rr_type == 5) { // PTR / CNAME
                append_dns_name(offset);  // CHANGED — return value still discarded, same as original
            }
            else if (rr_type == 33 && rdlength >= 7) { // SRV
                uint16_t srv_port = (payload[offset+4] << 8) | payload[offset+5];
                char port_str[32];
                snprintf(port_str, sizeof(port_str), "[Port: %u]", srv_port);
                int p_len = strlen(port_str);
                
                if (d_idx + p_len + 3 < sizeof(domains)) {
                    if (valid_labels > 0) {
                        domains[d_idx++] = ','; 
                        domains[d_idx++] = ' ';
                    }
                    memcpy(&domains[d_idx], port_str, p_len);
                    d_idx += p_len;
                    valid_labels++;
                }
                append_dns_name(offset + 6);  // CHANGED
            }

            offset += rdlength; 
        } else {
            break;
        }
    }

    domains[d_idx] = '\0';

    if (valid_labels > 0) {
        snprintf(out_text, max_len, "%s %s: %s", is_mdns ? "mDNS" : "DNS", is_response ? "Ans" : "Qry", domains);
        return true;
    }

    // 3. Salvaged TXT Record Sweeper — unchanged
    if (is_mdns) {
        int best_score = 0, best_s = 0, best_l = 0;
        int cur_s = 0, cur_l = 0;
        bool has_equals = false;

        for (int i = 12; i < length; i++) {
            char c = payload[i];
            if (c >= 32 && c <= 126) { 
                if (cur_l == 0) cur_s = i;
                if (c == '=') has_equals = true;
                cur_l++;
            } else {
                if (cur_l > 0) {
                    int cur_score = cur_l + (has_equals ? 15 : 0);
                    if (cur_score > best_score) {
                        best_score = cur_score; best_l = cur_l; best_s = cur_s;
                    }
                }
                cur_l = 0;
                has_equals = false;
            }
        }
        
        if (cur_l > 0) { 
            int cur_score = cur_l + (has_equals ? 15 : 0);
            if (cur_score > best_score) {
                best_score = cur_score; best_l = cur_l; best_s = cur_s;
            }
        }

        if (best_l >= 6 && best_score >= 15) {
            int copy_len = std::min(best_l, (int)max_len - 15);
            snprintf(out_text, max_len, "mDNS TXT: %.*s", copy_len, &payload[best_s]);
            return true;
        }
    }

    return false;
}

/*
bool parse_dns_mdns(const uint8_t* payload, uint16_t length, bool is_mdns, char* out_text, size_t max_len) {
    if (length < 12) return false; 

    bool is_response = (payload[2] & 0x80) != 0;
    
    // Read the DNS structural boundaries
    uint16_t qdcount = (payload[4] << 8) | payload[5];
    uint16_t ancount = (payload[6] << 8) | payload[7];
    uint16_t nscount = (payload[8] << 8) | payload[9];
    uint16_t arcount = (payload[10] << 8) | payload[11];

    char domains[256] = {0};
    int d_idx = 0;
    int valid_labels = 0;

    #define NOISE_MATCH(str) (len_byte == (sizeof(str) - 1) && memcmp(&payload[cur+1], str, sizeof(str) - 1) == 0)

    // A helper function to safely extract names and return the exact offset where the name ends
    auto process_name = [&](int start_offset) -> int {
        int cur = start_offset;
        bool in_domain = false;
        
        while (cur < length) {
            uint8_t len_byte = payload[cur];
            
            if (len_byte == 0x00) {
                return cur + 1; // End of name
            }
            if ((len_byte & 0xC0) == 0xC0) {
                return cur + 2; // End of name (Compression Pointer)
            }
            
            if (len_byte > 0 && len_byte <= 63 && cur + 1 + len_byte <= length) {
                bool is_printable = true;
                for (int j = 0; j < len_byte; j++) {
                    uint8_t c = payload[cur + 1 + j]; // Cast to unsigned to handle UTF-8 safely
                    if (c < 32 || c == 127) {         // Block control chars and DEL. Allow 128+ for UTF-8
                        is_printable = false;
                        break;
                    }
                }

                if (is_printable) {
                    bool is_noise = false;
                    //if (NOISE_MATCH("_tcp")) is_noise = true;
                    //else if (NOISE_MATCH("_udp")) is_noise = true;
                    //else if (NOISE_MATCH("local")) is_noise = true;
                    //else if (NOISE_MATCH("arpa")) is_noise = true;
                    //else if (NOISE_MATCH("in-addr")) is_noise = true;
                    //else if (NOISE_MATCH("ip6")) is_noise = true;
                    //else if (NOISE_MATCH("_appsvcprepair")) is_noise = true;
                    //else if (NOISE_MATCH("_companion-link")) is_noise = true;
                    //else if (NOISE_MATCH("_services")) is_noise = true;
                    //else if (NOISE_MATCH("_dns-sd")) is_noise = true;
                    //else if (NOISE_MATCH("_asquic")) is_noise = true; 
                    //else if (NOISE_MATCH("_apple-mobdev2")) is_noise = true; 

                    if (!is_noise) {
                        if (d_idx + len_byte + 3 < sizeof(domains)) {
                            bool is_duplicate = false;
                            if (valid_labels > 0 && !in_domain) {
                                if (d_idx >= len_byte && memcmp(&domains[d_idx - len_byte], &payload[cur+1], len_byte) == 0) {
                                    is_duplicate = true;
                                }
                            }

                            if (!is_duplicate) {
                                if (valid_labels > 0) {
                                    if (in_domain) domains[d_idx++] = '.';
                                    else {
                                        domains[d_idx++] = ','; 
                                        domains[d_idx++] = ' ';
                                    }
                                }
                                memcpy(&domains[d_idx], &payload[cur+1], len_byte);
                                d_idx += len_byte;
                                valid_labels++;
                                in_domain = true; 
                            } else {
                                in_domain = false;
                            }
                        }
                    } else {
                        in_domain = false; 
                    }
                } else {
                    in_domain = false; 
                }
                cur += len_byte + 1; // Jump to the next label in this name
            } else {
                return cur + 1; // Fallback for malformed bytes
            }
        }
        return cur;
    };

    // ==========================================
    // THE STATE MACHINE
    // ==========================================
    int offset = 12;

    // 1. Process Questions
    for (int i = 0; i < qdcount && offset < length; i++) {
        offset = process_name(offset);
        offset += 4; // Unconditionally skip QTYPE (2) and QCLASS (2)
    }

    // 2. Process Answers, Authorities, and Additionals
    int total_answers = ancount + nscount + arcount;
    for (int i = 0; i < total_answers && offset < length; i++) {
        offset = process_name(offset);
        
        if (offset + 10 <= length) {
            // CAPTURE THE RECORD TYPE BEFORE SKIPPING
            uint16_t rr_type = (payload[offset] << 8) | payload[offset+1];
            uint16_t rdlength = (payload[offset+8] << 8) | payload[offset+9];
            
            offset += 10; // Skip TYPE, CLASS, TTL, and RDLENGTH bytes
            
            if (offset + rdlength > length) break; // Memory safety check
            
            // ==========================================
            // RECORD EXTRACTORS
            // ==========================================
            if (rr_type == 16) { // 16 = TXT Record
                int txt_off = offset;
                int txt_end = offset + rdlength;
                
                while (txt_off < txt_end) {
                    uint8_t txt_len = payload[txt_off];
                    if (txt_off + 1 + txt_len > txt_end) break; // Bounds safety
                    
                    // Ensure the TXT chunk is printable ASCII or UTF-8
                    bool is_printable = true;
                    for (int j = 0; j < txt_len; j++) {
                        uint8_t c = payload[txt_off + 1 + j];
                        if (c < 32 || c == 127) {
                            is_printable = false;
                            break;
                        }
                    }
                    
                    if (is_printable && txt_len > 0) {
                        if (d_idx + txt_len + 3 < sizeof(domains)) {
                            if (valid_labels > 0) {
                                domains[d_idx++] = ','; 
                                domains[d_idx++] = ' ';
                            }
                            memcpy(&domains[d_idx], &payload[txt_off+1], txt_len);
                            d_idx += txt_len;
                            valid_labels++;
                        }
                    }
                    txt_off += 1 + txt_len; 
                }
            }
            else if (rr_type == 1 && rdlength == 4) { // 1 = A Record (IPv4)
                char ip_str[32];
                snprintf(ip_str, sizeof(ip_str), "[IP: %d.%d.%d.%d]", 
                         payload[offset], payload[offset+1], payload[offset+2], payload[offset+3]);
                int ip_len = strlen(ip_str);
                
                if (d_idx + ip_len + 3 < sizeof(domains)) {
                    if (valid_labels > 0) {
                        domains[d_idx++] = ','; 
                        domains[d_idx++] = ' ';
                    }
                    memcpy(&domains[d_idx], ip_str, ip_len);
                    d_idx += ip_len;
                    valid_labels++;
                }
            }
            else if (rr_type == 12 || rr_type == 5) { // 12 = PTR (Pointer), 5 = CNAME (Alias)
                process_name(offset); 
            }
            else if (rr_type == 33 && rdlength >= 7) { // 33 = SRV Record (Service Location)
                uint16_t srv_port = (payload[offset+4] << 8) | payload[offset+5];
                char port_str[32];
                snprintf(port_str, sizeof(port_str), "[Port: %u]", srv_port);
                int p_len = strlen(port_str);
                
                if (d_idx + p_len + 3 < sizeof(domains)) {
                    if (valid_labels > 0) {
                        domains[d_idx++] = ','; 
                        domains[d_idx++] = ' ';
                    }
                    memcpy(&domains[d_idx], port_str, p_len);
                    d_idx += p_len;
                    valid_labels++;
                }
                process_name(offset + 6); 
            }
            // ==========================================

            // Skip the RDATA block to maintain perfect alignment for the next record
            offset += rdlength; 
        } else {
            break; // Malformed packet boundary
        }
    }
    
    #undef NOISE_MATCH 

    domains[d_idx] = '\0';

    if (valid_labels > 0) {
        snprintf(out_text, max_len, "%s %s: %s", is_mdns ? "mDNS" : "DNS", is_response ? "Ans" : "Qry", domains);
        return true;
    }

    // ==========================================
    // 3. SALVAGED TXT RECORD SWEEPER (Fallback)
    // ==========================================
    if (is_mdns) {
        int best_score = 0, best_s = 0, best_l = 0;
        int cur_s = 0, cur_l = 0;
        bool has_equals = false;

        for (int i = 12; i < length; i++) {
            char c = payload[i];
            if (c >= 32 && c <= 126) { 
                if (cur_l == 0) cur_s = i;
                if (c == '=') has_equals = true;
                cur_l++;
            } else {
                if (cur_l > 0) {
                    int cur_score = cur_l + (has_equals ? 15 : 0);
                    if (cur_score > best_score) {
                        best_score = cur_score; best_l = cur_l; best_s = cur_s;
                    }
                }
                cur_l = 0;
                has_equals = false;
            }
        }
        
        if (cur_l > 0) { 
            int cur_score = cur_l + (has_equals ? 15 : 0);
            if (cur_score > best_score) {
                best_score = cur_score; best_l = cur_l; best_s = cur_s;
            }
        }

        if (best_l >= 6 && best_score >= 15) {
            int copy_len = std::min(best_l, (int)max_len - 15);
            snprintf(out_text, max_len, "mDNS TXT: %.*s", copy_len, &payload[best_s]);
            return true;
        }
    }

    return false;
}

bool parse_dns_mdns(const uint8_t* payload, uint16_t length, bool is_mdns, char* out_text, size_t max_len) {
    if (length < 12) return false; 

    bool is_response = (payload[2] & 0x80) != 0;

    // ==========================================
    // 1. THE SMART OSINT DOMAIN RIPPER 
    // ==========================================
    char domains[256] = {0};
    int d_idx = 0;
    int offset = 12; // Start immediately after the 12-byte DNS header
    int valid_labels = 0;
    bool in_domain = false; 

    // Helper macro to perfectly match strings and lengths at compile-time
    #define NOISE_MATCH(str) (len_byte == (sizeof(str) - 1) && memcmp(&payload[offset+1], str, sizeof(str) - 1) == 0)

    // Scan the ENTIRE payload, ignoring strict DNS structural boundaries
    while (offset < length) {
        uint8_t len_byte = payload[offset];

        if (len_byte == 0x00) {
            in_domain = false; 
            offset++;
            continue;
        }

        if ((len_byte & 0xC0) == 0xC0) {
            in_domain = false; 
            offset += 2;
            continue; 
        }

        if (len_byte > 0 && len_byte <= 63 && offset + 1 + len_byte <= length) {
            
            bool is_printable = true;
            for (int j = 0; j < len_byte; j++) {
                char c = payload[offset + 1 + j];
                if (c < 32 || c > 126) {
                    is_printable = false;
                    break;
                }
            }

            if (is_printable) {
                // The Macro-Hardened Noise Filter
                bool is_noise = false;
                //if (NOISE_MATCH("_tcp")) is_noise = true;
                //else if (NOISE_MATCH("_udp")) is_noise = true;
                //else if (NOISE_MATCH("local")) is_noise = true;
                //else if (NOISE_MATCH("arpa")) is_noise = true;
                //else if (NOISE_MATCH("in-addr")) is_noise = true;
                //else if (NOISE_MATCH("ip6")) is_noise = true;
                //else if (NOISE_MATCH("_appsvcprepair")) is_noise = true;
                //else if (NOISE_MATCH("_companion-link")) is_noise = true;
                //else if (NOISE_MATCH("_services")) is_noise = true;
                //else if (NOISE_MATCH("_dns-sd")) is_noise = true;

                if (!is_noise) {
                    if (d_idx + len_byte + 3 < sizeof(domains)) {
                        bool is_duplicate = false;
                        if (valid_labels > 0 && !in_domain) {
                            // Fast heuristic deduplication against the immediate prior string
                            if (d_idx >= len_byte && memcmp(&domains[d_idx - len_byte], &payload[offset+1], len_byte) == 0) {
                                is_duplicate = true;
                            }
                        }

                        if (!is_duplicate) {
                            if (valid_labels > 0) {
                                if (in_domain) domains[d_idx++] = '.';
                                else {
                                    domains[d_idx++] = ','; 
                                    domains[d_idx++] = ' ';
                                }
                            }
                            memcpy(&domains[d_idx], &payload[offset+1], len_byte);
                            d_idx += len_byte;
                            valid_labels++;
                            in_domain = true; 
                        } else {
                            in_domain = false;
                        }
                    }
                } else {
                    in_domain = false; 
                }
            } else {
                in_domain = false; 
            }
            offset += len_byte + 1; 
        } else {
            in_domain = false; 
            offset++;
        }
    }
    
    #undef NOISE_MATCH 

    domains[d_idx] = '\0';

    if (valid_labels > 0) {
        snprintf(out_text, max_len, "%s %s: %s", is_mdns ? "mDNS" : "DNS", is_response ? "Ans" : "Qry", domains);
        return true;
    }

    // ==========================================
    // 2. SALVAGED TXT RECORD SWEEPER (Fallback)
    // ==========================================
    if (is_mdns) {
        int best_score = 0, best_s = 0, best_l = 0;
        int cur_s = 0, cur_l = 0;
        bool has_equals = false;

        for (int i = 12; i < length; i++) {
            char c = payload[i];
            if (c >= 32 && c <= 126) { 
                if (cur_l == 0) cur_s = i;
                if (c == '=') has_equals = true;
                cur_l++;
            } else {
                if (cur_l > 0) {
                    int cur_score = cur_l + (has_equals ? 15 : 0);
                    if (cur_score > best_score) {
                        best_score = cur_score;
                        best_l = cur_l;
                        best_s = cur_s;
                    }
                }
                cur_l = 0;
                has_equals = false;
            }
        }
        
        if (cur_l > 0) { 
            int cur_score = cur_l + (has_equals ? 15 : 0);
            if (cur_score > best_score) {
                best_score = cur_score; best_l = cur_l; best_s = cur_s;
            }
        }

        if (best_l >= 6 && best_score >= 15) {
            int copy_len = std::min(best_l, (int)max_len - 15);
            snprintf(out_text, max_len, "mDNS TXT: %.*s", copy_len, &payload[best_s]);
            return true;
        }
    }

    return false;
}
*/
/*
bool parse_dns_mdns(const uint8_t* payload, uint16_t length, bool is_mdns, char* out_text, size_t max_len) {
    if (length < 12) return false; // Minimum size for a DNS header

    const char* p = (const char*)payload;
    
    // Check the QR (Query/Response) bit in the DNS Flags (Byte 2)
    bool is_response = (payload[2] & 0x80) != 0;

    // ==========================================
    // 1. mDNS TXT RECORD EXTRACTION
    // ==========================================
    if (is_mdns) {
        char device_name[64] = {0};
        char service_name[64] = {0};
        bool found_dnm = false;
        bool found_sn = false;

        // A. Targeted Apple AWDL Extraction
        for (int i = 12; i < length - 4; i++) {
            if (!found_dnm && memcmp(&p[i], "dnm=", 4) == 0) {
                int copy_len = 0;
                while (i + 4 + copy_len < length && copy_len < 63 && 
                       p[i + 4 + copy_len] >= 32 && p[i + 4 + copy_len] <= 126) {
                    copy_len++;
                }
                memcpy(device_name, &p[i + 4], copy_len);
                device_name[copy_len] = '\0';
                found_dnm = true;
            }
            else if (!found_sn && memcmp(&p[i], "sn=", 3) == 0) {
                int copy_len = 0;
                while (i + 3 + copy_len < length && copy_len < 63 && 
                       p[i + 3 + copy_len] >= 32 && p[i + 3 + copy_len] <= 126) {
                    copy_len++;
                }
                memcpy(service_name, &p[i + 3], copy_len);
                service_name[copy_len] = '\0';
                found_sn = true;
            }
        }

        if (found_dnm && found_sn) {
            snprintf(out_text, max_len, "Apple mDNS: %s [%s]", device_name, service_name);
            return true;
        } else if (found_dnm) {
            snprintf(out_text, max_len, "Apple mDNS: %s", device_name);
            return true;
        } else if (found_sn) {
            snprintf(out_text, max_len, "Apple mDNS: Svc=[%s]", service_name);
            return true;
        }

        // B. SALVAGED: Generic TXT Sweeper (For non-Apple devices)
        // If no Apple tags were found, sweep for the longest key=value string
        int best_s = 0, best_l = 0, cur_s = 0, cur_l = 0;
        bool has_equals = false;
        bool best_has_equals = false;

        for (int i = 12; i < length; i++) {
            char c = payload[i];
            if (c >= 32 && c <= 126) { // Printable ASCII
                if (cur_l == 0) cur_s = i;
                if (c == '=') has_equals = true;
                cur_l++;
                
                if (cur_l > best_l || (has_equals && !best_has_equals)) {
                    best_l = cur_l; 
                    best_s = cur_s;
                    best_has_equals = has_equals;
                }
            } else {
                cur_l = 0;
                has_equals = false;
            }
        }

        // Only trigger if we found a reasonably sized string with an equals sign
        if (best_l >= 6 && best_has_equals) {
            int copy_len = std::min(best_l, (int)max_len - 15);
            snprintf(out_text, max_len, "mDNS TXT: %.*s", copy_len, &payload[best_s]);
            return true;
        }
    }

    // ==========================================
    // 2. STANDARD DNS DOMAIN EXTRACTION (Fallback)
    // ==========================================
    char domain[128] = {0};
    int d_idx = 0;
    int i = 12; // Start immediately after DNS header
    
    while (i < length && p[i] != 0x00 && d_idx < sizeof(domain) - 2) {
        uint8_t label_len = p[i];
        
        // Abort if we hit a DNS compression pointer (0xC0) to prevent infinite loops
        if ((label_len & 0xC0) == 0xC0) {
            break; 
        }

        if (label_len > 0 && label_len <= 63 && (i + 1 + label_len) < length) {
            if (d_idx > 0) domain[d_idx++] = '.';
            memcpy(&domain[d_idx], &p[i + 1], label_len);
            d_idx += label_len;
            i += label_len + 1;
        } else {
            break; // Malformed or out of bounds
        }
    }
    
    domain[d_idx] = '\0';

    if (d_idx > 0) {
        // SALVAGED: The Noise Filter
        //if (strstr(domain, "in-addr.arpa") || 
        //    strstr(domain, "ip6.arpa") || 
        //    strstr(domain, "_tcp.local") || 
        //    strstr(domain, "_udp.local")) {
        //    return false; // Silently drop noisy infrastructure queries
        //}

        if (is_mdns) {
            snprintf(out_text, max_len, "mDNS %s: %s", is_response ? "Ans" : "Qry", domain);
        } else {
            snprintf(out_text, max_len, "DNS %s: %s", is_response ? "Ans" : "Qry", domain);
        }
        return true;
    }

    return false;
}
*/
/*
bool parse_dns_mdns(const uint8_t* payload, uint16_t length, uint16_t dst_port, char* out_text, size_t max_len) {
    if (length < 12) return false;

    uint16_t qdcount = (payload[4] << 8) | payload[5];
    uint16_t ancount = (payload[6] << 8) | payload[7];
    if (qdcount == 0 && ancount == 0) return false;

    const char* proto = (dst_port == 5353) ? "mDNS" : "DNS";
    int written = snprintf(out_text, max_len, "%s %uQ,%uA:", proto, qdcount, ancount);
    int cursor = 12;

    // --- Questions ---
    for (uint16_t q = 0; q < qdcount && cursor < length && written < (int)max_len - 1; q++) {
        char qname[96] = {0};
        int next = decode_dns_name(payload, length, cursor, qname, sizeof(qname));
        if (next <= cursor) break;           // malformed name, bail safely
        cursor = next;

        uint16_t qtype = read_u16(payload, length, cursor);
        cursor += 4;                          // QTYPE + QCLASS

        // --- RESCUED: The Noise Filter ---
        // Ignore generic local arpa/service queries as they clutter the screen.
        // We still advanced the cursor (above) so the parser doesn't break!
        bool is_noisy = (strstr(qname, "in-addr.arpa") || 
                         strstr(qname, "ip6.arpa") || 
                         strstr(qname, "_tcp.local") || 
                         strstr(qname, "_udp.local"));

        if (!is_noisy) {
            int n = snprintf(out_text + written, max_len - written, " Q:%s(%u)", qname, qtype);
            written = std::min((int)max_len - 1, written + n);
        }
    }

    // --- Answers ---
    for (uint16_t a = 0; a < ancount && cursor < length && written < (int)max_len - 1; a++) {
        char aname[96] = {0};
        int next = decode_dns_name(payload, length, cursor, aname, sizeof(aname));
        if (next <= cursor) break;
        cursor = next;

        uint16_t atype  = read_u16(payload, length, cursor);
        uint16_t rdlen  = read_u16(payload, length, cursor + 8);
        int rdata_off   = cursor + 10;         // past TYPE(2)+CLASS(2)+TTL(4)+RDLENGTH(2)

        if (rdata_off + rdlen <= length) {
            if (atype == 12) {  
                // --- PTR Record (Standard Reverse Lookup) ---
                char target[96] = {0};
                decode_dns_name(payload, length, rdata_off, target, sizeof(target));
                int n = snprintf(out_text + written, max_len - written, " A:%s->%s", aname, target);
                written = std::min((int)max_len - 1, written + n);
                
            } else if (atype == 16 && dst_port == 5353) { 
                // --- RESCUED: The TXT Record Sweeper (mDNS Specs) ---
                // Targeted ASCII sweep looking for key=value pairs in the RDATA payload
                int best_s = 0, best_l = 0, cur_s = 0, cur_l = 0;
                bool has_equals = false;
                bool best_has_equals = false;

                for (int i = rdata_off; i < rdata_off + rdlen; i++) {
                    char c = payload[i];
                    if (c >= 32 && c <= 126) { // Printable ASCII
                        if (cur_l == 0) cur_s = i;
                        if (c == '=') has_equals = true;
                        cur_l++;
                        
                        if (cur_l > best_l || (has_equals && !best_has_equals)) {
                            best_l = cur_l; 
                            best_s = cur_s;
                            best_has_equals = has_equals;
                        }
                    } else {
                        cur_l = 0;
                        has_equals = false;
                    }
                }

                if (best_l >= 6) {
                    // Safely copy the discovered TXT string into the UI buffer
                    int copy_len = std::min(best_l, (int)(max_len - written - 15));
                    if (copy_len > 0) {
                        int n = snprintf(out_text + written, max_len - written, " TXT:%.*s", copy_len, &payload[best_s]);
                        written = std::min((int)max_len - 1, written + n);
                    }
                }
            } else {
                // --- Standard Fallback for A/AAAA/Other Records ---
                int n = snprintf(out_text + written, max_len - written, " A:%s(t%u)", aname, atype);
                written = std::min((int)max_len - 1, written + n);
            }
        }

        cursor = rdata_off + rdlen;   // always skip the full RDATA, decoded or not
    }

    format_reverse_lookups(out_text, max_len);
    return true;
}
*/
/*
bool parse_dns_mdns(const uint8_t* payload, uint16_t length, uint16_t dst_port, char* out_text, size_t max_len) {
    if (length < 12) return false;

    uint16_t qdcount = (payload[4] << 8) | payload[5];
    uint16_t ancount = (payload[6] << 8) | payload[7];
    if (qdcount == 0 && ancount == 0) return false;

    const char* proto = (dst_port == 5353) ? "mDNS" : "DNS";
    int written = snprintf(out_text, max_len, "%s %uQ,%uA:", proto, qdcount, ancount);
    int cursor = 12;

    // --- Questions ---
    for (uint16_t q = 0; q < qdcount && cursor < length && written < (int)max_len - 1; q++) {
        char qname[96] = {0};
        int next = decode_dns_name(payload, length, cursor, qname, sizeof(qname));
        if (next <= cursor) break;           // malformed name, bail safely
        cursor = next;

        uint16_t qtype = read_u16(payload, length, cursor);
        cursor += 4;                          // QTYPE + QCLASS

        int n = snprintf(out_text + written, max_len - written, " Q:%s(%u)", qname, qtype);
        written = std::min((int)max_len - 1, written + n);
    }

    // --- Answers ---
    for (uint16_t a = 0; a < ancount && cursor < length && written < (int)max_len - 1; a++) {
        char aname[96] = {0};
        int next = decode_dns_name(payload, length, cursor, aname, sizeof(aname));
        if (next <= cursor) break;
        cursor = next;

        uint16_t atype  = read_u16(payload, length, cursor);
        uint16_t rdlen  = read_u16(payload, length, cursor + 8);
        int rdata_off   = cursor + 10;         // past TYPE(2)+CLASS(2)+TTL(4)+RDLENGTH(2)

        if (atype == 12 && rdata_off < length) {  // PTR
            char target[96] = {0};
            decode_dns_name(payload, length, rdata_off, target, sizeof(target));
            int n = snprintf(out_text + written, max_len - written, " A:%s->%s", aname, target);
            written = std::min((int)max_len - 1, written + n);
        } else {
            int n = snprintf(out_text + written, max_len - written, " A:%s(t%u)", aname, atype);
            written = std::min((int)max_len - 1, written + n);
        }

        cursor = rdata_off + rdlen;   // always skip the full RDATA, decoded or not
    }

    format_reverse_lookups(out_text, max_len);
    return true;
}

// ---------------------------------------------------------
// DNS & mDNS PARSER (Ports 53, 5353)
// Extracts requested domains, local hostnames, and TXT specs
// ---------------------------------------------------------
bool parse_dns_mdns(const uint8_t* payload, uint16_t length, uint16_t dst_port, char* out_text, size_t max_len) {
    if (length < 12) return false; // DNS header is exactly 12 bytes

    uint16_t qdcount = (payload[4] << 8) | payload[5]; // Question count
    uint16_t ancount = (payload[6] << 8) | payload[7]; // Answer count

    const char* proto = (dst_port == 5353) ? "mDNS" : "DNS";

    // 1. If it's a Query, extract the domain being asked for
    if (qdcount > 0) {
        char qname[80] = {0};
        decode_dns_name(payload, length, 12, qname, sizeof(qname));
        
        if (qname[0] != '\0') {
            // Ignore generic local arpa/service queries as they clutter the screen
            if (strstr(qname, "in-addr.arpa") || strstr(qname, "ip6.arpa") || strstr(qname, "_tcp.local")) {
                // If it's a generic service scan, fall through and look for TXT answers instead
            } else {
                snprintf(out_text, max_len, "%s: %s", proto, qname);
                return true;
            }
        }
    }
    
    // 2. If it's an mDNS Reply, devices leak specs in TXT records.
    // Instead of complex DNS tree parsing, we use a targeted ASCII sweep 
    // looking for key=value pairs (like "model=MacBook")
    if (dst_port == 5353 && ancount > 0) {
        int best_s = 0, best_l = 0, cur_s = 0, cur_l = 0;
        bool has_equals = false;
        bool best_has_equals = false;

        for (int i = 12; i < length; i++) {
            char c = payload[i];
            if (c >= 32 && c <= 126) {
                if (cur_l == 0) cur_s = i;
                if (c == '=') has_equals = true;
                cur_l++;
                
                // Prioritize strings containing '=' (Standard TXT spec format)
                if (cur_l > best_l || (has_equals && !best_has_equals)) {
                    best_l = cur_l; 
                    best_s = cur_s;
                    best_has_equals = has_equals;
                }
            } else {
                cur_l = 0;
                has_equals = false;
            }
        }

        if (best_l >= 6) {
            snprintf(out_text, max_len, "mDNS Info: %.*s", best_l, &payload[best_s]);
            return true;
        }
    }

    return false;
}
*/

// --- Memory-Safe HTTP Header Helper ---
static bool extract_header(const char* p, uint16_t length, const char* target, char* out_buf, size_t max_out) {
    size_t t_len = strlen(target);
    if (length <= t_len) return false;

    for (int i = 0; i <= length - t_len; i++) {
        // Enforce boundary: Header must start at the beginning of the payload OR immediately after a newline
        if (i == 0 || p[i-1] == '\n') {
            
            // Case-insensitive match (e.g., "Host:", "host:", "HOST:")
            bool match = true;
            for (size_t j = 0; j < t_len; j++) {
                char c1 = p[i+j];
                char c2 = target[j];
                if (c1 >= 'A' && c1 <= 'Z') c1 += 32; // tolower
                if (c2 >= 'A' && c2 <= 'Z') c2 += 32; // tolower
                if (c1 != c2) {
                    match = false;
                    break;
                }
            }
            
            if (match) {
                // Slide past the header name and any subsequent spaces/tabs
                const char* val_start = &p[i + t_len];
                while (val_start < p + length && (*val_start == ' ' || *val_start == '\t')) {
                    val_start++;
                }
                
                // Read until end of line or end of payload
                const char* val_end = val_start;
                while (val_end < p + length && *val_end != '\r' && *val_end != '\n') {
                    val_end++;
                }
                
                int copy_len = val_end - val_start;
                if (copy_len > 0) {
                    copy_len = std::min(copy_len, (int)max_out - 1);
                    memcpy(out_buf, val_start, copy_len);
                    out_buf[copy_len] = '\0';
                    return true;
                }
            }
        }
    }
    return false;
}

// --- The Upgraded Parser ---
bool parse_http_host(
    const uint8_t* payload,
    uint16_t length,
    char* out_text,
    size_t max_len
) {
    if (length < 16 ||
        payload == nullptr ||
        out_text == nullptr ||
        max_len < 20) {
        return false;
    }

    const char* p =
        reinterpret_cast<const char*>(payload);

    char first_line[128] = {0};
    char host_domain[64] = {0};
    char user_agent[64]  = {0};
    char auth_basic[64]  = {0};

    // -----------------------------------------------------
    // 1. REQUEST START LINE
    //
    // Only parse actual HTTP requests.
    // HTTP responses deliberately return false so they can
    // continue to the generic printable-run extractor.
    // -----------------------------------------------------

    if (memcmp(p, "GET ", 4) == 0 ||
        memcmp(p, "POST ", 5) == 0 ||
        memcmp(p, "PUT ", 4) == 0 ||
        memcmp(p, "HEAD ", 5) == 0) {

        const char* line_end =
            static_cast<const char*>(
                memchr(p, '\n', length)
            );

        if (!line_end) {
            return false;
        }

        size_t flen =
            static_cast<size_t>(line_end - p);

        if (flen > 0 && p[flen - 1] == '\r') {
            flen--;
        }

        size_t copy_len =
            std::min(
                flen,
                sizeof(first_line) - 1
            );

        memcpy(
            first_line,
            p,
            copy_len
        );

        first_line[copy_len] = '\0';

    } else {
        // HTTP response or unknown payload.
        // Deliberately fall through to catch-all.
        return false;
    }

    // -----------------------------------------------------
    // 2. DEEP HEADER EXTRACTION
    // -----------------------------------------------------

    bool found_host =
        extract_header(
            p,
            length,
            "Host:",
            host_domain,
            sizeof(host_domain)
        );

    bool found_ua =
        extract_header(
            p,
            length,
            "User-Agent:",
            user_agent,
            sizeof(user_agent)
        );

    bool found_auth =
        extract_header(
            p,
            length,
            "Authorization: Basic",
            auth_basic,
            sizeof(auth_basic)
        );

    // -----------------------------------------------------
    // 3. COMPACT UI STRING
    // -----------------------------------------------------

    char temp_out[MAX_LEAK_STR_LEN] = {0};

    // IMPORTANT:
    // Preserve "HTTP/1.1" in the request line so the
    // existing High-Value Triage can recognize HTTP.
    snprintf(
        temp_out,
        sizeof(temp_out),
        "%s",
        first_line
    );

    char chunk[128];

    if (found_host) {
        snprintf(
            chunk,
            sizeof(chunk),
            " [Host: %s]",
            host_domain
        );

        strncat(
            temp_out,
            chunk,
            sizeof(temp_out) - strlen(temp_out) - 1
        );
    }

    if (found_ua) {
        snprintf(
            chunk,
            sizeof(chunk),
            " [UA: %s]",
            user_agent
        );

        strncat(
            temp_out,
            chunk,
            sizeof(temp_out) - strlen(temp_out) - 1
        );
    }

    if (found_auth) {
        snprintf(
            chunk,
            sizeof(chunk),
            " [Auth: Basic %s]",
            auth_basic
        );

        strncat(
            temp_out,
            chunk,
            sizeof(temp_out) - strlen(temp_out) - 1
        );
    }

    snprintf(
        out_text,
        max_len,
        "%s",
        temp_out
    );

    return true;
}
/*
bool parse_http_host(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // --- STEP 0: Standard Entry Guard ---
    if (length < 16 || payload == nullptr || out_text == nullptr || max_len < 20) return false;

    const char* p = (const char*)payload;
    
    char method_uri[64] = {0};
    char host_domain[64] = {0};
    char user_agent[64] = {0};
    char auth_basic[64] = {0};
    
    bool found_req = false;

    // --- STEP 1: Extract Method and URI ---
    if (memcmp(p, "GET ", 4) == 0 || memcmp(p, "POST ", 5) == 0 || 
        memcmp(p, "PUT ", 4) == 0 || memcmp(p, "HEAD ", 5) == 0) {
        
        const char* uri_end = nullptr;
        for (int i = 0; i < length - 6 && i < 256; i++) {
            if (p[i] == ' ' && p[i+1] == 'H' && p[i+2] == 'T' && 
                p[i+3] == 'T' && p[i+4] == 'P' && p[i+5] == '/') {
                uri_end = &p[i];
                break;
            }
        }

        if (uri_end) {
            int req_len = uri_end - p;
            int copy_len = std::min(req_len, (int)sizeof(method_uri) - 1);
            memcpy(method_uri, p, copy_len);
            method_uri[copy_len] = '\0';
            found_req = true;
        }
    }

    // --- STEP 2: Deep Extraction ---
    bool found_host = extract_header(p, length, "Host:", host_domain, sizeof(host_domain));
    bool found_ua   = extract_header(p, length, "User-Agent:", user_agent, sizeof(user_agent));
    bool found_auth = extract_header(p, length, "Authorization: Basic", auth_basic, sizeof(auth_basic));

    if (!found_req && !found_host && !found_ua && !found_auth) {
        return false;
    }

    // --- STEP 3: UI Formatting Assembly ---
    char temp_out[256] = {0}; 
    
    if (found_req) snprintf(temp_out, sizeof(temp_out), "HTTP: %s", method_uri);
    else snprintf(temp_out, sizeof(temp_out), "HTTP:");

    char chunk[128];
    if (found_host) {
        snprintf(chunk, sizeof(chunk), " [Host: %s]", host_domain);
        strncat(temp_out, chunk, sizeof(temp_out) - strlen(temp_out) - 1);
    }
    if (found_ua) {
        snprintf(chunk, sizeof(chunk), " [UA: %s]", user_agent);
        strncat(temp_out, chunk, sizeof(temp_out) - strlen(temp_out) - 1);
    }
    if (found_auth) {
        snprintf(chunk, sizeof(chunk), " [Auth: Basic %s]", auth_basic);
        strncat(temp_out, chunk, sizeof(temp_out) - strlen(temp_out) - 1);
    }

    snprintf(out_text, max_len, "%s", temp_out);
    return true;
}
*/
/*
bool parse_http_host(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length < 16) return false;

    const char* p = (const char*)payload;
    const char* payload_end = p + length;
    
    char method_uri[64] = {0};
    char host_domain[64] = {0};
    bool found_req = false;
    bool found_host = false;

    // --- STEP 1: Extract Method and URI ---
    // Only attempt this if the payload cleanly starts with a standard HTTP method
    if (memcmp(p, "GET ", 4) == 0 || memcmp(p, "POST ", 5) == 0 || 
        memcmp(p, "PUT ", 4) == 0 || memcmp(p, "HEAD ", 5) == 0) {
        
        // Scan forward to find the " HTTP/" string, which always terminates the URI
        const char* uri_end = nullptr;
        for (int i = 0; i < length - 6 && i < 256; i++) {
            if (p[i] == ' ' && p[i+1] == 'H' && p[i+2] == 'T' && 
                p[i+3] == 'T' && p[i+4] == 'P' && p[i+5] == '/') {
                uri_end = &p[i];
                break;
            }
        }

        if (uri_end) {
            int req_len = uri_end - p;
            int copy_len = std::min(req_len, (int)sizeof(method_uri) - 1);
            memcpy(method_uri, p, copy_len);
            method_uri[copy_len] = '\0';
            found_req = true;
        }
    }

    // --- STEP 2: Extract Host Header ---
    // Sliding window search for "Host: " (preserves fragmentation resilience)
    const char* host_start = nullptr;
    for (int i = 0; i < length - 6; i++) {
        if ((p[i] == 'H' || p[i] == 'h') && 
            (p[i+1] == 'o' || p[i+1] == 'O') && 
            (p[i+2] == 's' || p[i+2] == 'S') && 
            (p[i+3] == 't' || p[i+3] == 'T') && 
            p[i+4] == ':' && (p[i+5] == ' ' || p[i+5] == '\t')) {
            
            host_start = &p[i+5];
            
            // Fast-forward past any extra spaces after the colon
            while (host_start < payload_end && (*host_start == ' ' || *host_start == '\t')) {
                host_start++;
            }
            break;
        }
    }

    if (host_start) {
        const char* host_end = host_start;
        // Scan until the carriage return or newline
        while (host_end < payload_end && *host_end != '\r' && *host_end != '\n') {
            host_end++;
        }
        int name_len = host_end - host_start;
        if (name_len > 0) {
            int copy_len = std::min(name_len, (int)sizeof(host_domain) - 1);
            memcpy(host_domain, host_start, copy_len);
            host_domain[copy_len] = '\0';
            found_host = true;
        }
    }

    // --- STEP 3: UI Formatting Assembly ---
    // Safely combine the intelligence based on what was successfully extracted
    if (found_req && found_host) {
        snprintf(out_text, max_len, "HTTP: %s [%s]", method_uri, host_domain);
        return true;
    } else if (found_req) {
        snprintf(out_text, max_len, "HTTP Req: %s", method_uri);
        return true;
    } else if (found_host) {
        snprintf(out_text, max_len, "HTTP Host: %s", host_domain);
        return true;
    }

    return false;
}
*/

// --- Helper: Trim Whitespace ---
// Strips leading and trailing whitespace/newlines from extracted XML values
static void trim_ascii(char* s) {
    if (!s || !*s) return;

    char* start = s;
    while (*start && isspace((unsigned char)*start))
        start++;

    if (start != s)
        memmove(s, start, strlen(start) + 1);

    size_t n = strlen(s);
    while (n > 0 && isspace((unsigned char)s[n - 1]))
        s[--n] = '\0';
}

// --- Memory-Safe XML Value Extractor ---
static bool extract_xml_value(const char* p, uint16_t length, const char* tag_suffix, char* out_buf, size_t max_out) {
    // Hardened entry guard
    if (!p || !tag_suffix || !out_buf || max_out < 2) return false;

    size_t t_len = strlen(tag_suffix);
    if (length < t_len) return false;

    const char* end = p + length; 

    for (int i = 0; i <= length - t_len; i++) {
        bool match = true;
        for (size_t j = 0; j < t_len; j++) {
            if (p[i+j] != tag_suffix[j]) {
                match = false;
                break;
            }
        }
        
        // Fully tightened heuristic: strictly requires the start of a tag or namespace
        if (match && (i == 0 || p[i-1] == '<' || p[i-1] == ':')) {
            const char* val_start = &p[i + t_len];
            const char* val_end = val_start;
            
            while (val_end < end && *val_end != '<') {
                val_end++;
            }
            
            int copy_len = val_end - val_start;
            
            // Explicit defensive check
            if (copy_len <= 0) continue;
            
            copy_len = std::min(copy_len, (int)max_out - 1);
            memcpy(out_buf, val_start, copy_len);
            out_buf[copy_len] = '\0';
            return true;
        }
    }
    return false;
}

// --- The WS-Discovery Parser ---
bool parse_ws_discovery(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length < 20 || payload == nullptr || out_text == nullptr || max_len < 20) return false;

    const char* p = (const char*)payload;

    char action_val[128] = {0};   // unchanged — action URIs are a fixed enum-like set, rarely long
char types_val[64]   = {0};   // unchanged — same reasoning
char xaddrs_val[192] = {0};   // was 96 — the most likely actual truncation point
char scopes_val[192] = {0};   // was 128 — ONVIF scope lists can carry several space-separated scope URIs (name, hardware, location, profile), similar risk to xaddrs

    bool found_action = extract_xml_value(p, length, "Action>", action_val, sizeof(action_val));
    bool found_types  = extract_xml_value(p, length, "Types>", types_val, sizeof(types_val));
    bool found_xaddrs = extract_xml_value(p, length, "XAddrs>", xaddrs_val, sizeof(xaddrs_val));
    bool found_scopes = extract_xml_value(p, length, "Scopes>", scopes_val, sizeof(scopes_val));

    // Trim XML whitespace artifacts from all successful extractions
    if (found_action) trim_ascii(action_val);
    if (found_types)  trim_ascii(types_val);
    if (found_xaddrs) trim_ascii(xaddrs_val);
    if (found_scopes) trim_ascii(scopes_val);

    if (!found_types && !found_xaddrs && !found_scopes) {
        return false;
    }

    // --- STEP 1: Determine the Action Type ---
    const char* msg_type = "WS-Discovery";
    if (found_action) {
        if (strstr(action_val, "ProbeMatch")) msg_type = "WS-Discovery [ProbeMatch]";
        else if (strstr(action_val, "Probe")) msg_type = "WS-Discovery [Probe]";
        else if (strstr(action_val, "Hello")) msg_type = "WS-Discovery [Hello]";
        else if (strstr(action_val, "Bye")) msg_type = "WS-Discovery [Bye]";
    }

    // --- STEP 2: UI Formatting Assembly ---
    char temp_out[MAX_LEAK_STR_LEN] = {0}; // was 256
    snprintf(temp_out, sizeof(temp_out), "%s:", msg_type);
    
    char chunk[128];

    if (found_types) {
        char type_buf[64] = {0};
        const char* type_start = types_val;
        
        char* colon = strchr(types_val, ':');
        if (colon) type_start = colon + 1;
        
        // Bulletproof QName isolation handling all XML whitespace chars
        size_t type_len = strcspn(type_start, " \t\r\n");
        if (type_len >= sizeof(type_buf)) type_len = sizeof(type_buf) - 1;
        
        memcpy(type_buf, type_start, type_len);
        type_buf[type_len] = '\0';
        
        snprintf(chunk, sizeof(chunk), " [Type: %s]", type_buf);
        strncat(temp_out, chunk, sizeof(temp_out) - strlen(temp_out) - 1);
    }
    
    if (found_scopes) {
        const char* prefix = "onvif://www.onvif.org/name/";
        size_t prefix_len = strlen(prefix);
        char* name_ptr = strstr(scopes_val, prefix);
        
        if (name_ptr) {
            name_ptr += prefix_len; 
            
            char clean_name[32] = {0};
            int idx = 0;
            while (name_ptr[idx] != ' ' && name_ptr[idx] != '\0' && idx < 31) {
                clean_name[idx] = name_ptr[idx];
                idx++;
            }
            snprintf(chunk, sizeof(chunk), " [Name: %s]", clean_name);
            strncat(temp_out, chunk, sizeof(temp_out) - strlen(temp_out) - 1);
        }
    }

    if (found_xaddrs) {
        snprintf(chunk, sizeof(chunk), " [URL: %s]", xaddrs_val);
        strncat(temp_out, chunk, sizeof(temp_out) - strlen(temp_out) - 1);
    }

    snprintf(out_text, max_len, "%s", temp_out);
    return true;
}

// ============================================================================
// UPGRADED X.509 CERTIFICATE & IDENTITY EXTRACTOR
// ============================================================================
// Scans raw TLS Handshakes / A-MSDU blobs for ASN.1 DER structures.
// Extracts Subject (Target Server), Issuer (CA), Geographic Location, 
// SANs, URLs, Emails, and Establishment Dates.
// ============================================================================
bool parse_tls_cert(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length < 24 || payload == nullptr || out_text == nullptr || max_len == 0) {
        return false;
    }

    char subject_cn[64]   = {0};
    char subject_org[64]  = {0};
    char subject_loc[32]  = {0};
    char subject_state[32]= {0};
    char subject_c[8]     = {0};

    char issuer_cn[64]    = {0};
    char issuer_org[64]   = {0};

    char san_dns[64]      = {0};
    char cert_url[64]     = {0}; 
    char cert_email[64]   = {0};
    char cert_date[32]    = {0};

    bool has_subject_cn  = false;
    bool has_subject_org = false;
    bool has_issuer_cn   = false;
    bool has_issuer_org  = false;
    bool has_cert_url    = false;
    bool has_email       = false;
    bool has_date        = false;

    for (uint16_t i = 0; i + 7 < length; i++) {
        // --- 1. X.500 RDN Attributes (OID Prefix: 06 03 55 04 XX) ---
        if (payload[i] == 0x06 && payload[i+1] == 0x03 && 
            payload[i+2] == 0x55 && payload[i+3] == 0x04) {
            
            uint8_t attr_type = payload[i+4];
            uint8_t tag_type  = payload[i+5]; // 0x13 = PrintableString, 0x0C = UTF8String, etc.
            uint8_t str_len   = payload[i+6];

            if ((tag_type == 0x13 || tag_type == 0x0C || tag_type == 0x16 || tag_type == 0x14) &&
                (i + 7 + str_len <= length) && str_len > 0) {
                
                const uint8_t* str_data = &payload[i + 7];

                switch (attr_type) {
                    case 0x03: { // Common Name (CN)
                        if (!has_issuer_cn) {
                            int copy_len = std::min((int)str_len, 63);
                            memcpy(issuer_cn, str_data, copy_len);
                            issuer_cn[copy_len] = '\0';
                            has_issuer_cn = true;
                        } else {
                            int copy_len = std::min((int)str_len, 63);
                            memcpy(subject_cn, str_data, copy_len);
                            subject_cn[copy_len] = '\0';
                            has_subject_cn = true;
                        }
                        break;
                    }
                    case 0x0A: { // Organization (O)
                        if (!has_issuer_org) {
                            int copy_len = std::min((int)str_len, 63);
                            memcpy(issuer_org, str_data, copy_len);
                            issuer_org[copy_len] = '\0';
                            has_issuer_org = true;
                        } else {
                            int copy_len = std::min((int)str_len, 63);
                            memcpy(subject_org, str_data, copy_len);
                            subject_org[copy_len] = '\0';
                            has_subject_org = true;
                        }
                        break;
                    }
                    case 0x07: { // Locality / City (L)
                        int copy_len = std::min((int)str_len, 31);
                        memcpy(subject_loc, str_data, copy_len);
                        subject_loc[copy_len] = '\0';
                        break;
                    }
                    case 0x08: { // State / Province (ST)
                        int copy_len = std::min((int)str_len, 31);
                        memcpy(subject_state, str_data, copy_len);
                        subject_state[copy_len] = '\0';
                        break;
                    }
                    case 0x06: { // Country (C)
                        int copy_len = std::min((int)str_len, 7);
                        memcpy(subject_c, str_data, copy_len);
                        subject_c[copy_len] = '\0';
                        break;
                    }
                    default:
                        break;
                }
                i += (6 + str_len);
                continue;
            }
        }

        // --- 2. Subject Alternative Name (SAN) (OID: 06 03 55 1D 11) ---
        if (payload[i] == 0x06 && payload[i+1] == 0x03 && 
            payload[i+2] == 0x55 && payload[i+3] == 0x1D && payload[i+4] == 0x11) {
            
            for (uint16_t s = i + 5; s + 2 < length && s < i + 30; s++) {
                if (payload[s] == 0x82) { // 0x82 is context tag [2] for dNSName
                    uint8_t dlen = payload[s+1];
                    if (dlen > 0 && (s + 2 + dlen <= length)) {
                        int copy_len = std::min((int)dlen, 63);
                        memcpy(san_dns, &payload[s+2], copy_len);
                        san_dns[copy_len] = '\0';
                        break;
                    }
                }
            }
        }

        // --- 3. Extract CA URLs (OCSP/CRL) (Tag 0x86 UniformResourceIdentifier) ---
        if (!has_cert_url && payload[i] == 0x86 && 
            payload[i+2] == 'h' && payload[i+3] == 't' && 
            payload[i+4] == 't' && payload[i+5] == 'p') {
            
            uint8_t url_len = payload[i+1];
            if (i + 2 + url_len <= length) {
                uint8_t start = (payload[i+6] == 's') ? 10 : 9; // skip http(s)://
                uint8_t end = start;
                while (end < url_len + 2 && payload[i + end] != '/') {
                    end++;
                }

                int domain_len = end - start;
                if (domain_len > 0 && domain_len < 63) {
                    memcpy(cert_url, &payload[i + start], domain_len);
                    cert_url[domain_len] = '\0';
                    has_cert_url = true;
                }
            }
        }

        // --- 4. Extract Email Addresses (OID: 1.2.840.113549.1.9.1) ---
        if (!has_email && i + 12 < length &&
            payload[i] == 0x06 && payload[i+1] == 0x09 &&
            payload[i+2] == 0x2A && payload[i+3] == 0x86 && payload[i+4] == 0x48 &&
            payload[i+5] == 0x86 && payload[i+6] == 0xF7 && payload[i+7] == 0x0D &&
            payload[i+8] == 0x01 && payload[i+9] == 0x09 && payload[i+10] == 0x01) {

            uint8_t str_len = payload[i+12];
            
            if (i + 13 + str_len <= length && str_len > 0 && str_len < 63) {
                memcpy(cert_email, &payload[i+13], str_len);
                cert_email[str_len] = '\0';
                has_email = true;
            }
        }

        // --- 5. Extract UTCTime (Tag 0x17) ---
        if (!has_date && payload[i] == 0x17 && payload[i+1] == 13) {
            if (i + 14 <= length && payload[i+2] >= '0' && payload[i+2] <= '9') {
                
                // Peek exactly 15 bytes ahead to see if the "Not After" date is appended
                if (i + 15 + 14 <= length && payload[i+15] == 0x17 && payload[i+16] == 13 && payload[i+17] >= '0') {
                    // We successfully caught both dates!
                    snprintf(cert_date, sizeof(cert_date), "20%c%c/%c%c/%c%c-20%c%c/%c%c/%c%c", 
                        payload[i+2], payload[i+3], payload[i+4], payload[i+5], payload[i+6], payload[i+7],
                        payload[i+17], payload[i+18], payload[i+19], payload[i+20], payload[i+21], payload[i+22]);
                    i += 28; // Fast-forward past both date blocks to save CPU cycles
                } else {
                    // Fallback: We only found the first date
                    snprintf(cert_date, sizeof(cert_date), "20%c%c/%c%c/%c%c", 
                        payload[i+2], payload[i+3], payload[i+4], payload[i+5], payload[i+6], payload[i+7]);
                    i += 14; 
                }
                has_date = true;
            }
        }
    }

    // Determine target entity: Subject takes precedence, fall back to SAN or Issuer
    const char* target_host = has_subject_cn ? subject_cn : (san_dns[0] != '\0' ? san_dns : issuer_cn);
    const char* target_org  = has_subject_org ? subject_org : issuer_org;

    // Fail if we didn't find ANY recognizable string
    if (target_host[0] == '\0' && target_org[0] == '\0' && cert_url[0] == '\0' && cert_email[0] == '\0') {
        return false; 
    }

    // Build rich location token if present: " (Spring, Texas US)"
    char geo_tag[48] = {0};
    if (subject_loc[0] != '\0' || subject_state[0] != '\0' || subject_c[0] != '\0') {
        if (subject_loc[0] != '\0' && subject_state[0] != '\0') {
            snprintf(geo_tag, sizeof(geo_tag), " (%s, %s %s)", subject_loc, subject_state, subject_c);
        } else if (subject_state[0] != '\0') {
            snprintf(geo_tag, sizeof(geo_tag), " (%s %s)", subject_state, subject_c);
        } else if (subject_c[0] != '\0') {
            snprintf(geo_tag, sizeof(geo_tag), " (%s)", subject_c);
        }
    }

    // Build the CA tag
    char ca_tag[70] = {0};
    if (has_issuer_cn && strcmp(target_host, issuer_cn) != 0) {
        snprintf(ca_tag, sizeof(ca_tag), " [CA:%s]", issuer_cn);
    }
    
    // Chain together our extra intelligence to save space
    char ext_tag[128] = {0};
    int ext_idx = 0;
    if (has_email) ext_idx += snprintf(ext_tag + ext_idx, sizeof(ext_tag) - ext_idx, " [E: %s]", cert_email);
    if (has_cert_url) ext_idx += snprintf(ext_tag + ext_idx, sizeof(ext_tag) - ext_idx, " [URI: %s]", cert_url);
    if (has_date) ext_idx += snprintf(ext_tag + ext_idx, sizeof(ext_tag) - ext_idx, " [Valid:%s]", cert_date);

    // Format output
    if (target_host[0] != '\0' && target_org[0] != '\0') {
        snprintf(out_text, max_len, "TLS Cert: %s|%s%s%s%s", target_host, target_org, geo_tag, ca_tag, ext_tag);
    } else if (target_host[0] != '\0') {
        snprintf(out_text, max_len, "TLS Cert: %s%s%s%s", target_host, geo_tag, ca_tag, ext_tag);
    } else if (target_org[0] != '\0') {
        snprintf(out_text, max_len, "TLS Cert Org: %s%s%s%s", target_org, geo_tag, ca_tag, ext_tag);
    } else {
        snprintf(out_text, max_len, "TLS Cert Info:%s", ext_tag);
    }

    return true;
}

// ==========================================
// UPGRADED TLS SNI PARSER (Client Hello)
// ==========================================
bool parse_tls_sni(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    const char prefix[] = "HTTPS SNI: ";
    const size_t prefix_len = sizeof(prefix) - 1;

    // Minimum captured length required for our fixed-offset ClientHello parsing.
    if (length < 44 || payload == nullptr || out_text == nullptr || max_len <= prefix_len) {
        return false; 
    }

    int32_t start_offset = -1;
    uint32_t record_end = 0;

    // --- 1. THE SLIDING WINDOW (A-MSDU Bypass & Validation) ---
    for (uint16_t i = 0; i <= length - 44; i++) {

        // Check for TLS Handshake (0x16), Major Version (0x03), Valid Minor Version (0x00-0x04), ClientHello (0x01)
        if (payload[i] == 0x16 && 
            payload[i+1] == 0x03 && 
            payload[i+2] <= 0x04 &&   // <-- TIGHTER FILTER: Covers SSL 3.0 through theoretical TLS 1.4
            payload[i+5] == 0x01) {       

            uint16_t record_len = ((uint16_t)payload[i+3] << 8) | payload[i+4];
            uint32_t hs_len = ((uint32_t)payload[i+6] << 16) |
                              ((uint32_t)payload[i+7] << 8)  |
                               payload[i+8];

            // Safety Check 1: TLS record must fit entirely inside our captured buffer
            if ((uint32_t)i + 5 + record_len > length) {
                continue;
            }

            // Safety Check 2: The ClientHello (4-byte header + body) must fit inside its own TLS record
            if (hs_len + 4 > record_len) {
                continue;
            }

            // Passed all physical bounds checks. Lock onto this offset!
            start_offset = i;
            
            // --- STRICT RECORD BOUNDARY ---
            record_end = start_offset + 5 + record_len;
            break;
        }
    }

    if (start_offset == -1) return false;

    // Anchor the 32-bit cursor to the start of the Session ID length byte
    uint32_t cursor = start_offset + 43; 

    // 2. Skip Session ID
    if (cursor >= record_end) return false;
    uint8_t sid_len = payload[cursor++];
    if (sid_len > record_end - cursor) return false;
    cursor += sid_len;

    // 3. Skip Cipher Suites
    if (cursor + 2 > record_end) return false;
    uint16_t cipher_len = ((uint16_t)payload[cursor] << 8) | payload[cursor + 1];
    cursor += 2;
    if (cipher_len > record_end - cursor) return false;
    cursor += cipher_len;

    // 4. Skip Compression Methods
    if (cursor >= record_end) return false;
    uint8_t comp_len = payload[cursor++];
    if (comp_len > record_end - cursor) return false;
    cursor += comp_len;

    // 5. Get Extensions Length
    if (cursor + 2 > record_end) return false; 
    uint16_t ext_total_len = ((uint16_t)payload[cursor] << 8) | payload[cursor + 1];
    cursor += 2;

    // Explicitly fail if extensions declare a length that bleeds outside the known TLS record
    if (ext_total_len > record_end - cursor) return false;
    
    uint32_t ext_end = cursor + ext_total_len;

    // 6. Walk the Extensions List
    while (cursor + 4 <= ext_end) {
        uint16_t ext_type = (payload[cursor] << 8) | payload[cursor + 1];
        uint16_t ext_len = (payload[cursor + 2] << 8) | payload[cursor + 3];
        cursor += 4;

        // Ensure this specific extension doesn't bleed past the total extensions block
        if (ext_len > ext_end - cursor) return false;

        if (ext_type == 0x0000) { // Server Name Indication (SNI)
            
            // Validate the SNI list length before reading
            if (ext_len < 2) return false;
            uint16_t list_len = ((uint16_t)payload[cursor] << 8) | payload[cursor + 1];
            if (list_len > ext_len - 2) return false;

            uint32_t list_end = cursor + 2 + list_len;
            uint32_t list_cursor = cursor + 2;

            // Walk to list_end instead of ext_end
            while (list_cursor + 3 <= list_end) {
                uint8_t name_type = payload[list_cursor];
                uint16_t name_len = ((uint16_t)payload[list_cursor + 1] << 8) | payload[list_cursor + 2];
                list_cursor += 3;

                // Ensure the individual domain name doesn't bleed past the SNI list boundary
                if (name_len > list_end - list_cursor) return false;

                if (name_type == 0x00) { // 0x00 designates a DNS Hostname
                    if (name_len > 0) {
                        int copy_len = std::min((int)name_len, (int)(max_len - prefix_len - 1)); 
                        snprintf(out_text, max_len, "%s%.*s", prefix, copy_len, &payload[list_cursor]);
                        return true;
                    }
                }
                list_cursor += name_len;
            }
            return false; // Found SNI but couldn't resolve string
        }
        
        cursor += ext_len; // Jump to the next extension
    }

    return false;
}

// ============================================================================
// MEMORY-SAFE IPP (INTERNET PRINTING PROTOCOL) PARSER
// ============================================================================
// Walks strict TLV structures: Tag -> NameLen -> Name -> ValLen -> Value
// Rejects malformed structures. Extracts user and document names securely.
// ============================================================================
static bool parse_ipp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (!payload || !out_text || max_len == 0 || length < 8) return false;

    out_text[0] = '\0';
    size_t pos = 0;

    auto append_fmt = [&](const char* fmt, ...) -> bool {
        if (pos >= max_len) return false;
        va_list args;
        va_start(args, fmt);
        int written = vsnprintf(out_text + pos, max_len - pos, fmt, args);
        va_end(args);
        
        if (written < 0 || (size_t)written >= max_len - pos) {
            out_text[max_len - 1] = '\0';
            return false;
        }
        pos += (size_t)written;
        return true;
    };

    // 1. Handle initial HTTP POST negotiation on Port 631
    if (length >= 5 && memcmp(payload, "POST ", 5) == 0) {
        return append_fmt("IPP/CUPS: Print Job Initiated (HTTP POST)");
    }

    // 2. IPP Header Validation (Version + Opcode Plausibility)
    uint8_t major_version = payload[0];
    uint8_t minor_version = payload[1];
    
    if ((major_version != 1 && major_version != 2) || minor_version > 2) {
        return false;
    }
    
    // Basic Opcode/Status check: valid codes are never 0x0000 or 0xFFFF
    uint16_t op_status = (payload[2] << 8) | payload[3];
    if (op_status == 0x0000 || op_status == 0xFFFF) return false;

    uint16_t offset = 8; // Skip Version (2), Operation/Status (2), Request ID (4)
    
    char user[32] = {0};
    char doc[64]  = {0};
    bool found_user = false;
    bool found_doc  = false;
    bool malformed  = false;

    // 3. Strict TLV Walk
    while (offset < length) {
        uint8_t tag = payload[offset++];
        
        // End-of-attributes
        if (tag == 0x03) break; 
        
        // Explicitly handle known group delimiter tags
        if (tag == 0x01 || tag == 0x02 || tag == 0x04 || tag == 0x05 || tag == 0x06) {
            continue; 
        }
        
        // Ensure space for Name Length (2 bytes)
        if (length - offset < 2) { malformed = true; break; }
        uint16_t name_len = (payload[offset] << 8) | payload[offset + 1];
        offset += 2;
        
        // Ensure space for Name string
        if (length - offset < name_len) { malformed = true; break; }
        const uint8_t* name_ptr = &payload[offset];
        offset += name_len;
        
        // Ensure space for Value Length (2 bytes)
        if (length - offset < 2) { malformed = true; break; }
        uint16_t val_len = (payload[offset] << 8) | payload[offset + 1];
        offset += 2;
        
        // Ensure space for Value payload
        if (length - offset < val_len) { malformed = true; break; }
        const uint8_t* val_ptr = &payload[offset];
        offset += val_len;

        // 4. Extract Target Attributes (with ASCII sanitization)
        if (name_len == 20 && memcmp(name_ptr, "requesting-user-name", 20) == 0) {
            size_t copy_len = std::min((size_t)val_len, sizeof(user) - 1);
            for (size_t j = 0; j < copy_len; j++) {
                uint8_t c = val_ptr[j];
                user[j] = (c >= 32 && c <= 126) ? (char)c : '.';
            }
            user[copy_len] = '\0';
            found_user = true;
        } 
        else if (name_len == 13 && memcmp(name_ptr, "document-name", 13) == 0) {
            size_t copy_len = std::min((size_t)val_len, sizeof(doc) - 1);
            for (size_t j = 0; j < copy_len; j++) {
                uint8_t c = val_ptr[j];
                doc[j] = (c >= 32 && c <= 126) ? (char)c : '.';
            }
            doc[copy_len] = '\0';
            found_doc = true;
        }
    }

    // 5. Build Final Output (Reject completely if structural bounds were violated)
    if (malformed) return false;

    if (found_user && found_doc) {
        return append_fmt("IPP Print: %s -> '%s'", user, doc);
    } else if (found_doc) {
        return append_fmt("IPP Print: doc '%s'", doc);
    } else if (found_user) {
        return append_fmt("IPP Print: user '%s'", user);
    }

    return false;
}

// ============================================================================
// MEMORY-SAFE SYSLOG PARSER
// Extracts a single-line syslog message while validating an optional PRI.
// ============================================================================

static bool parse_syslog(const uint8_t* payload,
                         uint16_t length,
                         char* out_text,
                         size_t max_len)
{
    if (!payload || !out_text || max_len < 10 || length < 2)
        return false;

    out_text[0] = '\0';

    uint16_t start_idx = 0;
    bool valid_pri = false;

    // ---------------------------------------------------------
    // Optional RFC 3164 / RFC 5424 PRI: <0> ... <191>
    // ---------------------------------------------------------
    if (payload[0] == '<') {
        uint16_t pri = 0;
        uint8_t digits = 0;
        uint16_t i = 1;

        while (i < length && digits < 3 &&
               payload[i] >= '0' && payload[i] <= '9') {

            pri = (uint16_t)(pri * 10 + (payload[i] - '0'));
            digits++;
            i++;
        }

        if (digits > 0 && i < length && payload[i] == '>' && pri <= 191) {
            valid_pri = true;
            start_idx = i + 1;
        }
    }

    // ---------------------------------------------------------
    // If there's no valid PRI, don't immediately reject:
    // some implementations emit syslog-like plaintext without it.
    // But require enough printable content below.
    // ---------------------------------------------------------

    char clean_log[96] = {0};
    size_t write_idx = 0;

    for (uint16_t i = start_idx;
         i < length && write_idx < sizeof(clean_log) - 1;
         i++) {

        uint8_t c = payload[i];

        // End of syslog line
        if (c == '\r' || c == '\n')
            break;

        // Flatten tabs for single-line UI
        if (c == '\t') {
            clean_log[write_idx++] = ' ';
        }
        // Printable ASCII
        else if (c >= 32 && c <= 126) {
            clean_log[write_idx++] = (char)c;
        }
        // Ignore other binary/control bytes
    }

    if (write_idx == 0)
        return false;

    clean_log[write_idx] = '\0';

    // ---------------------------------------------------------
    // Atomic output construction
    // ---------------------------------------------------------

    const char* prefix = valid_pri ? "Syslog: " : "Syslog?: ";

    int written = snprintf(
        out_text,
        max_len,
        "%s%.*s",
        prefix,
        (int)(max_len > strlen(prefix) ? max_len - strlen(prefix) - 1 : 0),
        clean_log
    );

    if (written < 0 || (size_t)written >= max_len) {
        out_text[0] = '\0';
        return false;
    }

    return true;
}

bool parse_rtsp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // 9 bytes is the absolute minimum for an RTSP command (e.g., "PLAY \r\n\r\n")
    if (length < 9) return false;

    const char* p = (const char*)payload;
    const char* payload_end = p + length;

    // Fast gate: Ensure this is actually RTSP traffic
    bool is_rtsp = (memcmp(p, "RTSP/1.", 7) == 0 || memcmp(p, "OPTIONS ", 8) == 0 || 
                    memcmp(p, "DESCRIBE ", 9) == 0 || memcmp(p, "SETUP ", 6) == 0 || 
                    memcmp(p, "PLAY ", 5) == 0 || memcmp(p, "TEARDOWN ", 9) == 0);
    
    if (!is_rtsp) return false;

    char device_info[64] = {0};
    char uri[64] = {0};
    char auth_type[16] = {0};
    char auth_creds[64] = {0}; 
    bool found_intel = false;

    // The longest needles we check inside the loop are exactly 21 bytes long
    // ("Authorization: Basic " and "Authorization: Digest")
    int max_i = (int)length - 21;

    // Sliding window to sweep for all metadata in one pass
    for (int i = 0; i <= max_i; i++) {
        
        // 1. Extract Hardware / Software Identifier (First match wins)
        if (device_info[0] == '\0') {
            const char* id_start = nullptr;
            if (memcmp(&p[i], "Server: ", 8) == 0) id_start = &p[i+8];
            else if (memcmp(&p[i], "User-Agent: ", 12) == 0) id_start = &p[i+12];
            
            if (id_start) {
                const char* end = id_start;
                while (end < payload_end && *end != '\r' && *end != '\n') end++;
                int copy_len = std::min((int)(end - id_start), 63);
                memcpy(device_info, id_start, copy_len);
                device_info[copy_len] = '\0';
                found_intel = true;
            }
        }

        // 2. Extract Stream URI
        if (uri[0] == '\0' && memcmp(&p[i], "rtsp://", 7) == 0) {
            const char* uri_end = &p[i];
            while (uri_end < payload_end && *uri_end != ' ' && *uri_end != '\r' && *uri_end != '\n') uri_end++;
            int copy_len = std::min((int)(uri_end - &p[i]), 63);
            memcpy(uri, &p[i], copy_len);
            uri[copy_len] = '\0';
            found_intel = true;
        }

        // 3. Extract Authentication State & Credentials
        if (auth_type[0] == '\0') {
            if (memcmp(&p[i], "Authorization: Basic ", 21) == 0) {
                snprintf(auth_type, sizeof(auth_type), "Basic");
                
                const char* b64_start = &p[i + 21];
                const char* b64_end = b64_start;
                while (b64_end < payload_end && *b64_end != '\r' && *b64_end != '\n' && *b64_end != ' ') b64_end++;
                
                int copy_len = std::min((int)(b64_end - b64_start), 63);
                if (copy_len > 0) {
                    memcpy(auth_creds, b64_start, copy_len);
                    auth_creds[copy_len] = '\0';
                }
                found_intel = true;
            }
            else if (memcmp(&p[i], "Authorization: Digest", 21) == 0) {
                snprintf(auth_type, sizeof(auth_type), "Digest");
                found_intel = true;
            }
            else if (memcmp(&p[i], "WWW-Authenticate: ", 18) == 0) {
                snprintf(auth_type, sizeof(auth_type), "Req");
                found_intel = true;
            }
        }
    }

    // Fallback: If it's an RTSP packet but has no headers
    if (!found_intel) {
        const char* end = p;
        while (end < payload_end && *end != '\r' && *end != '\n') end++;
        int copy_len = std::min((int)(end - p), (int)(max_len - 15));
        snprintf(out_text, max_len, "RTSP Cmd: %.*s", copy_len, p);
        return true;
    }

    // Assemble the final tactical string
    int idx = snprintf(out_text, max_len, "RTSP Cam");
    
    if (device_info[0] != '\0') {
        idx += snprintf(out_text + idx, max_len - idx, ": %s", device_info);
    }
    if (uri[0] != '\0') {
        idx += snprintf(out_text + idx, max_len - idx, " | %s", uri);
    }
    if (auth_type[0] != '\0') {
        if (auth_creds[0] != '\0') {
            snprintf(out_text + idx, max_len - idx, " (Auth:%s [%s])", auth_type, auth_creds);
        } else {
            snprintf(out_text + idx, max_len - idx, " (Auth:%s)", auth_type);
        }
    }

    return true;
}

bool parse_ftp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // Defensive entry guard
    if (length < 6 || payload == nullptr || out_text == nullptr || max_len < 20) return false;

    const char* p = (const char*)payload;

    // 1. Hunt for authentication commands (Case-insensitive using strncasecmp)
    if (strncasecmp(p, "USER ", 5) == 0 || strncasecmp(p, "PASS ", 5) == 0) {
        const char* end = p;
        
        // Read until the end of the line
        while (end < p + length && *end != '\r' && *end != '\n') end++;
        
        int copy_len = std::min((int)(end - p), (int)(max_len - 6));
        if (copy_len > 0) {
            snprintf(out_text, max_len, "FTP: %.*s", copy_len, p);
            return true;
        }
    }

    // 2. Catch Authentication Responses (Status codes are always numeric)
    if (memcmp(p, "230 ", 4) == 0) {
        snprintf(out_text, max_len, "FTP: Login Successful");
        return true;
    }
    else if (memcmp(p, "530 ", 4) == 0) {
        snprintf(out_text, max_len, "FTP: Login Failed");
        return true;
    }
    
    // 3. Catch Data Connection Routing (PASV / PORT)
    if (strncasecmp(p, "PORT ", 5) == 0 || memcmp(p, "227 ", 4) == 0) {
        const char* tuple_start = nullptr;
        int search_len = std::min((int)length, 64); // Bound the search space
        
        if (memcmp(p, "227 ", 4) == 0) {
            // Find the opening parenthesis for PASV: 227 Entering Passive Mode (h1,h2,h3,h4,p1,p2)
            for (int i = 4; i < search_len; i++) {
                if (p[i] == '(') {
                    tuple_start = &p[i + 1];
                    break;
                }
            }
        } else {
            // PORT command: numbers start immediately after "PORT "
            tuple_start = p + 5;
        }

        if (tuple_start) {
            // Extract the tuple into a safe, null-terminated buffer
            char tuple_buf[64] = {0};
            int i = 0;
            while (tuple_start + i < p + length && tuple_start[i] != '\r' && 
                   tuple_start[i] != ')' && i < 63) {
                tuple_buf[i] = tuple_start[i];
                i++;
            }

            int h1, h2, h3, h4, p1, p2;
            if (sscanf(tuple_buf, "%d,%d,%d,%d,%d,%d", &h1, &h2, &h3, &h4, &p1, &p2) == 6) {
                // Ensure all octets and port bytes strictly conform to 8-bit limits (0-255)
                bool valid = (h1 >= 0 && h1 <= 255) && (h2 >= 0 && h2 <= 255) &&
                             (h3 >= 0 && h3 <= 255) && (h4 >= 0 && h4 <= 255) &&
                             (p1 >= 0 && p1 <= 255) && (p2 >= 0 && p2 <= 255);
                
                if (valid) {
                    uint16_t port = (p1 << 8) | p2; 
                    snprintf(out_text, max_len, "FTP Data: %d.%d.%d.%d:%u", h1, h2, h3, h4, port);
                    return true;
                }
            }
        }
    }

    return false;
}

bool parse_telnet(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // Defensive entry guard
    if (length < 1 || payload == nullptr || out_text == nullptr || max_len < 16) return false;

    char clean_text[64] = {0};
    uint8_t write_idx = 0;

    // Use uint16_t to strictly match the 'length' variable type
    for (uint16_t i = 0; i < length && write_idx < sizeof(clean_text) - 1; i++) {
        
        // Handle Telnet IAC (Interpret As Command)
        if (payload[i] == 0xFF) {
            if (i + 1 >= length) break;

            // IAC IAC = literal 0xFF data byte.
            // Not printable ASCII, so discard it.
            if (payload[i + 1] == 0xFF) {
                i++;
                continue;
            }

            // Most standard Telnet negotiation commands are 3 bytes: IAC <command> <option>
            if (i + 2 < length) {
                i += 2;
            } else {
                break;
            }
            continue;
        }

        // Only grab printable ASCII characters
        if (payload[i] >= 32 && payload[i] <= 126) {
            clean_text[write_idx++] = payload[i];
        } 
        // Stop if we hit a newline (extracts only the first line of the packet)
        else if (payload[i] == '\r' || payload[i] == '\n') {
            if (write_idx > 0) break;
        }
    }

    if (write_idx > 2) {
        snprintf(out_text, max_len, "Telnet: %s", clean_text);
        return true;
    }

    return false;
}

bool parse_tftp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (!payload || !out_text || length < 4 || max_len < 20) return false;

    uint16_t opcode = ((uint16_t)payload[0] << 8) | payload[1];
    if (opcode != 1 && opcode != 2) return false;

    const char* action = (opcode == 1) ? "Read" : "Write";

    // ------------------------------------------
    // 1. Locate filename
    // ------------------------------------------
    uint16_t pos = 2;
    while (pos < length && payload[pos] != '\0') pos++;
    
    if (pos >= length || pos == 2) return false;
    uint16_t filename_len = pos - 2;

    pos++; // Move past filename NUL

    // ------------------------------------------
    // 2. Locate mode
    // ------------------------------------------
    uint16_t mode_start = pos;
    while (pos < length && payload[pos] != '\0') pos++;
    
    if (pos >= length || pos == mode_start) return false;
    uint16_t mode_len = pos - mode_start;

    // ------------------------------------------
    // 3. Validate common TFTP modes (Case-Insensitive per RFC 1350)
    // ------------------------------------------
    bool valid_mode =
        (mode_len == 5 && strncasecmp((const char*)&payload[mode_start], "octet", 5) == 0) ||
        (mode_len == 8 && strncasecmp((const char*)&payload[mode_start], "netascii", 8) == 0) ||
        (mode_len == 4 && strncasecmp((const char*)&payload[mode_start], "mail", 4) == 0);

    if (!valid_mode) return false;

    // ------------------------------------------
    // 4. Extract filename
    // ------------------------------------------
    int copy_len = std::min((int)filename_len, (int)(max_len - 15));
    if (copy_len <= 0) return false;

    snprintf(out_text, max_len, "TFTP %s: %.*s", action, copy_len, (const char*)&payload[2]);
    return true;
}

bool parse_smtp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // Defensive entry guard
    if (length < 4 || payload == nullptr || out_text == nullptr || max_len < 30) return false;

    const char* p = (const char*)payload;
    const char* payload_end = p + length;

    int max_i = (int)length - 4;

    // Slide through the packet looking for line boundaries
    for (int i = 0; i <= max_i; i++) {

        // A command must start at the very beginning of the payload
        // OR immediately after a newline.
        if (i == 0 || p[i - 1] == '\n') {
            const char* line = p + i;
            int rem = length - i;

            // Skip leading CR/LF just in case of unusual formatting.
            while (rem > 0 && (*line == '\r' || *line == '\n')) {
                line++;
                rem--;
            }

            if (rem < 4) continue;

            const char* target_label = nullptr;
            int skip_bytes = 0;

            // EHLO / HELO
            if (rem >= 5 &&
                (strncasecmp(line, "EHLO ", 5) == 0 ||
                 strncasecmp(line, "HELO ", 5) == 0)) {

                target_label = "HELO";
                skip_bytes = 5;
            }

            // MAIL FROM
            else if (rem >= 10 &&
                     strncasecmp(line, "MAIL FROM:", 10) == 0) {

                target_label = "From";
                skip_bytes = 10;
            }

            // RCPT TO
            else if (rem >= 8 &&
                     strncasecmp(line, "RCPT TO:", 8) == 0) {

                target_label = "To";
                skip_bytes = 8;
            }

            // SMTP server banner: 220 text / 220-text
            else if (rem >= 4 &&
                     memcmp(line, "220", 3) == 0 &&
                     (line[3] == ' ' || line[3] == '-')) {

                target_label = "Server";
                skip_bytes = 4;
            }

            // AUTH LOGIN
            else if (rem >= 10 &&
                     strncasecmp(line, "AUTH LOGIN", 10) == 0) {

                if (rem == 10 ||
                    line[10] == ' ' ||
                    line[10] == '\r' ||
                    line[10] == '\n') {

                    snprintf(out_text, max_len, "SMTP AUTH LOGIN");
                    return true;
                }
            }

            // AUTH PLAIN
            else if (rem >= 10 &&
                     strncasecmp(line, "AUTH PLAIN", 10) == 0) {

                if (rem == 10 ||
                    line[10] == ' ' ||
                    line[10] == '\r' ||
                    line[10] == '\n') {

                    snprintf(out_text, max_len, "SMTP AUTH PLAIN");
                    return true;
                }
            }

            // Extract matched field
            if (target_label) {
                const char* target_data = line + skip_bytes;

                while (target_data < payload_end &&
                       (*target_data == ' ' || *target_data == '<')) {
                    target_data++;
                }

                const char* end = target_data;

                while (end < payload_end &&
                       *end != '\r' &&
                       *end != '\n' &&
                       *end != '>') {
                    end++;
                }

                int copy_len =
                    std::min((int)(end - target_data),
                             (int)(max_len - 15));

                if (copy_len > 0) {
                    snprintf(out_text, max_len,
                             "SMTP %s: %.*s",
                             target_label,
                             copy_len,
                             target_data);
                    return true;
                }
            }
        }
    }

    return false;
}

bool parse_smb(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // 1. Lower global minimum length to 20
    if (length < 20 || payload == nullptr || out_text == nullptr || max_len < 40) return false;

    const char magic_sig[] = "NTLMSSP\0";
    int max_i = (int)length - 20; 

    for (int i = 0; i <= max_i; i++) {
        if (memcmp(&payload[i], magic_sig, 8) == 0) {
            
            uint8_t msg_type = payload[i + 8];
            uint32_t rem = length - i;

            // ---------------------------------------------------------
            // Type 1: Negotiate (Client -> Server)
            // ---------------------------------------------------------
            if (msg_type == 0x01) {
                if ((uint32_t)i + 32 > length) continue; // 2. Message-specific length check
                
                uint16_t dom_len = payload[i + 16] | (payload[i + 17] << 8);
                uint32_t dom_off = payload[i + 20] | (payload[i + 21] << 8) | (payload[i + 22] << 16) | (payload[i + 23] << 24);
                
                uint16_t ws_len = payload[i + 24] | (payload[i + 25] << 8);
                uint32_t ws_off = payload[i + 28] | (payload[i + 29] << 8) | (payload[i + 30] << 16) | (payload[i + 31] << 24);

                char dom_name[32] = {0};
                char ws_name[32] = {0};

                // 3. Hardened offset subtraction arithmetic
                if (dom_len > 0 && dom_off <= rem && dom_len <= rem - dom_off) {
                    int d_idx = 0;
                    for (int k = 0; k < dom_len && d_idx < 31; k++) {
                        char c = payload[i + dom_off + k];
                        if (c >= 32 && c <= 126) dom_name[d_idx++] = c;
                    }
                }

                if (ws_len > 0 && ws_off <= rem && ws_len <= rem - ws_off) {
                    int w_idx = 0;
                    for (int k = 0; k < ws_len && w_idx < 31; k++) {
                        char c = payload[i + ws_off + k];
                        if (c >= 32 && c <= 126) ws_name[w_idx++] = c;
                    }
                }

                if (ws_name[0] != '\0') {
                    // 4. Do not invent "WORKGROUP"
                    snprintf(out_text, max_len, "SMB Client: %s\\%s", dom_name[0] ? dom_name : "?", ws_name);
                    return true;
                }
            }
            
            // ---------------------------------------------------------
            // Type 2: Challenge (Server -> Client)
            // ---------------------------------------------------------
            else if (msg_type == 0x02) {
                if ((uint32_t)i + 20 > length) continue;

                uint16_t tgt_len = payload[i + 12] | (payload[i + 13] << 8);
                uint32_t tgt_off = payload[i + 16] | (payload[i + 17] << 8) | (payload[i + 18] << 16) | (payload[i + 19] << 24);

                if (tgt_len > 0 && tgt_off <= rem && tgt_len <= rem - tgt_off) {
                    char tgt_name[32] = {0};
                    int t_idx = 0;
                    for (int k = 0; k < tgt_len && t_idx < 31; k++) {
                        char c = payload[i + tgt_off + k];
                        if (c >= 32 && c <= 126) tgt_name[t_idx++] = c;
                    }
                    if (t_idx > 0) {
                        snprintf(out_text, max_len, "SMB Server: %s", tgt_name);
                        return true;
                    }
                }
            }

            // ---------------------------------------------------------
            // Type 3: Authenticate (Client -> Server)
            // ---------------------------------------------------------
            else if (msg_type == 0x03) {
                if ((uint32_t)i + 44 > length) continue;

                uint16_t usr_len = payload[i + 36] | (payload[i + 37] << 8);
                uint32_t usr_off = payload[i + 40] | (payload[i + 41] << 8) | (payload[i + 42] << 16) | (payload[i + 43] << 24);

                if (usr_len > 0 && usr_off <= rem && usr_len <= rem - usr_off) {
                    char usr_name[32] = {0};
                    int u_idx = 0;
                    for (int k = 0; k < usr_len && u_idx < 31; k++) {
                        char c = payload[i + usr_off + k];
                        if (c >= 32 && c <= 126) usr_name[u_idx++] = c;
                    }
                    if (u_idx > 0) {
                        snprintf(out_text, max_len, "SMB Auth [User: %s]", usr_name);
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

static constexpr uint32_t MQTT_MAX_REMAINING_LENGTH = 268435455UL;

// --- Helper: Decode Variable Length Integer ---
static uint32_t decode_mqtt_length(const uint8_t* p, uint16_t max_len, uint16_t& bytes_read) {
    uint32_t multiplier = 1;
    uint32_t value = 0;
    uint8_t encoded_byte;
    bytes_read = 0;
    
    do {
        if (bytes_read >= max_len || bytes_read >= 4) {
            bytes_read = 0; 
            return 0;
        }
        encoded_byte = p[bytes_read++];
        value += (encoded_byte & 127) * multiplier;
        multiplier *= 128;
    } while ((encoded_byte & 128) != 0);
    
    if (value > MQTT_MAX_REMAINING_LENGTH) {
        bytes_read = 0;
        return 0;
    }
    return value;
}

// --- Helper: Memory-Safe String Extractor ---
static const uint8_t* extract_mqtt_string(const uint8_t* p, uint32_t remaining_len, char* out_buf, size_t max_out, uint32_t& bytes_consumed) {
    bytes_consumed = 0;
    if (!p || remaining_len < 2) return nullptr;
    
    uint16_t str_len = (p[0] << 8) | p[1];
    uint32_t total = 2u + (uint32_t)str_len;
    
    if (remaining_len < total) return nullptr;
    bytes_consumed = total;
    
    if (out_buf && max_out > 0) {
        size_t copy_len = std::min((size_t)str_len, max_out - 1);
        memcpy(out_buf, p + 2, copy_len);
        out_buf[copy_len] = '\0';
    }
    
    return p + total;
}

// --- Helper: Topic Validator (Operates on RAW bytes) ---
static bool mqtt_topic_name_valid(const uint8_t* p, uint32_t remaining_len) {
    if (!p || remaining_len < 2) return false;
    
    uint16_t str_len = (p[0] << 8) | p[1];
    if (str_len == 0 || remaining_len < 2u + str_len) return false;

    // Scan the raw, untruncated string for illegal PUBLISH characters
    for (uint16_t i = 0; i < str_len; ++i) {
        if (p[2 + i] == '#' || p[2 + i] == '+') return false;
    }
    return true;
}

// --- MQTT Type 1: CONNECT ---
static bool parse_mqtt_connect(const uint8_t* remaining, uint32_t bytes_left, char* out_text, size_t max_len, bool& is_high_value) {
    char proto_name[10] = {0};
    uint32_t consumed = 0;
    
    const uint8_t* p = extract_mqtt_string(remaining, bytes_left, proto_name, sizeof(proto_name), consumed);
    if (!p || bytes_left < consumed + 4) return false;
    bytes_left -= consumed;

    if (strcmp(proto_name, "MQTT") != 0) return false;
    
    uint8_t protocol_level = p[0];
    if (protocol_level != 4) return false; 
    
    uint8_t connect_flags = p[1];
    if (connect_flags & 0x01) return false; 
    
    bool has_username = (connect_flags & 0x80) != 0;
    bool has_password = (connect_flags & 0x40) != 0;
    bool has_will     = (connect_flags & 0x04) != 0;
    uint8_t will_qos  = (connect_flags >> 3) & 0x03;
    bool will_retain  = (connect_flags & 0x20) != 0;
    
    if (has_password && !has_username) return false;
    
    if (!has_will) {
        if (will_qos != 0 || will_retain) return false;
    } else {
        if (will_qos == 3) return false;
    }

    p += 4; 
    bytes_left -= 4;

    char client_id[64]  = {0};      // was 32 — covers UUID-style IDs with margin
    p = extract_mqtt_string(p, bytes_left, client_id, sizeof(client_id), consumed);
    if (!p) return false;
    bytes_left -= consumed;

    char temp_out[MAX_LEAK_STR_LEN] = {0};  // was 256 — now genuinely needed given the above
    char chunk[256]      = {0};     // was 128 — must grow to avoid re-clipping username at the chunk-formatting stage
    snprintf(temp_out, sizeof(temp_out), "MQTT [CONNECT]: [Client: %s]", client_id);

    if (has_will) {
        for (int i = 0; i < 2; i++) {
            p = extract_mqtt_string(p, bytes_left, nullptr, 0, consumed);
            if (!p) return false; 
            bytes_left -= consumed;
        }
    }

    if (has_username) {
        char username[192]  = {0};      // was 32 — sized for realistic JWT/token lengths
        p = extract_mqtt_string(p, bytes_left, username, sizeof(username), consumed);
        if (!p) return false;
        bytes_left -= consumed;
        
        snprintf(chunk, sizeof(chunk), " [User: %s]", username);
        strncat(temp_out, chunk, sizeof(temp_out) - strlen(temp_out) - 1);
    }

    if (has_password) {
        p = extract_mqtt_string(p, bytes_left, nullptr, 0, consumed);
        if (!p) return false;
        bytes_left -= consumed;
        
        snprintf(chunk, sizeof(chunk), " [Password: present]");
        strncat(temp_out, chunk, sizeof(temp_out) - strlen(temp_out) - 1);
        is_high_value = true;
    }

    snprintf(out_text, max_len, "%s", temp_out);
    return true;
}

// --- MQTT Type 3: PUBLISH ---
static bool parse_mqtt_publish(uint8_t flags, const uint8_t* remaining, uint32_t bytes_left, char* out_text, size_t max_len) {
    uint8_t qos = (flags >> 1) & 0x03;
    if (qos == 3) return false; 

    // Validate raw topic before extracting
    if (!mqtt_topic_name_valid(remaining, bytes_left)) return false;

    char topic[128] = {0};  // was 64
    uint32_t consumed = 0;
    
    const uint8_t* p = extract_mqtt_string(remaining, bytes_left, topic, sizeof(topic), consumed);
    if (!p) return false;
    bytes_left -= consumed;

    // Consume Packet Identifier if QoS > 0
    if (qos > 0) {
        if (bytes_left < 2) return false; 
        
        // MQTT Spec: Packet Identifier cannot be zero
        uint16_t packet_id = ((uint16_t)p[0] << 8) | (uint16_t)p[1];
        if (packet_id == 0) return false;
        
        p += 2;
        bytes_left -= 2;
    }
    
    // (p now correctly points to the start of the application payload)

    snprintf(out_text, max_len, "MQTT [PUBLISH]: [Topic: %s]", topic);
    return true;
}

// --- Main Entry: MQTT Framing Validation ---
bool parse_mqtt(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len, bool& is_high_value) {
    // FIXED: Explicitly reset the flag state to prevent false-positive leakage between packets
    is_high_value = false;

    if (!payload || length < 2 || !out_text || max_len < 20) return false;

    uint8_t msg_type = payload[0] >> 4;
    uint8_t flags = payload[0] & 0x0F;
    
    if (msg_type == 1 && flags != 0) return false; 

    if (msg_type != 1 && msg_type != 3) return false; 

    uint16_t len_bytes = 0;
    uint32_t remaining_length = decode_mqtt_length(&payload[1], length - 1, len_bytes);
    
    if (len_bytes == 0 || len_bytes + 1 + remaining_length > length) {
        return false; 
    }

    const uint8_t* remaining = payload + 1 + len_bytes;
    uint32_t bytes_left = remaining_length;

    if (msg_type == 1) {
        return parse_mqtt_connect(remaining, bytes_left, out_text, max_len, is_high_value);
    } else if (msg_type == 3) {
        return parse_mqtt_publish(flags, remaining, bytes_left, out_text, max_len);
    }

    return false;
}

// ============================================================================
// MEMORY-SAFE CoAP (CONSTRAINED APPLICATION PROTOCOL) PARSER
// ============================================================================
// Validates the fixed CoAP header and walks the variable-length option
// encoding safely.
//
// Extracts:
//   - Message type
//   - Request/response code
//   - URI-Path
//   - URI-Query
//   - Content-Format
//   - Observe
//   - Printable payload data
//
// CoAP RFC 7252:
//   Byte 0: Ver | Type | TKL
//   Byte 1: Code
//   Byte 2-3: Message ID
//   Byte 4+: Token
//   Then: Options
//   0xFF: Payload Marker
//
// Designed for packet-level parsing. It does not perform TCP/DTLS
// reassembly or decryption.
// ============================================================================

static bool parse_coap(const uint8_t* payload,
                       uint16_t length,
                       char* out_text,
                       size_t max_len) {
    if (!payload || !out_text || max_len == 0 || length < 4) {
        return false;
    }

    out_text[0] = '\0';
    size_t pos = 0;

    // ------------------------------------------------------------------------
    // Safe output helper
    // ------------------------------------------------------------------------
    auto append_fmt = [&](const char* fmt, ...) -> bool {
        if (pos >= max_len) return false;

        va_list args;
        va_start(args, fmt);

        int written = vsnprintf(
            out_text + pos,
            max_len - pos,
            fmt,
            args
        );

        va_end(args);

        if (written < 0 ||
            (size_t)written >= max_len - pos) {
            out_text[max_len - 1] = '\0';
            return false;
        }

        pos += (size_t)written;
        return true;
    };

    // ------------------------------------------------------------------------
    // 1. Fixed CoAP Header
    // ------------------------------------------------------------------------

    uint8_t ver  = (payload[0] >> 6) & 0x03;
    uint8_t type = (payload[0] >> 4) & 0x03;
    uint8_t tkl  = payload[0] & 0x0F;

    // CoAP currently uses Version 1.
    if (ver != 1) {
        return false;
    }

    // TKL values 0-8 are valid.
    // 9-15 are reserved.
    if (tkl > 8) {
        return false;
    }

    // Token must fit completely inside this packet.
    if ((uint32_t)4 + tkl > length) {
        return false;
    }

    uint8_t code = payload[1];

    uint16_t message_id =
        ((uint16_t)payload[2] << 8) |
        payload[3];

    // ------------------------------------------------------------------------
    // 2. Decode CoAP Code
    // ------------------------------------------------------------------------

    const char* code_str = "Unknown";

    switch (code) {
        // Request codes
        case 0x01: code_str = "GET";    break;
        case 0x02: code_str = "POST";   break;
        case 0x03: code_str = "PUT";    break;
        case 0x04: code_str = "DELETE"; break;

        // RFC 8132
        case 0x05: code_str = "FETCH";  break;
        case 0x06: code_str = "PATCH";  break;
        case 0x07: code_str = "iPATCH"; break;

        // 2.xx Success
        case 0x41: code_str = "2.01 Created";  break;
        case 0x42: code_str = "2.02 Deleted";  break;
        case 0x43: code_str = "2.03 Valid";    break;
        case 0x44: code_str = "2.04 Changed";  break;
        case 0x45: code_str = "2.05 Content";  break;

        // 4.xx Client Error
        case 0x80: code_str = "4.00 Bad Request";        break;
        case 0x81: code_str = "4.01 Unauthorized";       break;
        case 0x82: code_str = "4.02 Bad Option";         break;
        case 0x83: code_str = "4.03 Forbidden";          break;
        case 0x84: code_str = "4.04 Not Found";          break;
        case 0x85: code_str = "4.05 Method Not Allowed"; break;
        case 0x86: code_str = "4.06 Not Acceptable";     break;

        // 5.xx Server Error
        case 0xA0: code_str = "5.00 Internal Server Error"; break;
        case 0xA1: code_str = "5.01 Not Implemented";      break;
        case 0xA2: code_str = "5.02 Bad Gateway";           break;
        case 0xA3: code_str = "5.03 Service Unavailable";  break;
        case 0xA4: code_str = "5.04 Gateway Timeout";      break;
        case 0xA5: code_str = "5.05 Proxying Not Supported"; break;

        default:
            break;
    }

    // ------------------------------------------------------------------------
    // 3. Decode Message Type
    // ------------------------------------------------------------------------

    const char* type_str = "UNKNOWN";

    switch (type) {
        case 0: type_str = "CON"; break;
        case 1: type_str = "NON"; break;
        case 2: type_str = "ACK"; break;
        case 3: type_str = "RST"; break;
        default: return false;
    }

    // ------------------------------------------------------------------------
    // 4. Walk Token + Options
    // ------------------------------------------------------------------------

    uint16_t offset = (uint16_t)(4 + tkl);

    // CoAP option numbers are cumulative.
    uint16_t option_number = 0;

    char uri_path[64] = {0};
    char uri_query[96] = {0};
    char payload_text[64] = {0};

    bool has_uri_path = false;
    bool has_uri_query = false;
    bool has_payload_text = false;

    uint16_t content_format = 0;
    bool has_content_format = false;

    uint32_t observe_value = 0;
    bool has_observe = false;

    // ------------------------------------------------------------------------
    // 5. Option Walker
    // ------------------------------------------------------------------------

    while (offset < length) {

        // --------------------------------------------------------------------
        // Payload Marker
        // --------------------------------------------------------------------
        if (payload[offset] == 0xFF) {
            offset++;

            // A payload marker must be followed by at least one payload byte.
            if (offset >= length) {
                return false;
            }

            size_t copy_len =
                std::min(
                    (size_t)(length - offset),
                    sizeof(payload_text) - 1
                );

            size_t write_pos = 0;

            for (size_t i = 0; i < copy_len; i++) {
                uint8_t c = payload[offset + i];

                if (c >= 32 && c <= 126) {
                    payload_text[write_pos++] = (char)c;
                }
                else if (c == '\r' ||
                         c == '\n' ||
                         c == '\t') {
                    payload_text[write_pos++] = ' ';
                }
                else {
                    payload_text[write_pos++] = '.';
                }
            }

            payload_text[write_pos] = '\0';

            if (write_pos > 0) {
                has_payload_text = true;
            }

            break;
        }

        // --------------------------------------------------------------------
        // Option Header
        //
        // 4-bit delta + 4-bit length
        //
        // 0-12  = value directly
        // 13    = next byte + 13
        // 14    = next two bytes + 269
        // 15    = reserved
        // --------------------------------------------------------------------

        uint8_t option_byte = payload[offset++];

        uint16_t actual_delta =
            (uint16_t)((option_byte >> 4) & 0x0F);

        uint8_t opt_len =
            option_byte & 0x0F;

        // --------------------------------------------------------------------
        // Decode Option Delta
        // --------------------------------------------------------------------

        if (actual_delta == 13) {

            if (offset >= length) {
                return false;
            }

            actual_delta =
                (uint16_t)payload[offset++] + 13;
        }
        else if (actual_delta == 14) {

            if (length - offset < 2) {
                return false;
            }

            uint16_t ext =
                ((uint16_t)payload[offset] << 8) |
                payload[offset + 1];

            offset += 2;

            if (ext > (uint16_t)(0xFFFF - 269)) {
                return false;
            }

            actual_delta =
                (uint16_t)(269 + ext);
        }
        else if (actual_delta == 15) {

            // Reserved.
            return false;
        }

        // --------------------------------------------------------------------
        // Apply Delta to Running Option Number
        // --------------------------------------------------------------------

        if (actual_delta != 0) {

            if (option_number >
                (uint16_t)(0xFFFF - actual_delta)) {
                return false;
            }

            option_number =
                (uint16_t)(option_number + actual_delta);
        }

        // --------------------------------------------------------------------
        // Decode Option Length
        // --------------------------------------------------------------------

        uint16_t actual_len = opt_len;

        if (opt_len == 13) {

            if (offset >= length) {
                return false;
            }

            actual_len =
                (uint16_t)payload[offset++] + 13;
        }
        else if (opt_len == 14) {

            if (length - offset < 2) {
                return false;
            }

            uint16_t ext =
                ((uint16_t)payload[offset] << 8) |
                payload[offset + 1];

            offset += 2;

            if (ext > (uint16_t)(0xFFFF - 269)) {
                return false;
            }

            actual_len =
                (uint16_t)(269 + ext);
        }
        else if (opt_len == 15) {

            // Reserved.
            return false;
        }

        // --------------------------------------------------------------------
        // Option Value Must Fit Completely
        // --------------------------------------------------------------------

        if (actual_len > length - offset) {
            return false;
        }

        const uint8_t* value =
            &payload[offset];

        // --------------------------------------------------------------------
        // URI-Path Option = 11
        // --------------------------------------------------------------------

        if (option_number == 11 &&
            actual_len > 0) {

            size_t existing =
                strlen(uri_path);

            if (existing <
                sizeof(uri_path) - 1) {

                size_t available =
                    sizeof(uri_path) - 1 - existing;

                // Each URI-Path segment is separated by '/'.
                if (existing > 0 &&
                    available > 0) {

                    uri_path[existing++] = '/';
                    available--;
                }

                size_t copy_len =
                    std::min(
                        (size_t)actual_len,
                        available
                    );

                for (size_t i = 0;
                     i < copy_len;
                     i++) {

                    uint8_t c = value[i];

                    uri_path[existing++] =
                        (c >= 32 && c <= 126)
                            ? (char)c
                            : '.';
                }

                uri_path[existing] = '\0';
                has_uri_path = true;
            }
        }

        // --------------------------------------------------------------------
        // URI-Query Option = 15
        // --------------------------------------------------------------------

        else if (option_number == 15 &&
                 actual_len > 0) {

            size_t existing =
                strlen(uri_query);

            if (existing <
                sizeof(uri_query) - 1) {

                if (existing > 0) {
                    uri_query[existing++] = '&';
                }

                if (existing <
                    sizeof(uri_query) - 1) {

                    size_t available =
                        sizeof(uri_query) - 1 - existing;

                    size_t copy_len =
                        std::min(
                            (size_t)actual_len,
                            available
                        );

                    for (size_t i = 0;
                         i < copy_len;
                         i++) {

                        uint8_t c = value[i];

                        uri_query[existing++] =
                            (c >= 32 && c <= 126)
                                ? (char)c
                                : '.';
                    }

                    uri_query[existing] = '\0';
                    has_uri_query = true;
                }
            }
        }

        // --------------------------------------------------------------------
        // Content-Format Option = 12
        // --------------------------------------------------------------------

        else if (option_number == 12 &&
                 actual_len > 0 &&
                 actual_len <= 2) {

            uint16_t fmt = 0;

            for (uint16_t i = 0;
                 i < actual_len;
                 i++) {

                fmt =
                    (uint16_t)(
                        (fmt << 8) |
                        value[i]
                    );
            }

            content_format = fmt;
            has_content_format = true;
        }

        // --------------------------------------------------------------------
        // Observe Option = 6
        // --------------------------------------------------------------------

        else if (option_number == 6 &&
                 actual_len <= 3) {

            uint32_t obs = 0;

            for (uint16_t i = 0;
                 i < actual_len;
                 i++) {

                obs =
                    (obs << 8) |
                    value[i];
            }

            observe_value = obs;
            has_observe = true;
        }

        // Advance over option value.
        offset =
            (uint16_t)(offset + actual_len);
    }

    // ------------------------------------------------------------------------
    // 6. Require Something Meaningful
    // ------------------------------------------------------------------------

    if (code == 0 &&
        !has_uri_path &&
        !has_uri_query &&
        !has_payload_text &&
        !has_observe) {

        return false;
    }

    // ------------------------------------------------------------------------
    // 7. Build Output
    // ------------------------------------------------------------------------

    if (!append_fmt("CoAP: %s %s",
                    type_str,
                    code_str)) {
        return false;
    }

    if (has_uri_path) {

        if (!append_fmt(" [/%s]",
                        uri_path)) {
            return false;
        }
    }

    if (has_uri_query) {

        if (!append_fmt("?%s",
                        uri_query)) {
            return false;
        }
    }

    // ------------------------------------------------------------------------
    // Content-Format
    // ------------------------------------------------------------------------

    if (has_content_format) {

        const char* fmt_str = nullptr;

        switch (content_format) {
            case 0:
                fmt_str = "text/plain";
                break;

            case 40:
                fmt_str = "application/link-format";
                break;

            case 41:
                fmt_str = "application/xml";
                break;

            case 50:
                fmt_str = "application/json";
                break;

            case 60:
                fmt_str = "application/cbor";
                break;

            default:
                break;
        }

        if (fmt_str) {
            if (!append_fmt(" [Fmt:%s]",
                            fmt_str)) {
                return false;
            }
        }
    }

    // ------------------------------------------------------------------------
    // Observe
    // ------------------------------------------------------------------------

    if (has_observe) {

        if (!append_fmt(
                " [Observe:%lu]",
                (unsigned long)observe_value)) {
            return false;
        }
    }

    // ------------------------------------------------------------------------
    // Printable Payload
    // ------------------------------------------------------------------------

    if (has_payload_text) {

        if (!append_fmt(
                " [Data:%s]",
                payload_text)) {
            return false;
        }
    }

    return true;
}

// ---------------------------------------------------------
// SSDP VERBOSE / SAFE PARSER
//
// Handles:
//   M-SEARCH * HTTP/1.1
//   NOTIFY * HTTP/1.1
//   HTTP/1.1 200 OK
//
// Extracts useful SSDP/UPnP headers while keeping the
// resulting string bounded by max_len.
// ---------------------------------------------------------

static void ssdp_copy_trimmed(
    const char* src,
    size_t len,
    char* dst,
    size_t dst_size
) {
    if (!dst || dst_size == 0) return;

    while (len > 0 &&
           (*src == ' ' || *src == '\t')) {
        src++;
        len--;
    }

    while (len > 0 &&
           (src[len - 1] == ' ' ||
            src[len - 1] == '\t' ||
            src[len - 1] == '\r')) {
        len--;
    }

    size_t n = (len < dst_size - 1) ? len : dst_size - 1;

    if (n > 0) {
        memcpy(dst, src, n);
    }

    dst[n] = '\0';
}

static void ssdp_append(
    char* out,
    size_t max_len,
    size_t& used,
    const char* fmt,
    ...
) {
    if (!out || max_len == 0 || used >= max_len - 1) return;

    va_list args;
    va_start(args, fmt);

    int written = vsnprintf(
        out + used,
        max_len - used,
        fmt,
        args
    );

    va_end(args);

    if (written <= 0) return;

    size_t remaining = max_len - used - 1;

    if ((size_t)written > remaining) {
        used = max_len - 1;
    } else {
        used += (size_t)written;
    }
}

bool parse_ssdp(
    const uint8_t* payload,
    uint16_t length,
    char* out_text,
    size_t max_len
) {
    if (!payload || !out_text || max_len < 2 || length < 8) {
        return false;
    }

    out_text[0] = '\0';

    // -----------------------------------------------------
    // Local bounded fields
    // -----------------------------------------------------

    char first_line[64] = {0};      // was 40

char host[64]          = {0};   // was 40
char man[40]           = {0};   // unchanged — "ssdp:discover" etc., always short
char mx[8]             = {0};   // unchanged — single-digit seconds value

char target_key[4]     = {0};   // unchanged — "ST" / "NT"
char target_val[128]   = {0};   // was 80 — URNs like your Samsung example run 40-50 chars; other vendors' nested service URNs can run longer

char nts[32]           = {0};   // unchanged — "ssdp:alive" / "ssdp:byebye"
char server[128]       = {0};   // was 80 — SERVER strings often chain 3+ tokens (OS/version, UPnP/version, product/version)
char usn[128]          = {0};   // was 80 — this is your actual bug; 82 chars needed, giving headroom for longer UUIDs+URN combos
char location[160]     = {0};   // was 100 — full URLs with paths, occasionally query strings
char cache_control[48] = {0};   // unchanged — "max-age=1800" style, always short
char date[40]          = {0};   // unchanged — RFC1123 dates are ~29 chars, some margin already

    const char* p =
        reinterpret_cast<const char*>(payload);

    const char* end = p + length;

    // -----------------------------------------------------
    // 1. FIRST LINE
    // -----------------------------------------------------

    const char* line_end =
        static_cast<const char*>(
            memchr(p, '\n', end - p)
        );

    if (!line_end) {
        line_end = end;
    }

    size_t line_len =
        static_cast<size_t>(line_end - p);

    ssdp_copy_trimmed(
        p,
        line_len,
        first_line,
        sizeof(first_line)
    );

    // -----------------------------------------------------
    // 2. CLASSIFY THE START LINE
    //
    // We only accept actual SSDP request/notification/
    // response syntax here.
    // -----------------------------------------------------

    bool looks_ssdp = false;

    if (strncasecmp(
            first_line,
            "M-SEARCH ",
            9
        ) == 0) {

        looks_ssdp = true;

    } else if (strncasecmp(
                   first_line,
                   "NOTIFY ",
                   7
               ) == 0) {

        looks_ssdp = true;

    } else if (strncasecmp(
                   first_line,
                   "HTTP/1.1 200",
                   12
               ) == 0) {

        looks_ssdp = true;

    } else if (strncasecmp(
                   first_line,
                   "HTTP/1.0 200",
                   12
               ) == 0) {

        looks_ssdp = true;
    }

    // Don't parse arbitrary HTTP traffic as SSDP.
    if (!looks_ssdp) {
        return false;
    }

    // Advance beyond first line.
    p = (line_end < end) ? line_end + 1 : end;

    // -----------------------------------------------------
    // 3. HEADER WALKER
    // -----------------------------------------------------

    while (p < end) {

        line_end =
            static_cast<const char*>(
                memchr(p, '\n', end - p)
            );

        if (!line_end) {
            line_end = end;
        }

        size_t current_len =
            static_cast<size_t>(line_end - p);

        // Blank line => end of HTTP-like headers.
        size_t meaningful_len = current_len;

        while (meaningful_len > 0 &&
               (p[meaningful_len - 1] == '\r' ||
                p[meaningful_len - 1] == ' '  ||
                p[meaningful_len - 1] == '\t')) {
            meaningful_len--;
        }

        if (meaningful_len == 0) {
            break;
        }

        const char* colon =
            static_cast<const char*>(
                memchr(p, ':', meaningful_len)
            );

        if (colon) {

            size_t key_len =
                static_cast<size_t>(colon - p);

            const char* value = colon + 1;

            size_t value_len =
                meaningful_len - key_len - 1;

            // Trim whitespace.
            while (value_len > 0 &&
                   (*value == ' ' || *value == '\t')) {
                value++;
                value_len--;
            }

            while (value_len > 0 &&
                   (value[value_len - 1] == '\r' ||
                    value[value_len - 1] == ' '  ||
                    value[value_len - 1] == '\t')) {
                value_len--;
            }

            // -------------------------------------------------
            // HOST
            // -------------------------------------------------
            if (key_len == 4 &&
                strncasecmp(p, "HOST", 4) == 0) {

                ssdp_copy_trimmed(
                    value, value_len,
                    host, sizeof(host)
                );
            }

            // -------------------------------------------------
            // MAN
            // -------------------------------------------------
            else if (key_len == 3 &&
                     strncasecmp(p, "MAN", 3) == 0) {

                ssdp_copy_trimmed(
                    value, value_len,
                    man, sizeof(man)
                );
            }

            // -------------------------------------------------
            // MX
            // -------------------------------------------------
            else if (key_len == 2 &&
                     strncasecmp(p, "MX", 2) == 0) {

                ssdp_copy_trimmed(
                    value, value_len,
                    mx, sizeof(mx)
                );
            }

            // -------------------------------------------------
            // ST / NT
            // -------------------------------------------------
            else if (
                key_len == 2 &&
                (strncasecmp(p, "ST", 2) == 0 ||
                 strncasecmp(p, "NT", 2) == 0)
            ) {

                target_key[0] = p[0];
                target_key[1] = p[1];
                target_key[2] = '\0';

                ssdp_copy_trimmed(
                    value, value_len,
                    target_val, sizeof(target_val)
                );
            }

            // -------------------------------------------------
            // NTS
            // -------------------------------------------------
            else if (
                key_len == 3 &&
                strncasecmp(p, "NTS", 3) == 0
            ) {

                ssdp_copy_trimmed(
                    value, value_len,
                    nts, sizeof(nts)
                );
            }

            // -------------------------------------------------
            // SERVER / USER-AGENT
            // -------------------------------------------------
            else if (
                (key_len == 6 &&
                 strncasecmp(p, "SERVER", 6) == 0) ||

                (key_len == 10 &&
                 strncasecmp(p, "USER-AGENT", 10) == 0)
            ) {

                if (server[0] == '\0') {
                    ssdp_copy_trimmed(
                        value, value_len,
                        server, sizeof(server)
                    );
                }
            }

            // -------------------------------------------------
            // USN
            // -------------------------------------------------
            else if (
                key_len == 3 &&
                strncasecmp(p, "USN", 3) == 0
            ) {

                ssdp_copy_trimmed(
                    value, value_len,
                    usn, sizeof(usn)
                );
            }

            // -------------------------------------------------
            // LOCATION / SECURELOCATION
            // -------------------------------------------------
            else if (
                (key_len == 8 &&
                 strncasecmp(p, "LOCATION", 8) == 0) ||

                (key_len == 14 &&
                 strncasecmp(p, "SECURELOCATION", 14) == 0)
            ) {

                if (location[0] == '\0') {
                    ssdp_copy_trimmed(
                        value, value_len,
                        location, sizeof(location)
                    );
                }
            }

            // -------------------------------------------------
            // CACHE-CONTROL
            // -------------------------------------------------
            else if (
                key_len == 13 &&
                strncasecmp(p, "CACHE-CONTROL", 13) == 0
            ) {

                ssdp_copy_trimmed(
                    value, value_len,
                    cache_control, sizeof(cache_control)
                );
            }

            // -------------------------------------------------
            // DATE
            // -------------------------------------------------
            else if (
                key_len == 4 &&
                strncasecmp(p, "DATE", 4) == 0
            ) {

                ssdp_copy_trimmed(
                    value, value_len,
                    date, sizeof(date)
                );
            }
        }

        p = (line_end < end) ? line_end + 1 : end;
    }

    // -----------------------------------------------------
    // 4. Clean common UPnP URN prefixes
    // -----------------------------------------------------

    const char* clean_target = target_val;

    if (strncmp(
            target_val,
            "urn:schemas-upnp-org:device:",
            28
        ) == 0) {

        clean_target = target_val + 28;

    } else if (strncmp(
                   target_val,
                   "urn:schemas-upnp-org:service:",
                   29
               ) == 0) {

        clean_target = target_val + 29;
    }

    // -----------------------------------------------------
    // 5. Assemble compact UI string
    // -----------------------------------------------------

    size_t used = 0;

    ssdp_append(
        out_text,
        max_len,
        used,
        "SSDP %s",
        first_line
    );

    if (host[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            " | HOST=%s",
            host
        );
    }

    if (target_val[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            " | %s=%s",
            target_key,
            clean_target
        );
    }

    if (man[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            "\n    MAN=%s",
            man
        );
    }

    if (mx[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            " MX=%s",
            mx
        );
    }

    if (nts[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            "\n    NTS=%s",
            nts
        );
    }

    if (server[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            "\n    SERVER=%s",
            server
        );
    }

    if (usn[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            "\n    USN=%s",
            usn
        );
    }

    if (location[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            "\n    LOCATION=%s",
            location
        );
    }

    if (cache_control[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            "\n    CACHE=%s",
            cache_control
        );
    }

    if (date[0]) {
        ssdp_append(
            out_text,
            max_len,
            used,
            "\n    DATE=%s",
            date
        );
    }

    return used > 0;
}

// ---------------------------------------------------------
// LLMNR PARSER (Port 5355)
// Extracts Windows local network name resolution queries
// ---------------------------------------------------------
bool parse_llmnr(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // Defensive entry guard
    if (length < 12 || payload == nullptr || out_text == nullptr || max_len < 30) {
        return false; 
    }

    uint16_t flags = (payload[2] << 8) | payload[3];
    bool is_response = (flags & 0x8000) != 0; // Check the QR bit (Query vs Response)
    uint16_t qdcount = (payload[4] << 8) | payload[5];

    // We primarily care about the Question section (what name are they looking for?)
    if (qdcount > 0) {
        char domain[80] = {0};
        int d_idx = 0;
        int i = 12; // Start immediately after header
        
        // SAFE SLIDING WINDOW
        while (i < length && payload[i] != 0x00) {
            uint8_t label_len = payload[i];
            
            // Abort on compression pointer (0xC0) to prevent infinite loops
            if ((label_len & 0xC0) == 0xC0) {
                break; 
            }

            // 1. Verify label doesn't exceed the packet payload
            if (label_len > 0 && label_len <= 63 && (i + 1 + label_len) <= length) {
                
                // 2. Verify label won't overflow our local domain buffer!
                if (d_idx + label_len + 1 >= sizeof(domain)) {
                    break;
                }
                
                if (d_idx > 0) domain[d_idx++] = '.';
                memcpy(&domain[d_idx], &payload[i + 1], label_len);
                d_idx += label_len;
                i += label_len + 1;
            } else {
                break;
            }
        }
        domain[d_idx] = '\0';

        if (d_idx > 0) {
            const char* type_str = is_response ? "Reply" : "Query";
            snprintf(out_text, max_len, "LLMNR [%s] Tgt: %s", type_str, domain);
            
            // Retained your original formatting call
            format_reverse_lookups(out_text, max_len);
            
            return true;
        }
    }
    return false;
}

// ---------------------------------------------------------
// LLMNR PARSER (Port 5355)
// Extracts Windows local network name resolution queries
// ---------------------------------------------------------
/*
bool parse_llmnr(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length < 12) return false; // Standard DNS header is 12 bytes

    uint16_t flags = (payload[2] << 8) | payload[3];
    bool is_response = (flags & 0x8000) != 0; // Check the QR bit (Query vs Response)
    uint16_t qdcount = (payload[4] << 8) | payload[5];

    // We primarily care about the Question section (what name are they looking for?)
    if (qdcount > 0) {
        char domain[80] = {0};
        int d_idx = 0;
        int i = 12; // Start immediately after header
        
        // SAFE SLIDING WINDOW (Replaces unsafe decode_dns_name)
        while (i < length && payload[i] != 0x00 && d_idx < sizeof(domain) - 2) {
            uint8_t label_len = payload[i];
            
            // Abort on compression pointer (0xC0) to prevent infinite loops
            if ((label_len & 0xC0) == 0xC0) {
                break; 
            }

            if (label_len > 0 && label_len <= 63 && (i + 1 + label_len) < length) {
                if (d_idx > 0) domain[d_idx++] = '.';
                memcpy(&domain[d_idx], &payload[i + 1], label_len);
                d_idx += label_len;
                i += label_len + 1;
            } else {
                break;
            }
        }
        domain[d_idx] = '\0';

        if (d_idx > 0) {
            // NOISE FILTER: Drop WPAD, ISATAP, and reverse lookup spam
            //if (strcasecmp(domain, "wpad") == 0 || 
                //strcasecmp(domain, "isatap") == 0 ||
                //strstr(domain, "in-addr.arpa") || 
                //strstr(domain, "ip6.arpa")) {
                //return false; 
            //}

            const char* type_str = is_response ? "Reply" : "Query";
            snprintf(out_text, max_len, "LLMNR [%s] Tgt: %s", type_str, domain);
            
            // Retained your original formatting call
            format_reverse_lookups(out_text, max_len);
            
            return true;
        }
    }
    return false;
}
*/

// --- Memory-Safe LLDP Parser ---
static bool parse_lldp(const uint8_t* payload, uint16_t length, char* out_buf, size_t max_out) {
    if (!payload || !out_buf || length < 2 || max_out < 8) return false;
    
    out_buf[0] = '\0';
    uint16_t offset = 0;
    size_t pos = 0;
    
    uint8_t mandatory_stage = 0;
    bool have_end = false;

    // Bounded append helper with explicit NUL reservation
    auto append_str = [&](const char* str) -> bool {
        size_t len = strlen(str);
        if (pos >= max_out) return false;
        
        size_t available = max_out - pos - 1; // Reserve 1 byte for '\0'
        if (len > available) return false;

        memcpy(out_buf + pos, str, len);
        pos += len;
        out_buf[pos] = '\0';
        return true;
    };

    if (!append_str("LLDP: ")) return false;

    // Subtraction-based invariant: At least two bytes remain for a TLV header
    while (length - offset >= 2) {
        uint8_t tlv_type = payload[offset] >> 1;
        uint16_t tlv_len = ((payload[offset] & 0x01) << 8) | payload[offset + 1];
        
        offset += 2;
        
        // Subtraction-safe boundary check
        if (tlv_len > length - offset) return false; 

        // Enforce strict 1 -> 2 -> 3 ordering for false-positive elimination
        if (tlv_type == 1) {
            if (mandatory_stage != 0 || tlv_len < 2) return false;
            mandatory_stage = 1;
        } else if (tlv_type == 2) {
            if (mandatory_stage != 1 || tlv_len < 2) return false;
            mandatory_stage = 2;
        } else if (tlv_type == 3) {
            if (mandatory_stage != 2 || tlv_len != 2) return false;
            mandatory_stage = 3;
        } else if (tlv_type == 0) {
            if (mandatory_stage != 3 || tlv_len != 0) return false;
            have_end = true;
            break;
        }
        
        // Extract High-Information TLVs (Port Desc, Sys Name, Sys Desc)
        if (tlv_type == 4 || tlv_type == 5 || tlv_type == 6) {
            const char* label = (tlv_type == 4) ? "[Port: " : (tlv_type == 5) ? "[Name: " : "[Desc: ";
            size_t label_len = strlen(label);
            
            // Atomic check: Ensure space for label + at least 1 char + "] " + '\0'
            size_t min_required = label_len + 4; 
            
            if (pos < max_out && (max_out - pos) >= min_required) {
                append_str(label);
                
                size_t available = max_out - pos - 3; // Reserve space for "] \0"
                size_t copy_len = std::min((size_t)tlv_len, available);
                
                for (size_t i = 0; i < copy_len; i++) {
                    uint8_t c = payload[offset + i];
                    out_buf[pos++] = (c >= 32 && c <= 126) ? (char)c : '.';
                }
                out_buf[pos] = '\0';
                
                append_str("] ");
            }
        }
        
        offset += tlv_len;
    }

    // Fail if the frame didn't cleanly terminate with a Type 0 TLV
    if (!have_end) {
        return false;
    }

    return (pos > 6);
}

static bool cdp_checksum_valid(const uint8_t* p, uint16_t length) {
    if (!p || length < 4) return false;

    uint32_t sum = 0;

    for (uint16_t i = 0; i + 1 < length; i += 2) {
        sum += ((uint16_t)p[i] << 8) | p[i + 1];

        while (sum >> 16) {
            sum = (sum & 0xFFFF) + (sum >> 16);
        }
    }

    if (length & 1) {
        sum += (uint16_t)p[length - 1] << 8;
        while (sum >> 16) {
            sum = (sum & 0xFFFF) + (sum >> 16);
        }
    }

    return (sum & 0xFFFF) == 0xFFFF;
}

// --- Memory-Safe CDP (Cisco Discovery Protocol) Parser ---
static bool parse_cdp(const uint8_t* payload, uint16_t length, char* out_buf, size_t max_out) {
    if (!payload || !out_buf || length < 8 || max_out < 8) return false;
    
    out_buf[0] = '\0';
    uint16_t offset = 0;
    size_t pos = 0;

    auto append_str = [&](const char* str) -> bool {
        size_t len = strlen(str);
        if (pos >= max_out) return false;
        
        size_t available = max_out - pos - 1; 
        if (len > available) return false;

        memcpy(out_buf + pos, str, len);
        pos += len;
        out_buf[pos] = '\0';
        return true;
    };

    // Skip LLC/SNAP if present (AA AA 03 00 00 0C 20 00)
    if (payload[0] == 0xAA && payload[1] == 0xAA && payload[2] == 0x03) {
        if (length >= 8 && payload[3] == 0x00 && payload[4] == 0x00 && payload[5] == 0x0C && 
            payload[6] == 0x20 && payload[7] == 0x00) {
            offset += 8;
        } else {
            return false;
        }
    }

    // CDP Header Validation (Version, TTL, Checksum)
    if (length - offset < 4) return false;
    
    uint8_t version = payload[offset];
    uint8_t ttl = payload[offset + 1];
    
    if (version != 1 && version != 2) return false;
    if (ttl == 0) return false;
    
    // Strict checksum validation over the CDP frame
    if (!cdp_checksum_valid(payload + offset, length - offset)) return false;
    
    offset += 4;

    if (!append_str("CDP: ")) return false;

    // TLV Walk
    while (length - offset >= 4) {
        uint16_t tlv_type = (payload[offset] << 8) | payload[offset + 1];
        uint16_t tlv_len  = (payload[offset + 2] << 8) | payload[offset + 3];
        
        if (tlv_len < 4 || tlv_len > length - offset) return false; 

        uint16_t val_len = tlv_len - 4;
        uint16_t val_offset = offset + 4;

        // Expanded OSINT Extraction
        if (tlv_type == 0x01 || tlv_type == 0x03 || tlv_type == 0x05 || 
            tlv_type == 0x06 || tlv_type == 0x09 || tlv_type == 0x0A || tlv_type == 0x0B) {
            
            const char* label = (tlv_type == 0x01) ? "[Dev: " : 
                                (tlv_type == 0x03) ? "[Port: " : 
                                (tlv_type == 0x05) ? "[SW: "  : 
                                (tlv_type == 0x06) ? "[Plat: " :
                                (tlv_type == 0x09) ? "[VTP: " :
                                (tlv_type == 0x0A) ? "[VLAN: " : "[Duplex: ";
            
            size_t label_len = strlen(label);
            size_t min_required = label_len + 4; 
            
            if (pos < max_out && (max_out - pos) >= min_required) {
                append_str(label);
                
                size_t available = max_out - pos - 3; 
                size_t copy_len = std::min((size_t)val_len, available);
                
                for (size_t i = 0; i < copy_len; i++) {
                    uint8_t c = payload[val_offset + i];
                    // Sanitize logic now includes tabs
                    if (c == '\r' || c == '\n' || c == '\t') {
                        out_buf[pos++] = ' ';
                    } else {
                        out_buf[pos++] = (c >= 32 && c <= 126) ? (char)c : '.';
                    }
                }
                out_buf[pos] = '\0';
                append_str("] ");
            }
        }
        offset += tlv_len;
    }

    // Every byte must belong to a complete TLV sequence
    if (offset != length) return false;

    return (pos > 5); 
}

// ============================================================================
// PRODUCTION-GRADE SOCKS4 / SOCKS4a / SOCKS5 PARSER
// ============================================================================
// Handles:
//   SOCKS4  request / response
//   SOCKS4a domain-name requests
//   SOCKS5 method negotiation
//   SOCKS5 username/password method negotiation
//   SOCKS5 CONNECT / BIND / UDP ASSOCIATE
//   SOCKS5 IPv4 / IPv6 / domain destinations
//   SOCKS5 replies
//
// Security / robustness:
//   - No reads occur before explicit length validation
//   - All variable-length fields are subtraction-bounded
//   - No password contents are extracted
//   - Output construction is strictly bounded
//   - Rejects malformed/truncated structures
// ============================================================================

static bool parse_socks(const uint8_t* payload,
                        uint16_t length,
                        char* out_text,
                        size_t max_len) {
    if (!payload || !out_text || length < 2 || max_len < 20)
        return false;

    out_text[0] = '\0';

    size_t pos = 0;

    // ------------------------------------------------------------------------
    // Bounded output helper
    // ------------------------------------------------------------------------
    auto append_str = [&](const char* str) -> bool {
        if (!str || pos >= max_len)
            return false;

        size_t len = strlen(str);

        // Reserve one byte for terminating NUL.
        if (len > max_len - pos - 1)
            return false;

        memcpy(out_text + pos, str, len);
        pos += len;
        out_text[pos] = '\0';

        return true;
    };

    // ------------------------------------------------------------------------
    // Bounded formatted append
    // ------------------------------------------------------------------------
    auto append_fmt = [&](const char* fmt, ...) -> bool {
        if (!fmt || pos >= max_len)
            return false;

        va_list args;
        va_start(args, fmt);

        int written = vsnprintf(
            out_text + pos,
            max_len - pos,
            fmt,
            args
        );

        va_end(args);

        if (written < 0)
            return false;

        size_t available = max_len - pos;

        // vsnprintf returns the number of characters that WOULD have
        // been written, excluding the terminating NUL.
        if ((size_t)written >= available) {
            out_text[max_len - 1] = '\0';
            return false;
        }

        pos += (size_t)written;
        return true;
    };

    // ------------------------------------------------------------------------
    // Safe C-string reader inside packet
    // ------------------------------------------------------------------------
    auto find_nul = [&](uint16_t start, uint16_t& end) -> bool {
        if (start >= length)
            return false;

        for (uint16_t i = start; i < length; i++) {
            if (payload[i] == '\0') {
                end = i;
                return true;
            }
        }

        return false;
    };

    // ------------------------------------------------------------------------
    // Printable username / domain helper
    // ------------------------------------------------------------------------
    auto append_sanitized = [&](uint16_t start,
                                uint16_t field_len,
                                const char* prefix,
                                const char* suffix) -> bool {
        size_t prefix_len = strlen(prefix);
        size_t suffix_len = strlen(suffix);

        // Need prefix + at least one character + suffix + NUL.
        if (pos >= max_len ||
            prefix_len > max_len - pos ||
            suffix_len > max_len - pos - prefix_len - 1) {
            return false;
        }

        if (!append_str(prefix))
            return false;

        size_t available = max_len - pos - suffix_len - 1;

        size_t copy_len = std::min(
            (size_t)field_len,
            available
        );

        for (size_t i = 0; i < copy_len; i++) {
            uint8_t c = payload[start + i];

            if (c >= 32 && c <= 126)
                out_text[pos++] = (char)c;
            else
                out_text[pos++] = '.';
        }

        out_text[pos] = '\0';

        return append_str(suffix);
    };

    // =========================================================================
    // SOCKS4 / SOCKS4a
    // =========================================================================
    if (payload[0] == 0x04) {

        // Minimum:
        // VN + CD + DSTPORT(2) + DSTIP(4) + USERID NUL
        if (length < 9)
            return false;

        uint8_t command = payload[1];

        // ---------------------------------------------------------------------
        // SOCKS4 REQUEST
        // ---------------------------------------------------------------------
        if (command == 0x01 || command == 0x02) {

            uint16_t dst_port =
                ((uint16_t)payload[2] << 8) |
                payload[3];

            uint32_t dst_ip =
                ((uint32_t)payload[4] << 24) |
                ((uint32_t)payload[5] << 16) |
                ((uint32_t)payload[6] << 8)  |
                payload[7];

            uint16_t user_end = 0;

            if (!find_nul(8, user_end))
                return false;

            uint16_t user_len = user_end - 8;

            // SOCKS4a:
            // 0.0.0.x where x != 0 indicates a domain follows USERID.
            bool is_socks4a =
                payload[4] == 0x00 &&
                payload[5] == 0x00 &&
                payload[6] == 0x00 &&
                payload[7] != 0x00;

            const char* action =
                (command == 0x01) ? "CONNECT" : "BIND";

            if (!append_fmt("SOCKS4 %s ", action))
                return false;

            // -----------------------------------------------------------------
            // SOCKS4a domain
            // -----------------------------------------------------------------
            if (is_socks4a) {
                uint16_t domain_start = user_end + 1;

                if (domain_start >= length)
                    return false;

                uint16_t domain_end = 0;

                if (!find_nul(domain_start, domain_end))
                    return false;

                uint16_t domain_len =
                    domain_end - domain_start;

                if (domain_len == 0)
                    return false;

                if (!append_sanitized(
                        domain_start,
                        domain_len,
                        "Domain:",
                        "")) {
                    return false;
                }

            } else {
                // -----------------------------------------------------------------
                // SOCKS4 IPv4
                // -----------------------------------------------------------------
                if (!append_fmt(
                        "IPv4:%u.%u.%u.%u",
                        payload[4],
                        payload[5],
                        payload[6],
                        payload[7])) {
                    return false;
                }
            }

            if (!append_fmt(":%u", dst_port))
                return false;

            // Username is useful OSINT, but don't emit an empty field.
            if (user_len > 0) {
                // Keep this bounded and sanitized.
                if (!append_sanitized(
                        8,
                        user_len,
                        " [User:",
                        "]")) {
                    return false;
                }
            }

            return true;
        }

        // ---------------------------------------------------------------------
        // SOCKS4 RESPONSE
        //
        // VN is normally 0x00.
        // CD:
        //   90 = request granted
        //   91 = request rejected / failed
        //   92 = rejected because identd could not connect
        //   93 = rejected because user ID mismatch
        // ---------------------------------------------------------------------
        if (payload[1] >= 90 && payload[1] <= 93) {

            uint8_t status = payload[1];

            const char* status_text = nullptr;

            switch (status) {
                case 90:
                    status_text = "Granted";
                    break;
                case 91:
                    status_text = "Rejected";
                    break;
                case 92:
                    status_text = "Ident Failed";
                    break;
                case 93:
                    status_text = "User ID Mismatch";
                    break;
                default:
                    return false;
            }

            uint16_t dst_port =
                ((uint16_t)payload[2] << 8) |
                payload[3];

            if (!append_fmt(
                    "SOCKS4 Reply: %s IPv4:%u.%u.%u.%u:%u",
                    status_text,
                    payload[4],
                    payload[5],
                    payload[6],
                    payload[7],
                    dst_port)) {
                return false;
            }

            return true;
        }

        return false;
    }

    // =========================================================================
    // SOCKS5
    // =========================================================================
    if (payload[0] == 0x05) {

        // ---------------------------------------------------------------------
        // SOCKS5 METHOD NEGOTIATION
        //
        // VER | NMETHODS | METHODS...
        // ---------------------------------------------------------------------
        uint8_t nmethods = payload[1];

        if (nmethods == 0)
            return false;

        if (nmethods > length - 2)
            return false;

        bool no_auth = false;
        bool userpass = false;
        bool gssapi = false;

        for (uint16_t i = 0; i < nmethods; i++) {
            switch (payload[2 + i]) {
                case 0x00:
                    no_auth = true;
                    break;

                case 0x01:
                    gssapi = true;
                    break;

                case 0x02:
                    userpass = true;
                    break;

                default:
                    break;
            }
        }

        // Exact method-negotiation length is a useful discriminator.
        if (length == (uint16_t)(2 + nmethods)) {

            if (!append_str("SOCKS5 Methods: "))
                return false;

            bool first = true;

            if (no_auth) {
                if (!append_str("NoAuth"))
                    return false;
                first = false;
            }

            if (userpass) {
                if (!first && !append_str(", "))
                    return false;
                if (!append_str("UserPass"))
                    return false;
                first = false;
            }

            if (gssapi) {
                if (!first && !append_str(", "))
                    return false;
                if (!append_str("GSSAPI"))
                    return false;
                first = false;
            }

            // Don't reject completely unknown method lists. A valid SOCKS5
            // implementation may use private/vendor-defined methods.
            if (first) {
                if (!append_fmt(
                        "Other(%u)",
                        nmethods)) {
                    return false;
                }
            }

            return true;
        }

        // ---------------------------------------------------------------------
        // SOCKS5 METHOD SELECTION RESPONSE
        //
        // VER | METHOD
        // ---------------------------------------------------------------------
        if (length == 2) {

            uint8_t method = payload[1];

            const char* method_text = nullptr;

            switch (method) {
                case 0x00:
                    method_text = "NoAuth";
                    break;

                case 0x01:
                    method_text = "GSSAPI";
                    break;

                case 0x02:
                    method_text = "UserPass";
                    break;

                case 0xFF:
                    method_text = "NoAcceptableMethod";
                    break;

                default:
                    method_text = "Other";
                    break;
            }

            if (!append_fmt(
                    "SOCKS5 Method: %s",
                    method_text)) {
                return false;
            }

            return true;
        }

        // ---------------------------------------------------------------------
        // SOCKS5 USERNAME/PASSWORD SUBNEGOTIATION
        //
        // VER | ULEN | UNAME | PLEN | PASSWD
        //
        // IMPORTANT:
        // We deliberately do NOT extract or display the password.
        // ---------------------------------------------------------------------
        if (payload[0] == 0x01) {
            // This overlaps with the first byte of other protocols, so only
            // recognize this form when the internal length structure matches.

            if (length >= 3) {
                uint8_t ulen = payload[1];

                if (ulen > 0 &&
                    ulen <= length - 3) {

                    uint16_t pass_len_pos =
                        (uint16_t)(2 + ulen);

                    if (pass_len_pos < length) {

                        uint8_t plen =
                            payload[pass_len_pos];

                        uint16_t pass_start =
                            (uint16_t)(pass_len_pos + 1);

                        if (plen <= length - pass_start &&
                            pass_start + plen == length) {

                            if (!append_fmt(
                                    "SOCKS5 UserPass Auth [UserLen:%u] [Password:present]",
                                    ulen)) {
                                return false;
                            }

                            return true;
                        }
                    }
                }
            }
        }

        // ---------------------------------------------------------------------
        // SOCKS5 REQUEST / RESPONSE
        //
        // VER | CMD/REP | RSV | ATYP | ADDR | PORT
        // ---------------------------------------------------------------------
        if (length < 7)
            return false;

        uint8_t field = payload[1];
        uint8_t reserved = payload[2];
        uint8_t atyp = payload[3];

        if (reserved != 0x00)
            return false;

        uint16_t offset = 4;

        // ---------------------------------------------------------------------
        // Parse destination/bind address
        // ---------------------------------------------------------------------
        char address[128] = {0};
        size_t addr_pos = 0;

        auto append_addr_char = [&](char c) -> bool {
            if (addr_pos + 1 >= sizeof(address))
                return false;

            address[addr_pos++] = c;
            address[addr_pos] = '\0';
            return true;
        };

        // IPv4
        if (atyp == 0x01) {

            if (length - offset < 4 + 2)
                return false;

            if (!snprintf(
                    address,
                    sizeof(address),
                    "%u.%u.%u.%u",
                    payload[offset],
                    payload[offset + 1],
                    payload[offset + 2],
                    payload[offset + 3])) {
                return false;
            }

            offset += 4;
        }

        // Domain
        else if (atyp == 0x03) {

            if (length - offset < 1)
                return false;

            uint8_t domain_len = payload[offset++];

            if (domain_len == 0)
                return false;

            if (domain_len > length - offset - 2)
                return false;

            if (domain_len >= sizeof(address))
                return false;

            for (uint16_t i = 0; i < domain_len; i++) {
                uint8_t c = payload[offset + i];

                address[i] =
                    (c >= 32 && c <= 126) ?
                    (char)c :
                    '.';
            }

            address[domain_len] = '\0';
            addr_pos = domain_len;

            offset += domain_len;
        }

        // IPv6
        else if (atyp == 0x04) {

            if (length - offset < 16 + 2)
                return false;

            // Print uncompressed IPv6. It's longer, but deterministic and
            // avoids introducing a separate compression routine.
            int written = snprintf(
                address,
                sizeof(address),
                "%02X%02X:%02X%02X:%02X%02X:%02X%02X:"
                "%02X%02X:%02X%02X:%02X%02X:%02X%02X",
                payload[offset],
                payload[offset + 1],
                payload[offset + 2],
                payload[offset + 3],
                payload[offset + 4],
                payload[offset + 5],
                payload[offset + 6],
                payload[offset + 7],
                payload[offset + 8],
                payload[offset + 9],
                payload[offset + 10],
                payload[offset + 11],
                payload[offset + 12],
                payload[offset + 13],
                payload[offset + 14],
                payload[offset + 15]
            );

            if (written < 0 ||
                (size_t)written >= sizeof(address)) {
                return false;
            }

            addr_pos = (size_t)written;
            offset += 16;
        }

        else {
            return false;
        }

        // Port must follow the address.
        if (length - offset != 2)
            return false;

        uint16_t port =
            ((uint16_t)payload[offset] << 8) |
            payload[offset + 1];

        // ---------------------------------------------------------------------
        // Determine whether this is a request or response.
        //
        // Requests use:
        //   1 CONNECT
        //   2 BIND
        //   3 UDP ASSOCIATE
        //
        // Replies use:
        //   0 success
        //   1 general failure
        //   2 connection not allowed
        //   3 network unreachable
        //   4 host unreachable
        //   5 connection refused
        //   6 TTL expired
        //   7 command not supported
        //   8 address type not supported
        //
        // Ambiguity exists because numeric values overlap, so use the
        // protocol context heuristically but conservatively.
        // ---------------------------------------------------------------------

        if (field == 0x01 ||
            field == 0x02 ||
            field == 0x03) {

            const char* command =
                (field == 0x01) ? "CONNECT" :
                (field == 0x02) ? "BIND" :
                                  "UDP ASSOCIATE";

            if (!append_fmt(
                    "SOCKS5 %s %s:%u",
                    command,
                    address,
                    port)) {
                return false;
            }

            return true;
        }

        // SOCKS5 reply
        const char* reply = nullptr;

        switch (field) {
            case 0x00:
                reply = "Success";
                break;
            case 0x01:
                reply = "GeneralFailure";
                break;
            case 0x02:
                reply = "NotAllowed";
                break;
            case 0x03:
                reply = "NetworkUnreachable";
                break;
            case 0x04:
                reply = "HostUnreachable";
                break;
            case 0x05:
                reply = "ConnectionRefused";
                break;
            case 0x06:
                reply = "TTLExpired";
                break;
            case 0x07:
                reply = "CommandUnsupported";
                break;
            case 0x08:
                reply = "AddressTypeUnsupported";
                break;
            default:
                return false;
        }

        if (!append_fmt(
                "SOCKS5 Reply: %s %s:%u",
                reply,
                address,
                port)) {
            return false;
        }

        return true;
    }

    return false;
}

// ---------------------------------------------------------
// TINY JSON EXTRACTOR (No dynamic memory required)
// ---------------------------------------------------------
bool extract_json_val(const char* payload, uint16_t len, const char* key, char* out, size_t out_max) {
    char qkey[32];
    snprintf(qkey, sizeof(qkey), "\"%s\"", key);
    int qlen = strlen(qkey);
    
    const char* end = payload + len;
    const char* found = nullptr;
    
    // Bounded search for the key (e.g., "displayname")
    for (const char* curr = payload; curr <= end - qlen; curr++) {
        if (memcmp(curr, qkey, qlen) == 0) {
            found = curr;
            break;
        }
    }
    
    if (!found) return false;
    
    const char* p = found + qlen;
    while (p < end && *p != ':') p++;
    if (p >= end) return false;
    p++; // skip ':'
    
    while (p < end && (*p == ' ' || *p == '\t')) p++; // skip whitespace
    if (p >= end) return false;
    
    int i = 0;
    bool in_quotes = (*p == '"');
    int bracket_depth = 0; // Tracks [ ] arrays so we don't break on inner commas
    
    if (in_quotes) p++; // skip opening quote
    
    while (p < end && i < (int)out_max - 1) {
        if (in_quotes) {
            if (*p == '"') break; // end of string
        } else {
            if (*p == '[') bracket_depth++;
            else if (*p == ']') bracket_depth--;
            
            // Break on comma only if we aren't inside an array literal
            if (bracket_depth == 0 && (*p == ',' || *p == '}' || *p == '\r' || *p == '\n')) break;
        }
        out[i++] = *p++;
    }
    out[i] = '\0';
    return i > 0;
}

// ---------------------------------------------------------
// DROPBOX LAN SYNC PARSER (Port 17500)
// Extracts version, namespaces, displayname, and host_int
// ---------------------------------------------------------
bool parse_dropbox(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length < 2 || payload[0] != '{') return false; // Must look like JSON
    
    char version[32] = {0};
    char namespaces[64] = {0};
    char displayname[64] = {0};
    char host_int[32] = {0};
    
    bool has_ver = extract_json_val((const char*)payload, length, "version", version, sizeof(version));
    bool has_ns = extract_json_val((const char*)payload, length, "namespaces", namespaces, sizeof(namespaces));
    bool has_name = extract_json_val((const char*)payload, length, "displayname", displayname, sizeof(displayname));
    bool has_host = extract_json_val((const char*)payload, length, "host_int", host_int, sizeof(host_int));
    
    if (!has_ver && !has_ns && !has_name && !has_host) return false;
    
    int written = snprintf(out_text, max_len, "DROPBOX:");
    bool first = true;
    
    if (has_ver) {
        written += snprintf(out_text + written, max_len - written, "%s ver=%s", first ? "" : " |", version);
        first = false;
    }
    if (has_ns) {
        written += snprintf(out_text + written, max_len - written, "%s ns=%s", first ? "" : " |", namespaces);
        first = false;
    }
    if (has_name && displayname[0]) {
        written += snprintf(out_text + written, max_len - written, "%s name=\"%s\"", first ? "" : " |", displayname);
        first = false;
    }
    if (has_host) {
        written += snprintf(out_text + written, max_len - written, "%s host=%s", first ? "" : " |", host_int);
    }
    
    return true;
}

// ---------------------------------------------------------
// SNMP PARSER (Ports 161, 162)
// Extracts cleartext community strings from SNMPv1/v2c
// ---------------------------------------------------------
bool parse_snmp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // SNMP packets are ASN.1 BER encoded. 
    // They must start with 0x30 (Sequence Tag)
    if (length < 10 || payload[0] != 0x30) return false;

    uint16_t idx = 1;
    
    // 1. Skip the Sequence Length field
    if (payload[idx] & 0x80) {
        uint8_t len_bytes = payload[idx] & 0x7F;
        idx += 1 + len_bytes;
    } else {
        idx += 1;
    }

    if (idx + 5 >= length) return false;

    // 2. Extract Version (Tag 0x02, Length 0x01)
    if (payload[idx] != 0x02 || payload[idx+1] != 0x01) return false;
    uint8_t ver = payload[idx+2];
    idx += 3;

    // SNMPv3 (ver == 3) encrypts/hashes community strings, so we only care about v1 (0) and v2c (1)
    if (ver != 0 && ver != 1) return false; 
    
    // 3. Extract Community String (Tag 0x04 for Octet String)
    if (payload[idx] != 0x04) return false;
    idx++;
    
    // String length (Assuming < 128 bytes, which is standard)
    if (payload[idx] & 0x80) return false; 
    uint8_t comm_len = payload[idx];
    idx++;

    // Bounds check
    if (idx + comm_len > length || comm_len >= 32) return false;

    char community[32] = {0};
    memcpy(community, &payload[idx], comm_len);
    
    int print_ver = (ver == 0) ? 1 : 2; // ver 0 is SNMPv1, ver 1 is SNMPv2c

    // 4. Check for default vulnerabilities
    bool is_vuln = (strcmp(community, "public") == 0 || strcmp(community, "private") == 0);

    snprintf(out_text, max_len, "SNMPv%d: '%s'%s", 
             print_ver, 
             community, 
             is_vuln ? " [! VULNERABLE !]" : "");
             
    return true;
}

// ---------------------------------------------------------
// GENERIC JSON CATCH-ALL
// Tries to extract useful data from unknown proprietary JSON UDP protocols
// ---------------------------------------------------------
// Finds "outer_key": { ... }, then searches for inner_key strictly inside that
// object's span (via brace matching), mirroring Python's data['body']['deviceInfo']['model'].
bool extract_nested_json_val(const char* json, uint16_t json_len,
                              const char* outer_key, const char* inner_key,
                              char* out, size_t out_max) {
    char pattern[32];
    int plen = snprintf(pattern, sizeof(pattern), "\"%s\"", outer_key);

    const char* search_end = json + json_len - plen;
    const char* key_pos = nullptr;
    for (const char* c = json; c <= search_end; c++) {
        if (memcmp(c, pattern, plen) == 0) { key_pos = c; break; }
    }
    if (!key_pos) return false;

    // Find the '{' that opens this key's object value
    const char* json_end = json + json_len;
    const char* obj_start = key_pos + plen;
    while (obj_start < json_end && *obj_start != '{') obj_start++;
    if (obj_start >= json_end) return false;

    // Match the closing brace for THIS object only
    int depth = 1;
    const char* obj_end = obj_start + 1;
    while (obj_end < json_end && depth > 0) {
        if (*obj_end == '{') depth++;
        else if (*obj_end == '}') depth--;
        obj_end++;
    }
    if (depth != 0) return false; // truncated mid-object — don't guess

    return extract_json_val(obj_start, (uint16_t)(obj_end - obj_start), inner_key, out, out_max);
}

// Approximates what json.loads() gives you for free: rejects binary garbage that
// happens to contain '{'/'}' bytes, while still tolerating a missing final '}'
// from mid-capture truncation (unlike json.loads, which would just discard that too).
bool looks_like_json(const char* s, uint16_t len) {
    int depth = 0;
    bool in_string = false;
    for (uint16_t i = 0; i < len; i++) {
        char c = s[i];
        if (in_string) {
            if (c == '\\') { i++; continue; }
            if (c == '"') in_string = false;
            continue;
        }
        if (c == '"') { in_string = true; continue; }
        if (c == '{') { depth++; continue; }
        if (c == '}') { depth--; if (depth < 0) return false; continue; }
        if (!(isspace((unsigned char)c) || strchr(":,[]-+.eEtrufalsn0123456789", c))) {
            return false; // a byte json.loads() would choke on
        }
    }
    return true; // depth may be >0 here — that's fine, that's the truncation case
}

bool parse_generic_json(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    const char* p = (const char*)payload;
    const char* end = p + length;
    const char* json_start = nullptr;
    const char* json_end = nullptr;

    for (int i = 0; i < length; i++) {
        if (!json_start && p[i] == '{') json_start = &p[i];
        if (p[i] == '}') json_end = &p[i];
    }
    if (json_start && !json_end) json_end = end - 1;
    if (!json_start || !json_end || json_end <= json_start) return false;
    
    // Reject binary garbage that merely happens to contain '{'/'}' bytes
    uint16_t json_len = (json_end - json_start) + 1;
    if (!looks_like_json(json_start, json_len)) return false;
    
    char model[64] = {0};
    char ip[32] = {0};
    char name[64] = {0};

    bool has_model = extract_json_val(json_start, json_len, "model", model, sizeof(model));
    if (!has_model) has_model = extract_nested_json_val(json_start, json_len, "deviceInfo", "model", model, sizeof(model));

    bool has_ip = extract_json_val(json_start, json_len, "ip", ip, sizeof(ip));
    if (!has_ip) has_ip = extract_nested_json_val(json_start, json_len, "deviceInfo", "ip", ip, sizeof(ip));

    bool has_name = extract_json_val(json_start, json_len, "name", name, sizeof(name));

    // Single header write — everything below appends onto this, nothing resets it again.
    int written = snprintf(out_text, max_len, "JSON:");
    written = std::min((int)max_len - 1, written);
    bool found_something = false;

    // --- Step 3: known high-value keys ---
    if (has_model) {
        written += snprintf(out_text + written, max_len - written, " mod=%s", model);
        written = std::min((int)max_len - 1, written);
        found_something = true;
    }
    if (has_ip) {
        written += snprintf(out_text + written, max_len - written, " ip=%s", ip);
        written = std::min((int)max_len - 1, written);
        found_something = true;
    }
    if (has_name) {
        written += snprintf(out_text + written, max_len - written, " name=%s", name);
        written = std::min((int)max_len - 1, written);
        found_something = true;
    }

    // --- Step 4: fall through unconditionally to grab keys up to depth 3 ---
    int keys_found = 0;
    int brace_depth = 0;
    bool any_root_key_written = false;
    const char* curr = json_start;

    // EXPANDED: Allow up to 15 keys to be found
    while (curr <= json_end && keys_found < 15 && written < (int)max_len - 1) {
        if (*curr == '{') {
            brace_depth++;
        } else if (*curr == '}') {
            brace_depth--;
        } 
        // EXPANDED: Dig up to 3 JSON layers deep to catch nested telemetry
        else if (*curr == '"' && brace_depth >= 1 && brace_depth <= 3) {
            const char* q_start = curr;
            const char* q_end = nullptr;
            for (const char* c = q_start + 1; c <= json_end; c++) {
                if (*c == '"' && *(c - 1) != '\\') { q_end = c; break; }
            }
            
            if (q_end) {
                const char* colon_check = q_end + 1;
                while (colon_check <= json_end && (*colon_check == ' ' || *colon_check == '\t')) colon_check++;
                
                if (colon_check <= json_end && *colon_check == ':') {
                    // EXPANDED: Allow slightly longer key names
                    int key_len = std::min((int)(q_end - (q_start + 1)), 16);

                    // Find where the value starts (skip colon + whitespace)
                    const char* val_start = colon_check + 1;
                    while (val_start <= json_end && (*val_start == ' ' || *val_start == '\t')) val_start++;

                    // EXPANDED: 64-byte buffer to accommodate full URLs
                    char value_buf[64] = {0};
                    bool has_scalar_value = false;

                    if (val_start <= json_end) {
                        if (*val_start == '"') {
                            // String value — find closing quote, respecting escaped quotes
                            const char* v_end = nullptr;
                            for (const char* c = val_start + 1; c <= json_end; c++) {
                                if (*c == '"' && *(c - 1) != '\\') { v_end = c; break; }
                            }
                            if (v_end) {
                                int vlen = std::min((int)(v_end - (val_start + 1)), (int)sizeof(value_buf) - 1);
                                memcpy(value_buf, val_start + 1, vlen);
                                value_buf[vlen] = '\0';
                                has_scalar_value = true;
                            }
                        } else if (*val_start != '{' && *val_start != '[') {
                            // Number / bool / null — scan until a JSON delimiter
                            const char* v_end = val_start;
                            while (v_end <= json_end && *v_end != ',' && *v_end != '}' &&
                                   *v_end != ']' && *v_end != ' ' && *v_end != '\t' && *v_end != '\n') {
                                v_end++;
                            }
                            int vlen = std::min((int)(v_end - val_start), (int)sizeof(value_buf) - 1);
                            memcpy(value_buf, val_start, vlen);
                            value_buf[vlen] = '\0';
                            has_scalar_value = true;
                        }
                    }

                    const char* sep = any_root_key_written ? "," : (found_something ? " keys:" : " ");
                    int n;
                    if (has_scalar_value) {
                        n = snprintf(out_text + written, max_len - written, "%s%.*s=%s",
                                     sep, key_len, q_start + 1, value_buf);
                    } else {
                        // If it's an object/array, just print the key as a breadcrumb
                        n = snprintf(out_text + written, max_len - written, "%s%.*s",
                                     sep, key_len, q_start + 1);
                    }
                    written = std::min((int)max_len - 1, written + n);
                    any_root_key_written = true;
                    keys_found++;
                }
                curr = q_end; // always skip past this quoted string
            }
        }
        curr++;
    }

    return found_something || keys_found > 0;
}

// ---------------------------------------------------------
// ARP PARSER
// Extracts IPv4 <-> MAC mappings
//
// ARP packet layout:
//   0-1   Hardware Type
//   2-3   Protocol Type
//   4     Hardware Address Length
//   5     Protocol Address Length
//   6-7   Opcode
//   8-13  Sender Hardware Address (SHA)
//   14-17 Sender Protocol Address (SPA)
//   18-23 Target Hardware Address (THA)
//   24-27 Target Protocol Address (TPA)
// ---------------------------------------------------------
bool parse_arp(const uint8_t* payload, uint16_t length,
               char* out_text, size_t max_len) {

    if (!payload || !out_text || max_len == 0 || length < 28)
        return false;

    // Standard Ethernet / IPv4 ARP validation
    uint16_t htype = ((uint16_t)payload[0] << 8) | payload[1];
    uint16_t ptype = ((uint16_t)payload[2] << 8) | payload[3];
    uint8_t  hlen  = payload[4];
    uint8_t  plen  = payload[5];

    // Ethernet = 1
    // IPv4    = 0x0800
    // MAC     = 6 bytes
    // IPv4    = 4 bytes
    if (htype != 1 || ptype != 0x0800 ||
        hlen != 6 || plen != 4)
        return false;

    uint16_t opcode = ((uint16_t)payload[6] << 8) | payload[7];

    if (opcode != 1 && opcode != 2)
        return false;

    const uint8_t* sender_mac = &payload[8];
    const uint8_t* sender_ip  = &payload[14];
    const uint8_t* target_mac = &payload[18];
    const uint8_t* target_ip  = &payload[24];

    // -----------------------------------------------------
    // ARP REQUEST
    // "Who has target IP? Tell sender IP."
    // -----------------------------------------------------
    if (opcode == 1) {

        snprintf(out_text, max_len,
                 "ARP Req: Who has %d.%d.%d.%d? "
                 "Tell %d.%d.%d.%d",
                 target_ip[0], target_ip[1],
                 target_ip[2], target_ip[3],
                 sender_ip[0], sender_ip[1],
                 sender_ip[2], sender_ip[3]);

        return true;
    }

    // -----------------------------------------------------
    // ARP REPLY
    // "Target IP is at sender MAC."
    // -----------------------------------------------------
    snprintf(out_text, max_len,
             "ARP Reply: %d.%d.%d.%d is-at "
             "%02X:%02X:%02X:%02X:%02X:%02X",
             sender_ip[0], sender_ip[1],
             sender_ip[2], sender_ip[3],
             sender_mac[0], sender_mac[1],
             sender_mac[2], sender_mac[3],
             sender_mac[4], sender_mac[5]);

    return true;
}

bool parse_ephemeral_upnp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length < 16) return false;

    const char* p = (const char*)payload;
    
    // Payload Signature Gate: Only process if it starts like an SSDP response or event
    if (memcmp(p, "HTTP/1.", 7) != 0 && memcmp(p, "NOTIFY ", 7) != 0 && memcmp(p, "M-SEARCH ", 9) != 0) {
        return false;
    }

    char server[64] = {0};
    char location[64] = {0};
    bool found_something = false;

    // Sliding window for Server and Location headers
    for (int i = 0; i < length - 10; i++) {
        if (memcmp(&p[i], "Server: ", 8) == 0) {
            const char* end = &p[i+8];
            while (end < p + length && *end != '\r' && *end != '\n') end++;
            
            int copy_len = std::min((int)(end - (&p[i+8])), 63);
            memcpy(server, &p[i+8], copy_len);
            server[copy_len] = '\0';
            found_something = true;
        }
        else if (memcmp(&p[i], "Location: ", 10) == 0) {
            const char* end = &p[i+10];
            while (end < p + length && *end != '\r' && *end != '\n') end++;
            
            // Clean up the URL slightly by skipping "http://" if present to save screen space
            int offset = 10;
            if (memcmp(&p[i+10], "http://", 7) == 0) offset = 17;
            
            int copy_len = std::min((int)(end - (&p[i+offset])), 63);
            memcpy(location, &p[i+offset], copy_len);
            location[copy_len] = '\0';
            found_something = true;
        }
    }

    if (server[0] != '\0' && location[0] != '\0') {
        snprintf(out_text, max_len, "UPnP: %s @ %s", server, location);
        return true;
    } else if (server[0] != '\0') {
        snprintf(out_text, max_len, "UPnP Server: %s", server);
        return true;
    } else if (location[0] != '\0') {
        snprintf(out_text, max_len, "UPnP Loc: %s", location);
        return true;
    }
    
    return false; // Let it fall through to generic text extractors if we didn't find the juicy headers
}

// ==========================================
// LIGHTWEIGHT ICMPv4 PARSER (OSINT Upgraded)
// ==========================================
bool parse_icmpv4(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // ICMPv4 header is 8 bytes.
    if (length < 8 || payload == nullptr || out_text == nullptr || max_len == 0) {
        return false;
    }

    uint8_t type = payload[0];
    uint8_t code = payload[1];

    switch (type) {
        case 0:  
            snprintf(out_text, max_len, "ICMPv4: Echo Reply"); 
            return true;
        case 3: 
            // Destination Unreachable has highly specific codes
            switch(code) {
                case 0: snprintf(out_text, max_len, "ICMPv4: Dest Unreachable (Network)"); return true;
                case 1: snprintf(out_text, max_len, "ICMPv4: Dest Unreachable (Host)"); return true;
                case 3: snprintf(out_text, max_len, "ICMPv4: Dest Unreachable (Port Closed)"); return true;
                case 9: snprintf(out_text, max_len, "ICMPv4: Dest Unreachable (Admin Prohibited)"); return true;
                case 13: snprintf(out_text, max_len, "ICMPv4: Dest Unreachable (Firewall Block)"); return true;
                default: snprintf(out_text, max_len, "ICMPv4: Dest Unreachable (Code %u)", code); return true;
            }
        case 4:
            snprintf(out_text, max_len, "ICMPv4: Source Quench");
            return true;
        case 8:  
            snprintf(out_text, max_len, "ICMPv4: Echo Request (Ping)"); 
            return true;
        case 11: 
            snprintf(out_text, max_len, "ICMPv4: Time Exceeded (Traceroute)"); 
            return true;
        case 12:
            snprintf(out_text, max_len, "ICMPv4: Parameter Problem");
            return true;
        case 13:
            snprintf(out_text, max_len, "ICMPv4: Timestamp Request (Recon)");
            return true;
        case 14:
            snprintf(out_text, max_len, "ICMPv4: Timestamp Reply (Recon)");
            return true;
        default: 
            snprintf(out_text, max_len, "ICMPv4: Type %u, Code %u", type, code); 
            return true;
    }
}

// ---------------------------------------------------------
// ICMPv6 DNSSL / DNS SEARCH LIST DECODER
//
// Decodes the Domain Names field of an ICMPv6 Neighbor
// Discovery DNSSL option (ND option type 31).
//
// Input:
//   data     = beginning of Domain Names field
//   data_len = number of bytes available
//
// Output:
//   "domain1,domain2,domain3"
//
// Returns number of characters written, or -1 on malformed
// input.
// ---------------------------------------------------------
int decode_dns_search_list(const uint8_t* data,
                           int data_len,
                           char* out,
                           int max_len) {

    if (!data || !out || data_len <= 0 || max_len <= 0)
        return -1;

    out[0] = '\0';

    int pos = 0;
    int out_idx = 0;
    bool first_domain = true;

    while (pos < data_len) {

        // Padding / end of domain list.
        if (data[pos] == 0) {
            pos++;
            continue;
        }

        int domain_start = pos;
        int domain_len = 0;
        bool domain_valid = true;

        while (pos < data_len) {

            uint8_t label_len = data[pos];

            // End of this domain.
            if (label_len == 0) {
                pos++;
                break;
            }

            // Compression pointers are not expected here.
            // Reject them rather than trying to interpret them.
            if ((label_len & 0xC0) != 0) {
                domain_valid = false;
                break;
            }

            // DNS labels are limited to 63 bytes.
            if (label_len > 63) {
                domain_valid = false;
                break;
            }

            // Need label bytes.
            if (pos + 1 > data_len ||
                label_len > data_len - pos - 1) {
                domain_valid = false;
                break;
            }

            // Account for this label.
            pos += 1 + label_len;
            domain_len += 1 + label_len;
        }

        if (!domain_valid)
            return -1;

        // Empty / malformed domain.
        if (domain_len <= 1)
            continue;

        // Add comma separator.
        if (!first_domain) {
            if (out_idx >= max_len - 1)
                break;

            out[out_idx++] = ',';
        }

        first_domain = false;

        // Re-decode the domain from domain_start.
        int p = domain_start;
        bool first_label = true;

        while (p < pos && data[p] != 0) {

            uint8_t label_len = data[p++];

            if (label_len > 63 ||
                p + label_len > pos) {
                return -1;
            }

            if (!first_label) {
                if (out_idx >= max_len - 1)
                    break;

                out[out_idx++] = '.';
            }

            first_label = false;

            for (int i = 0; i < label_len; i++) {

                if (out_idx >= max_len - 1)
                    break;

                uint8_t c = data[p++];

                // Sanitize for TFT output.
                out[out_idx++] =
                    (c >= 32 && c <= 126) ? (char)c : '.';
            }
        }
    }

    out[out_idx] = '\0';
    return out_idx;
}

// ---------------------------------------------------------
// ICMPv6 / NDP PARSER
//
// Extracts high-value IPv6 control-plane information:
//   - Echo Request / Reply
//   - Destination Unreachable
//   - Packet Too Big
//   - Time Exceeded
//   - Parameter Problem
//   - Router Solicitation
//   - Router Advertisement
//   - Neighbor Solicitation
//   - Neighbor Advertisement
//   - Redirect
//
// NDP options:
//   1  = Source Link-Layer Address
//   2  = Target Link-Layer Address
//   3  = Prefix Information
//   5  = MTU
//   24 = Route Information
//   25 = RDNSS
//   31 = DNSSL
//
// ICMPv6 payload begins at byte 0.
// ---------------------------------------------------------

// ---------------------------------------------------------
// ICMPv6 MESSAGE TYPE NAME
// ---------------------------------------------------------
const char* icmpv6_type_name(uint8_t type) {

    switch (type) {

        // Errors
        case 1:   return "Destination Unreachable";
        case 2:   return "Packet Too Big";
        case 3:   return "Time Exceeded";
        case 4:   return "Parameter Problem";

        // Echo / MLD / ND
        case 128: return "Echo Request";
        case 129: return "Echo Reply";
        case 130: return "MLD Query";
        case 131: return "MLD Report";
        case 132: return "MLD Done";
        case 133: return "Router Solicitation";
        case 134: return "Router Advertisement";
        case 135: return "Neighbor Solicitation";
        case 136: return "Neighbor Advertisement";
        case 137: return "Redirect";

        // Less-common but assigned ICMPv6
        case 138: return "Router Renumbering";
        case 139: return "Node Information Query";
        case 140: return "Node Information Response";
        case 141: return "Inverse ND Solicitation";
        case 142: return "Inverse ND Advertisement";
        case 143: return "MLDv2 Report";
        case 144: return "Home Agent Discovery Request";
        case 145: return "Home Agent Discovery Reply";
        case 146: return "Mobile Prefix Solicitation";
        case 147: return "Mobile Prefix Advertisement";
        case 148: return "Certification Path Solicitation";
        case 149: return "Certification Path Advertisement";
        case 150: return "Seamoby Mobility";
        case 151: return "Multicast Router Advertisement";
        case 152: return "Multicast Router Solicitation";
        case 153: return "Multicast Router Termination";
        case 154: return "FMIPv6";
        case 155: return "RPL Control";
        case 156: return "ILNPv6 Locator Update";
        case 157: return "Duplicate Address Request";
        case 158: return "Duplicate Address Confirmation";
        case 159: return "MPL Control";
        case 160: return "Extended Echo Request";
        case 161: return "Extended Echo Reply";

        default:
            return "Unknown";
    }
}


// ---------------------------------------------------------
// ICMPv6 CODE NAME
// ---------------------------------------------------------
const char* icmpv6_code_name(uint8_t type, uint8_t code) {

    if (type == 1) {

        switch (code) {
            case 0: return "No route";
            case 1: return "Admin prohibited";
            case 2: return "Beyond source scope";
            case 3: return "Address unreachable";
            case 4: return "Port unreachable";
            case 5: return "Ingress/Egress policy";
            case 6: return "Reject route";
            case 7: return "SRH error";
            case 8: return "Headers too long";
            case 9: return "P-Route error";
            default: return "Unknown";
        }
    }

    if (type == 3) {
        switch (code) {
            case 0: return "Hop limit exceeded";
            case 1: return "Fragment reassembly timeout";
            default: return "Unknown";
        }
    }

    if (type == 4) {
        switch (code) {
            case 0: return "Erroneous header field";
            case 1: return "Unknown Next Header";
            case 2: return "Unknown IPv6 option";
            case 3: return "Incomplete first fragment";
            case 4: return "SR upper-layer error";
            case 5: return "Unknown Next Header (intermediate)";
            case 6: return "Extension header too big";
            case 7: return "Extension chain too long";
            case 8: return "Too many extension headers";
            case 9: return "Too many options";
            case 10: return "Option too big";
            default: return "Unknown";
        }
    }

    return "OK";
}


// ---------------------------------------------------------
// APPEND TEXT SAFELY
// ---------------------------------------------------------
static bool icmp6_append(char* out,
                         size_t max_len,
                         int& written,
                         const char* fmt,
                         ...) {

    if (!out || written < 0 || written >= (int)max_len)
        return false;

    va_list args;
    va_start(args, fmt);

    int n = vsnprintf(out + written,
                      max_len - written,
                      fmt,
                      args);

    va_end(args);

    if (n < 0)
        return false;

    written += n;

    return written < (int)max_len;
}

// ---------------------------------------------------------
// ICMPv6 PARSER
// ---------------------------------------------------------
bool parse_icmpv6(const uint8_t* payload,
                  uint16_t length,
                  char* out_text,
                  size_t max_len,
                  bool& is_high_value) {

    if (!payload ||
        !out_text ||
        max_len == 0 ||
        length < 4)
        return false;

    is_high_value = false;
    out_text[0] = '\0';

    uint8_t type = payload[0];
    uint8_t code = payload[1];

    const char* type_name = icmpv6_type_name(type);

    // -----------------------------------------------------
    // Mark particularly useful ICMPv6 traffic
    // -----------------------------------------------------

    switch (type) {

        case 133: // Router Solicitation
        case 134: // Router Advertisement
        case 135: // Neighbor Solicitation
        case 136: // Neighbor Advertisement
        case 137: // Redirect
        case 157: // DAR
        case 158: // DAC
            is_high_value = true;
            break;

        default:
            break;
    }


    // -----------------------------------------------------
    // BASIC HEADER-ONLY CASES
    // -----------------------------------------------------

    if (type >= 5 && type <= 127) {

        snprintf(out_text,
                 max_len,
                 "ICMPv6 [%u] %s Code:%u",
                 type,
                 type_name,
                 code);

        return true;
    }


    // -----------------------------------------------------
    // ERROR MESSAGES
    // -----------------------------------------------------

    if (type >= 1 && type <= 4) {

        snprintf(out_text,
                 max_len,
                 "ICMPv6 %s: %s",
                 type_name,
                 icmpv6_code_name(type, code));

        return true;
    }


    // -----------------------------------------------------
    // ECHO REQUEST / REPLY
    //
    // Bytes 4-5 = Identifier
    // Bytes 6-7 = Sequence
    // -----------------------------------------------------

    if (type == 128 || type == 129) {

        if (length < 8) {
            snprintf(out_text,
                     max_len,
                     "ICMPv6 %s (Malformed)",
                     type_name);
            return true;
        }

        uint16_t id =
            ((uint16_t)payload[4] << 8) | payload[5];

        uint16_t seq =
            ((uint16_t)payload[6] << 8) | payload[7];

        snprintf(out_text,
                 max_len,
                 "ICMPv6 %s ID:%u Seq:%u",
                 type_name,
                 id,
                 seq);

        return true;
    }


    // -----------------------------------------------------
    // ROUTER SOLICITATION
    //
    // Fixed body = 4 reserved bytes
    // Options begin at offset 8.
    // -----------------------------------------------------

    if (type == 133) {

        if (length < 8) {
            snprintf(out_text,
                     max_len,
                     "ICMPv6 RS (Malformed)");
            return true;
        }

        snprintf(out_text,
                 max_len,
                 "ICMPv6 Router Solicitation");

        return true;
    }


    // -----------------------------------------------------
    // ROUTER ADVERTISEMENT
    //
    // Fixed body:
    //
    // 4   Type/Code/Checksum
    // 1   Cur Hop Limit
    // 1   Flags
    // 2   Router Lifetime
    // 4   Reachable Time
    // 4   Retrans Timer
    //
    // Options begin at offset 16.
    // -----------------------------------------------------

    if (type == 134) {

        if (length < 16) {
            snprintf(out_text,
                     max_len,
                     "ICMPv6 RA (Malformed)");
            return true;
        }

        uint8_t hop_limit = payload[4];
        uint8_t flags = payload[5];

        uint16_t lifetime =
            ((uint16_t)payload[6] << 8) | payload[7];

        bool managed = (flags & 0x80) != 0;
        bool other   = (flags & 0x40) != 0;

        char prefix_buf[96] = {0};
        char dns_buf[128] = {0};
        char search_buf[128] = {0};
        char mtu_buf[32] = {0};

        int offset = 16;

        while (offset + 2 <= length) {

            uint8_t opt_type = payload[offset];
            uint8_t opt_units = payload[offset + 1];

            // ND option length is in units of 8 bytes.
            if (opt_units == 0)
                break;

            int opt_len = opt_units * 8;

            if (opt_len < 8 ||
                opt_len > length - offset)
                break;

            int opt_data = offset + 2;

            // -------------------------------------------------
            // Source Link-Layer Address
            // -------------------------------------------------

            if (opt_type == 1 && opt_len >= 8) {

                snprintf(out_text + strlen(out_text),
                         max_len - strlen(out_text),
                         "\nSLLA:%02X:%02X:%02X:%02X:%02X:%02X",
                         payload[opt_data],
                         payload[opt_data + 1],
                         payload[opt_data + 2],
                         payload[opt_data + 3],
                         payload[opt_data + 4],
                         payload[opt_data + 5]);
            }

            // -------------------------------------------------
            // Prefix Information
            //
            // Prefix length at +2.
            // Prefix itself at +14.
            // -------------------------------------------------

            else if (opt_type == 3 && opt_len >= 32) {

                uint8_t prefix_len = payload[opt_data];

                char ip[40] = {0};

                format_ipv6_addr(
                    &payload[opt_data + 14],
                    ip,
                    sizeof(ip));

                snprintf(prefix_buf,
                         sizeof(prefix_buf),
                         "%s/%u",
                         ip,
                         prefix_len);
            }

            // -------------------------------------------------
            // MTU
            // -------------------------------------------------

            else if (opt_type == 5 && opt_len >= 8) {

                uint32_t mtu =
                    ((uint32_t)payload[opt_data + 2] << 24) |
                    ((uint32_t)payload[opt_data + 3] << 16) |
                    ((uint32_t)payload[opt_data + 4] << 8) |
                    payload[opt_data + 5];

                snprintf(mtu_buf,
                         sizeof(mtu_buf),
                         "%lu",
                         (unsigned long)mtu);
            }

            // -------------------------------------------------
            // RDNSS
            //
            // Option:
            // +0  Reserved
            // +4  Lifetime
            // +8  IPv6 addresses
            // -------------------------------------------------

            else if (opt_type == 25 &&
                     opt_len >= 24 &&
                     ((opt_len - 8) % 16 == 0)) {

                int dns_idx = 0;

                dns_idx += snprintf(
                    dns_buf + dns_idx,
                    sizeof(dns_buf) - dns_idx,
                    "DNS:");

                for (int p = opt_data + 8;
                     p + 16 <= offset + opt_len;
                     p += 16) {

                    if (dns_idx >=
                        (int)sizeof(dns_buf) - 42)
                        break;

                    char ip[40] = {0};

                    format_ipv6_addr(
                        &payload[p],
                        ip,
                        sizeof(ip));

                    dns_idx += snprintf(
                        dns_buf + dns_idx,
                        sizeof(dns_buf) - dns_idx,
                        " %s",
                        ip);
                }
            }

            // -------------------------------------------------
            // DNSSL
            //
            // +0  Reserved
            // +4  Lifetime
            // +8  Domain Names
            // -------------------------------------------------

            else if (opt_type == 31 &&
                     opt_len >= 16) {

                int res = decode_dns_search_list(
                    &payload[opt_data + 6],
                    opt_len - 6,
                    search_buf,
                    sizeof(search_buf));

                if (res < 0)
                    search_buf[0] = '\0';
            }

            offset += opt_len;
        }

        // -----------------------------------------------------
        // Construct compact display.
        //
        // RA is one of the most information-rich packets,
        // so prioritize:
        //
        //   Router / flags
        //   Prefix
        //   DNS
        //   Search domain
        //   MTU
        // -----------------------------------------------------

        int written = snprintf(
            out_text,
            max_len,
            "ICMPv6 RA HL:%u LT:%u M:%u O:%u",
            hop_limit,
            lifetime,
            managed ? 1 : 0,
            other ? 1 : 0);

        if (prefix_buf[0] &&
            written < (int)max_len) {

            written += snprintf(
                out_text + written,
                max_len - written,
                "\nPrefix:%s",
                prefix_buf);
        }

        if (dns_buf[0] &&
            written < (int)max_len) {

            written += snprintf(
                out_text + written,
                max_len - written,
                "\n%s",
                dns_buf);
        }

        if (search_buf[0] &&
            written < (int)max_len) {

            written += snprintf(
                out_text + written,
                max_len - written,
                "\nSearch:%s",
                search_buf);
        }

        if (mtu_buf[0] &&
            written < (int)max_len) {

            snprintf(
                out_text + written,
                max_len - written,
                "\nMTU:%s",
                mtu_buf);
        }

        return true;
    }


    // -----------------------------------------------------
    // NEIGHBOR SOLICITATION
    //
    // Fixed body:
    // 4 reserved bytes
    // 16-byte Target Address
    //
    // Options begin at offset 24.
    // -----------------------------------------------------

    if (type == 135) {

        if (length < 24) {
            snprintf(out_text,
                     max_len,
                     "ICMPv6 NS (Malformed)");
            return true;
        }

        char target[40] = {0};

        format_ipv6_addr(
            &payload[8],
            target,
            sizeof(target));

        snprintf(out_text,
                 max_len,
                 "ICMPv6 NS Target:%s",
                 target);

        return true;
    }


    // -----------------------------------------------------
    // NEIGHBOR ADVERTISEMENT
    //
    // Fixed body:
    // 4 flags/reserved
    // 16 Target Address
    //
    // Options begin at offset 24.
    // -----------------------------------------------------

    if (type == 136) {

        if (length < 24) {
            snprintf(out_text,
                     max_len,
                     "ICMPv6 NA (Malformed)");
            return true;
        }

        uint32_t flags =
            ((uint32_t)payload[4] << 24) |
            ((uint32_t)payload[5] << 16) |
            ((uint32_t)payload[6] << 8) |
            payload[7];

        char target[40] = {0};

        format_ipv6_addr(
            &payload[8],
            target,
            sizeof(target));

        bool router =
            (flags & 0x80000000UL) != 0;

        bool solicited =
            (flags & 0x40000000UL) != 0;

        bool override =
            (flags & 0x20000000UL) != 0;

        snprintf(out_text,
                 max_len,
                 "ICMPv6 NA %s R:%u S:%u O:%u",
                 target,
                 router ? 1 : 0,
                 solicited ? 1 : 0,
                 override ? 1 : 0);

        return true;
    }


    // -----------------------------------------------------
    // MLD
    // -----------------------------------------------------

    if (type == 130 ||
        type == 131 ||
        type == 132 ||
        type == 143) {

        snprintf(out_text,
                 max_len,
                 "ICMPv6 %s",
                 type_name);

        return true;
    }


    // -----------------------------------------------------
    // FALLBACK
    // -----------------------------------------------------

    snprintf(out_text,
             max_len,
             "ICMPv6 [%u] %s Code:%u",
             type,
             type_name,
             code);

    return true;
}

// ==========================================
// TKIP/WEP RATE LIMITER (ISR SAFE)
// ==========================================
// Returns true if we should push this alert to the queue
bool should_alert_crypto(const uint8_t* mac_a, const uint8_t* mac_b, uint32_t current_ms) {
    
    // --- THE MAC NORMALIZATION FIX ---
    // Always store the numerically smaller MAC first. 
    // This collapses AP->STA and STA->AP into a single bidirectional conversation slot.
    const uint8_t* lo = (memcmp(mac_a, mac_b, 6) <= 0) ? mac_a : mac_b;
    const uint8_t* hi = (lo == mac_a) ? mac_b : mac_a;

    int oldest_idx = 0;
    uint32_t oldest_time = 0xFFFFFFFF;

    // 1. Scan the cache for a match AND track the oldest slot simultaneously
    for (int i = 0; i < ALERT_CACHE_SIZE; i++) {
        
        // Match found using the normalized MACs!
        if (memcmp(crypto_cache[i].mac_src, lo, 6) == 0 &&
            memcmp(crypto_cache[i].mac_dst, hi, 6) == 0) {
            
            if (current_ms - crypto_cache[i].last_alert_ms > SEC_COOLDOWN_MS) {
                crypto_cache[i].last_alert_ms = current_ms;
                return true;
            }
            return false; // Still in cooldown
        }

        // --- THE LRU EVICTION FIX ---
        // Keep track of the stalest entry in case we need to evict.
        if (crypto_cache[i].last_alert_ms < oldest_time) {
            oldest_time = crypto_cache[i].last_alert_ms;
            oldest_idx = i;
        }
    }
    
    // 2. New flow: Overwrite the genuinely oldest slot (True LRU)
    memcpy(crypto_cache[oldest_idx].mac_src, lo, 6);
    memcpy(crypto_cache[oldest_idx].mac_dst, hi, 6);
    crypto_cache[oldest_idx].last_alert_ms = current_ms;
    
    return true;
}

void drawTelemetryHeader() {
    // 1. Snapshot the volatile variables
    uint32_t current_total = ui_total_arrived;
    uint32_t current_drops = ui_dropped_packets;

    // 2. Reset the counters for the next 3-second window
    ui_total_arrived = 0;
    ui_dropped_packets = 0;

    // 3. Calculate how many successfully entered the queue
    uint32_t current_processed = 0;
    if (current_total > current_drops) {
        current_processed = current_total - current_drops;
    }

    // 4. MATCH THE "OTHER" BANNER STYLING
    tft.setFreeFont(&UbuntuMono_Regular9pt7b);
    tft.setTextDatum(TL_DATUM); 
    tft.setTextColor(COLOR_HOT_CHEST, TFT_BLACK);
    
    // 5. Erase the old numbers (Aligned to the OTHER wipe zone, but slightly wider)
    tft.fillRect(285, 0, 135, 20, TFT_BLACK); 
    
    // 6. Format with strict 3-digit padding to prevent text jitter
    char stat_text[32];
    snprintf(stat_text, sizeof(stat_text), "Pkts:%3u/%3u", current_processed, current_total);
    
    // 7. Draw the string exactly where OTHER goes
    tft.drawString(stat_text, 285, 1);
}

bool parse_eapol(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (!payload || !out_text || max_len == 0 || length < 2)
        return false;

    uint8_t eapol_type = payload[1];

    switch (eapol_type) {
        case 0:
            snprintf(out_text, max_len, "EAPOL: EAP Packet (802.1X Auth)");
            return true;
        case 1:
            snprintf(out_text, max_len, "EAPOL: Start");
            return true;
        case 2:
            snprintf(out_text, max_len, "EAPOL: Logoff");
            return true;
        case 3: {   // EAPOL-Key
            if (length < 7) {
                snprintf(out_text, max_len, "EAPOL-Key (Malformed)");
                return true;
            }

            uint8_t desc_type = payload[4];
            const char* desc_str = "UNK";
            if (desc_type == 2) desc_str = "RSN";
            else if (desc_type == 254) desc_str = "WPA";

            uint16_t key_info = ((uint16_t)payload[5] << 8) | payload[6];
            bool pairwise   = (key_info & 0x0008) != 0;
            bool install    = (key_info & 0x0040) != 0;
            bool ack        = (key_info & 0x0080) != 0;
            bool mic        = (key_info & 0x0100) != 0;
            bool secure     = (key_info & 0x0200) != 0;

            const char* msg_type = "Unknown";
            int msg_num = 0; 

            if (pairwise) {
                if (ack && !mic) { msg_type = "M1 (AP->STA)"; msg_num = 1; }
                else if (!ack && mic && !secure) { msg_type = "M2 (STA->AP)"; msg_num = 2; }
                else if (ack && mic && install && secure) { msg_type = "M3 (AP->STA)"; msg_num = 3; }
                else if (!ack && mic && !install && secure) { msg_type = "M4 (STA->AP)"; msg_num = 4; }
            } else {
                msg_type = "Group/Other Key";
            }

            // --- CRYPTO EXTRACTION BLOCK ---
            bool have_nonce = (length >= 49); // offset 17 + 32 bytes
            bool have_mic   = (length >= 97); // offset 81 + 16 bytes

            if (msg_num > 0 && have_nonce) { 
                char nonce_hex[65] = {0}; 
                char mic_hex[33] = {0};   

                const uint8_t* p_nonce = &payload[17];
                for (int i = 0; i < 32; i++) {
                    snprintf(&nonce_hex[i * 2], 3, "%02X", p_nonce[i]);
                }

                if (have_mic) {
                    const uint8_t* p_mic = &payload[81];
                    for (int i = 0; i < 16; i++) {
                        snprintf(&mic_hex[i * 2], 3, "%02X", p_mic[i]);
                    }
                }

                if (msg_num == 1) {
                    snprintf(out_text, max_len, "EAPOL-Key [%s]: %s | ANonce: %s", desc_str, msg_type, nonce_hex);
                } else if (msg_num == 2 && have_mic) {
                    snprintf(out_text, max_len, "EAPOL-Key [%s]: %s | SNonce: %s | MIC: %s", desc_str, msg_type, nonce_hex, mic_hex);
                } else if (msg_num == 3 && have_mic) {
                    snprintf(out_text, max_len, "EAPOL-Key [%s]: %s | ANonce: %s | MIC: %s", desc_str, msg_type, nonce_hex, mic_hex);
                } else if (msg_num == 4 && have_mic) {
                    snprintf(out_text, max_len, "EAPOL-Key [%s]: %s | MIC: %s", desc_str, msg_type, mic_hex);
                } else {
                    // Fallback if M2/M3/M4 is truncated before the MIC
                    snprintf(out_text, max_len, "EAPOL-Key [%s]: %s (Truncated)", desc_str, msg_type);
                }
            } else {
                snprintf(out_text, max_len, "EAPOL-Key [%s]: %s", desc_str, msg_type);
            }

            return true;
        }
        case 4:
            snprintf(out_text, max_len, "EAPOL: Encapsulated-ASF-Alert");
            return true;
        default:
            snprintf(out_text, max_len, "EAPOL: Unknown Type %d", eapol_type);
            return true;
    }
}

bool parse_ssh(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // Defensive entry guard: valid pointers, minimum payload size, and sufficient output buffer
    if (length < 10 || payload == nullptr || out_text == nullptr || max_len < 16) {
        return false;
    }

    // SSH banners are strictly required to sit at the absolute beginning of the payload
    if (memcmp(payload, "SSH-", 4) == 0) {
        const char* p = (const char*)payload;
        const char* end = p;
        const char* payload_end = p + length;

        // Read until the end of the line (usually \r\n)
        while (end < payload_end && *end != '\r' && *end != '\n') end++;

        // Safely bound the copy to our UI limits
        int copy_len = std::min((int)(end - p), (int)(max_len - 15));
        if (copy_len > 0) {
            snprintf(out_text, max_len, "SSH Banner: %.*s", copy_len, p);
            return true;
        }
    }
    return false;
}

bool parse_rdp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // Defensive entry guard: valid pointers, minimum payload size, and sufficient output buffer
    if (length < 17 || payload == nullptr || out_text == nullptr || max_len < 40) {
        return false;
    }

    // Fast gate: RDP X.224 Connection Requests ride on top of TPKT.
    // TPKT headers always start with Version 3 (0x03) and Reserved (0x00).
    if (payload[0] != 0x03 || payload[1] != 0x00) return false;

    const char* p = (const char*)payload;
    const char* payload_end = p + length;
    
    // The needle is 17 bytes long. Signed int prevents underflow.
    int max_i = (int)length - 17; 

    // Sliding window to hunt for the routing cookie
    for (int i = 0; i <= max_i; i++) {
        if (memcmp(&p[i], "Cookie: mstshash=", 17) == 0) {
            const char* user_start = &p[i + 17];
            const char* user_end = user_start;
            
            // Read the username until we hit a newline or space
            while (user_end < payload_end && *user_end != '\r' && *user_end != '\n' && *user_end != ' ') {
                user_end++;
            }

            int copy_len = std::min((int)(user_end - user_start), (int)(max_len - 30));
            if (copy_len > 0) {
                snprintf(out_text, max_len, "RDP Connect [User: %.*s]", copy_len, user_start);
                return true;
            }
        }
    }
    
    // Fallback: It passed the TPKT gate but didn't have a username cookie.
    // Is it actually an initial Connection Request (X.224 CR)? 
    // Byte 5 must be 0xE0 for a Connection Request.
    if (length > 5 && payload[5] == 0xE0) {
        snprintf(out_text, max_len, "RDP Connection Request (No Cookie)");
        return true;
    }

    // It is just ordinary TPKT-framed encrypted RDP traffic (e.g., mouse movements).
    // Silently ignore it to prevent display spam.
    return false;
}

// --- The Smart Endpoint Wi-Fi Sniffer Callback ---
void sniffer_callback(void* buf, wifi_promiscuous_pkt_type_t type) {
  if (pause_sniffing) return;
  wifi_promiscuous_pkt_t *pkt = (wifi_promiscuous_pkt_t *)buf;
  uint16_t len = pkt->rx_ctrl.sig_len;
  uint8_t* payload = pkt->payload;

  if (len < 24) return; // Safety check ensures bytes 22 and 23 exist!

  // Extract MAC addresses immediately since we need them for both modes
  uint8_t* addr1 = payload + 4;  // Receiver
  uint8_t* addr2 = payload + 10; // Transmitter
  uint8_t* mac3 = payload + 16;  // BSSID / Source / Dest

  // ==========================================
  // DIRECT FOXHUNT ISR FEEDER (GLOBAL)
  // ==========================================
  if (is_foxhunting) {
      // Pre-calculate to keep the ISR blazing fast
      bool target_is_tx = (memcmp(addr2, foxhunt_target_mac, 6) == 0);

      if (currentRadioMode == RADIO_AP || currentRadioMode == RADIO_WIFI) {
          
          // THE PHYSICS FIX (Signal Strength)
          // ONLY feed the math engine if our target is the physical transmitter.
          // Because we require an AP lock first, the channel is already frozen.
          // We don't need any dynamic channel-locking logic here!
          if (target_is_tx) {
              updateFoxhuntSignal(pkt->rx_ctrl.rssi);
          }
      }
  }
  // ==========================================

  // ==========================================
  // NEW: MODE-AGNOSTIC PASSIVE SSID SCRAPER 
  // Runs in ALL modes to silently maintain the BSSID Cache
  // ==========================================
  uint16_t fc = payload[0] | (payload[1] << 8);
  
  // Check if Beacon (0x80) or Probe Response (0x50)
  if ((fc & 0xFF) == 0x80 || (fc & 0xFF) == 0x50) {
      // Address 3 (mac3) is the BSSID in these frames
      int offset = 36; // Skip MAC header (24 bytes) + Fixed Mgmt Params (12 bytes)
      
      if (offset + 1 < len && payload[offset] == 0x00) { // Tag 0 is SSID
          uint8_t ssid_len = payload[offset + 1];
          
          if (ssid_len > 0 && ssid_len <= 32 && (offset + 2 + ssid_len) <= len) {
              int target_idx = -1;
              int oldest_idx = 0;
              uint32_t oldest_time = 0xFFFFFFFF;
              
              for (int i = 0; i < MAX_BSSID_CACHE; i++) {
                  if (memcmp(bssidCache[i].bssid, mac3, 6) == 0) {
                      target_idx = i;
                      break;
                  }
                  if (bssidCache[i].last_seen < oldest_time) {
                      oldest_time = bssidCache[i].last_seen;
                      oldest_idx = i;
                  }
              }
              
              if (target_idx == -1) target_idx = oldest_idx;
              
              memcpy(bssidCache[target_idx].bssid, mac3, 6);
              memcpy(bssidCache[target_idx].ssid, &payload[offset + 2], ssid_len);
              bssidCache[target_idx].ssid[ssid_len] = '\0';
              bssidCache[target_idx].last_seen = millis();
          }
      }
  }
  // ==========================================

  // ==========================================
  // BYPASS: AP WATERFALL MODE FUNNEL
  // ==========================================
  if (currentRadioMode == RADIO_AP) {
    
    // PART 1: THE DICTIONARY (Catch Beacons to learn SSIDs)
    if (type == WIFI_PKT_MGMT) {
      uint8_t subtype = (payload[0] >> 4) & 0x0F;
      
      // Subtype 8 is a Beacon Frame
      if (subtype == 8) { 
        int ap_index = -1;
        for (int i = 0; i < liveApCount; i++) {
          if (memcmp((void*)liveApData[i].bssid, addr2, 6) == 0) {
            ap_index = i;
            break;
          }
        }
        
        if (ap_index == -1) {
          if (liveApCount < MAX_AP_RECORDS) {
            // Space available, claim the next slot
            ap_index = liveApCount;
            liveApCount++;
          } else {
            // ==========================================
            // THE STALE & WEAK HYBRID EVICTION
            // ==========================================
            unsigned long now = millis();
            int stalest_idx = 0;
            int weakest_idx = 0;
            unsigned long oldest_time = 0xFFFFFFFF;
            int lowest_rssi = 127; // Max possible int8_t

            for (int i = 0; i < MAX_AP_RECORDS; i++) {
              if (liveApData[i].last_seen < oldest_time) {
                oldest_time = liveApData[i].last_seen;
                stalest_idx = i;
              }
              if (liveApData[i].rssi < lowest_rssi) {
                lowest_rssi = liveApData[i].rssi;
                weakest_idx = i;
              }
            }

            // 1. The Ghost Hunt (Evict if silent for > 60 seconds)
            if ((now - oldest_time) > 60000) {
              ap_index = stalest_idx;
            }
            // 2. The Weakest Link (Evict if new AP is stronger than our worst AP)
            else if (pkt->rx_ctrl.rssi > lowest_rssi) {
              ap_index = weakest_idx;
            }
          }

          // If we successfully claimed a slot (either a new one or an evicted one)
          if (ap_index != -1) {
            
            // --- NEW: EVICTION SAFETY INIT ---
            // Explicitly clear the country memory before the IE walk so 
            // the new AP doesn't inherit a stale code from the previous occupant.
            liveApData[ap_index].country[0] = '\0';
            liveApData[ap_index].country[1] = '\0';
            liveApData[ap_index].country[2] = '\0';
            // ---------------------------------

            // ==========================================
            // THE BEACON DECODER (Extract True Channel & SSID)
            // ==========================================
            uint8_t true_channel = CHANNELS[current_ch_idx]; // Fallback to current hopper
            char extracted_ssid[32] = "<HIDDEN>"; // Default to hidden
            
            // Beacons have a 24-byte MAC Header + 12-byte Fixed Parameters = 36 bytes before Tags begin.
            int offset = 36; 
            
            while (offset < len - 4) { // Loop through tags, stopping before the 4-byte FCS checksum
              uint8_t tag_num = payload[offset];
              uint8_t tag_len = payload[offset + 1];
              
              if (offset + 2 + tag_len > len) break; // Memory safety bounds check
              
              // Tag 0: SSID
              if (tag_num == 0) {
                if (tag_len > 0 && tag_len <= 31) {
                  memcpy(extracted_ssid, payload + offset + 2, tag_len);
                  extracted_ssid[tag_len] = '\0'; // Null terminate
                }
              }
              // Tag 3: DS Parameter Set (Current Channel)
              else if (tag_num == 3 && tag_len == 1) {
                true_channel = payload[offset + 2];
              }
              // --- NEW: TAG 7 COUNTRY CODE PARSER ---
              else if (tag_num == 7 && tag_len >= 2) {
                uint8_t c0 = payload[offset + 2];
                uint8_t c1 = payload[offset + 3];
                
                // Sanity check: valid ISO country codes are uppercase ASCII letters
                if (c0 >= 'A' && c0 <= 'Z' && c1 >= 'A' && c1 <= 'Z') {
                    liveApData[ap_index].country[0] = c0;
                    liveApData[ap_index].country[1] = c1;
                    liveApData[ap_index].country[2] = '\0';
                }
              }
              // --------------------------------------
              offset += 2 + tag_len; // Jump to the next tag
            }
            ingestBeacon(addr2, extracted_ssid, pkt->rx_ctrl.rssi);

            // ==========================================
            // POPULATE THE AP RECORD
            // ==========================================
            memcpy((void*)liveApData[ap_index].bssid, addr2, 6);
            
            unsigned long now = millis();
            liveApData[ap_index].first_seen = now;
            liveApData[ap_index].last_seen = now;
            liveApData[ap_index].packets = 0;
            liveApData[ap_index].sum_bytes = 0;
            liveApData[ap_index].sum_sq_bytes = 0;
            liveApData[ap_index].tx_bytes = 0;
            liveApData[ap_index].rx_bytes = 0;
            liveApData[ap_index].max_rate = 0;
            liveApData[ap_index].rssi = pkt->rx_ctrl.rssi;
            liveApData[ap_index].rssi_min = pkt->rx_ctrl.rssi;
            liveApData[ap_index].rssi_max = pkt->rx_ctrl.rssi;
            liveApData[ap_index].channel = true_channel; // <--- INJECT THE TRUE CHANNEL
            
            // ssid is char ssid[26] — trimmed from 28 to accommodate rssi_min/rssi_max
            strncpy((char*)liveApData[ap_index].ssid, extracted_ssid, sizeof(liveApData[ap_index].ssid));
            
            // ADD THIS LINE: Force null termination to prevent runaway memory reads
            liveApData[ap_index].ssid[sizeof(liveApData[ap_index].ssid) - 1] = '\0';

            // ==========================================
            // NEW: O(N) CLONE DETECTION ON DISCOVERY
            // ==========================================
            liveApData[ap_index].has_clone = false;

            if (strlen((char*)liveApData[ap_index].ssid) > 0 && 
                strcmp((char*)liveApData[ap_index].ssid, "<HIDDEN>") != 0 && 
                strcmp((char*)liveApData[ap_index].ssid, "<UNKNOWN>") != 0) {
                
                for (int i = 0; i < liveApCount; i++) {
                    // Skip self-comparison (crucial if ap_index claimed an evicted slot)
                    if (i == ap_index) continue;

                    if (strcmp((char*)liveApData[i].ssid, (char*)liveApData[ap_index].ssid) == 0) {
                        liveApData[ap_index].has_clone = true;
                        liveApData[i].has_clone = true;
                        break; 
                    }
                }
            }
            // ==========================================

          } // Closes `if (ap_index != -1)`
        } // Closes `if (ap_index == -1)`

        // If the AP made it into the array, update metadata but IGNORE TRAFFIC MATH!
        if (ap_index != -1) {
          liveApData[ap_index].last_seen = millis();
          liveApData[ap_index].rssi = pkt->rx_ctrl.rssi; 
          if (pkt->rx_ctrl.rssi < liveApData[ap_index].rssi_min) {
              liveApData[ap_index].rssi_min = pkt->rx_ctrl.rssi;
          }
          // rssi_max == 0 means uninitialized — same sentinel logic as MacRecord
          if (pkt->rx_ctrl.rssi > liveApData[ap_index].rssi_max || 
              liveApData[ap_index].rssi_max == 0) {
              liveApData[ap_index].rssi_max = pkt->rx_ctrl.rssi;
          }
          // --- TRAFFIC COUNTERS INTENTIONALLY DELETED HERE ---
          // We only want WIFI_PKT_DATA frames (handled below) to trigger the math engine!

          uint8_t current_rate = getBitrateMbps(pkt);
          if (current_rate > liveApData[ap_index].max_rate) {
              liveApData[ap_index].max_rate = current_rate;
          }
        }
      }
    }

    // PART 2: THE COUNTER (Catch Data frames to measure volume)
    else if (type == WIFI_PKT_DATA) {
      for (int i = 0; i < liveApCount; i++) {
        bool is_tx = (memcmp((void*)liveApData[i].bssid, addr2, 6) == 0);
        bool is_rx = (memcmp((void*)liveApData[i].bssid, addr1, 6) == 0);
        
        if (is_tx || is_rx) {
          liveApData[i].packets += 1;
          liveApData[i].sum_bytes += len;
          liveApData[i].sum_sq_bytes += ((uint64_t)len * len);
          liveApData[i].rssi = pkt->rx_ctrl.rssi;
          liveApData[i].last_seen = millis();
          
          // Max Rate Trap: Only update if the new packet is faster!
          uint8_t current_rate = getBitrateMbps(pkt);
          if (current_rate > liveApData[i].max_rate) {
              liveApData[i].max_rate = current_rate;
          }

          // Route the traffic
          if (is_tx) liveApData[i].tx_bytes += len;
          else       liveApData[i].rx_bytes += len;
          
          break; 
        }
      }
    }
    
    return; // Returns cleanly from RADIO_AP mode
  }

  // ==========================================
  // BYPASS: CHANNEL SPECTRUM MODE
  // ==========================================
  if (currentRadioMode == RADIO_CHANNELS) {
    uint8_t ch = CHANNELS[current_ch_idx];
    int idx = -1; 

    // 1. Search for the active channel in our existing array
    for (int i = 0; i < liveChannelCount; i++) {
        if (liveChannelData[i].channel == ch) {
            idx = i;
            break;
        }
    }

    // 2. If it's a completely new channel, claim the next available slot
    if (idx == -1) {
        if (liveChannelCount < MAX_CHANNEL_RECORDS) {
            idx = liveChannelCount;
            liveChannelData[idx].channel = ch;
            unsigned long now = millis();
            liveChannelData[idx].first_seen = now;
            liveChannelData[idx].last_seen = now;
            
            // Seed the physics engine
            liveChannelData[idx].avg_rssi = (float)pkt->rx_ctrl.rssi;
            liveChannelData[idx].prev_rssi = (float)pkt->rx_ctrl.rssi; // Remember the very first packet
            liveChannelData[idx].ema_variance = 0.0; 
            liveChannelData[idx].ema_cov = 0.0;      
            
            liveChannelCount++; 
        } else {
            return; 
        }
    }

    // 3. Process the packet exactly as before
    liveChannelData[idx].packets += 1;
    liveChannelData[idx].sum_bytes += len;
    liveChannelData[idx].sum_sq_bytes += ((uint64_t)len * len);
    liveChannelData[idx].last_seen = millis();
    
    // --- EMA MEAN, VARIANCE, & COVARIANCE CALCULATION ---
    float alpha = 0.05; // 5% weight to new packets, 95% to history
    float current_rssi = (float)pkt->rx_ctrl.rssi;
    
    // 1. Calculate the difference from the mean for the CURRENT packet
    float diff = current_rssi - liveChannelData[idx].avg_rssi;
    
    // 2. Calculate the difference from the mean for the PREVIOUS packet
    float prev_diff = liveChannelData[idx].prev_rssi - liveChannelData[idx].avg_rssi;
    
    // 3. Update Autocovariance (Must happen before updating variance/mean)
    liveChannelData[idx].ema_cov = (1.0 - alpha) * (liveChannelData[idx].ema_cov + alpha * diff * prev_diff);
    
    // 4. Update Variance
    liveChannelData[idx].ema_variance = (1.0 - alpha) * (liveChannelData[idx].ema_variance + alpha * diff * diff);
    
    // 5. Update Mean
    liveChannelData[idx].avg_rssi += (alpha * diff);
    
    // 6. Store current RSSI into memory for the next packet's covariance check
    liveChannelData[idx].prev_rssi = current_rssi;
    
    // --- UPLINK / DOWNLINK ROUTER ---
    uint8_t ds_flags = payload[1] & 0x03;
    bool to_ds   = (ds_flags & 0x01); // Client -> AP
    bool from_ds = (ds_flags & 0x02); // AP -> Client

    bool is_uplink = false;
    if (to_ds && !from_ds) is_uplink = true;
    else if (payload[0] == 0x40) is_uplink = true; // Probe Requests

    if (is_uplink) liveChannelData[idx].rx_bytes += len; 
    else           liveChannelData[idx].tx_bytes += len; 

    return; 
  }

  // ==========================================
  // PROBE REQUEST BOUNCER (Runs only in WIFI mode)
  // ==========================================
  // Check if Frame Control byte 0 is 0x40 (Subtype 4: Probe Request)
  if (payload[0] == 0x40) {
    
  /*  
    // --- SAFE HEX DUMPER FOR IE DEBUGGING ---
    static unsigned long last_debug_dump = 0;
    if (millis() - last_debug_dump > 2000) { // Only dump one packet every 2 seconds
        last_debug_dump = millis();
        
        Serial.printf("\n--- PROBE REQUEST IE DUMP (MAC: %02X:%02X:%02X:%02X:%02X:%02X) ---\n", 
                      addr2[0], addr2[1], addr2[2], addr2[3], addr2[4], addr2[5]);
        
        // Probe Requests have no fixed parameters, tags start exactly at byte 24
        int debug_offset = 24; 
        
        while (debug_offset < len - 4) { // Stop before the 4-byte FCS checksum
            uint8_t tag_num = payload[debug_offset];
            uint8_t tag_len = payload[debug_offset + 1];
            
            if (debug_offset + 2 + tag_len > len) break; // Memory safety boundary
            
            // Print the Tag ID and Length
            Serial.printf("Tag %3d (0x%02X) | Len: %2d | Data: ", tag_num, tag_num, tag_len);
            
            // Print the raw Hex payload of the tag
            for (int d = 0; d < tag_len; d++) {
                Serial.printf("%02X ", payload[debug_offset + 2 + d]);
            }
            
            // If it is an SSID (Tag 0), print the human-readable ASCII next to it
            if (tag_num == 0 && tag_len > 0) {
                Serial.print("  (\"");
                for (int d = 0; d < tag_len; d++) {
                    char c = payload[debug_offset + 2 + d];
                    if (c >= 32 && c <= 126) Serial.print(c); // Printable ASCII
                    else Serial.print('.');                   // Unprintable character
                }
                Serial.print("\")");
            }
            Serial.println(); // Next tag
            
            debug_offset += 2 + tag_len; // Jump to the next tag in the chain
        }
        Serial.println("-----------------------------------------------------------\n");
    }
    // ----------------------------------------
*/
    // ==========================================
    // THE SMART BOUNCER & IE PARSER
    // ==========================================
    bool is_randomized = (addr2[0] & 0x02) != 0;
    
    int offset = 24; 
    char final_ssid[33] = "";
    bool is_valid_ssid = false; 
    
    char ie_vendor[25] = "";    
    uint8_t highest_weight_found = 0; // Resets for every new packet
    uint32_t live_hw_hash = 5381;
    // 1. FIRST PASS: Parse the IE tags to build the profile
    while (offset < len - 4) {
      uint8_t tag_num = payload[offset];
      uint8_t tag_len = payload[offset + 1];
      
      if (offset + 2 + tag_len > len) break; // Memory safety boundary
      
      // --- BUILD THE HARDWARE HASH ---
      // 1. Always hash the tag_num (Captures the structural skeleton)
      live_hw_hash = ((live_hw_hash << 5) + live_hw_hash) + tag_num;

      // 2. Selectively hash the payload (Captures the unchangeable DNA)
      // Tag 45: HT Caps | Tag 127: Ext Caps | Tag 221: Vendor Specific
      if (tag_num == 45 || tag_num == 127 || tag_num == 221) {
          for (int p = 0; p < tag_len; p++) {
              live_hw_hash = ((live_hw_hash << 5) + live_hw_hash) + payload[offset + 2 + p];
          }
      }
      // ------------------------------------

      // Extract the SSID (Tag 0)
      if (tag_num == 0) {
        if (tag_len == 0) {
          strlcpy(final_ssid, "<Wld>", sizeof(final_ssid));
        } 
        else if (tag_len <= 32) {
          if (payload[offset + 2] == 0x00) {
            strlcpy(final_ssid, "<Nul>", sizeof(final_ssid));
          } else {
            bool has_valid_chars = false;
            for (int c = 0; c < tag_len; c++) {
              char ch = payload[offset + 2 + c];
              if (ch >= 32 && ch <= 126) {
                final_ssid[c] = ch;
                has_valid_chars = true; 
              } else {
                final_ssid[c] = '.';
              }
            }
            final_ssid[tag_len] = '\0';
            
            if (has_valid_chars) {
              is_valid_ssid = true; // Valid printable network name found!
            } else {
              strlcpy(final_ssid, "<Nul>", sizeof(final_ssid));
            }
          }
        }
      }
      
      // Extract the True Vendor via Tag 221
      else if (tag_num == 221 && tag_len >= 3) {
        // Search the compiled array from your include/tag221Lookup.h file
        for (int v = 0; v < TAG_221_COUNT; v++) {
          if (payload[offset+2] == TAG_221_DATABASE[v].oui[0] && 
              payload[offset+3] == TAG_221_DATABASE[v].oui[1] && 
              payload[offset+4] == TAG_221_DATABASE[v].oui[2]) {
                
            if (TAG_221_DATABASE[v].weight > highest_weight_found) {
              highest_weight_found = TAG_221_DATABASE[v].weight;
              snprintf(ie_vendor, sizeof(ie_vendor), "%s~IE", TAG_221_DATABASE[v].name);
            }
            break; 
          }
        }
      }
      
      offset += 2 + tag_len; 
    }

    // 2. THE DECISION GATE
    // Universal Pass: Real MACs get through.
    // Conditional Pass: Randomized MACs only get through if targeting a named network.
    if (!is_randomized || (is_randomized && is_valid_ssid)) {
      if (strlen(final_ssid) > 0) { 
        
        // ONLY pass the Tag 221 guess if the MAC is randomized!
        // If it is a physical MAC, pass an empty string so Core 1 checks the SD Card.
        if (is_randomized) {
          processProbeRequestShared(addr2, final_ssid, ie_vendor, pkt->rx_ctrl.rssi, live_hw_hash);
        } else {
          processProbeRequestShared(addr2, final_ssid, "", pkt->rx_ctrl.rssi, live_hw_hash); 
        }
        
      }
    }    
    return; // EXIT EARLY: Do not let Management frames hit the bandwidth math!
  }
  // ==========================================
  // L2 handling:
  // ==========================================
  // 1. MASTER FRAME FILTER (Data & Deauths)
  // ==========================================
  uint8_t frame_type = payload[0] & 0x0C;
  uint8_t frame_subtype = (payload[0] & 0xF0) >> 4;

  // Allow Data frames (Type 0x08) AND Deauth frames (Type 0x00, Subtype 12)
  if (frame_type != 0x08 && !(frame_type == 0x00 && frame_subtype == 12)) return;

  // ==========================================
  // 2. INSTANT DEAUTH INTERCEPTOR
  // ==========================================
  if (frame_type == 0x00 && frame_subtype == 12) {
      uint32_t now_ms = xTaskGetTickCountFromISR() * portTICK_PERIOD_MS;
      
      // Management frame headers are strictly 24 bytes. 
      // The 2-byte Reason Code sits immediately after the header (Little-Endian).
      uint16_t reason_code = 0;
      if (len >= 26) {
          reason_code = payload[24] | (payload[25] << 8);
      }

      Layer2Capture leak;
      memset(&leak, 0, sizeof(Layer2Capture));
      
      leak.meta.timestamp = now_ms;
      leak.meta.frame_length = pkt->rx_ctrl.sig_len;
      leak.meta.channel = pkt->rx_ctrl.channel;
      leak.meta.frame_subtype = 12;
      leak.meta.is_high_value = true; // Deauths are always a massive red flag!
      
      // Address 1: Destination, Address 2: Source, Address 3: BSSID
      memcpy(leak.meta.dst_mac, payload + 4, 6);
      memcpy(leak.meta.src_mac, payload + 10, 6);
      memcpy(leak.meta.bssid, payload + 16, 6);

      // Create a highly visible alert using the Reason Code
      snprintf(leak.text, MAX_LEAK_STR_LEN - 1, "DEAUTH (Reason: %d)", reason_code);

      // Fire directly to the UI, completely bypassing the Data parser
      if (leakQueue != NULL) {
          leak_isr_attempts++;
          if (xQueueSendFromISR(leakQueue, &leak, NULL) != pdTRUE) leak_isr_dropped++;
      }
      // Fire directly to the UI, completely bypassing the Data parser
      //if (leakQueue != NULL) xQueueSendFromISR(leakQueue, &leak, NULL);
      // Fire directly to the UI and Logger, completely bypassing the Data parser
      //if (leakQueue != NULL) xQueueSendFromISR(leakQueue, &leak, NULL);
      //if (liveDumpQueue != NULL) xQueueSendFromISR(liveDumpQueue, &leak, NULL);
      
      return; 
  }

  // ==========================================
  // 3. LEAKY LAYER 2 CLEARTEXT EXTRACTOR
  // ==========================================
  if (currentRadioMode == RADIO_LAYER2) { // <-- THE CRITICAL GATE
      // 1. TALLY ABSOLUTE RF VOLUME (Before the gate!)
      l2_bytes_tick += pkt->rx_ctrl.sig_len;
      
      bool is_protected = (payload[1] & 0x40) != 0;
      
      if (!is_protected) {
          // ==========================================
          // DYNAMIC MAC HEADER SIZING (HT Control & WDS)
          // ==========================================
          bool is_qos = (payload[0] & 0x80) != 0;
          bool to_ds = (payload[1] & 0x01) != 0;
          bool from_ds = (payload[1] & 0x02) != 0;
          
          // FIX 1: Strict check for +HTC. The Order bit (0x80) only means +HTC 
          // if it is a QoS Data frame! Otherwise, it just means "Strictly Ordered".
          bool has_ht_ctrl = is_qos && ((payload[1] & 0x80) != 0); 
          
          uint8_t header_len = 24;          // Base MAC Header
          if (to_ds && from_ds) {
              header_len += 6;              // Address 4 present (WDS Bridge)
          }
          
          // --- SAFE QOS OFFSET ---
          // Save the exact location of the QoS Control field before HT Control shifts the header length!
          uint8_t qos_offset = header_len; 
          
          if (is_qos) {
              header_len += 2;              // QoS Control present
          }
          if (has_ht_ctrl) {
              header_len += 4;              // HT Control present
          }
          // ==========================================

          // --- METADATA EXTRACTION ---
          uint8_t captured_subtype = (payload[0] & 0xF0) >> 4;
          uint8_t captured_direction = payload[1] & 0x03; 
          uint8_t captured_channel = pkt->rx_ctrl.channel; 
          uint8_t captured_protocol = 0; 
          // --------------------------------
          
          if (len > header_len) {
              uint8_t* frame_body = payload + header_len;
              uint16_t body_len = len - header_len;
              
              // --- STRIP LLC, IP, AND UDP HEADERS ---
              uint16_t captured_src_port = 0;
              uint16_t captured_dst_port = 0;
              uint16_t ether_type = 0; 
              uint8_t tcp_flags = 0;   
              
              uint8_t captured_ip_version = 0;
              uint8_t captured_src_ip[16] = {0};
              uint8_t captured_dst_ip[16] = {0};

              // =======================================================
              // FIX 2: THE A-MSDU BYPASS
              // =======================================================
              bool is_amsdu = false;
              if (is_qos) {
                  is_amsdu = (payload[qos_offset] & 0x80) != 0;
              }

              if (is_amsdu) {
                  // Do NOT chop `body_len`. Do NOT step `frame_body`.
                  // Force an unknown protocol (255) so it bypasses all strict IP parsers.
                  // The ENTIRE massive aggregate blob will fall straight through to the Catch-All!
                  captured_protocol = 255;
              }
              
              // 1. Skip LLC/SNAP Header (8 bytes) if present AND not an A-MSDU.
              if (!is_amsdu && body_len > 8 && frame_body[0] == 0xAA && frame_body[1] == 0xAA) {
                  bool is_apple = (frame_body[3] == 0x00 && frame_body[4] == 0x17 && frame_body[5] == 0xF2);
                  ether_type = (frame_body[6] << 8) | frame_body[7]; // <--- GRAB ETHERTYPE HERE  
                  frame_body += 8;
                  body_len -= 8;

                  // --- NEW: APPLE AWDL SHIM BYPASS ---
                  // Apple AWDL injects a 6-byte shim before the real IPv6 header (86 DD).
                  // --- UPGRADED: APPLE AWDL SHIM BYPASS (SLIDING WINDOW) ---
                  if (is_apple && body_len > 8) {
                      // Apple's shim changes size. We hunt up to 16 bytes ahead for the IPv6 header (86 DD).
                      int shim_len = -1;
                      for (int s = 0; s < 16; s++) {
                          if (s + 1 < body_len && frame_body[s] == 0x86 && frame_body[s+1] == 0xDD) {
                              shim_len = s;
                              break;
                          }
                      }
                      
                      if (shim_len != -1) {
                          ether_type = 0x86DD; // Force the EtherType to IPv6
                          
                          // THE FIX: Step OVER the 86 DD bytes (+2) to reach the 0x60 IPv6 header!
                          frame_body += (shim_len + 2);
                          body_len -= (shim_len + 2);
                      }
                  }

                  // --- 802.1Q VLAN TAG STRIPPING ---
                  // If EtherType is 0x8100, the packet has a 4-byte VLAN tag injected before the IP header.
                  if (ether_type == 0x8100 && body_len > 4) {
                      // The real EtherType is located right after the 2-byte TCI (Tag Control Information)
                      ether_type = (frame_body[2] << 8) | frame_body[3];
                      frame_body += 4; // Step over the VLAN tag
                      body_len -= 4;
                  }
                  // --------------------------------------
              }

              // 2. Check for IPv4 (First nibble is 4)
              if (!is_amsdu && body_len > 20 && (frame_body[0] & 0xF0) == 0x40) {
                  captured_ip_version = 4;
                  // --- NEW: Read Logical IP Length to strip Wi-Fi FCS/Padding ---
                  uint16_t ip_total_len = (frame_body[2] << 8) | frame_body[3];
                  // Safety check: ensure IP length isn't larger than our physical capture
                  if (ip_total_len < body_len) {
                  body_len = ip_total_len; 
                  }
                  // --------------------------------------------------------------
                  // IPv4 Source IP is at offset 12, Destination IP is at offset 16
                  memcpy(captured_src_ip, &frame_body[12], 4);
                  memcpy(captured_dst_ip, &frame_body[16], 4);

                  uint8_t ip_header_len = (frame_body[0] & 0x0F) * 4;
                  
                  // 3. Check Protocol field (Byte 9) for UDP (17)
                  if (frame_body[9] == 17 && body_len > (ip_header_len + 8)) {
                      captured_protocol = 17;
                      uint8_t* udp_header = frame_body + ip_header_len;
                      captured_src_port = (udp_header[0] << 8) | udp_header[1];
                      captured_dst_port = (udp_header[2] << 8) | udp_header[3];
                      
                      frame_body += (ip_header_len + 8);
                      body_len -= (ip_header_len + 8);
                  }
                  // 4. Check Protocol field for TCP (6)
                  else if (frame_body[9] == 6 && body_len > (ip_header_len + 20)) {
                      captured_protocol = 6;
                      uint8_t* tcp_header = frame_body + ip_header_len;
                      captured_src_port = (tcp_header[0] << 8) | tcp_header[1];
                      captured_dst_port = (tcp_header[2] << 8) | tcp_header[3];
                      tcp_flags = tcp_header[13]; // <--- GRAB TCP FLAGS HERE

                      uint8_t tcp_header_len = ((tcp_header[12] & 0xF0) >> 4) * 4;
                      if (body_len > (ip_header_len + tcp_header_len)) {
                          frame_body += (ip_header_len + tcp_header_len);
                          body_len -= (ip_header_len + tcp_header_len);
                      } else {
                          body_len = 0; // Prevent underflow if no payload
                      }
                  }
                  // --- ICMPv4 (1) and Unknown Protocol Catch-All ---
                  else if (frame_body[9] == 1 && body_len > ip_header_len) {
                      captured_protocol = 1; // ICMPv4
                      frame_body += ip_header_len; 
                      body_len -= ip_header_len;
                  } else {
                      // Unknown protocol (e.g. IGMP, GRE). 
                      // Strip the IP header so payload catch-alls don't print garbage!
                      if (body_len > ip_header_len) {
                          frame_body += ip_header_len;
                          body_len -= ip_header_len;
                      } else {
                          body_len = 0;
                      }
                  }
              }
              // 2.5 Check for IPv6 (First nibble is 6)
              else if (!is_amsdu && body_len > 40 && (frame_body[0] & 0xF0) == 0x60) {
                  captured_ip_version = 6;
                  
                  // IPv6 Source IP is at offset 8, Destination IP is at offset 24
                  memcpy(captured_src_ip, &frame_body[8], 16);
                  memcpy(captured_dst_ip, &frame_body[24], 16);

                  uint8_t next_header = frame_body[6]; // IPv6 uses "Next Header" instead of Protocol
                  uint8_t ip_header_len = 40; // Fixed size for base IPv6 header

                  // ==========================================
                  // NEW: EXTENSION HEADER HOPPER (Hop-by-Hop)
                  // Apple injects Hop-by-Hop (0) into mDNS and ICMPv6 multicasts.
                  // ==========================================
                  if (next_header == 0 && body_len > ip_header_len + 8) {
                      // The first byte of the extension is the TRUE protocol (e.g., 17 for UDP)
                      next_header = frame_body[ip_header_len];
                      
                      // Length is calculated as (Byte[1] + 1) * 8
                      uint8_t ext_len_modifier = frame_body[ip_header_len + 1];
                      uint16_t total_ext_len = (ext_len_modifier + 1) * 8;
                      
                      // Safely advance the IP header boundary to step over the extension
                      if (body_len > ip_header_len + total_ext_len) {
                          ip_header_len += total_ext_len;
                      }
                  }
                  // ==========================================
                  if (next_header == 17 && body_len > (ip_header_len + 8)) {
                      captured_protocol = 17; // UDP
                      uint8_t* udp_header = frame_body + ip_header_len;
                      captured_src_port = (udp_header[0] << 8) | udp_header[1];
                      captured_dst_port = (udp_header[2] << 8) | udp_header[3];
                      
                      frame_body += (ip_header_len + 8);
                      body_len -= (ip_header_len + 8);
                  } else if (next_header == 6 && body_len > (ip_header_len + 20)) {
                      captured_protocol = 6; // TCP
                      uint8_t* tcp_header = frame_body + ip_header_len;
                      captured_src_port = (tcp_header[0] << 8) | tcp_header[1];
                      captured_dst_port = (tcp_header[2] << 8) | tcp_header[3];
                      tcp_flags = tcp_header[13]; // <--- GRAB TCP FLAGS HERE

                      uint8_t tcp_header_len = ((tcp_header[12] & 0xF0) >> 4) * 4;
                      if (body_len > (ip_header_len + tcp_header_len)) {
                          frame_body += (ip_header_len + tcp_header_len);
                          body_len -= (ip_header_len + tcp_header_len);
                      }
                  } else if (next_header == 58 && body_len > ip_header_len) {
                      // --- NEW: ICMPv6 (58) ---
                      captured_protocol = 58; // ICMPv6
                      frame_body += ip_header_len;
                      body_len -= ip_header_len;
                  } else {
                      // Unknown protocol or contains extension headers. Just strip the fixed IP header.
                      if (body_len > ip_header_len) {
                          frame_body += ip_header_len;
                          body_len -= ip_header_len;
                      } else {
                          body_len = 0;
                      }
                  }
              }

              // =========================================================
              // TCP/443 PAYLOAD HANDOFF DIAGNOSTIC
              // =========================================================
              /*
              if (captured_protocol == 6 &&
                  (captured_src_port == 443 || captured_dst_port == 443)) {

                  Serial.printf(
                      "[SNIFF-TCP443] src=%u dst=%u flags=0x%02X "
                      "payload_len=%u ether=0x%04X ip_ver=%u\n",
                      captured_src_port,
                      captured_dst_port,
                      tcp_flags,
                      body_len,
                      ether_type,
                      captured_ip_version
                  );

                  if (body_len > 0 && frame_body != nullptr) {
                      Serial.print("[SNIFF-TCP443] payload first32: ");

                      uint16_t dump_len =
                          min((uint16_t)32, body_len);

                      for (uint16_t i = 0; i < dump_len; i++) {
                          Serial.printf("%02X ", frame_body[i]);
                      }

                      Serial.println();
                  }
              }
              */

              // =========================================================
              // 3. THE HIGH-SPEED ISR FUNNEL (LRU Cache & Deduplication)
              // =========================================================
              leak_funnel_seen++;
              // 1. Generate the fast integer hash of the flow
              uint32_t current_hash = hash_flow(frame_body, body_len, captured_src_port, captured_dst_port);
              
              uint32_t now_ms = millis();
              bool should_process = false;
              int cache_idx = -1;
              int oldest_idx = 0;
              uint32_t oldest_time = 0xFFFFFFFF;

              // 2. Scan the LRU Cache
              for (int i = 0; i < MAX_ACTIVE_FLOWS; i++) {
                  // Found an existing flow
                  if (flow_cache[i].flow_hash == current_hash) {
                      cache_idx = i;
                      break;
                  }
                  // Keep track of the stalest record in case we need to evict
                  if (flow_cache[i].last_seen_ms < oldest_time) {
                      oldest_time = flow_cache[i].last_seen_ms;
                      oldest_idx = i;
                  }
              }

              if (cache_idx != -1) {
                  // Existing Flow: Update stats and check the 30-second cooldown
                  flow_cache[cache_idx].count++;
                  flow_cache[cache_idx].last_seen_ms = now_ms;
                  
                  if (now_ms - flow_cache[cache_idx].last_printed_ms > LIVE_DUMP_COOLDOWN_MS) {
                      should_process = true;
                      flow_cache[cache_idx].last_printed_ms = now_ms;
                  } else {
                      leak_funnel_suppressed++;
                      static uint32_t suppressed = 0;
                      suppressed++;
                      if (suppressed % 20 == 1) {
                          //Serial.printf("[L2-DEDUP] Cooldown suppressed repeat (hash=0x%08X, total=%u)\n", current_hash, suppressed);
                      }
                  }
              } else {
                  // New Flow: Evict the oldest record and claim the slot
                  cache_idx = oldest_idx;
                  flow_cache[cache_idx].flow_hash = current_hash;
                  flow_cache[cache_idx].first_seen_ms = now_ms;
                  flow_cache[cache_idx].last_seen_ms = now_ms;
                  flow_cache[cache_idx].last_printed_ms = now_ms;
                  flow_cache[cache_idx].count = 1;
                  should_process = true;
              }

              // =========================================================
              // 4. SHIP RAW BYTES TO CORE 1 
              // =========================================================
              
                            if (should_process) {

                  // =========================================================
                  // BUILD TRANSIENT FULL-PAYLOAD TRANSPORT EVENT
                  // =========================================================

                  uint16_t copy_len = body_len;

                  if (copy_len > MAX_LIVE_CAPTURE) {
                      copy_len = MAX_LIVE_CAPTURE;
                  }

                  // The '&' reference lets the compiler treat the heap memory exactly like a local object!
                  LiveCaptureEvent& live_evt = *ptr_isr_evt;
                  memset(&live_evt, 0, sizeof(LiveCaptureEvent));

                  live_evt.meta.timestamp     = now_ms;
                  live_evt.meta.frame_length  = pkt->rx_ctrl.sig_len;
                  live_evt.meta.flow_hash     = current_hash;

                  live_evt.meta.src_port      = captured_src_port;
                  live_evt.meta.dst_port      = captured_dst_port;
                  live_evt.raw_len   = copy_len;
                  live_evt.meta.ether_type    = ether_type;

                  live_evt.meta.ip_version    = captured_ip_version;
                  live_evt.meta.protocol      = captured_protocol;
                  live_evt.meta.tcp_flags     = tcp_flags;
                  live_evt.meta.channel       = captured_channel;
                  live_evt.meta.direction     = captured_direction;
                  live_evt.meta.frame_subtype = captured_subtype;

                  memcpy(live_evt.meta.bssid,   mac3,         6);
                  memcpy(live_evt.meta.src_mac, payload + 10, 6);
                  memcpy(live_evt.meta.dst_mac, payload + 4,  6);

                  memcpy(live_evt.meta.src_ip, captured_src_ip, 16);
                  memcpy(live_evt.meta.dst_ip, captured_dst_ip, 16);

                  if (copy_len > 0) {
                      memcpy(live_evt.raw_payload, frame_body, copy_len);
                  }

                  // =========================================================
                  // TCP/443 DIAGNOSTIC
                  // =========================================================
                  /*
                  if (captured_protocol == 6 &&
                      (captured_src_port == 443 || captured_dst_port == 443)) {

                      Serial.printf(
                          "[CALLBACK-TCP443] "
                          "src=%u dst=%u flags=0x%02X "
                          "body_len=%u copy_len=%u sig_len=%u\n",
                          captured_src_port,
                          captured_dst_port,
                          tcp_flags,
                          body_len,
                          copy_len,
                          pkt->rx_ctrl.sig_len
                      );

                      if (copy_len > 0) {
                          Serial.print("[CALLBACK-TCP443] first32: ");

                          uint16_t dump_len = min((uint16_t)32, copy_len);

                          for (uint16_t i = 0; i < dump_len; i++) {
                              Serial.printf("%02X ", live_evt.raw_payload[i]);
                          }

                          Serial.println();
                      }
                  }
                  */

                  // =========================================================
                  // SHIP FULL PAYLOAD TO CORE 1
                  // =========================================================

                                    if (liveDumpQueue != NULL) {
                      ui_total_arrived++;

                      if (xQueueSendFromISR(
                              liveDumpQueue,
                              &live_evt,
                              NULL) != pdTRUE) {

                          debug_dropped_packets++;
                          ui_dropped_packets++;
                          live_dump_dropped++;
                      } else {
                          leak_funnel_shipped++; // <-- IT BELONGS EXACTLY HERE
                      }
                  }

              }   // closes if (should_process)

          }       // <-- THIS closes if (len > header_len)
      }           // <-- THIS closes if (!is_protected)
      else {
          // ==========================================
          // INSECURE ENCRYPTION DETECTION (TKIP/WEP)
          // ==========================================
          
          // --- UPGRADED: STRICT HEADER SIZING ---
          bool is_qos = (payload[0] & 0x80) != 0;
          bool to_ds = (payload[1] & 0x01) != 0;
          bool from_ds = (payload[1] & 0x02) != 0;
          
          // The +HTC bit ONLY dictates a 4-byte shift if it is a QoS Data frame!
          bool has_ht_ctrl = is_qos && ((payload[1] & 0x80) != 0); 
          
          uint8_t header_len = 24;          // Base MAC Header
          if (to_ds && from_ds) header_len += 6; // Address 4 present (WDS Bridge)
          if (is_qos) header_len += 2;           // QoS Control present
          if (has_ht_ctrl) header_len += 4;      // HT Control present
          // ---------------------------------------
          
          if (len > header_len + 4) {
              uint8_t* iv_ptr = payload + header_len;
              
              bool is_ext_iv = (iv_ptr[3] & 0x20) != 0;
              bool is_valid_key_id = (iv_ptr[3] & 0x1F) == 0;
              
              char tid_str[16] = {0};
              if (is_qos) { 
                  uint8_t tid = payload[header_len - 2] & 0x0F;
                  snprintf(tid_str, sizeof(tid_str), "[TID:%d] ", tid);
              }
              
              bool triggered = false;
              char temp_text[MAX_LEAK_STR_LEN] = {0};

              // ONLY evaluate if we mathematically proved it is a valid IV header structure
              if (is_valid_key_id) {
                  if (is_ext_iv) {
                      // CCMP strictly reserves Byte 2 as 0x00. 
                      // TKIP uses it as a Dummy Byte, mathematically computed as: (TSC1 | 0x20) & 0x7F
                      if (iv_ptr[2] != 0x00) {
                          // THE SILVER BULLET: Verify the IEEE TKIP RFC math
                          if (iv_ptr[2] == ((iv_ptr[1] | 0x20) & 0x7F)) {
                              snprintf(temp_text, MAX_LEAK_STR_LEN, "%sWPA/TKIP Encryption Detected (INSECURE)", tid_str);
                              triggered = true;
                          }
                      }
                  } else {
                      // WEP signature: KeyID is valid, but it is NOT an Extended IV.
                      snprintf(temp_text, MAX_LEAK_STR_LEN, "%sWEP Encryption Detected (INSECURE)", tid_str);
                      triggered = true;
                  }
              }

              // Apply the LRU cache deduplication
              if (triggered) {
                  uint32_t now_ms = xTaskGetTickCountFromISR() * portTICK_PERIOD_MS;
                  
                  if (should_alert_crypto(payload + 10, payload + 4, now_ms)) {
                      
                      Layer2Capture leak;
                      memset(&leak, 0, sizeof(Layer2Capture));
                      
                      leak.meta.timestamp = now_ms;
                      leak.meta.frame_length = pkt->rx_ctrl.sig_len;
                      leak.meta.flow_hash = (payload[9] << 24) | (payload[8] << 16) | (payload[15] << 8) | payload[14];
                      leak.meta.frame_subtype = (payload[0] & 0xF0) >> 4;
                      leak.meta.direction = payload[1] & 0x03;
                      leak.meta.channel = pkt->rx_ctrl.channel;
                      
                      memcpy(leak.meta.src_mac, payload + 10, 6);
                      memcpy(leak.meta.dst_mac, payload + 4, 6);
                      memcpy(leak.meta.bssid, mac3, 6);

                      strncpy(leak.text, temp_text, MAX_LEAK_STR_LEN - 1);
                      
                      if (leakQueue != NULL) {
    leak_isr_attempts++;

    if (xQueueSendFromISR(leakQueue, &leak, NULL) != pdTRUE) {
        leak_isr_dropped++;
    }
}
                  }
              }
          } 
      } 
  }
  // ==========================================

  // 2. The Target AP Lock Gate
  if (target_locked) {
    bool belongs_to_target = false;

    // --- THE UNIVERSAL FOXHUNT EXCEPTION ---
    if (is_foxhunting && (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP)) {
        if (memcmp(addr1, foxhunt_target_mac, 6) == 0 || 
            memcmp(addr2, foxhunt_target_mac, 6) == 0 || 
            memcmp(mac3, foxhunt_target_mac, 6) == 0) {
            belongs_to_target = true;
        }
    }

    // Legacy AP Scanner Lock
    if (memcmp(addr1, target_bssid, 6) == 0) belongs_to_target = true;
    else if (memcmp(addr2, target_bssid, 6) == 0) belongs_to_target = true;
    else if (memcmp(mac3, target_bssid, 6) == 0) belongs_to_target = true;

    if (!belongs_to_target) return; // The Ruthless Drop
  }

  // 3. Extract DS Flags to determine traffic direction
  uint8_t ds_flags = payload[1] & 0x03;
  bool to_ds   = (ds_flags & 0x01); // Bit 0: Client -> AP (Upload)
  bool from_ds = (ds_flags & 0x02); // Bit 1: AP -> Client (Download)

  // 4. Smart Endpoint Identification
  uint8_t* client_mac = addr2; // Default to Transmitter (mac2)

  if (from_ds && !to_ds) {
    client_mac = addr1; // mac1
  }
  else if (to_ds && !from_ds) {
    client_mac = addr2; // mac2
  }

  // 5. Handle Broadcasts and Multicasts
  bool is_broadcast = (client_mac[0] == 0xFF);
  bool is_ipv4_multicast = (client_mac[0] == 0x01 && client_mac[1] == 0x00 && client_mac[2] == 0x5E);
  bool is_ipv6_multicast = (client_mac[0] == 0x33 && client_mac[1] == 0x33);
  bool is_stp_multicast = (client_mac[0] == 0x01 && client_mac[1] == 0x80 && client_mac[2] == 0xC2);

  if (is_broadcast || is_ipv4_multicast || is_ipv6_multicast || is_stp_multicast) {
    client_mac = mac3; 
  }

  // 6. Target Exclusion Gate
  if (target_locked && memcmp(client_mac, target_bssid, 6) == 0) return;

  // 7. Update the deduplication buffer
  bool is_tx = (client_mac == addr2); // mac2

  // WiFi client foxhunt — uses correctly derived client_mac:
  if (is_foxhunting && currentRadioMode == RADIO_WIFI) {
      if (memcmp(client_mac, foxhunt_target_mac, 6) == 0) {
          updateFoxhuntSignal(pkt->rx_ctrl.rssi);
      }
  }

  for(int i = 0; i < liveMacCount; i++) {
    if(memcmp((void*)liveData[i].mac, client_mac, 6) == 0) {
      liveData[i].packets += 1;
      liveData[i].sum_bytes += len;
      liveData[i].sum_sq_bytes += ((uint64_t)len * len);
      
      // THE FIX 1: Pure Window Stretching
      // Track the absolute min/max for this 2-second window without ever 
      // deleting history. Only updates when the target is transmitting.
      if (is_tx) {
          liveData[i].rssi = pkt->rx_ctrl.rssi;
          
          if (liveData[i].rssi_min == 0 || pkt->rx_ctrl.rssi < liveData[i].rssi_min) {
              liveData[i].rssi_min = pkt->rx_ctrl.rssi;
          }
          if (liveData[i].rssi_max == -100 || pkt->rx_ctrl.rssi > liveData[i].rssi_max) {
              liveData[i].rssi_max = pkt->rx_ctrl.rssi;
          }
      }
      
      uint8_t current_rate = getBitrateMbps(pkt);
      if (current_rate > liveData[i].rate) {
          liveData[i].rate = current_rate;
      }
      liveData[i].last_seen = millis();
      if (is_tx) liveData[i].tx_bytes += len;
      else       liveData[i].rx_bytes += len;
      
      return;
    }
  }

  // If we made it here, it's a completely new MAC address!
  if(liveMacCount < MAX_MACS) {
    memcpy((void*)liveData[liveMacCount].mac, client_mac, 6);
    
    // Seed the first packet's math
    liveData[liveMacCount].packets = 1;
    liveData[liveMacCount].sum_bytes = len;
    liveData[liveMacCount].sum_sq_bytes = ((uint64_t)len * len);
    liveData[liveMacCount].rssi = pkt->rx_ctrl.rssi;
    liveData[liveMacCount].rate = getBitrateMbps(pkt);
    unsigned long now = millis();
    liveData[liveMacCount].first_seen = now;
    liveData[liveMacCount].last_seen = now;
    
    // THE FIX 2: Dynamic Initializer
    // Seed the bounds directly to the first packet if it's a physical transmission.
    // Otherwise, use the safe defaults so they stretch correctly later.
    if (is_tx) {
        liveData[liveMacCount].rssi_min = pkt->rx_ctrl.rssi;
        liveData[liveMacCount].rssi_max = pkt->rx_ctrl.rssi;
    } else {
        liveData[liveMacCount].rssi_min = 0; 
        liveData[liveMacCount].rssi_max = -100; 
    }
    
    // Route the first packet to TX or RX
    if (is_tx) {
      liveData[liveMacCount].tx_bytes = len;
      liveData[liveMacCount].rx_bytes = 0;
    } else {
      liveData[liveMacCount].tx_bytes = 0;
      liveData[liveMacCount].rx_bytes = len;
    }
    
    liveData[liveMacCount].vendorFound = false;
    
    // --- ADD THESE 3 LINES ---
    liveData[liveMacCount].needs_lookup = true; // Tell Core 1 to check the SD card
    strncpy((char*)liveData[liveMacCount].vendor, "Resolving...", 27); 
    liveData[liveMacCount].vendor[27] = '\0';
    // -------------------------

    liveMacCount++; // Advance the tracker
  } else {
    // If the buffer is full, dump the size into the overflow bucket
    liveOtherBytes += len; 
  }
}

static bool is_lldp_multicast(const uint8_t* mac) {
    return mac && mac[0] == 0x01 && mac[1] == 0x80 && mac[2] == 0xC2 && 
           mac[3] == 0x00 && mac[4] == 0x00 && mac[5] == 0x0E;
}
static bool is_cdp_multicast(const uint8_t* mac) {
    // 01:00:0C:CC:CC:CC is the dedicated Cisco CDP/VTP multicast address
    return mac && mac[0] == 0x01 && mac[1] == 0x00 && mac[2] == 0x0C && 
           mac[3] == 0xCC && mac[4] == 0xCC && mac[5] == 0xCC;
}

void processLiveDumpQueue() {
    if (liveDumpQueue == NULL) return;
    
    UBaseType_t waiting = uxQueueMessagesWaiting(liveDumpQueue);
    if (waiting >= LIVE_DUMP_QUEUE_DEPTH - 2) {
    Serial.printf(
        "WARNING: Queue backing up! (%u/%u waiting)\n",
        (unsigned)waiting,
        (unsigned)LIVE_DUMP_QUEUE_DEPTH
    );
}

    LiveCaptureEvent& live_evt = *ptr_core1_evt;
    int packets_processed = 0; 
    uint32_t start_time = micros();
    static char temp_text[MAX_LEAK_STR_LEN];
    static char eapol_text[MAX_LEAK_STR_LEN];
    
    // FIXED: Short-circuit evaluation order. Check count BEFORE pulling from the queue.
    while (packets_processed < 5 &&
       xQueueReceive(liveDumpQueue, &live_evt, 0) == pdTRUE) {
        packets_processed++;

        memset(temp_text, 0, sizeof(temp_text));
        bool custom_extracted = false;
        memset(eapol_text, 0, sizeof(eapol_text));
        bool eapol_detected = false;

        if (live_evt.meta.protocol == 6 ||
    live_evt.meta.src_port == 80 ||
    live_evt.meta.dst_port == 80) {

    /*
    Serial.printf(
        "[HTTPDBG] eth=0x%04X ip=%u proto=%u "
        "src=%u dst=%u flags=0x%02X raw_len=%u | ",
        live_evt.meta.ether_type,
        live_evt.meta.ip_version,
        live_evt.meta.protocol,
        live_evt.meta.src_port,
        live_evt.meta.dst_port,
        live_evt.meta.tcp_flags,
        live_evt.raw_len
    );
    */

    for (int i = 0; i < 32 && i < live_evt.raw_len; i++) {
        uint8_t c = live_evt.raw_payload[i];

        if (c >= 32 && c <= 126)
            Serial.printf("%c", c);
        else
            Serial.printf(".");
    }

    Serial.println();
}

        // =========================================================
        // --- STRICT PROTOCOL PARSERS ---
        // =========================================================
        // =========================================================
        // --- 0.0 UPNP / SSDP RESPONSE BYPASS (UDP Ephemeral) ---
        // =========================================================
        // Reinstated: Guarded strictly by UDP (Protocol 17) to prevent
        // colliding with standard TCP web traffic!
        if (live_evt.meta.protocol == 17 && 
            live_evt.raw_len > 15 && 
            memcmp(live_evt.raw_payload, "HTTP/1.", 7) == 0) {
            
            custom_extracted = parse_ssdp(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            
            // Unicast SSDP replies are pure gold. Elevate immediately!
            if (custom_extracted) {
                live_evt.meta.is_high_value = true;
            }
        }
        // FIXED: The entire chain is now guarded so the SSDP bypass isn't overwritten
        if (!custom_extracted) {
            if (live_evt.meta.ether_type == 0x0806) {
                custom_extracted = parse_arp(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.ether_type == 0x888E) {

    eapol_detected = parse_eapol(
        live_evt.raw_payload,
        live_evt.raw_len,
        eapol_text,
        MAX_LEAK_STR_LEN
    );

    // Preserve the existing M1/M2/M3/M4 detection exactly.
    if (eapol_detected &&
        (strstr(eapol_text, "M1") ||
         strstr(eapol_text, "M2") ||
         strstr(eapol_text, "M3") ||
         strstr(eapol_text, "M4"))) {

        live_evt.meta.is_high_value = false;
    }

    // Deliberately do NOT set custom_extracted here.
    // The packet should continue into the deeper/catch-all
    // payload inspection below.
}
            else if (is_cdp_multicast(live_evt.meta.dst_mac)) {
                custom_extracted = parse_cdp(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
                if (custom_extracted) {
                    live_evt.meta.is_high_value = true; 
                }
            }
            else if (live_evt.meta.ether_type == 0x88CC || is_lldp_multicast(live_evt.meta.dst_mac)) {
                custom_extracted = parse_lldp(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
                if (custom_extracted) {
                    live_evt.meta.is_high_value = true; 
                }
            }
            else if (live_evt.meta.dst_port == 67 || live_evt.meta.src_port == 67 ||
         live_evt.meta.dst_port == 68 || live_evt.meta.src_port == 68) {
                custom_extracted = parse_dhcp_v4(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }            
            else if (live_evt.meta.dst_port == 546 || live_evt.meta.src_port == 546 ||
         live_evt.meta.dst_port == 547 || live_evt.meta.src_port == 547) {
                custom_extracted = parse_dhcp_v6(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.dst_port == 137 || live_evt.meta.src_port == 137) {
                custom_extracted = parse_netbios(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.dst_port == 138 || live_evt.meta.src_port == 138) {
                custom_extracted = parse_nbds(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.dst_port == 53 || live_evt.meta.src_port == 53 || 
                     live_evt.meta.dst_port == 5353 || live_evt.meta.src_port == 5353) {
                custom_extracted = parse_dns_mdns(live_evt.raw_payload, live_evt.raw_len, live_evt.meta.dst_port == 5353 || live_evt.meta.src_port == 5353, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.dst_port == 80 ||
                     live_evt.meta.src_port == 80) {
                custom_extracted = parse_http_host(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
                if (custom_extracted && strstr(temp_text, "[Auth: Basic ")) live_evt.meta.is_high_value = true;
            }
            else if (live_evt.meta.dst_port == 3702 || live_evt.meta.src_port == 3702) {
                custom_extracted = parse_ws_discovery(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
                if (custom_extracted && strstr(temp_text, "[URL: ")) live_evt.meta.is_high_value = true;
            }
            else if (live_evt.meta.dst_port == 631 || live_evt.meta.src_port == 631) {
    custom_extracted = parse_ipp(
        live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN
    );
    // is_high_value intentionally remains false.
}
            else if (live_evt.meta.dst_port == 514 || live_evt.meta.src_port == 514) {
    custom_extracted = parse_syslog(
        live_evt.raw_payload,
        live_evt.raw_len,
        temp_text,
        MAX_LEAK_STR_LEN
    );
}
            else if (live_evt.meta.dst_port == 554 || live_evt.meta.src_port == 554) {
                custom_extracted = parse_rtsp(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.dst_port == 21 || live_evt.meta.src_port == 21) {
                custom_extracted = parse_ftp(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
                if (custom_extracted) live_evt.meta.is_high_value = true;
            }
            else if (live_evt.meta.dst_port == 23 || live_evt.meta.src_port == 23) {
                custom_extracted = parse_telnet(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
                if (custom_extracted) live_evt.meta.is_high_value = true;
            }
            else if (live_evt.meta.dst_port == 22 || live_evt.meta.src_port == 22) {
                custom_extracted = parse_ssh(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.dst_port == 69 || live_evt.meta.src_port == 69) {
    custom_extracted = parse_tftp(
        live_evt.raw_payload,
        live_evt.raw_len,
        temp_text,
        MAX_LEAK_STR_LEN
    );

    if (custom_extracted)
        live_evt.meta.is_high_value = true;
}
            else if (live_evt.meta.dst_port == 3389 || live_evt.meta.src_port == 3389) {
                custom_extracted = parse_rdp(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
                if (custom_extracted) live_evt.meta.is_high_value = true;
            }
            else if (live_evt.meta.dst_port == 25 || live_evt.meta.src_port == 25 || 
                     live_evt.meta.dst_port == 587 || live_evt.meta.src_port == 587) {
                custom_extracted = parse_smtp(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
                if (custom_extracted) live_evt.meta.is_high_value = true;
            }
            else if (live_evt.meta.dst_port == 445 || live_evt.meta.src_port == 445) {
                custom_extracted = parse_smb(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
                if (custom_extracted) live_evt.meta.is_high_value = true; 
            }
            else if (live_evt.meta.dst_port == 1900 || live_evt.meta.src_port == 1900) {
                custom_extracted = parse_ssdp(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.dst_port == 5355 || live_evt.meta.src_port == 5355) {
                custom_extracted = parse_llmnr(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.dst_port == 17500 || live_evt.meta.src_port == 17500) {
                custom_extracted = parse_dropbox(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN);
            }
            else if (live_evt.meta.dst_port == 161 || live_evt.meta.src_port == 161 ||
         live_evt.meta.dst_port == 162 || live_evt.meta.src_port == 162) {
    custom_extracted = parse_snmp(
        live_evt.raw_payload,
        live_evt.raw_len,
        temp_text,
        MAX_LEAK_STR_LEN
    );
}
else if (live_evt.meta.dst_port == 1080 || live_evt.meta.src_port == 1080 ||
         live_evt.meta.dst_port == 9050 || live_evt.meta.src_port == 9050) {
    custom_extracted = parse_socks(
        live_evt.raw_payload,
        live_evt.raw_len,
        temp_text,
        MAX_LEAK_STR_LEN
    );
}
            else if (live_evt.meta.protocol == 6 && (live_evt.meta.tcp_flags & 0x02)) { 
                snprintf(temp_text, MAX_LEAK_STR_LEN, "TCP SYN (Port %d)", live_evt.meta.dst_port); 
                custom_extracted = true; 
            } 
            else if (live_evt.meta.protocol == 6 && (live_evt.meta.tcp_flags & 0x04)) { 
                snprintf(temp_text, MAX_LEAK_STR_LEN, "TCP RST (Port %d)", live_evt.meta.dst_port); 
                custom_extracted = true; 
            } 
            else if (live_evt.meta.protocol == 1) {
                if (!parse_icmpv4(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN)) {
                    snprintf(temp_text, MAX_LEAK_STR_LEN, "ICMPv4: Malformed");
                }
                custom_extracted = true;
            }
        }

        // =========================================================
        // --- DEEP PARSERS & SIGNATURES ---
        // =========================================================
        if (!custom_extracted && live_evt.raw_len > 0) {
            const uint8_t* p = live_evt.raw_payload;
            uint16_t len = live_evt.raw_len;

            // ICMPv6
            if (!custom_extracted && live_evt.meta.ip_version == 6 && live_evt.meta.protocol == 58) {
                if (parse_icmpv6(p, len, temp_text, MAX_LEAK_STR_LEN, live_evt.meta.is_high_value)) {
                    custom_extracted = true;
                }
            }
            
            // MQTT
            if (!custom_extracted && live_evt.meta.protocol == 6 && (live_evt.meta.src_port == 1883 || live_evt.meta.dst_port == 1883)) {
                if (parse_mqtt(p, len, temp_text, MAX_LEAK_STR_LEN, live_evt.meta.is_high_value)) {
                    custom_extracted = true;
                }
            }
            // CoAP
if (!custom_extracted &&
    (live_evt.meta.src_port == 5683 || live_evt.meta.dst_port == 5683)) {

    if (parse_coap(p, len, temp_text, MAX_LEAK_STR_LEN)) {
        custom_extracted = true;
        // Leave is_high_value false for ordinary CoAP traffic.
    }
}

            // TLS Diagnostic Walker
if (!custom_extracted &&
    live_evt.meta.protocol == 6 &&
    (live_evt.meta.src_port == 443 || live_evt.meta.dst_port == 443) &&
    len > 0) {

    uint16_t offset = 0;
    bool found_tls = false;

    // ---------------------------------------------------------
    // 1. Walk TLS records that begin at this TCP payload boundary
    // ---------------------------------------------------------
    while (offset + 5 <= len) {
        uint8_t rec_type = p[offset];
        uint16_t rec_version = ((uint16_t)p[offset + 1] << 8) | p[offset + 2];
        uint16_t rec_len = ((uint16_t)p[offset + 3] << 8) | p[offset + 4];

        if (rec_type >= 0x14 && rec_type <= 0x17 &&
            (rec_version == 0x0301 ||
             rec_version == 0x0302 ||
             rec_version == 0x0303)) {

            found_tls = true;

            Serial.printf(
                "\n[TLS-RECORD] offset=%u type=%02X version=%04X len=%u\n",
                offset, rec_type, rec_version, rec_len
            );

            if (rec_type == 0x16 && offset + 5 < len) {
                uint8_t hs_type = p[offset + 5];
                const char* hs_str = "Unknown";

                if (hs_type == 0x01) hs_str = "ClientHello";
                else if (hs_type == 0x02) hs_str = "ServerHello";
                else if (hs_type == 0x0B) hs_str = "Certificate";
                else if (hs_type == 0x0E) hs_str = "ServerHelloDone";
                else if (hs_type == 0x10) hs_str = "ClientKeyExchange";

                Serial.printf(
                    "  -> [TLS-HS] type=%02X %s\n",
                    hs_type, hs_str
                );

                if (hs_type == 0x0B &&
                    rec_len > len - offset - 5) {
                    Serial.printf(
                        "  -> [TLS-FRAG] Warning: Certificate record extends beyond this TCP segment!\n"
                    );
                }
            }

            // Subtraction-safe boundary check
            if (rec_len > len - offset - 5)
                break;

            offset += 5 + rec_len;
        } else {
            break;
        }
    }

    // ---------------------------------------------------------
    // 2. Parse information from recognized TLS records
    // ---------------------------------------------------------
    if (found_tls) {
        custom_extracted =
            parse_tls_sni(p, len, temp_text, MAX_LEAK_STR_LEN);

        if (!custom_extracted) {
            custom_extracted =
                parse_tls_cert(p, len, temp_text, MAX_LEAK_STR_LEN);

            if (custom_extracted)
                live_evt.meta.is_high_value = true;
        }

        if (!custom_extracted) {
            snprintf(
                temp_text,
                MAX_LEAK_STR_LEN,
                "TLS Encrypted Traffic (Port %u)",
                live_evt.meta.dst_port == 443 ?
                    live_evt.meta.src_port :
                    live_evt.meta.dst_port
            );

            custom_extracted = true;
        }
    }

    // ---------------------------------------------------------
    // 3. IMPORTANT: Raw certificate scan for non-header segments
    // ---------------------------------------------------------
    if (!custom_extracted) {
        custom_extracted =
            parse_tls_cert(p, len, temp_text, MAX_LEAK_STR_LEN);

        if (custom_extracted)
            live_evt.meta.is_high_value = true;
    }
}

            // Other structured deep extractors
            if (!custom_extracted) {
                if (len >= 8 && p[4] == 0x21 && p[5] == 0x12 && p[6] == 0xA4 && p[7] == 0x42) {
                    snprintf(temp_text, MAX_LEAK_STR_LEN, "STUN: Live VoIP/WebRTC Stream");
                    custom_extracted = true;
                    live_evt.meta.is_high_value = true;
                }
                else if ((len >= 4 &&
          (memcmp(p, "GET ", 4) == 0 ||
           memcmp(p, "PUT ", 4) == 0)) ||
         (len >= 5 &&
          (memcmp(p, "POST ", 5) == 0 ||
           memcmp(p, "HEAD ", 5) == 0))) {

    custom_extracted =
        parse_http_host(p, len, temp_text, MAX_LEAK_STR_LEN);

    if (custom_extracted) {
        if (strstr(temp_text, "[Auth: Basic ")) {
            live_evt.meta.is_high_value = true;
        }
    } else {
        snprintf(
            temp_text,
            MAX_LEAK_STR_LEN,
            "HTTP Request (Hidden Port)"
        );
        custom_extracted = true;
    }
}

else if (len >= 20 &&
         p[0] == 0x13 &&
         memcmp(&p[1], "BitTorrent protocol", 19) == 0) {

    snprintf(
        temp_text,
        MAX_LEAK_STR_LEN,
        "P2P: BitTorrent Handshake"
    );
    custom_extracted = true;
    live_evt.meta.is_high_value = true;
}

else if (len == 148 &&
         p[0] == 0x01 &&
         p[1] == 0x00 &&
         p[2] == 0x00 &&
         p[3] == 0x00) {

    snprintf(
        temp_text,
        MAX_LEAK_STR_LEN,
        "VPN: WireGuard Handshake"
    );
    custom_extracted = true;
    live_evt.meta.is_high_value = true;
}
            }

            if (!custom_extracted) {
                if (parse_ephemeral_upnp(p, len, temp_text, MAX_LEAK_STR_LEN)) {
                    custom_extracted = true;
                    live_evt.meta.is_high_value = true;
                }
            }
        }

        // =========================================================
        // --- STATIC PORT FINGERPRINTS ---
        // =========================================================
        if (!custom_extracted) {
            if (live_evt.meta.dst_port == 3544 || live_evt.meta.src_port == 3544) {
                snprintf(temp_text, MAX_LEAK_STR_LEN, "Teredo: Windows IPv6 Tunnel");
                custom_extracted = true;
            }
            else if (live_evt.meta.dst_port == 5350 || live_evt.meta.src_port == 5350) {
                snprintf(temp_text, MAX_LEAK_STR_LEN, "PCP: Port Control Protocol");
                custom_extracted = true;
            }
            else if (live_evt.meta.dst_port == 5351 || live_evt.meta.src_port == 5351) {
                snprintf(temp_text, MAX_LEAK_STR_LEN, "NAT-PMP: Apple Port Mapping");
                custom_extracted = true;
            }
            else if (live_evt.meta.dst_port == 1883 || live_evt.meta.src_port == 1883) {
                snprintf(temp_text, MAX_LEAK_STR_LEN, "MQTT (IoT Telemetry/PubSub)");
                custom_extracted = true;
                // FIXED: Removed the automatic high_value elevation here so generic telemetry stays normal
            }
            else if (live_evt.meta.dst_port == 5683 || live_evt.meta.src_port == 5683) {
    snprintf(temp_text, MAX_LEAK_STR_LEN,
             "CoAP (IoT Constrained App Protocol)");
    custom_extracted = true;
    // is_high_value intentionally remains false.
}
        }

        // =========================================================
// --- EAPOL FALLBACK ---
// If no deeper payload extraction succeeded, preserve the
// normal EAPOL classification.
// =========================================================
if (!custom_extracted && eapol_detected) {
    strncpy(temp_text, eapol_text, MAX_LEAK_STR_LEN - 1);
    temp_text[MAX_LEAK_STR_LEN - 1] = '\0';
    custom_extracted = true;
}

        // =========================================================
        // --- CATCH-ALL FOR UNKNOWN CLEARTEXT ---
        // =========================================================
        if (!custom_extracted && live_evt.raw_len > 0) {
            if (extract_printable_runs(live_evt.raw_payload, live_evt.raw_len, temp_text, MAX_LEAK_STR_LEN, 4, false, "|")) {
                custom_extracted = true; 
            } else {
                Serial.printf("[FALLTHROUGH] ip_ver=%u proto=%u src=%u dst=%u eth=0x%04X len=%u | first16: ",
                              live_evt.meta.ip_version, live_evt.meta.protocol, live_evt.meta.src_port, live_evt.meta.dst_port,
                              live_evt.meta.ether_type, live_evt.raw_len);
                for (int b = 0; b < 16 && b < live_evt.raw_len; b++) {
                    Serial.printf("%02X ", live_evt.raw_payload[b]);
                }
                Serial.println();
            }
        }

        // ==========================================
// --- UI ROUTING ---
// ==========================================
if (custom_extracted) {

    // =========================================================
    // Create the compact persistent/UI object ONLY after parsing
    // =========================================================
    Layer2Capture l2_cap;
    memset(&l2_cap, 0, sizeof(Layer2Capture));

    // Copy packet metadata from the full-payload transport event
    l2_cap.meta = live_evt.meta;

    // =========================================================
    // Copy parsed text into persistent storage.
    // MAX_LEAK_STR_LEN includes the terminating NUL.
    // =========================================================
    size_t text_len = strnlen(temp_text, MAX_LEAK_STR_LEN - 1);

    l2_cap.retained_len = (uint16_t)text_len; // <--- INJECT THIS LINE

    memcpy(l2_cap.text, temp_text, text_len);
    l2_cap.text[text_len] = '\0';

    // =========================================================
    // High-Value Triage
    // =========================================================
    if (strcasestr(temp_text, "M-SEARCH") ||
        strcasestr(temp_text, "HTTP/1.") ||
        strcasestr(temp_text, "spotify") ||
        strcasestr(temp_text, "cast") ||
        strcasestr(temp_text, "bearer ") ||
        strcasestr(temp_text, "token=") ||
        strcasestr(temp_text, "password=") ||
        strcasestr(temp_text, "pwd=") ||
        strcasestr(temp_text, "user=") ||
        strcasestr(temp_text, "login=") ||
        strcasestr(temp_text, "login:") ||
        strcasestr(temp_text, "/admin") ||
        strcasestr(temp_text, "rtsp://") ||
        strcasestr(temp_text, "tasmota")) {

        l2_cap.meta.is_high_value = true;

       // if (leakQueue != NULL) {
       //     leak_core1_attempts++;

       // if (xQueueSend(leakQueue, &l2_cap, 0) != pdTRUE) {
       //     leak_core1_dropped++;
       // }
     //}
   }

    // =========================================================
    // Copy final parsed text into the compact UI union
    // =========================================================
    //strncpy(l2_cap.text, temp_text, MAX_LEAK_STR_LEN - 1);
    //l2_cap.text[MAX_LEAK_STR_LEN - 1] = '\0';

    // =========================================================
    // Send compact object to the UI/history pipeline
    // =========================================================
    if (leakQueue != NULL) {
        leak_core1_attempts++;

        if (xQueueSend(leakQueue, &l2_cap, 0) != pdTRUE) {
            leak_core1_dropped++;
        }
    }
}
    
    if (packets_processed > 0) {
        uint32_t elapsed = micros() - start_time;
        Serial.printf("Processed %d packets in %u us\n", packets_processed, elapsed);
    }
}
}

void resetMonitorState() {
  pause_sniffing = true;
  current_x = 0;

  // ==========================================
  // FLUSH SHARED ARRAYS (Wi-Fi sizes cover BLE and AP too)
  // ==========================================
  memset((void*)liveData, 0, sizeof(liveData));
  liveMacCount = 0;
  liveOtherBytes = 0;
  liveBleCount = 0;
  liveApCount = 0;
  liveChannelCount = 0;

  memset(sortData, 0, sizeof(sortData));
  sortMacCount = 0;
  sortOtherBytes = 0;
  sortBleCount = 0;
  sortApCount = 0;
  sortChannelCount = 0;

  memset(sessionData, 0, sizeof(sessionData));
  sessionMacCount = 0;
  sessionOtherBytes = 0;
  sessionBleCount = 0;
  sessionApCount = 0;
  sessionChannelCount = 0;

  pause_sniffing = false;
}

bool lookupVendorCache(
    const uint8_t* mac,
    char* vendor,
    size_t vendorSize
) {
    // Defensive argument validation
    if (mac == nullptr || vendor == nullptr || vendorSize == 0) {
        return false;
    }

    vendor[0] = '\0';

    // ==========================================
    // 0. SPECIAL MAC CLASSES
    // ==========================================

    // Broadcast
    if (mac[0] == 0xFF &&
        mac[1] == 0xFF &&
        mac[2] == 0xFF &&
        mac[3] == 0xFF &&
        mac[4] == 0xFF &&
        mac[5] == 0xFF) {

        strlcpy(vendor, "Bcast", vendorSize);
        return true;
    }

    // IPv6 multicast
    if (mac[0] == 0x33 &&
        mac[1] == 0x33) {

        strlcpy(vendor, "Mcast6", vendorSize);
        return true;
    }

    // IPv4 multicast
    if (mac[0] == 0x01 &&
        mac[1] == 0x00 &&
        mac[2] == 0x5E) {

        strlcpy(vendor, "Mcast4", vendorSize);
        return true;
    }

    // Locally administered / randomized
    if ((mac[0] & 0x02) != 0) {

        strlcpy(vendor, "<Random>", vendorSize);
        return true;
    }

    // ==========================================
    // 1. FAST OUI RAM CACHE
    // ==========================================

    for (int i = 0; i < cacheCount; i++) {

        if (vendorCache[i].oui[0] == mac[0] &&
            vendorCache[i].oui[1] == mac[1] &&
            vendorCache[i].oui[2] == mac[2]) {

            strlcpy(
                vendor,
                vendorCache[i].vendor,
                vendorSize
            );

            return true;
        }
    }

    // ==========================================
    // 2. NOT FOUND IN FAST CACHE
    //    IMPORTANT: NO SD ACCESS HERE
    // ==========================================

    return false;
}

void resolveMacVendor(MacRecord* record) {
  // If already resolved (e.g., via Information Elements "(IE)"), skip.
  if (record->vendorFound) return;

// 2. FAST PATH: RAM OUI CACHE / SPECIAL MAC CLASSES
if (lookupVendorCache(
        record->mac,
        record->vendor,
        sizeof(record->vendor))) {

    record->vendorFound = true;
    return;
}

  char target[7];
  snprintf(target, sizeof(target), "%02X%02X%02X", record->mac[0], record->mac[1], record->mac[2]);

  // 3. Binary Search the SD Card
  bool foundInDB = false;
  FsFile file = sd.open("/oui_db.txt", O_READ);
  if (file) { 
    uint32_t low = 0;
    uint32_t high = (file.fileSize() / 32) - 1;

    while (low <= high) {
      uint32_t mid = low + (high - low) / 2;
      file.seek(mid * 32);
      char line[32];
      file.read(line, 32);
      char prefix[7];
      strncpy(prefix, line, 6);
      prefix[6] = '\0';

      int cmp = strcmp(target, prefix);
      if (cmp == 0) {
        // MATCH FOUND
        int text_start = 7;
        while(text_start < 32 && (line[text_start] == ' ' || line[text_start] == '\t')) {
          text_start++;
        }
        
        int available_chars = 32 - text_start;
        int max_capacity = sizeof(record->vendor) - 1;
        int copy_len = (available_chars < max_capacity) ? available_chars : max_capacity;
        
        strncpy(record->vendor, &line[text_start], copy_len); 
        record->vendor[copy_len] = '\0';
        
        for(int i = copy_len - 1; i >= 0; i--) {         
          if(record->vendor[i] == ' ' || record->vendor[i] == '\r' || record->vendor[i] == '\n') {
              record->vendor[i] = '\0';
          } else {
              break;
          }
        }
        foundInDB = true;
        break; 
      }
      else if (cmp < 0) {
        if (mid == 0) break;
        high = mid - 1;
      }
      else {
        low = mid + 1;
      }
    }
    file.close();
  }

  // 4. Handle SD Card Miss (Fallback)
  if (!foundInDB) {
      strncpy(record->vendor, "Unknown", sizeof(record->vendor) - 1);
      record->vendor[sizeof(record->vendor) - 1] = '\0';
  }

  record->vendorFound = true; // Mark as found so we don't search SD again for "Unknown"

  // 5. Save to RAM Cache
  vendorCache[cacheHead].oui[0] = record->mac[0];
  vendorCache[cacheHead].oui[1] = record->mac[1];
  vendorCache[cacheHead].oui[2] = record->mac[2];
  
  // Cleaned up the magic number 26!
  strncpy(vendorCache[cacheHead].vendor, record->vendor, sizeof(vendorCache[cacheHead].vendor) - 1);
  vendorCache[cacheHead].vendor[sizeof(vendorCache[cacheHead].vendor) - 1] = '\0';
  
  if (cacheCount < OUI_CACHE_SIZE) cacheCount++;
  cacheHead = (cacheHead + 1) % OUI_CACHE_SIZE;
}

/*
void resolveMacVendor(MacRecord* record) {
  // If already resolved (e.g., via Information Elements "(IE)"), skip.
  if (record->vendorFound) return;

  // 0.1 FAST-FAIL: Broadcast MAC
if (record->mac[0] == 0xFF && record->mac[1] == 0xFF && record->mac[2] == 0xFF) {
strncpy(record->vendor, "Bcast", sizeof(record->vendor) - 1);
record->vendor[sizeof(record->vendor) - 1] = '\0';
record->vendorFound = true;
return;
}

// 0.2 FAST-FAIL: IPv6 Multicast (33:33:xx)
if (record->mac[0] == 0x33 && record->mac[1] == 0x33) {
strncpy(record->vendor, "Mcast6", sizeof(record->vendor) - 1);
record->vendor[sizeof(record->vendor) - 1] = '\0';
record->vendorFound = true;
return;
}

// 0.3 FAST-FAIL: IPv4 Multicast (01:00:5E)
if (record->mac[0] == 0x01 && record->mac[1] == 0x00 && record->mac[2] == 0x5E) {
strncpy(record->vendor, "Mcast4", sizeof(record->vendor) - 1);
record->vendor[sizeof(record->vendor) - 1] = '\0';
record->vendorFound = true;
return;
}

// 1. FAST-FAIL: Check for Randomized (Locally Administered) MACs
// Skips the slow SD card search entirely!
if ((record->mac[0] & 0x02) == 0x02) {
    strncpy(record->vendor, "<Random>", sizeof(record->vendor) - 1);
    record->vendor[sizeof(record->vendor) - 1] = '\0';
    record->vendorFound = true;
    return; 
}
  // 1. FAST-FAIL: Check for Randomized (Locally Administered) MACs
  // Skips the slow SD card search entirely!
  //if ((record->mac[0] & 0x02) == 0x02) {
  //    strncpy(record->vendor, "<Randomized>", sizeof(record->vendor) - 1);
  //    record->vendor[sizeof(record->vendor) - 1] = '\0';
  //    record->vendorFound = true;
  //    return; 
  //}

  // 2. Check RAM Cache
  for (int i = 0; i < cacheCount; i++) {
    if (vendorCache[i].oui[0] == record->mac[0] &&
        vendorCache[i].oui[1] == record->mac[1] &&
        vendorCache[i].oui[2] == record->mac[2]) {
      
      strncpy(record->vendor, vendorCache[i].vendor, sizeof(record->vendor) - 1);
      record->vendor[sizeof(record->vendor) - 1] = '\0'; 
      record->vendorFound = true;
      return; 
    }
  }

  char target[7];
  snprintf(target, sizeof(target), "%02X%02X%02X", record->mac[0], record->mac[1], record->mac[2]);

  // 3. Binary Search the SD Card
  bool foundInDB = false;
  FsFile file = sd.open("/oui_db.txt", O_READ);
  if (file) { 
    uint32_t low = 0;
    uint32_t high = (file.fileSize() / 32) - 1;

    while (low <= high) {
      uint32_t mid = low + (high - low) / 2;
      file.seek(mid * 32);
      char line[32];
      file.read(line, 32);
      char prefix[7];
      strncpy(prefix, line, 6);
      prefix[6] = '\0';

      int cmp = strcmp(target, prefix);
      if (cmp == 0) {
        // MATCH FOUND
        int text_start = 7;
        while(text_start < 32 && (line[text_start] == ' ' || line[text_start] == '\t')) {
          text_start++;
        }
        
        int available_chars = 32 - text_start;
        int max_capacity = sizeof(record->vendor) - 1;
        int copy_len = (available_chars < max_capacity) ? available_chars : max_capacity;
        
        strncpy(record->vendor, &line[text_start], copy_len); 
        record->vendor[copy_len] = '\0';
        
        for(int i = copy_len - 1; i >= 0; i--) {         
          if(record->vendor[i] == ' ' || record->vendor[i] == '\r' || record->vendor[i] == '\n') {
              record->vendor[i] = '\0';
          } else {
              break;
          }
        }
        foundInDB = true;
        break; 
      }
      else if (cmp < 0) {
        if (mid == 0) break;
        high = mid - 1;
      }
      else {
        low = mid + 1;
      }
    }
    file.close();
  }

  // 4. Handle SD Card Miss (Fallback)
  if (!foundInDB) {
      strncpy(record->vendor, "Unknown", sizeof(record->vendor) - 1);
      record->vendor[sizeof(record->vendor) - 1] = '\0';
  }

  record->vendorFound = true; // Mark as found so we don't search SD again for "Unknown"

  // 5. Save to RAM Cache
  vendorCache[cacheHead].oui[0] = record->mac[0];
  vendorCache[cacheHead].oui[1] = record->mac[1];
  vendorCache[cacheHead].oui[2] = record->mac[2];
  
  // Cleaned up the magic number 26!
  strncpy(vendorCache[cacheHead].vendor, record->vendor, sizeof(vendorCache[cacheHead].vendor) - 1);
  vendorCache[cacheHead].vendor[sizeof(vendorCache[cacheHead].vendor) - 1] = '\0';
  
  if (cacheCount < OUI_CACHE_SIZE) cacheCount++;
  cacheHead = (cacheHead + 1) % OUI_CACHE_SIZE;
}

*/

const char* resolveBleCompanyId(uint16_t companyId) {
  int left = 0;
  int right = numBleVendors - 1;

  while (left <= right) {
    int mid = left + (right - left) / 2;

    if (bleVendors[mid].id == companyId) {
      return bleVendors[mid].name; 
    }
    
    if (bleVendors[mid].id < companyId) {
      left = mid + 1; 
    } else {
      right = mid - 1; 
    }
  }
  return nullptr; // Use nullptr so the caller knows it failed
}

const char* resolveBleAppearance(uint16_t appearanceId) {
  // PASS 1: Search for the exact 16-bit ID
  int left = 0;
  int right = numBleAppearances - 1;

  while (left <= right) {
    int mid = left + (right - left) / 2;

    if (bleAppearances[mid].id == appearanceId) {
      return bleAppearances[mid].name; 
    }
    
    if (bleAppearances[mid].id < appearanceId) {
      left = mid + 1; 
    } else {
      right = mid - 1; 
    }
  }

  // PASS 2: Mask off the bottom 6 bits to search for Base Category
  uint16_t baseCategory = appearanceId & 0xFFC0;
  
  left = 0;
  right = numBleAppearances - 1;
  
  while (left <= right) {
    int mid = left + (right - left) / 2;

    if (bleAppearances[mid].id == baseCategory) {
      return bleAppearances[mid].name; 
    }
    
    if (bleAppearances[mid].id < baseCategory) {
      left = mid + 1; 
    } else {
      right = mid - 1; 
    }
  }
  
  return nullptr; 
}

/**
 * Fast Binary Search for Corporate Trackers (0x16 Service Data)
 */
const char* resolveBleMemberUuid(uint16_t targetId) {
  int left = 0;
  int right = numMemberUuids - 1;

  while (left <= right) {
    int mid = left + (right - left) / 2;

    if (memberUuids[mid].id == targetId) return memberUuids[mid].name;
    
    if (memberUuids[mid].id < targetId) left = mid + 1;
    else right = mid - 1;
  }
  return nullptr; 
}

/**
 * Fast Binary Search for Standard Hardware Services (0x02/0x03)
 */
const char* resolveBleServiceUuid(uint16_t targetId) {
  int left = 0;
  int right = numServiceUuids - 1;

  while (left <= right) {
    int mid = left + (right - left) / 2;

    if (serviceUuids[mid].id == targetId) return serviceUuids[mid].name;
    
    if (serviceUuids[mid].id < targetId) left = mid + 1;
    else right = mid - 1;
  }
  return nullptr; 
}

// --- UI Drawing Functions ---
void drawMenu() {
  tft.fillScreen(TFT_BLACK);
  tft.setTextSize(1);

  // HEADER
  tft.setFreeFont(&UbuntuMono_Regular11pt7b); 
  tft.setTextDatum(MC_DATUM); 
  tft.setTextColor(TFT_WHITE);
  tft.drawString("DASHBOARD SETTINGS", 240, 40); 

  tft.setFreeFont(&UbuntuMono_Regular9pt7b);

  // ==========================================
  // FOXHUNT BUTTON (Tactical Mode)
  // ==========================================
  tft.setTextDatum(MC_DATUM);

  bool foxhunt_available = false;

  // 1. BLE MODE EVALUATION
  if (currentRadioMode == RADIO_BLE) {
    if (sessionBleCount > 0) {
        foxhunt_available = true;
    }
  } 
  // 2. NETWORKS (AP) MODE EVALUATION
  else if (currentRadioMode == RADIO_AP) {
      if (sessionApCount > 0) {
          foxhunt_available = true;
      }
  } 
  // 3. WI-FI MODE EVALUATION (Isolated at the bottom)
  else if (currentRadioMode == RADIO_WIFI) {
      if (target_locked == true && sessionMacCount > 0) {
          foxhunt_available = true;
      }
  }

  if (foxhunt_available) {
      // Draw active red button
      tft.fillRoundRect(50, 90, 200, 40, 3, TFT_RED);   // Fill it red
      tft.drawRoundRect(50, 90, 200, 40, 3, TFT_WHITE); // Add the crisp border
      tft.setTextColor(TFT_WHITE);
      tft.drawString("FOXHUNT", 150, 110);
  } else {
      // Greyed out — no target locked
      uint16_t deadGrey = hex24to565(0x222222);
      tft.fillRect(50, 90, 200, 40, deadGrey);
      tft.drawRect(50, 90, 200, 40, TFT_DARKGREY);
      tft.setTextColor(TFT_DARKGREY);
      tft.drawString("FOXHUNT", 150, 110);
      
      // Hint text
      tft.setFreeFont(&UbuntuMono_Regular9pt7b);
      tft.setTextColor(hex24to565(0x444444));
      tft.drawString("(no targets yet)", 150, 125);
  }
  
  // ==========================================
  // PROBE REQUEST BUTTON (Right Column)
  // ==========================================
  uint16_t purpleColor = hex24to565(0x4A148C);
  tft.fillRect(300, 140, 150, 40, purpleColor);
  tft.drawRect(300, 140, 150, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("SNIFFED PROBES", 375, 160);

  // ==========================================
  // 3. AP SCANNER / CH SELECT BUTTON (Y: 190 - 230)
  // ==========================================
  if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_LAYER2) {
    // Active State
    tft.fillRect(50, 190, 200, 40, TFT_BLACK);
    tft.drawRect(50, 190, 200, 40, TFT_WHITE);
    tft.setTextColor(TFT_WHITE);
    
    if (currentRadioMode == RADIO_WIFI) {
        tft.drawString("SELECT AP", 150, 210);
    } else if (currentRadioMode == RADIO_AP || currentRadioMode == RADIO_LAYER2) {
        if (target_locked) {
            char chStr[16];
            snprintf(chStr, sizeof(chStr), "LOCKED: CH %d", target_channel);
            tft.drawString(chStr, 150, 210);
        } else {
            tft.drawString("SELECT CH", 150, 210);
        }
    }
  } else {
    // "Cold" Abyss State
    uint16_t deadGrey = hex24to565(0x222222);      // Almost black
    tft.fillRect(50, 190, 200, 40, deadGrey);
    tft.drawRect(50, 190, 200, 40, TFT_DARKGREY);
    tft.setTextColor(TFT_DARKGREY);
    tft.drawString("SELECT AP", 150, 210);
  }

  // 4. SEEN DEVICES BUTTON
  tft.fillRect(50, 240, 200, 40, TFT_BLACK);
  tft.drawRect(50, 240, 200, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("SNIFF LIST", 150, 260);

  // ==========================================
  // RADIO MODE TOGGLE
  // ==========================================
  tft.setTextColor(TFT_WHITE); // Set this once for all modes

  // 1. Draw the filled background based on the current mode
  if (currentRadioMode == RADIO_WIFI) {
    tft.fillRect(300, 190, 150, 40, TFT_BLUE);
  } 
  else if (currentRadioMode == RADIO_BLE) {
    tft.fillRect(300, 190, 150, 40, TFT_PURPLE);
  } 
  else if (currentRadioMode == RADIO_AP) {
    tft.fillRect(300, 190, 150, 40, TFT_DARKGREEN); 
  }
  else if (currentRadioMode == RADIO_CHANNELS) {
    tft.fillRect(300, 190, 150, 40, TFT_ORANGE); 
  }
  else if (currentRadioMode == RADIO_LAYER2) {
    tft.fillRect(300, 190, 150, 40, TFT_MAROON); 
  }

  // 2. Draw the universal white border
  tft.drawRect(300, 190, 150, 40, TFT_WHITE);

  // 3. Draw the corresponding text label
  if (currentRadioMode == RADIO_WIFI) {
    tft.drawString("MODE: WI-FI", 375, 210);
  } 
  else if (currentRadioMode == RADIO_BLE) {
    tft.drawString("MODE: BLE", 375, 210);
  } 
  else if (currentRadioMode == RADIO_AP) {
    tft.drawString("MODE: NETWORKS", 375, 210);
  }
  else if (currentRadioMode == RADIO_CHANNELS) {
    tft.drawString("MODE: CHANNELS", 375, 210);
  }
  else if (currentRadioMode == RADIO_LAYER2) {
    tft.drawString("MODE: LAYER 2", 375, 210);
  }

  // 5. EXIT BUTTON
  tft.fillRect(300, 240, 150, 40, TFT_RED);
  tft.drawRect(300, 240, 150, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("EXIT", 375, 260);
  
  // THE FIX: Reset datum to Top-Left for the rest of the UI ONLY at the very end!
  tft.setTextDatum(TL_DATUM); 
}

void drawChartHeader() {
  // 1. Gate the horizontal separator line so it doesn't cut through the L2 terminal
  if (currentRadioMode != RADIO_LAYER2) {
    tft.drawLine(0, HEADER_HEIGHT - 8, 480, HEADER_HEIGHT - 8, COLOR_HOT_CHEST);
  }

  // MENU BUTTON
  tft.drawRoundRect(420, 1, 55, 16, 2, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);  
  tft.setTextDatum(MC_DATUM);     
  tft.drawString("MENU", 447, 7); 
  tft.setTextDatum(TL_DATUM);     

  // BANNER
  tft.setTextWrap(false); 
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);

  char bannerStr[64];

  // ==========================================
  // THE 4-STATE HEADER LOGIC
  // ==========================================
  tft.setTextColor(COLOR_HOT_CHEST); 
  if (currentRadioMode == RADIO_BLE) {
    snprintf(bannerStr, sizeof(bannerStr), "SNIFFING BLE DEVICES");
  } 
  else if (currentRadioMode == RADIO_AP) {
    if (!target_locked) {
        snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | SNIFFING NETWORKS", CHANNELS[current_ch_idx]);
    } else {
        snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | TARGET LOCKED", target_channel);
    }
  }
  else if (currentRadioMode == RADIO_CHANNELS) { 
    snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | SNIFFING SPECTRUM", CHANNELS[current_ch_idx]);
  }
  else if (currentRadioMode == RADIO_LAYER2) { 
    if (!target_locked) {
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | L2 CAPTURE (HOPPING)", CHANNELS[current_ch_idx]);
    } else {
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | L2 CAPTURE (LOCKED)", target_channel);
    }
  }
  else if (currentRadioMode == RADIO_WIFI) {    
    if (!target_locked) {
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | FREE AIRSPACE", CHANNELS[current_ch_idx]);
    } else {
      char safe_ssid[15];
      strncpy(safe_ssid, target_ssid, 14);
      safe_ssid[14] = '\0';
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | %s (%ddBm)", target_channel, safe_ssid, target_rssi);
    }
  }
  tft.drawString(bannerStr, 5, 1);
}

// ==========================================
// WIFI SORTING STATE
// ==========================================
enum SortMode { SORT_TOTAL, SORT_TX, SORT_RX, SORT_AVG, SORT_CV, SORT_DIST, SORT_AGE };
SortMode currentSortMode = SORT_TOTAL; // Default state

double getSortMetric(MacRecord& record, SortMode mode) {
    switch(mode) {
        case SORT_TOTAL: 
            return (double)(record.tx_bytes + record.rx_bytes);
        case SORT_TX:    
            return (double)record.tx_bytes;
        case SORT_RX:    
            return (double)record.rx_bytes;
        case SORT_AVG:   
            return (record.packets > 0) ? ((double)record.sum_bytes / record.packets) : 0.0;
        case SORT_CV: {
            if (record.packets == 0) return 0.0;
            double mean = (double)record.sum_bytes / record.packets;
            if (mean == 0) return 0.0;
            double avg_sq_sum = (double)record.sum_sq_bytes / record.packets;
            double variance = avg_sq_sum - (mean * mean);
            if (variance < 0) variance = 0;
            return (sqrt(variance) / mean) * 100.0;
        }
        case SORT_DIST:
            // Swap this to smoothedDistance to use your new EMA filter!
            return (double)record.smoothedDistance; 
        case SORT_AGE:
            // Added the missing case and using the correct timestamp variable
            return (double)record.last_seen; 
    }
    return 0.0;
}

double getSortMetric(ApRecord& record, SortMode mode) {
    switch(mode) {
        case SORT_TOTAL: 
            return (double)(record.tx_bytes + record.rx_bytes);
        case SORT_TX:    
            return (double)record.tx_bytes;
        case SORT_RX:    
            return (double)record.rx_bytes;
        case SORT_AVG:   
            return (record.packets > 0) ? ((double)record.sum_bytes / record.packets) : 0.0;
        case SORT_CV: {
            if (record.packets == 0) return 0.0;
            double mean = (double)record.sum_bytes / record.packets;
            if (mean == 0) return 0.0;
            double avg_sq_sum = (double)record.sum_sq_bytes / record.packets;
            double variance = avg_sq_sum - (mean * mean);
            if (variance < 0) variance = 0;
            return (sqrt(variance) / mean) * 100.0;
        }
        case SORT_DIST:
            return (double)record.smoothedDistance; 
        case SORT_AGE:
            return (double)record.last_seen; 
    }
    return 0.0;
}

// ==========================================
// BLE SORTING STATE
// ==========================================
enum BleSortMode { SORT_BLE_HITS, SORT_BLE_DIST, SORT_BLE_AGE };
BleSortMode currentBleSortMode = SORT_BLE_HITS; // Default state

double getBleSortMetric(BLERecord& record, BleSortMode mode) {
    switch(mode) {
        case SORT_BLE_HITS:
            return (double)record.hits;
        case SORT_BLE_DIST:
            return (double)record.smoothedDistance;
        case SORT_BLE_AGE:
            // Fixed the variable name to match your struct
            return (double)record.lastSeen; 
    }
    return 0.0;
}

// ==========================================
// PROBE REQUEST SORTING
// ==========================================

double getProbeMetric(ProbeRecordShared record, ProbeSortMode mode) {
    if (mode == PROBE_SORT_HITS) return (double)record.hits;
    if (mode == PROBE_SORT_SSIDS) return (double)record.ssid_count;
    if (mode == PROBE_SORT_AGE) return (double)record.last_seen;
    
    if (mode == PROBE_SORT_DIST) {
        // Push devices with 0.0 distance (unknown/calculating) to the bottom
        if (record.smoothedDistance <= 0.0) return 99999.0; 
        return (double)record.smoothedDistance;
    }
    return 0.0;
}

void sortProbeList() {
    for (int i = 1; i < MAX_PROBE_SLOTS; i++) {
        ProbeRecordShared key = probeList[i];
        
        // Skip moving empty slots up the list
        bool key_empty = true;
        for(int b=0; b<6; b++) if(key.mac[b]!=0) { key_empty=false; break; }
        if (key_empty) continue; 

        double key_val = getProbeMetric(key, currentProbeSortMode);
        int j = i - 1;

        if (probe_sort_descending) {
            while (j >= 0) {
                bool j_empty = true;
                for(int b=0; b<6; b++) if(probeList[j].mac[b]!=0) { j_empty=false; break; }
                
                if (j_empty || getProbeMetric(probeList[j], currentProbeSortMode) < key_val) {
                    probeList[j + 1] = probeList[j];
                    j--;
                } else break;
            }
        } else {
            while (j >= 0) {
                bool j_empty = true;
                for(int b=0; b<6; b++) if(probeList[j].mac[b]!=0) { j_empty=false; break; }
                
                if (j_empty || getProbeMetric(probeList[j], currentProbeSortMode) > key_val) {
                    probeList[j + 1] = probeList[j];
                    j--;
                } else break;
            }
        }
        probeList[j + 1] = key;
    }
}

void drawChartFooter() {
  tft.fillRect(0, 296, 480, 24, TFT_BLACK);

  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextColor(TFT_WHITE);
  tft.setTextDatum(MC_DATUM); 

  if (currentRadioMode != RADIO_LAYER2) {
      // ==========================================
      // ZONE 1: SORT METRIC (Center X = 72)
      // ==========================================
      tft.drawRoundRect(2, 302, 141, 17, 3, TFT_WHITE); 

      char metricStr[32] = "SORT: ERR"; 
      
      if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
        if (currentSortMode == SORT_TOTAL) { strcpy(metricStr, "SORT: TOTAL"); tft.setTextColor(TFT_WHITE); }
        else if (currentSortMode == SORT_TX) { strcpy(metricStr, "SORT: TX"); tft.setTextColor(TFT_CYAN); }
        else if (currentSortMode == SORT_RX) { strcpy(metricStr, "SORT: RX"); tft.setTextColor(TFT_MAGENTA); }
        else if (currentSortMode == SORT_AVG) { strcpy(metricStr, "SORT: AVG"); tft.setTextColor(TFT_YELLOW); }
        else if (currentSortMode == SORT_CV) { strcpy(metricStr, "SORT: CV%"); tft.setTextColor(TFT_ORANGE); }
        else if (currentSortMode == SORT_DIST) { strcpy(metricStr, "SORT: DIST"); tft.setTextColor(TFT_GREEN); }
        else if (currentSortMode == SORT_AGE) { strcpy(metricStr, "SORT: AGE"); tft.setTextColor(TFT_BLUE); }
      } 
      else if (currentRadioMode == RADIO_CHANNELS) {
        if (currentSortMode == SORT_TOTAL) { strcpy(metricStr, "SORT: TOTAL"); tft.setTextColor(TFT_WHITE); }
        else if (currentSortMode == SORT_TX) { strcpy(metricStr, "SORT: DN"); tft.setTextColor(TFT_CYAN); }
        else if (currentSortMode == SORT_RX) { strcpy(metricStr, "SORT: UP"); tft.setTextColor(TFT_MAGENTA); }
        else if (currentSortMode == SORT_AVG) { strcpy(metricStr, "SORT: AVG"); tft.setTextColor(TFT_YELLOW); }
        else if (currentSortMode == SORT_CV) { strcpy(metricStr, "SORT: CV%"); tft.setTextColor(TFT_ORANGE); }
        else if (currentSortMode == SORT_DIST) { strcpy(metricStr, "SORT: PWR"); tft.setTextColor(TFT_GREEN); }
        else if (currentSortMode == SORT_AGE) { strcpy(metricStr, "SORT: AGE"); tft.setTextColor(TFT_BLUE); }
      }
      else if (currentRadioMode == RADIO_BLE) {
        if (currentBleSortMode == SORT_BLE_HITS) { strcpy(metricStr, "SORT: HITS"); tft.setTextColor(TFT_WHITE); }
        else if (currentBleSortMode == SORT_BLE_DIST) { strcpy(metricStr, "SORT: DIST"); tft.setTextColor(TFT_GREEN); }
        else if (currentBleSortMode == SORT_BLE_AGE) { strcpy(metricStr, "SORT: AGE"); tft.setTextColor(TFT_BLUE); }
      }
      
      tft.drawString(metricStr, 72, 308);
      tft.setTextColor(TFT_WHITE);
      
      // ==========================================
      // ZONE 2: SORT DIRECTION (Center X = 217)
      // ==========================================
      tft.drawRoundRect(147, 302, 141, 17, 3, TFT_WHITE); 

      if (sort_descending) {
        tft.drawString("ORDER: DESC", 217, 309);
      } else {
        tft.setTextColor(TFT_GREEN); 
        tft.drawString("ORDER: ASC", 217, 309);
        tft.setTextColor(TFT_WHITE); 
      }

      // ==========================================
      // ZONE 3: SCALE MODE (Center X = 362)
      // ==========================================
      tft.drawRoundRect(292, 302, 141, 17, 3, TFT_WHITE); 

      if (useLogScale) {
        tft.setTextColor(TFT_YELLOW); 
        tft.drawString("SCALE: LOG", 362, 309);
      } else {
        tft.drawString("SCALE: LIN", 362, 309);
      }
  } else {
      // Layer 2 gets a clean, unified label instead of useless sort buttons
      tft.setTextColor(TFT_DARKGREY);
      // Draw the static time scale on the far left
      tft.setTextDatum(TL_DATUM);
      tft.drawString("|=2m", 10, 301); 
      
      // Draw the main status label perfectly centered
      tft.setTextDatum(MC_DATUM);
      tft.drawString("PROMISCUOUS CAPTURE MODE", 240, 309); // 240 is true center of 480px screen
      tft.setTextColor(TFT_WHITE);
  }
    
  // ==========================================
  // ZONE 4: BATTERY PLACEHOLDER
  // ==========================================
  tft.drawRect(445, 304, 22, 12, TFT_WHITE); 
  tft.fillRect(467, 307, 3, 6, TFT_WHITE);   
  tft.fillRect(447, 306, 18, 8, TFT_GREEN);  
  
  tft.setTextDatum(TL_DATUM); 
  tft.setTextColor(TFT_WHITE);
}

float calculateRfDistance(int rssi, int txPower, RadioProtocol protocol, float customLoss = 0.0) {
    // Protection against invalid/corrupt packets. 
    // Returning -1.0 prevents the EMA filter from dragging the average down to 0!
    if (rssi >= 0 || rssi < -100) return -1.0; 

    float measuredPowerAtOneMeter;
    float pathLossExponent;

    // Set baselines based on the physical frequency and protocol
    switch (protocol) {
        case RADIO_BLE_24GHZ:
            measuredPowerAtOneMeter = (txPower != 0) ? (float)txPower - 62.0 : -59.0;
            pathLossExponent = (customLoss > 0.0) ? customLoss : 3.2; // Standard indoor
            break;

        case RADIO_WIFI_24GHZ:
            // Wi-Fi transmits significantly louder than BLE standard beacons
            measuredPowerAtOneMeter = (txPower != 0) ? (float)txPower - 65.0 : -45.0;
            pathLossExponent = (customLoss > 0.0) ? customLoss : 3.0; 
            break;

        case RADIO_WIFI_5GHZ:
            // 5GHz absorbs into the environment much faster than 2.4GHz
            measuredPowerAtOneMeter = (txPower != 0) ? (float)txPower - 68.0 : -50.0;
            pathLossExponent = (customLoss > 0.0) ? customLoss : 3.8; // Heavy indoor attenuation
            break;

        default:
            return -1.0;
    }
    
    // The core Log-Distance Formula: d = 10 ^ ((A - RSSI) / 10n)
    float ratio = (measuredPowerAtOneMeter - (float)rssi) / (10.0 * pathLossExponent);
    return std::pow(10.0, ratio);
}
/*
float calculateRfDistance(int rssi, int txPower, RadioProtocol protocol) {
    if (rssi >= 0 || rssi < -100) return -1.0; // Protection against invalid packets

    // ==========================================
    // ENGINE 1: YOUR FIELD-TESTED BLE MATH
    // ==========================================
    if (protocol == RADIO_BLE_24GHZ) {
        float measuredPowerAtOneMeter = (txPower != 0) ? (float)txPower - 62.0 : -59.0;
        float pathLossExponent = 3.2; // Your home's "magic" number
        
        float ratio = (measuredPowerAtOneMeter - (float)rssi) / (10.0 * pathLossExponent);
        return pow(10.0, ratio);
    } 
    
    // ==========================================
    // ENGINE 2: ALTBEACON MATH FOR WI-FI
    // ==========================================
    else {
        float measuredPowerAtOneMeter = (protocol == RADIO_WIFI_5GHZ) ? -50.0 : -45.0;
        double ratio = (double)rssi / (double)measuredPowerAtOneMeter;

        if (ratio < 1.0) {
            return pow(ratio, 10.0);
        } else {
            return (0.89976 * pow(ratio, 7.7095)) + 0.111;
        }
    }
}

float calculateRfDistance(int rssi, int txPower, RadioProtocol protocol, float customLoss = 0.0) {
    if (rssi >= 0) return 0.0; // Protection against invalid/corrupt packets

    float measuredPowerAtOneMeter;
    float pathLossExponent;

    // Set baselines based on the physical frequency and protocol
    switch (protocol) {
        case RADIO_BLE_24GHZ:
            measuredPowerAtOneMeter = (txPower != 0) ? (float)txPower - 62.0 : -59.0;
            pathLossExponent = (customLoss > 0.0) ? customLoss : 3.2; // Standard indoor
            break;

        case RADIO_WIFI_24GHZ:
            // Wi-Fi transmits significantly louder than BLE standard beacons
            measuredPowerAtOneMeter = (txPower != 0) ? (float)txPower - 65.0 : -45.0;
            pathLossExponent = (customLoss > 0.0) ? customLoss : 3.0; 
            break;

        case RADIO_WIFI_5GHZ:
            // 5GHz absorbs into the environment much faster than 2.4GHz
            measuredPowerAtOneMeter = (txPower != 0) ? (float)txPower - 68.0 : -50.0;
            pathLossExponent = (customLoss > 0.0) ? customLoss : 3.8; // Heavy indoor attenuation
            break;

        default:
            return 0.0;
    }
    
    // The core Log-Distance Formula: d = 10 ^ ((A - RSSI) / 10n)
    float ratio = (measuredPowerAtOneMeter - (float)rssi) / (10.0 * pathLossExponent);
    return std::pow(10.0, ratio);
}
*/

void drawApScanner() {
  tft.fillScreen(TFT_BLACK);
  tft.setTextSize(1); 

  int n = WiFi.scanComplete();
  if (n < 0) {
    ap_current_page = 0;

    tft.setFreeFont(&UbuntuMono_Regular11pt7b);
    tft.setTextDatum(MC_DATUM);
    tft.setTextColor(TFT_WHITE);
    tft.fillRect(0, 0, 480, 30, TFT_BLUE);
    tft.drawString("SCANNING ACCESS POINTS...", 240, 15);

    esp_wifi_set_promiscuous(false);
    WiFi.mode(WIFI_STA);
    WiFi.disconnect();
    delay(100);

    n = WiFi.scanNetworks();
  }

  tft.setFreeFont(&UbuntuMono_Regular11pt7b);
  tft.setTextDatum(MC_DATUM);
  tft.setTextColor(TFT_WHITE);
  tft.fillRect(0, 0, 480, 30, TFT_BLUE);
  
  // Build the dynamic header string using the 'n' variable
  char headerStr[64];
  snprintf(headerStr, sizeof(headerStr), "SELECT TARGET AP (%d)", n);
  tft.drawString(headerStr, 240, 15);

  tft.setFreeFont(&UbuntuMono_Regular11pt7b);
  tft.setTextDatum(TL_DATUM);
  tft.setTextColor(TFT_GREEN);
  tft.drawRect(0, 40, 480, 35, TFT_DARKGREY); 
  tft.drawString("CH:ALL (Sniff Free Airspace)", 5, 50);

  tft.setTextColor(TFT_WHITE);
  
  // ==========================================
  // LIST GENERATION
  // ==========================================
  if (n == 0) {
    tft.drawString("No networks found in airspace.", 5, 90);
  } else {
    int start_idx = ap_current_page * APS_PER_PAGE;

    if (start_idx >= n) {
      ap_current_page = 0;
      start_idx = 0;
    }

    int end_idx = start_idx + APS_PER_PAGE;
    if (end_idx > n) end_idx = n;

    int row = 0;
    for (int i = start_idx; i < end_idx; ++i) {
      int y = 80 + (row * 35); 

      // 1. Get the raw BSSID bytes and the SSID string
      uint8_t* bssid = WiFi.BSSID(i);
      String raw_ssid = WiFi.SSID(i);
      char tactical_ssid[26]; 

      // 2. Determine if this SSID is a duplicate in the airspace
      bool has_clone = false;
      if (raw_ssid.length() > 0) {
        for (int j = 0; j < n; ++j) {
          if (i != j && WiFi.SSID(j) == raw_ssid) {
            has_clone = true;
            break;
          }
        }
      }

      // 3. Construct the Tactical Suffix String
      if (raw_ssid.length() == 0) {
        snprintf(tactical_ssid, sizeof(tactical_ssid), "<HIDDEN> [%02X%02X]", bssid[4], bssid[5]);
      } else if (has_clone) {
        char temp_ssid[16]; 
        strncpy(temp_ssid, raw_ssid.c_str(), 15);
        temp_ssid[15] = '\0';
        snprintf(tactical_ssid, sizeof(tactical_ssid), "%s~%02X%02X", temp_ssid, bssid[4], bssid[5]);
      } else {
        char temp_ssid[22]; 
        strncpy(temp_ssid, raw_ssid.c_str(), 21);
        temp_ssid[21] = '\0';
        snprintf(tactical_ssid, sizeof(tactical_ssid), "%s", temp_ssid);
      }

      // 4. Calculate Distance dynamically
      float dist = calculateRfDistance(WiFi.RSSI(i), 0, RADIO_WIFI_24GHZ);

      // 5. SPLIT DRAWING LOGIC FOR PERFECT ALIGNMENT
      
      // Build the Left String (Channel & SSID)
      char leftStr[60];
      snprintf(leftStr, sizeof(leftStr), "CH:%02d %s", WiFi.channel(i), tactical_ssid);

      // Build the Right String (RSSI & Distance) with rigid width padding
      char rightStr[30];
      snprintf(rightStr, sizeof(rightStr), "%4ddBm %3.0fm", WiFi.RSSI(i), dist);

      // Paint Left Side (Flush Left at X=5)
      tft.setTextDatum(TL_DATUM);
      tft.drawString(leftStr, 5, y + 10);

      // Paint Right Side (Flush Right at X=475)
      tft.setTextDatum(TR_DATUM);
      tft.drawString(rightStr, 475, y + 10); 

      tft.drawRect(0, y, 480, 35, TFT_DARKGREY);
      row++;
    }
  }

  // ==========================================
  // FOOTER & NAVIGATION (Synced to Y=294)
  // ==========================================
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM); 

  // THE FIX: Pushed down from 285 to perfectly match the Probe Tracker footer
  tft.drawLine(0, 294, 480, 294, TFT_WHITE);
  
  tft.setTextColor(TFT_RED);
  tft.drawString("BACK", 215, 300);

  if (n > APS_PER_PAGE) {
    tft.setTextColor(TFT_WHITE);

    if (ap_current_page > 0) {
      tft.drawString("<- PREV", 20, 300);
    }
    
    if (((ap_current_page + 1) * APS_PER_PAGE) < n) {
      tft.drawString("NEXT ->", 360, 300);
    }
  }
}

void getAgeString(uint32_t timestamp, char* buf, size_t len) {
    if (timestamp == 0) {
        snprintf(buf, len, "00h00m");
        return;
    }
    
    // Using subtraction handles the millis() 50-day rollover safely
    uint32_t elapsed = millis() - timestamp; 
    uint32_t mins = elapsed / 60000;
    uint32_t hours = mins / 60;
    mins = mins % 60;

    // Cap at 99h to prevent layout breaking if left on for 4+ days
    if (hours > 99) {
        snprintf(buf, len, ">99h  ");
    } else {
        snprintf(buf, len, "%02luh%02lum", hours, mins);
    }
}

void cleanOsintString(char* s) {
    if (s == nullptr) return;

    // 1. Strip bulky corporate suffixes
    const char* suffixes[] = {", Inc.", " Inc.", " LLC", " Corp.", " Ltd."};
    for (int i = 0; i < 5; i++) {
        size_t suffix_len = strlen(suffixes[i]);
        char* pos;
        while ((pos = strstr(s, suffixes[i])) != nullptr) {
            // memmove safely handles overlapping memory regions.
            // We shift everything after the suffix leftward, including the '\0' terminator.
            memmove(pos, pos + suffix_len, strlen(pos + suffix_len) + 1);
        }
    }

    // 2. Crush double spaces after colons (e.g. "Apple:  Find My" -> "Apple:Find My")
    char* pos;
    while ((pos = strstr(s, ":  ")) != nullptr) {
        // Keep the ':', shift the rest of the string left by 2 bytes
        memmove(pos + 1, pos + 3, strlen(pos + 3) + 1); 
    }
    
    // 3. Crush single spaces after colons
    while ((pos = strstr(s, ": ")) != nullptr) {
        // Keep the ':', shift the rest of the string left by 1 byte
        memmove(pos + 1, pos + 2, strlen(pos + 2) + 1);
    }
}

void formatShortUnit(uint32_t bytes, char* buf, size_t len) {
    if (bytes < 1000) snprintf(buf, len, "%3luB", bytes);
    else if (bytes < 1024000) snprintf(buf, len, "%3luK", bytes / 1024);
    else if (bytes < 1048576000) snprintf(buf, len, "%3luM", bytes / 1048576);
    else snprintf(buf, len, "%3.1fG", (float)bytes / 1073741824.0);
}

void formatTotalUnit(uint32_t bytes, char* buf, size_t len) {
    if (bytes < 1000) snprintf(buf, len, "%4luB", bytes);
    else if (bytes < 1024000) snprintf(buf, len, "%4luK", bytes / 1024);
    else if (bytes < 1048576000) snprintf(buf, len, "%4luM", bytes / 1048576);
    else snprintf(buf, len, "%4.1fG", (float)bytes / 1073741824.0);
}

void drawDeviceList() {
  tft.fillScreen(TFT_BLACK);
  tft.setTextDatum(TL_DATUM);
  tft.setTextSize(1);

  // ==========================================
  // 1. DEVICE COUNTING
  // ==========================================
  int total_devices = 0;
  
  if (currentRadioMode == RADIO_WIFI) total_devices = sessionMacCount;
  else if (currentRadioMode == RADIO_BLE) total_devices = sessionBleCount;
  else if (currentRadioMode == RADIO_AP) total_devices = sessionApCount;
  else if (currentRadioMode == RADIO_CHANNELS) total_devices = sessionChannelCount;
  else if (currentRadioMode == RADIO_LAYER2) {
      for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
          if (leakHistory[i].leak.meta.timestamp > 0) total_devices++;
      }
  }

  // ==========================================
  // 2. DYNAMIC PAGINATION MATH
  // ==========================================
  int start_idx = 0;
  int end_idx = 0;
  bool has_next_page = false;

  // DECLARE IN OUTER SCOPE SO RENDERER CAN SEE THEM!
  int valid_indices[MAX_LEAK_SLOTS] = {0}; 
  int valid_count = 0;

  if (currentRadioMode == RADIO_LAYER2) {
      // --- 1. GATHER LOGICAL ENTRIES ---
      for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
          if (leakHistory[i].leak.meta.timestamp > 0) {
              valid_indices[valid_count++] = i;
          }
      }

      // --- 2. DYNAMIC L2 "SNUG" PACKING ---
      const int maxChars = 58;
      int page_starts[MAX_LEAK_SLOTS] = {0}; // FRIEND'S FIX: Eliminated the arbitrary 15
      int total_pages = 0;
      int test_y = 32;

      for (int v = 0; v < valid_count; v++) {
          int idx = valid_indices[v];
          int pLen = leakHistory[idx].leak.retained_len;

          // FRIEND'S FIX: Defensive clamping for the packing math
          if (pLen > MAX_LEAK_STR_LEN - 1) pLen = MAX_LEAK_STR_LEN - 1;

          // Dynamically scale up to 9 lines (512 bytes / 58 chars)
          int n_lines = (pLen > 0) ? ((pLen - 1) / maxChars) + 1 : 1;
          if (n_lines > 9) n_lines = 9;

          int item_h = 42 + (n_lines * 14) + 5; 

          if (test_y + item_h > 290) { 
              if (total_pages < MAX_LEAK_SLOTS - 1) { // Prevents out-of-bounds on page_starts
                  total_pages++;
                  page_starts[total_pages] = v; 
              }
              test_y = 32 + item_h; 
          } else {
              test_y += item_h; 
          }
      }

      if (device_current_page > total_pages) device_current_page = total_pages;
      start_idx = page_starts[device_current_page];
      end_idx = (device_current_page < total_pages) ? page_starts[device_current_page + 1] : valid_count;
      has_next_page = (device_current_page < total_pages);
      
  } else {
      // --- FIXED GRID PACKING (WIFI/AP/BLE/CHANNELS) ---
      int items_per_page = 7;
      start_idx = device_current_page * items_per_page;
      if (start_idx >= total_devices) {
          device_current_page = 0;
          start_idx = 0;
      }
      end_idx = start_idx + items_per_page;
      if (end_idx > total_devices) end_idx = total_devices;
      has_next_page = (((device_current_page + 1) * items_per_page) < total_devices);
  }

  // ==========================================
  // 3. DRAW TOP BANNER (WITH FOXHUNT OVERRIDE)
  // ==========================================
  tft.setTextColor(TFT_WHITE);
  tft.setFreeFont(&UbuntuMono_B9pt7b);
  
  if (is_selecting_target) {
    tft.fillRect(0, 0, 480, 24, TFT_RED); 
    char huntStr[64];
    const char* modeName = (currentRadioMode == RADIO_WIFI) ? "WI-FI" : (currentRadioMode == RADIO_BLE) ? "BLE" : "NETWORKS";
    snprintf(huntStr, sizeof(huntStr), " FOXHUNT TARGET (%s)", modeName);
    tft.drawString(huntStr, 5, 5);
  } else {
    uint16_t headerColor = TFT_BLUE;
    const char* modeStr = "WI-FI";
    
    if (currentRadioMode == RADIO_BLE) { headerColor = TFT_PURPLE; modeStr = "BLE"; } 
    else if (currentRadioMode == RADIO_AP) { headerColor = TFT_DARKGREEN; modeStr = "NETWORKS"; } 
    else if (currentRadioMode == RADIO_CHANNELS) { headerColor = TFT_ORANGE; modeStr = "CHANNELS"; } 
    else if (currentRadioMode == RADIO_LAYER2) { headerColor = TFT_MAROON; modeStr = "LAYER 2 LEAKS"; }
    
    tft.fillRect(0, 0, 480, 24, headerColor);
    char headerStr[64];
    snprintf(headerStr, sizeof(headerStr), " SNIFFED %s (%d)", modeStr, total_devices);
    tft.drawString(headerStr, 5, 5); 
  } 

  // ==========================================
  // 4. DYNAMIC SORT BUTTONS
  // ==========================================
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  char metricStr[32] = "SORT:ERR";
  uint16_t metricColor = TFT_RED;
  
  if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
    if (currentSortMode == SORT_TOTAL) { strcpy(metricStr, "SORT:TOTAL"); metricColor = TFT_WHITE; }
    else if (currentSortMode == SORT_TX) { strcpy(metricStr, "SORT:TX"); metricColor = TFT_CYAN; }
    else if (currentSortMode == SORT_RX) { strcpy(metricStr, "SORT:RX"); metricColor = TFT_MAGENTA; }
    else if (currentSortMode == SORT_AVG) { strcpy(metricStr, "SORT:AVG"); metricColor = TFT_YELLOW; }
    else if (currentSortMode == SORT_CV) { strcpy(metricStr, "SORT:CV%"); metricColor = TFT_ORANGE; }
    else if (currentSortMode == SORT_DIST) { strcpy(metricStr, "SORT:DIST"); metricColor = TFT_GREEN; }
    else if (currentSortMode == SORT_AGE) { strcpy(metricStr, "SORT:AGE"); metricColor = TFT_BLUE; }
  } 
  else if (currentRadioMode == RADIO_CHANNELS) {
    if (currentSortMode == SORT_TOTAL) { strcpy(metricStr, "SORT:TOTAL"); metricColor = TFT_WHITE; }
    else if (currentSortMode == SORT_TX) { strcpy(metricStr, "SORT:DN"); metricColor = TFT_CYAN; }
    else if (currentSortMode == SORT_RX) { strcpy(metricStr, "SORT:UP"); metricColor = TFT_MAGENTA; }
    else if (currentSortMode == SORT_AVG) { strcpy(metricStr, "SORT:AVG"); metricColor = TFT_YELLOW; }
    else if (currentSortMode == SORT_CV) { strcpy(metricStr, "SORT:CV%"); metricColor = TFT_ORANGE; }
    else if (currentSortMode == SORT_DIST) { strcpy(metricStr, "SORT:PWR"); metricColor = TFT_GREEN; }
  } 
  else if (currentRadioMode == RADIO_BLE) {
    if (currentBleSortMode == SORT_BLE_HITS) { strcpy(metricStr, "SORT:HITS"); metricColor = TFT_WHITE; }
    else if (currentBleSortMode == SORT_BLE_DIST) { strcpy(metricStr, "SORT:DIST"); metricColor = TFT_GREEN; }
    else if (currentBleSortMode == SORT_BLE_AGE) { strcpy(metricStr, "SORT:AGE"); metricColor = TFT_BLUE; }
  }
  else if (currentRadioMode == RADIO_LAYER2) {
    if (currentLeakSort == SORT_LEAK_AGE) { strcpy(metricStr, "SORT:AGE"); metricColor = TFT_BLUE; }
    else if (currentLeakSort == SORT_LEAK_LENGTH) { strcpy(metricStr, "SORT:SIZE"); metricColor = TFT_CYAN; }
    else if (currentLeakSort == SORT_LEAK_HITS) { strcpy(metricStr, "SORT:HITS"); metricColor = TFT_WHITE; }
  }

  tft.fillRoundRect(275, 2, 130, 20, 3, TFT_BLACK); 
  tft.drawRoundRect(275, 2, 130, 20, 3, TFT_WHITE);
  tft.setTextColor(metricColor);
  tft.drawString(metricStr, 282, 4);

  tft.fillRoundRect(410, 2, 65, 20, 3, TFT_BLACK); 
  tft.drawRoundRect(410, 2, 65, 20, 3, TFT_WHITE);
  
  if (sort_descending) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("DESC", 423, 4);
  } else {
    tft.setTextColor(TFT_GREEN);
    tft.drawString("ASC", 427, 4);
  }
  
  tft.setTextColor(TFT_WHITE);

  if (total_devices == 0) {
    tft.setFreeFont(&UbuntuMono_Regular9pt7b);
    tft.drawString("No devices captured yet.", 5, 45);
  } else {
    // ==========================================
    // 5. DRAW THE UNIFIED DUAL COLUMN HEADERS
    // ==========================================
    if (currentRadioMode != RADIO_LAYER2) {
        tft.setTextColor(TFT_GREEN);
        if (currentRadioMode == RADIO_WIFI) {
          tft.setFreeFont(&UbuntuMono_B9pt7b);
          tft.drawString("     VENDOR                 MAC            RSSI TOTAL", 5, 26); 
          tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
          tft.drawString("Per(s) FIRST | LAST DIST Mbps  AVG    CV%    TX | RX", 5, 41);
        } 
        else if (currentRadioMode == RADIO_AP) {
          tft.setFreeFont(&UbuntuMono_B9pt7b);
          tft.drawString("     SSID                 BSSID         CC RSSI TOTAL", 5, 26);       
          tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
          tft.drawString("    FIRST | LAST  DIST CH RATE  AVG  CV%    TX | RX", 5, 41);
        }
        else if (currentRadioMode == RADIO_CHANNELS) {
          tft.setFreeFont(&UbuntuMono_B9pt7b);
          tft.drawString("     CHANNEL           PWR(AVG dBm|STD)         TOTAL", 5, 26);       
          tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
          tft.drawString("    FIRST | LAST         STATE   AVG  CV%    DN | UP", 5, 41);
        }
        else {
          tft.setFreeFont(&UbuntuMono_B9pt7b);
          tft.drawString("    NAME                FIRST|LAST    RSSI  DIST  HITS", 5, 26);       
          tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
          tft.drawString("MAC ADDRESS        VENDOR/DIAGNOSTIC PAYLOAD", 5, 41);
        }
        tft.setTextColor(TFT_WHITE); 
        tft.drawLine(0, 57, 480, 57, TFT_WHITE); 
    }

    // ==========================================
    // 6. DRAW THE DATA ROWS
    // ==========================================
    int row = 0;
    int base_y = (currentRadioMode == RADIO_LAYER2) ? 32 : 62;
    int y_spacing = 33; // Fixed spacing for all non-L2 modes
    int dyn_y = base_y; // Dynamic tracker exclusively for L2 mode

    for (int i = start_idx; i < end_idx; i++) {
      
      // Select the correct Y coordinate based on the mode
      int y = (currentRadioMode == RADIO_LAYER2) ? dyn_y : (base_y + (row * y_spacing)); 
      
      if (currentRadioMode == RADIO_WIFI) {
        // ... [WIFI MODE LOGIC REMAINS UNCHANGED] ...
        char line1[90]; char line2[90];
        resolveMacVendor(&sessionData[i]);

        char macStr[18];
        snprintf(macStr, sizeof(macStr), "%02X:%02X:%02X:%02X:%02X:%02X",
                 sessionData[i].mac[0], sessionData[i].mac[1], sessionData[i].mac[2],
                 sessionData[i].mac[3], sessionData[i].mac[4], sessionData[i].mac[5]);

        char safeVendor[20]; 
        snprintf(safeVendor, sizeof(safeVendor), "%-18.18s", sessionData[i].vendor);

        double mean = 0.0; double cv_percent = 0.0;
        if (sessionData[i].packets > 0) {
            mean = (double)sessionData[i].sum_bytes / (double)sessionData[i].packets;
            double avg_sq_sum = (double)sessionData[i].sum_sq_bytes / (double)sessionData[i].packets;
            double variance = avg_sq_sum - (mean * mean);
            if (variance < 0) variance = 0; 
            double std_dev = sqrt(variance);
            if (mean > 0) cv_percent = (std_dev / mean) * 100.0;
        }

        char firstSeenStr[8], lastSeenStr[8], ageCombo[16];
        getAgeString(sessionData[i].first_seen, firstSeenStr, sizeof(firstSeenStr));
        getAgeString(sessionData[i].last_seen, lastSeenStr, sizeof(lastSeenStr));
        snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr); 

        uint32_t total_bytes = sessionData[i].tx_bytes + sessionData[i].rx_bytes;
        char totStr[10];
        formatTotalUnit(total_bytes, totStr, sizeof(totStr));

        char txStr[6], rxStr[6], trafficCombo[12];
        formatShortUnit(sessionData[i].tx_bytes, txStr, sizeof(txStr));
        formatShortUnit(sessionData[i].rx_bytes, rxStr, sizeof(rxStr));
        snprintf(trafficCombo, sizeof(trafficCombo), "%s|%s", txStr, rxStr); 

        char avgStr[6];
        formatShortUnit((uint32_t)mean, avgStr, sizeof(avgStr));

        int keep_alive_s = 0;
        if (sessionData[i].packets > 1) {
            unsigned long duration_ms = sessionData[i].last_seen - sessionData[i].first_seen;
            keep_alive_s = (duration_ms / sessionData[i].packets) / 1000;
            if (keep_alive_s > 99) keep_alive_s = 99; 
        }

        snprintf(line1, sizeof(line1), "%3d. %-18.18s %17s %4d %-5.5s", 
                 (i + 1), safeVendor, macStr, sessionData[i].rssi, totStr);

        snprintf(line2, sizeof(line2), "  %02d  %13s %4.0fm %3d  %-5.5s %4.0f%%   %9s", 
                 keep_alive_s, ageCombo, sessionData[i].smoothedDistance, sessionData[i].rate, 
                 avgStr, cv_percent, trafficCombo);

        tft.setFreeFont(&UbuntuMono_B9pt7b);
        tft.drawString(line1, 5, y);
        tft.setTextColor(TFT_LIGHTGREY);
        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.drawString(line2, 5, y + 15);
        tft.setTextColor(TFT_WHITE);      
        
      } else if (currentRadioMode == RADIO_BLE) {
        // ... [BLE MODE LOGIC REMAINS UNCHANGED] ...
        char line1[90]; 
        char safeName[20];
        
        snprintf(safeName, sizeof(safeName), "%-18.18s", sessionBleData[i].name);

        char firstSeenStr[8], lastSeenStr[8], ageCombo[16];
        getAgeString(sessionBleData[i].firstSeen, firstSeenStr, sizeof(firstSeenStr));
        getAgeString(sessionBleData[i].lastSeen, lastSeenStr, sizeof(lastSeenStr));
        snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr); 

        const char* trackerStr = "";
        switch (sessionBleData[i].trackerType) {
            case TRACKER_APPLE_FINDMY: trackerStr = "Apple: Find My"; break;
            case TRACKER_APPLE_IBEACON: trackerStr = "Apple: iBeacon"; break;
            case TRACKER_GOOGLE_FASTPAIR: trackerStr = "Google: FastPair"; break;
            case TRACKER_SAMSUNG_SMARTTAG: trackerStr = "Samsung: SmartTag"; break;
            case TRACKER_TILE: trackerStr = "Tile Tracker"; break;
            case TRACKER_MS_SWIFTPAIR: trackerStr = "MS: Swift Pair"; break;
            case TRACKER_EDDYSTONE: trackerStr = "Eddystone"; break;
            default: trackerStr = ""; break;
        }

        const char* appStr = resolveBleAppearance(sessionBleData[i].appearanceId);
        const char* srvStr = resolveBleServiceUuid(sessionBleData[i].serviceId);
        
        char tagStr[64] = {0}; 
        
        if (strlen(trackerStr) > 0 && sessionBleData[i].namePriority != 1) {
            strlcpy(tagStr, trackerStr, sizeof(tagStr));
        }
        
        if (appStr != nullptr && appStr[0] != '\0') {
            if (tagStr[0] != '\0') strlcat(tagStr, " | ", sizeof(tagStr));
            strlcat(tagStr, appStr, sizeof(tagStr));
        }
        
        if (srvStr != nullptr && srvStr[0] != '\0') {
            if (tagStr[0] != '\0') strlcat(tagStr, " | ", sizeof(tagStr));
            strlcat(tagStr, srvStr, sizeof(tagStr));
        }

        if (tagStr[0] == '\0') {
            if (sessionBleData[i].payload[0] != '\0') {
                if (sessionBleData[i].trackerType == TRACKER_APPLE_IBEACON) {
                    snprintf(tagStr, sizeof(tagStr), "iBeacon | %s", sessionBleData[i].payload);
                } else {
                    strlcpy(tagStr, sessionBleData[i].payload, sizeof(tagStr)); 
                }
            } else {
                strlcpy(tagStr, "No Data", sizeof(tagStr)); 
            }
        }
        
        cleanOsintString(tagStr); 

        char macStr[18];
        snprintf(macStr, sizeof(macStr), "%02X:%02X:%02X:%02X:%02X:%02X", 
                 sessionBleData[i].mac[0], sessionBleData[i].mac[1], sessionBleData[i].mac[2], 
                 sessionBleData[i].mac[3], sessionBleData[i].mac[4], sessionBleData[i].mac[5]);

        snprintf(line1, sizeof(line1), "%2d.%-18.18s %13s %4d %4.0fm %5u", 
                 (i + 1), safeName, ageCombo, sessionBleData[i].rssi, 
                 sessionBleData[i].smoothedDistance, sessionBleData[i].hits);

        char line2[90];
        snprintf(line2, sizeof(line2), "%17s  %-33.33s", macStr, tagStr);

        tft.setFreeFont(&UbuntuMono_B9pt7b);
        tft.drawString(line1, 5, y);
        tft.setTextColor(TFT_LIGHTGREY);
        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.drawString(line2, 5, y + 15);
        tft.setTextColor(TFT_WHITE);

      } else if (currentRadioMode == RADIO_AP) {
        // ... [AP MODE LOGIC REMAINS UNCHANGED] ...
        char line1[90];
        char line2[90];

        bool has_clone = false;
        if (strcmp(sessionApData[i].ssid, "<HIDDEN>") != 0 && strcmp(sessionApData[i].ssid, "<UNKNOWN>") != 0) {
          for (int j = 0; j < sessionApCount; j++) {
            if (i != j && strcmp(sessionApData[i].ssid, sessionApData[j].ssid) == 0) {
              has_clone = true; break;
            }
          }
        }

        char safeSsid[20];
        if (strcmp(sessionApData[i].ssid, "<HIDDEN>") == 0 || strcmp(sessionApData[i].ssid, "<UNKNOWN>") == 0) {
           snprintf(safeSsid, sizeof(safeSsid), "%-18.18s", sessionApData[i].ssid);
        } else if (has_clone) {
           char temp_ssid[13];
           strncpy(temp_ssid, sessionApData[i].ssid, 12); temp_ssid[12] = '\0';
           snprintf(safeSsid, sizeof(safeSsid), "%s~%02X%02X", temp_ssid, sessionApData[i].bssid[4], sessionApData[i].bssid[5]);
        } else {
           snprintf(safeSsid, sizeof(safeSsid), "%-18.18s", sessionApData[i].ssid);
        }

        char bssidStr[18];
        snprintf(bssidStr, sizeof(bssidStr), "%02X:%02X:%02X:%02X:%02X:%02X",
                 sessionApData[i].bssid[0], sessionApData[i].bssid[1], sessionApData[i].bssid[2],
                 sessionApData[i].bssid[3], sessionApData[i].bssid[4], sessionApData[i].bssid[5]);

        double mean = 0.0;
        double cv_percent = 0.0;
        if (sessionApData[i].packets > 0) {
            mean = (double)sessionApData[i].sum_bytes / (double)sessionApData[i].packets;
            double avg_sq_sum = (double)sessionApData[i].sum_sq_bytes / (double)sessionApData[i].packets;
            double variance = avg_sq_sum - (mean * mean);
            if (variance < 0) variance = 0; 
            double std_dev = sqrt(variance);
            if (mean > 0) cv_percent = (std_dev / mean) * 100.0;
        }

        char avgStr[6];
        formatShortUnit((uint32_t)mean, avgStr, sizeof(avgStr));

        char firstSeenStr[8], lastSeenStr[8], ageCombo[16];
        getAgeString(sessionApData[i].first_seen, firstSeenStr, sizeof(firstSeenStr));
        getAgeString(sessionApData[i].last_seen, lastSeenStr, sizeof(lastSeenStr));
        snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr); 

        uint32_t total_bytes = sessionApData[i].tx_bytes + sessionApData[i].rx_bytes;
        char totStr[10];
        formatTotalUnit(total_bytes, totStr, sizeof(totStr));

        char txStr[6], rxStr[6], trafficCombo[12];
        formatShortUnit(sessionApData[i].tx_bytes, txStr, sizeof(txStr));
        formatShortUnit(sessionApData[i].rx_bytes, rxStr, sizeof(rxStr));
        snprintf(trafficCombo, sizeof(trafficCombo), "%s|%s", txStr, rxStr); 
        
        char safeCountry[3] = "--";
        if (sessionApData[i].country[0] != '\0') {
            safeCountry[0] = sessionApData[i].country[0];
            safeCountry[1] = sessionApData[i].country[1];
        }

        snprintf(line1, sizeof(line1), "%3d. %-18.18s %17s %2s %4d %-5.5s", 
                 (i + 1), safeSsid, bssidStr, safeCountry, sessionApData[i].rssi, totStr);

        snprintf(line2, sizeof(line2), "    %13s %3.0fm %02d %3uM %-4.4s %3.0f%%   %9s", 
                 ageCombo, sessionApData[i].smoothedDistance, sessionApData[i].channel, 
                 sessionApData[i].max_rate, avgStr, cv_percent, trafficCombo);

        tft.setFreeFont(&UbuntuMono_B9pt7b);
        tft.drawString(line1, 5, y);
        tft.setTextColor(TFT_LIGHTGREY);
        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.drawString(line2, 5, y + 15);
        tft.setTextColor(TFT_WHITE); 
      }
      else if (currentRadioMode == RADIO_CHANNELS) {
        // ... [CHANNELS MODE LOGIC REMAINS UNCHANGED] ...
        char line1[90];
        char line2[90];

        double mean = 0.0;
        double cv_percent = 0.0;
        if (sessionChannelData[i].packets > 0) {
            mean = (double)sessionChannelData[i].sum_bytes / (double)sessionChannelData[i].packets;
            double avg_sq_sum = (double)sessionChannelData[i].sum_sq_bytes / (double)sessionChannelData[i].packets;
            double variance = avg_sq_sum - (mean * mean);
            if (variance < 0) variance = 0; 
            double std_dev = sqrt(variance);
            if (mean > 0) cv_percent = (std_dev / mean) * 100.0;
        }

        float avg_rssi = sessionChannelData[i].avg_rssi;
        double std_dev_rssi = sqrt(sessionChannelData[i].ema_variance);
        
        float rho = 0.0;
        if (sessionChannelData[i].ema_variance > 0.01) { 
            rho = sessionChannelData[i].ema_cov / sessionChannelData[i].ema_variance;
        }

        char stateStr[10];
        if (sessionChannelData[i].packets < 5) strcpy(stateStr, "CALC.."); 
        else if (rho > 0.6) strcpy(stateStr, "DRIFT");   
        else if (rho > 0.2) strcpy(stateStr, "ACTIVE");  
        else strcpy(stateStr, "STATIC");                 

        char avgStr[6];
        formatShortUnit((uint32_t)mean, avgStr, sizeof(avgStr));

        char firstSeenStr[8], lastSeenStr[8], ageCombo[16];
        getAgeString(sessionChannelData[i].first_seen, firstSeenStr, sizeof(firstSeenStr));
        getAgeString(sessionChannelData[i].last_seen, lastSeenStr, sizeof(lastSeenStr));
        snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr); 

        uint32_t total_bytes = sessionChannelData[i].tx_bytes + sessionChannelData[i].rx_bytes;
        char totStr[10];
        formatTotalUnit(total_bytes, totStr, sizeof(totStr));

        char txStr[6], rxStr[6], trafficCombo[12];
        formatShortUnit(sessionChannelData[i].tx_bytes, txStr, sizeof(txStr)); 
        formatShortUnit(sessionChannelData[i].rx_bytes, rxStr, sizeof(rxStr)); 
        snprintf(trafficCombo, sizeof(trafficCombo), "%s|%s", txStr, rxStr); 

        char pwrStr[16];
        if (sessionChannelData[i].packets == 0) strcpy(pwrStr, "N/A");
        else snprintf(pwrStr, sizeof(pwrStr), "%3.0f|~%-2.0f", avg_rssi, std_dev_rssi);

        snprintf(line1, sizeof(line1), "%3d. CHANNEL %02d %14s %-11.11s   %-5.5s", 
                 (i + 1), sessionChannelData[i].channel, "", pwrStr, totStr);

        snprintf(line2, sizeof(line2), "    %13s %5s %-7.7s %-4.4s %3.0f%%   %9s", 
                 ageCombo, "", stateStr, avgStr, cv_percent, trafficCombo);

        tft.setFreeFont(&UbuntuMono_B9pt7b);
        tft.drawString(line1, 5, y);
        tft.setTextColor(TFT_LIGHTGREY);
        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.drawString(line2, 5, y + 15);
        tft.setTextColor(TFT_WHITE); 
      }
      else if (currentRadioMode == RADIO_LAYER2) {
        // Map our logical loop variable 'i' back to the real array index!
        int real_idx = valid_indices[i];
        auto& lk = leakHistory[real_idx].leak;

        // ==========================================
        // LAYER 2 MODE - DYNAMIC 1 TO 3 LINE RENDERING
        // ==========================================
        char line1[90], line2[90], line3[90];

        char firstSeenStr[8], lastSeenStr[8], ageCombo[18];
        getAgeString(leakHistory[real_idx].first_seen, firstSeenStr, sizeof(firstSeenStr));
        getAgeString(lk.meta.timestamp, lastSeenStr, sizeof(lastSeenStr));
        snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr); 

        char safeSsid[13] = "Unknown";
        for (int ap = 0; ap < MAX_BSSID_CACHE; ap++) {
            if (bssidCache[ap].last_seen == 0) continue; 
            if (memcmp(lk.meta.bssid, bssidCache[ap].bssid, 6) == 0) {
                strncpy(safeSsid, bssidCache[ap].ssid, 12);
                safeSsid[12] = '\0';
                break;
            }
        }
        
        char srcVend[9], dstVend[9];
        strncpy(srcVend, leakHistory[real_idx].src_vendor, 8); srcVend[8] = '\0';
        strncpy(dstVend, leakHistory[real_idx].dst_vendor, 8); dstVend[8] = '\0';
        if(strlen(srcVend) == 0) strcpy(srcVend, "Unknown");
        if(strlen(dstVend) == 0) strcpy(dstVend, "Unknown");
        for (int v = 7; v >= 0; v--) { if (srcVend[v] == ' ') srcVend[v] = '\0'; else break; }
        for (int v = 7; v >= 0; v--) { if (dstVend[v] == ' ') dstVend[v] = '\0'; else break; }

        char lenStr[8];
        uint16_t fLen = lk.meta.frame_length;
        if (fLen < 1000) snprintf(lenStr, sizeof(lenStr), "%dB", fLen);
        else snprintf(lenStr, sizeof(lenStr), "%dK", fLen / 1000);
        
        char srcIpRaw[40] = {0}, dstIpRaw[40] = {0};
getIpString(lk.meta.ip_version, lk.meta.src_ip, srcIpRaw, sizeof(srcIpRaw));
getIpString(lk.meta.ip_version, lk.meta.dst_ip, dstIpRaw, sizeof(dstIpRaw));

char srcIpStr[40] = {0}, dstIpStr[40] = {0};
if (lk.meta.ip_version == 6) {
    compress_ipv6(srcIpRaw, srcIpStr, sizeof(srcIpStr));
    compress_ipv6(dstIpRaw, dstIpStr, sizeof(dstIpStr));
} else {
    strncpy(srcIpStr, srcIpRaw, sizeof(srcIpStr) - 1);
    strncpy(dstIpStr, dstIpRaw, sizeof(dstIpStr) - 1);
}

        snprintf(line1, sizeof(line1), "[x%d]%02X%02X%02X%02X%02X%02X(%s)>%02X%02X%02X%02X%02X%02X(%s)|%s|C%d", 
                 leakHistory[real_idx].hitCount,
                 lk.meta.src_mac[0], lk.meta.src_mac[1], lk.meta.src_mac[2],
                 lk.meta.src_mac[3], lk.meta.src_mac[4], lk.meta.src_mac[5], srcVend,
                 lk.meta.dst_mac[0], lk.meta.dst_mac[1], lk.meta.dst_mac[2],
                 lk.meta.dst_mac[3], lk.meta.dst_mac[4], lk.meta.dst_mac[5], dstVend, lenStr, lk.meta.channel);

        char portStr[24] = "";
        if (lk.meta.protocol == 6 || lk.meta.protocol == 17) {
            snprintf(portStr, sizeof(portStr), "|%d>%d", lk.meta.src_port, lk.meta.dst_port);
        }
        snprintf(line2, sizeof(line2), "%02X%02X%02X%02X%02X%02X(%s)|%s|%s|%s%s", 
                 lk.meta.bssid[0], lk.meta.bssid[1], lk.meta.bssid[2],
                 lk.meta.bssid[3], lk.meta.bssid[4], lk.meta.bssid[5],
                 safeSsid, getDirectionStr(lk.meta.direction), 
                 getSubtypeStr(lk.meta.frame_subtype),
                 getProtocolStr(lk.meta.protocol), portStr);

        snprintf(line3, sizeof(line3), "%s>%s|%s", srcIpStr, dstIpStr, ageCombo);

        // --- SAFE PAYLOAD SLICING (Explicit memcpy & Clamp) ---
        int pLen = lk.retained_len; 
        if (pLen > MAX_LEAK_STR_LEN - 1) {
            pLen = MAX_LEAK_STR_LEN - 1; // Defensive boundary clamp
        }
        
        char safePayload[MAX_LEAK_STR_LEN + 1] = {0};
        size_t copyLen = pLen;
        
        memcpy(safePayload, lk.text, copyLen);
        safePayload[copyLen] = '\0'; // Guarantee NUL termination

        // Fast sanitization loop utilizing clamped pLen
        for (int pt = 0; pt < pLen; pt++) {
            if (safePayload[pt] < 32 || safePayload[pt] > 126) safePayload[pt] = '.';
        }
        
        // --- DYNAMIC PAYLOAD SLICING (Loop-Based up to 9 lines) ---
        const int maxChars = 58;
        const int maxLinesAllowed = 9;
        char pLines[9][60] = {0}; // 2D array to hold up to 9 lines of 59 chars
        int n_lines = 1;

        for (int line = 0; line < maxLinesAllowed; line++) {
            int offset = line * maxChars;
            if (offset >= pLen) {
                if (line == 0) n_lines = 1; // Guarantee at least 1 line is counted
                break;
            }
            
            n_lines = line + 1;
            int remaining = pLen - offset;
            
            if (remaining <= maxChars) {
                strncpy(pLines[line], safePayload + offset, remaining);
            } else {
                // Truncate the final allowed line with +NNN if there's more payload
                if (line == maxLinesAllowed - 1) {
                    const int textChars = 54; // Leaves room for the "+NNN" tag
                    strncpy(pLines[line], safePayload + offset, textChars);
                    snprintf(pLines[line] + textChars, sizeof(pLines[line]) - textChars, "+%d", remaining - textChars);
                } else {
                    strncpy(pLines[line], safePayload + offset, maxChars);
                }
            }
        }

        // --- RENDER DYNAMIC HEIGHT ---
        tft.setFreeFont(&UbuntuMono_Regular8pt7b);
        tft.setTextColor(TFT_CYAN);
        tft.drawString(line1, 5, y);
        tft.setTextColor(TFT_YELLOW);
        tft.drawString(line2, 5, y + 14);
        tft.setTextColor(TFT_ORANGE);
        tft.drawString(line3, 5, y + 28);
        
        tft.setTextColor(TFT_GREEN);
        
        // Dynamically print exactly as many lines as this specific packet needs
        for (int l = 0; l < n_lines; l++) {
            tft.drawString(pLines[l], 5, y + 42 + (l * 14));
        }

        int current_item_h = 42 + (n_lines * 14);
        tft.drawLine(0, y + current_item_h + 2, 480, y + current_item_h + 2, COLOR_HOT_CHEST);
        
        dyn_y += current_item_h + 5; 
        tft.setTextColor(TFT_WHITE);
      }          // closes RADIO_LAYER2 branch
      row++;     // <-- also missing, see note below
    }            // closes the for loop
  }              // closes the total_devices==0 / else block

  // ==========================================
  // 7. SAFE NAVIGATION FOOTER
  // ==========================================
  tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
  tft.drawLine(0, 294, 480, 294, TFT_WHITE); 

  if (device_current_page > 0 && total_devices > 0) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("<- PREV", 20, 300);
  }
  
  tft.setTextColor(TFT_RED);
  tft.drawString("BACK", 215, 300); 

  if (has_next_page) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("NEXT ->", 360, 300);
  }
}

void decodeEddystoneURL(const std::string& sData, char* outBuffer, size_t maxLen) {
    // Ensure we have a valid buffer to write to
    if (maxLen == 0) return;
    outBuffer[0] = '\0'; 

    // Eddystone frame type 0x10 specifically means "URL"
    if (sData.length() < 3 || sData[0] != 0x10) {
        strlcpy(outBuffer, "Eddy: (Not URL)", maxLen);
        return;
    }

    size_t idx = 0;

    // 1. Decode the Prefix Scheme (Byte 2)
    const char* prefix = "";
    switch (sData[2]) {
        case 0x00: prefix = "http://www."; break;
        case 0x01: prefix = "https://www."; break;
        case 0x02: prefix = "http://"; break;
        case 0x03: prefix = "https://"; break;
        default:   prefix = "Unknown URI"; break;
    }

    // Write prefix to buffer safely
    while (*prefix && idx < maxLen - 1) {
        outBuffer[idx++] = *prefix++;
    }

    // 2. Decode the Body and Suffixes (Bytes 3+)
    const char* suffixes[] = {
        ".com/", ".org/", ".edu/", ".net/", ".info/", ".biz/", ".gov/",
        ".com", ".org", ".edu", ".net", ".info", ".biz", ".gov"
    };

    for (size_t i = 3; i < sData.length() && idx < maxLen - 1; i++) {
        uint8_t c = sData[i];
        if (c <= 0x0D) {
            const char* suffix = suffixes[c];
            // Inject the decompressed suffix
            while (*suffix && idx < maxLen - 1) {
                outBuffer[idx++] = *suffix++;
            }
        } else {
            // Standard ASCII text
            outBuffer[idx++] = (char)c;
        }
    }
    
    // Null-terminate the final string
    outBuffer[idx] = '\0';
}

class BLEPassiveCallbacks: public BLEAdvertisedDeviceCallbacks {
  void onResult(BLEAdvertisedDevice* advertisedDevice) {
    if (pause_sniffing) return; 

    const uint8_t* rawMac = advertisedDevice->getAddress().getNative();

    // ==========================================
    // BLE FOXHUNT ISR FEEDER
    // ==========================================
    if (is_foxhunting) {
        if (memcmp(rawMac, foxhunt_target_mac, 6) == 0) {
            updateFoxhuntSignal(advertisedDevice->getRSSI());
        }
    }

    // ==========================================
    // ON-THE-FLY RAW HEX DUMP (Zero SRAM Allocation)
    // ==========================================
    uint8_t* rawPayload = advertisedDevice->getPayload();
    size_t payloadLen = advertisedDevice->getPayloadLength();

    // Print MAC directly from bytes to avoid NimBLE's .toString() std::string allocation
    Serial.printf("RAW [%02d bytes] MAC: %02X:%02X:%02X:%02X:%02X:%02X | ", 
                  payloadLen, rawMac[5], rawMac[4], rawMac[3], rawMac[2], rawMac[1], rawMac[0]);
    
    for (size_t p = 0; p < payloadLen; p++) {
        Serial.printf("%02X ", rawPayload[p]);
    }
    Serial.println();
    
    int rssi = advertisedDevice->getRSSI();
    int txPower = advertisedDevice->haveTXPower() ? advertisedDevice->getTXPower() : 0;
    int sdCount = advertisedDevice->getServiceDataCount();

    // ==========================================
    // DE-STRINGIFIED PARSING VARIABLES
    // ==========================================
    char tempName[25] = {0};
    uint8_t tempPriority = 0;
    
    uint8_t newTrackerType = TRACKER_NONE; 
    uint16_t newAppearanceId = 0;          
    uint16_t newServiceId = 0;

    // ==========================================
    // STEP 1: Name (Priority 4)
    // ==========================================
    if (advertisedDevice->haveName()) {
        strlcpy(tempName, advertisedDevice->getName().c_str(), sizeof(tempName));
        tempPriority = 4;
    } 
    
    // ==========================================
    // STEP 2: Manufacturer Data (Priority 1 & 2)
    // ==========================================
    if (advertisedDevice->haveManufacturerData()) {
        // NimBLE forces a std::string return here, but we immediately extract its data
        std::string mfg = advertisedDevice->getManufacturerData();
        
        if (mfg.length() >= 2) {
            uint16_t companyId = (uint8_t)mfg[1] << 8 | (uint8_t)mfg[0];
            const char* resolvedCompany = resolveBleCompanyId(companyId);
            
            // Identify Tracker Types
            if (companyId == 0x004C && mfg.length() >= 3 && mfg[2] == 0x12) newTrackerType = TRACKER_APPLE_FINDMY;
            else if (companyId == 0x004C && mfg.length() >= 3 && mfg[2] == 0x02) newTrackerType = TRACKER_APPLE_IBEACON;
            else if (companyId == 0x00E0 && mfg.length() >= 3 && mfg[2] == 0xFC) newTrackerType = TRACKER_GOOGLE_FASTPAIR;
            else if (companyId == 0x000D) newTrackerType = TRACKER_TILE;
            else if (companyId == 0x0075 && mfg.length() >= 3 && mfg[2] == 0x42) newTrackerType = TRACKER_SAMSUNG_SMARTTAG;
            else if (companyId == 0x0006 && mfg.length() >= 3 && mfg[2] == 0x09) newTrackerType = TRACKER_MS_SWIFTPAIR;
            
            // Only format manufacturer strings if we don't already have a better name (Priority 3 or 4)
            if (tempPriority < 2) {
                if (newTrackerType != TRACKER_NONE) {
                    if (newTrackerType == TRACKER_APPLE_FINDMY) strlcpy(tempName, "Apple Find My", sizeof(tempName));
                    else if (newTrackerType == TRACKER_APPLE_IBEACON) strlcpy(tempName, "Apple iBeacon", sizeof(tempName));
                    else if (newTrackerType == TRACKER_GOOGLE_FASTPAIR) strlcpy(tempName, "Google FastPair", sizeof(tempName));
                    else if (newTrackerType == TRACKER_SAMSUNG_SMARTTAG) strlcpy(tempName, "Samsung SmartTag", sizeof(tempName));
                    else if (newTrackerType == TRACKER_TILE) strlcpy(tempName, "Tile Tracker", sizeof(tempName));
                    else if (newTrackerType == TRACKER_MS_SWIFTPAIR) strlcpy(tempName, "MS Swift Pair", sizeof(tempName));
                    
                    tempPriority = 2; // Priority 2: Known Tracker Type
                } 
                else if (resolvedCompany != nullptr && tempPriority < 1) {
                    if (mfg.length() >= 3) {
                        snprintf(tempName, sizeof(tempName), "%.12s:0x%02X", resolvedCompany, (uint8_t)mfg[2]);
                    } else {
                        snprintf(tempName, sizeof(tempName), "%.24s", resolvedCompany);
                    }
                    tempPriority = 1; // Priority 1: Manufacturer Fallback
                }
            }
        }
    }

    // ==========================================
    // STEP 3: Corporate Trackers & Eddystone (0x16)
    // ==========================================
    for (int k = 0; k < sdCount; k++) {
        NimBLEUUID sdUUID = advertisedDevice->getServiceDataUUID(k);
        
        if (sdUUID.bitSize() == 16) {
            uint16_t uuid16 = sdUUID.getNative()->u16.value;
            
            if (uuid16 == 0xFEAA) {
                newTrackerType = TRACKER_EDDYSTONE;
                
                // Only decode the URL if we don't have a real Broadcast Name (Priority 4)
                if (tempPriority < 4) {
                    decodeEddystoneURL(advertisedDevice->getServiceData(k), tempName, sizeof(tempName));
                    tempPriority = 3; // Priority 3: Eddystone URL
                }
                break; 
            }

            if (newServiceId == 0) {
                newServiceId = uuid16; 
            }
        } 
    }

    // ==========================================
    // STEP 4: Appearance (0x19) & Standard Services
    // ==========================================
    if (advertisedDevice->haveAppearance()) {
        newAppearanceId = advertisedDevice->getAppearance();
    } 

    if (advertisedDevice->haveServiceUUID()) {
        NimBLEUUID sUUID = advertisedDevice->getServiceUUID();
        if (sUUID.bitSize() == 16 && newServiceId == 0) {
            newServiceId = sUUID.getNative()->u16.value;
        }
    }

    // ==========================================
    // ARRAY MATCHING & STRUCT UPDATES (The Gatekeeper)
    // ==========================================
    bool found = false;
    
    for (int i = 0; i < liveBleCount; i++) {
        if (memcmp((void*)(uint8_t*)liveBleData[i].mac, rawMac, 6) == 0) {
            liveBleData[i].hits++;
            liveBleData[i].lastSeen = millis();
            liveBleData[i].rssi = rssi;
            liveBleData[i].txPower = txPower; 

            // THE GATEKEEPER: Only overwrite the name if the new string has higher priority,
            // or if it's an equal priority update (e.g., an Eddystone URL changing)
            if (tempPriority > liveBleData[i].namePriority || 
               (tempPriority == liveBleData[i].namePriority && tempPriority > 0)) {
                
                strlcpy((char*)liveBleData[i].name, tempName, sizeof(liveBleData[i].name));
                liveBleData[i].namePriority = tempPriority;
            }
            
            if (newTrackerType != TRACKER_NONE) liveBleData[i].trackerType = newTrackerType;
            if (newAppearanceId != 0) liveBleData[i].appearanceId = newAppearanceId;
            if (newServiceId != 0) liveBleData[i].serviceId = newServiceId;

            found = true;
            break;
        }
    }

    if (!found && liveBleCount < MAX_BLE_DEVICES) {
        memcpy((void*)(uint8_t*)liveBleData[liveBleCount].mac, rawMac, 6);

        // First time seeing it, write whatever we have and establish the baseline priority
        strlcpy((char*)liveBleData[liveBleCount].name, tempName, sizeof(liveBleData[liveBleCount].name));
        liveBleData[liveBleCount].namePriority = tempPriority;

        liveBleData[liveBleCount].trackerType = newTrackerType;
        liveBleData[liveBleCount].appearanceId = newAppearanceId;
        liveBleData[liveBleCount].serviceId = newServiceId;

        liveBleData[liveBleCount].rssi = rssi;
        liveBleData[liveBleCount].hits = 1;
        liveBleData[liveBleCount].txPower = txPower; 
        
        liveBleData[liveBleCount].firstSeen = millis();
        liveBleData[liveBleCount].lastSeen = millis();

        liveBleCount++;
    }
  }
};

// ADD THIS FLAG RIGHT ABOVE THE switchRadioMode FUNCTION
bool ble_initialized = false;

void switchRadioMode(RadioMode targetMode) {
  if (currentRadioMode == targetMode) return;

  // 1. Close the software gate IMMEDIATELY
  pause_sniffing = true; 
  delay(10); // Give the interrupt callback 10ms to finish parsing

  // 2. WIPE ARRAYS (Manual wipe ensures the software gate stays closed!)
  memset((void*)sessionData, 0, sizeof(sessionData));
  memset((void*)sortData, 0, sizeof(sortData));
  memset((void*)liveData, 0, sizeof(liveData));
  
  sessionMacCount = 0; sortMacCount = 0; liveMacCount = 0;
  sessionOtherBytes = 0; liveOtherBytes = 0;
  sessionBleCount = 0; sortBleCount = 0; liveBleCount = 0;
  sessionApCount = 0; sortApCount = 0; liveApCount = 0;
  sessionChannelCount = 0; sortChannelCount = 0; liveChannelCount = 0;

  // 3. HARDWARE ANTENNA TOGGLE
  if (targetMode == RADIO_WIFI || targetMode == RADIO_AP || targetMode == RADIO_CHANNELS) {
    // Put BLE to sleep so Wi-Fi gets 100% of the antenna
    if (pBLEScan != nullptr) {
      pBLEScan->stop();
      pBLEScan->clearResults();
    }
    // Wake up Wi-Fi
    WiFi.mode(WIFI_STA);
    WiFi.disconnect(); 
    esp_wifi_set_promiscuous(true);

    // THE MISSING LINK: Reattach the interrupt!
    esp_wifi_set_promiscuous_rx_cb(&sniffer_callback); 
    
  } else if (targetMode == RADIO_BLE) {
    // Violently kill Wi-Fi to free the antenna lock
    esp_wifi_set_promiscuous(false);
    WiFi.mode(WIFI_OFF); 

    // Cold Boot BLE the very first time
    if (!ble_initialized) {
      BLEDevice::init("");
      pBLEScan = BLEDevice::getScan();
      pBLEScan->setAdvertisedDeviceCallbacks(new BLEPassiveCallbacks(), true);
      pBLEScan->setActiveScan(false); 
      pBLEScan->setInterval(100);     
      pBLEScan->setWindow(99);        
      ble_initialized = true;
    }
    pBLEScan->clearResults();
    pBLEScan->start(0, nullptr, false);
  }

  currentRadioMode = targetMode;
  
  // 4. Open the gate!
  pause_sniffing = false; 
}

// Helper to find or allocate an SSID string in the shared pool
int addSsidToPool(const char* ssid, int head_idx, bool &already_exists, bool &added, uint8_t current_count) {
  already_exists = false;
  added = false;
  //---
  // Drop Wildcard / Hidden SSIDs if they somehow slipped through the initial filter in sniffer_callback()
  if (ssid == nullptr || strlen(ssid) == 0) {
    return head_idx; // Bail out immediately without claiming memory
  }
  //---
  int current = head_idx;
  int last = -1;

  // 1. Traverse the existing chain to check for duplicates
  while (current != -1) {
    if (strcmp(ssidPool[current].text, ssid) == 0) {
      already_exists = true;
      return head_idx;
    }
    last = current;
    current = ssidPool[current].next_node_idx;
  }

  // 2. Enforce the emergency cutoff per device
  if (current_count >= EMERGENCY_CUTOFF) {
    return head_idx; 
  }

  // 3. Find the first available slot in the global pool (Garbage Collection!)
  int new_idx = -1;
  for (int i = 0; i < TOTAL_SSID_POOL; i++) {
    if (ssidPool[i].text[0] == '\0') {
      new_idx = i;
      break;
    }
  }

  // If the pool is completely full and no slots are free, just bail out
  if (new_idx == -1) return head_idx; 

  // 4. Claim the slot
  strncpy(ssidPool[new_idx].text, ssid, 32);
  ssidPool[new_idx].text[32] = '\0'; // Ensure safe termination
  ssidPool[new_idx].next_node_idx = -1;
  added = true;

  // 5. Link it into the device's chain
  if (last == -1) {
    return new_idx; // This is the very first SSID for this device
  } else {
    ssidPool[last].next_node_idx = new_idx; // Append to the end of the chain
    return head_idx;
  }
}

void processProbeRequestShared(uint8_t* mac, const char* ssid, const char* known_vendor, int8_t rssi, uint32_t hw_hash) {
  int target_slot = -1;
  unsigned long oldest_time = 0xFFFFFFFF;
  int oldest_slot = 0;

  for (int i = 0; i < MAX_PROBE_SLOTS; i++) {
    if (memcmp(probeList[i].mac, mac, 6) == 0) {
      target_slot = i;
      break;
    }
    if (probeList[i].last_seen < oldest_time) {
      oldest_time = probeList[i].last_seen;
      oldest_slot = i;
    }
  }

  // Handle eviction/overwrite if it's a completely new device
  if (target_slot == -1) {
    target_slot = oldest_slot;

    // ==========================================
    // THE GARBAGE COLLECTOR (With Circuit Breaker)
    // ==========================================
    int current_node = probeList[target_slot].first_ssid_idx;
    int fail_safe = 0; 
    
    while (current_node != -1 && fail_safe < TOTAL_SSID_POOL) {
      int next = ssidPool[current_node].next_node_idx;
      ssidPool[current_node].text[0] = '\0'; 
      ssidPool[current_node].next_node_idx = -1; 
      current_node = next;
      fail_safe++;
    }
    // ==========================================

    // Safely claiming the slot:
    memcpy(probeList[target_slot].mac, mac, 6);
    probeList[target_slot].hits = 0;
    probeList[target_slot].ssid_count = 0;
    probeList[target_slot].first_ssid_idx = -1;
    probeList[target_slot].first_seen = millis();
    
    // --- CRITICAL MEMORY WIPE ---
    probeList[target_slot].pnl_hash = 0; 
    probeList[target_slot].mac_rotations = 1;
    // ----------------------------

    // CRITICAL: Increment generation to invalidate any in-flight SD lookups for this slot (ABA fix)
    probeList[target_slot].generation++; 
    
    // ==========================================
    // DEFER TO CORE 1 OR USE KNOWN VENDOR
    // ==========================================
    if (strlen(known_vendor) > 0) {
      // We already know who this is from Tag 221! Lock out Core 1.
      strncpy(probeList[target_slot].vendor, known_vendor, sizeof(probeList[target_slot].vendor) - 1);
      probeList[target_slot].needs_lookup = false; 
    } else {
      // We have no idea who this is. Tell Core 1 to check the SD Card.
      strncpy(probeList[target_slot].vendor, "Resolving...", sizeof(probeList[target_slot].vendor));
      probeList[target_slot].needs_lookup = true; 
    }
    // ==========================================
  }

  // 1. Standard Updates
  // In processProbeRequestShared:
  if (probeList[target_slot].hits < 65535) {
      probeList[target_slot].hits++;
  }
  probeList[target_slot].last_seen = millis();
  probeList[target_slot].rssi = rssi;
  
  // --- NEW: INJECT THE HARDWARE HASH HERE ---
  probeList[target_slot].hardware_hash = hw_hash;
  // ------------------------------------------

  // 2. EMA Physics Engine
  float rawDistance = calculateRfDistance(rssi, 0, RADIO_WIFI_24GHZ);
  if (rawDistance > 0) {
      if (probeList[target_slot].hits == 1) {
          probeList[target_slot].smoothedDistance = rawDistance; // First hit is absolute
      } else {
          probeList[target_slot].smoothedDistance = (0.2 * rawDistance) + (0.8 * probeList[target_slot].smoothedDistance);
      }
  }

  bool already_exists = false;
  bool added = false;
  
  int new_head = addSsidToPool(ssid, probeList[target_slot].first_ssid_idx, already_exists, added, probeList[target_slot].ssid_count);
  
  probeList[target_slot].first_ssid_idx = new_head;
  
  if (added) {
    probeList[target_slot].ssid_count++;
  }
  
  // 3. Update the Bloom Filter
  if (strcmp(ssid, "<Wld>") != 0 && strcmp(ssid, "<Nul>") != 0) {
      uint8_t bit_idx = getSsidBitIndex(ssid);
      probeList[target_slot].pnl_hash |= (1ULL << bit_idx);
  }
}

// --- Background Vendor Resolver (Runs safely on Core 1) ---
void processPendingVendors() {
  // ==========================================
  // 1. OSINT Probe Tracker Resolution Logic
  // ==========================================
  for (int i = 0; i < MAX_PROBE_SLOTS; i++) {
    if (probeList[i].needs_lookup) {
      MacRecord dummy;
      
      // A. Lock briefly to copy the MAC and the generation ticket
      pause_sniffing = true;
      memcpy(dummy.mac, probeList[i].mac, 6);
      uint32_t current_generation = probeList[i].generation; 
      pause_sniffing = false; // Unlock immediately! Let the radio sniff.
      
      dummy.vendorFound = false;
      resolveMacVendor(&dummy); // Slow SD Card read happens safely here
      
      // B. Lock again to write the result
      pause_sniffing = true;
      
      // CRITICAL: Did Core 0 evict this slot while we were reading?
      if (probeList[i].generation == current_generation) {
        // The generation matches! Safe to write.
        strlcpy(probeList[i].vendor, dummy.vendor, sizeof(probeList[i].vendor));
        probeList[i].needs_lookup = false; 
      }
      
      pause_sniffing = false; // Unlock
      break; // Only process one SD read per loop to prevent UI blocking
    }
  }

  // ==========================================
  // 2. Main Wi-Fi Device List Resolution
  // ==========================================
  if (currentRadioMode == RADIO_WIFI) {
    for (int i = 0; i < sessionMacCount; i++) {
      if (sessionData[i].needs_lookup) {
        MacRecord dummy;

        // A. Lock briefly to copy the MAC
        pause_sniffing = true;
        memcpy(dummy.mac, sessionData[i].mac, 6);
        pause_sniffing = false; 
        
        dummy.vendorFound = false;
        resolveMacVendor(&dummy); // Safe background lookup
        
        // B. Lock again to write the result
        pause_sniffing = true;
        
        // We use memcmp here since sessionData doesn't seem to have a generation counter yet
        if (memcmp(sessionData[i].mac, dummy.mac, 6) == 0) {
            strlcpy(sessionData[i].vendor, dummy.vendor, sizeof(sessionData[i].vendor));
            sessionData[i].needs_lookup = false; 
        }

        pause_sniffing = false;
        break; // Only process one SD read per loop
      }
    }
  }
}

void drawProbeTracker() {
  tft.fillScreen(TFT_BLACK);
  tft.setTextSize(1);

  // ==========================================
  // 1. DYNAMIC HEADER BANNER (Unified UI)
  // ==========================================
  sortProbeList();

  int active_probes = 0;
  for (int i = 0; i < MAX_PROBE_SLOTS; i++) {
    for (int b = 0; b < 6; b++) {
      if (probeList[i].mac[b] != 0) {
        active_probes++;
        break; 
      }
    }
  }
  total_sniffed_probes = active_probes;

  tft.setFreeFont(&UbuntuMono_B9pt7b);
  tft.setTextDatum(TL_DATUM);
  tft.setTextColor(TFT_WHITE);
  uint16_t osintHeaderColor = hex24to565(0x4A148C); 
  tft.fillRect(0, 0, 480, 24, osintHeaderColor);
  
  char headerStr[64];
  snprintf(headerStr, sizeof(headerStr), "PHYSICAL TARGETS (%d)", active_probes);
  tft.drawString(headerStr, 0, 5); 

  // --- INJECT SORT UI BUTTONS ---
  char metricStr[32];
  uint16_t metricColor = TFT_YELLOW;

  if (currentProbeSortMode == PROBE_SORT_HITS) strcpy(metricStr, "SORT:HITS");
  else if (currentProbeSortMode == PROBE_SORT_DIST) strcpy(metricStr, "SORT:DIST");
  else if (currentProbeSortMode == PROBE_SORT_SSIDS) strcpy(metricStr, "SORT:#SSIDs");
  else if (currentProbeSortMode == PROBE_SORT_AGE) strcpy(metricStr, "SORT:AGE");

  tft.fillRoundRect(275, 2, 130, 20, 3, TFT_BLACK); 
  tft.drawRoundRect(275, 2, 130, 20, 3, TFT_WHITE);
  tft.setTextColor(metricColor);
  tft.drawString(metricStr, 282, 4);

  tft.fillRoundRect(410, 2, 65, 20, 3, TFT_BLACK); 
  tft.drawRoundRect(410, 2, 65, 20, 3, TFT_WHITE);
  
  if (probe_sort_descending) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("DESC", 423, 4);
  } else {
    tft.setTextColor(TFT_GREEN);
    tft.drawString("ASC", 427, 4);
  }
  
  // ==========================================
  // 2. DUAL-LINE COLUMN HEADERS
  // ==========================================
  tft.setTextColor(TFT_GREEN);
  tft.setFreeFont(&UbuntuMono_B9pt7b);
  // --- UPDATED: Realigned spacing and injected #MAC column ---
  tft.drawString("ID VENDOR        FIRST|LAST   RSSI DIST #MAC HITS", 0, 26); 
  tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
  tft.drawString("MAC ADDRESS       CAPTURED SSIDs", 0, 41); 
  tft.drawLine(0, 57, 480, 57, TFT_WHITE); 

  // ==========================================
  // 3. DATA ROWS (3-Line Data Injection)
  // ==========================================
  int start_idx = probe_current_page * PROBES_PER_PAGE;
  int end_idx = start_idx + PROBES_PER_PAGE;

  int row = 0;
  for (int i = start_idx; i < end_idx; i++) {
    bool is_slot_empty = true;
    for (int b = 0; b < 6; b++) {
      if (probeList[i].mac[b] != 0) {
        is_slot_empty = false;
        break;
      }
    }

    int y = 60 + (row * 46); 

    if (!is_slot_empty) {
      
      // --- LINE 1: Metadata ---
      if (probeList[i].mac_rotations > 1) {
          tft.setTextColor(TFT_ORANGE); 
      } else {
          tft.setTextColor(TFT_GREEN);  
      }

      bool is_randomized = (probeList[i].mac[0] & 0x02) != 0;
      char safeVendor[20];
      char rawVendor[20];
      
      if (strcmp(probeList[i].vendor, "Resolving...") == 0) {
          strcpy(rawVendor, "Resolving...");
      } else if (strstr(probeList[i].vendor, "(IE)") != nullptr) {
          strncpy(rawVendor, probeList[i].vendor, 19);
          rawVendor[19] = '\0';
      } else if (is_randomized) {
          strcpy(rawVendor, "<Randomized>");
      } else if (probeList[i].vendor[2] == ':' || strcmp(probeList[i].vendor, "Unknown") == 0 || strlen(probeList[i].vendor) == 0) {
          strcpy(rawVendor, "Unknown Device");
      } else {
          strncpy(rawVendor, probeList[i].vendor, 19);
          rawVendor[19] = '\0';
      }

      // Reduced from 15 to 13 to make room for the new #MAC column
      snprintf(safeVendor, sizeof(safeVendor), "%-13.13s", rawVendor);

      char ageCombo[16];
      char firstSeenStr[8], lastSeenStr[8];
      getAgeString(probeList[i].first_seen, firstSeenStr, sizeof(firstSeenStr));
      getAgeString(probeList[i].last_seen, lastSeenStr, sizeof(lastSeenStr));
      snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr);

      char metaStr[80];
      // --- UPDATED: Injected mac_rotations into the Line 1 format string ---
      snprintf(metaStr, sizeof(metaStr), "%02d.%-13.13s %13s %4d %4.0fm %4d %4u",
               i + 1, safeVendor, ageCombo, probeList[i].rssi, probeList[i].smoothedDistance, probeList[i].mac_rotations, probeList[i].hits);
               
      tft.setFreeFont(&UbuntuMono_B9pt7b);
      tft.drawString(metaStr, 0, y); 

      // --- LINES 2 & 3: MAC Address & Smart SSID Word Wrapper ---
      tft.setFreeFont(&UbuntuMono_Regular8pt7b); 
      
      // Keep MAC Orange if it's a rotated device to act as a visual anchor
      if (probeList[i].mac_rotations > 1) {
          tft.setTextColor(TFT_ORANGE);
      } else {
          tft.setTextColor(TFT_WHITE);
      }
      
      // --- UPDATED: Flush left MAC address string ---
      char macStr[20];
      snprintf(macStr, sizeof(macStr), "%02X:%02X:%02X:%02X:%02X:%02X", 
               probeList[i].mac[0], probeList[i].mac[1], probeList[i].mac[2],
               probeList[i].mac[3], probeList[i].mac[4], probeList[i].mac[5]);
      tft.drawString(macStr, 0, y + 16); 

      tft.setTextColor(TFT_WHITE);
      char line1[80] = ""; 
      char line2[100] = ""; 
      
      int true_total_ssids = 0;
      int temp_node = probeList[i].first_ssid_idx;
      while (temp_node != -1) {
          if (strlen(ssidPool[temp_node].text) > 0) {
              true_total_ssids++;
          }
          temp_node = ssidPool[temp_node].next_node_idx;
      }

      int current_node = probeList[i].first_ssid_idx;
      int ssids_drawn = 0;
      bool on_line2 = false;

      while (current_node != -1) {
        char next_str[36];
        snprintf(next_str, sizeof(next_str), "%s", ssidPool[current_node].text);
        
        if (strlen(next_str) == 0) {
            current_node = ssidPool[current_node].next_node_idx;
            continue; 
        }
        
        char addition[40];
        if (ssids_drawn == 0) snprintf(addition, sizeof(addition), "%s", next_str); 
        else snprintf(addition, sizeof(addition), "|%s", next_str);

        // --- UPDATED: Expanded Line 1 limit to 41 chars ---
        if (!on_line2) {
            if (strlen(line1) + strlen(addition) <= 41) { 
                strlcat(line1, addition, sizeof(line1));
                ssids_drawn++;
            } else {
                on_line2 = true; 
            }
        }

        if (on_line2) {
            if (strlen(line2) == 0) snprintf(addition, sizeof(addition), "%s", next_str);
            else snprintf(addition, sizeof(addition), "|%s", next_str);

            if (strlen(line2) + strlen(addition) <= 58) { 
                strlcat(line2, addition, sizeof(line2));
                ssids_drawn++;
            } else {
                break; 
            }
        }
        current_node = ssidPool[current_node].next_node_idx;
      }

      if (ssids_drawn == 0) {
        strlcat(line1, "<no SSIDs captured>", sizeof(line1));
      } else if (ssids_drawn < true_total_ssids) {
        char plusStr[8];
        snprintf(plusStr, sizeof(plusStr), "|+%d", (true_total_ssids - ssids_drawn));
        
        // --- UPDATED: Increased Line 1 safety check to 36 for the +X tag ---
        if (on_line2 || strlen(line1) > 36) { 
            strlcat(line2, plusStr, sizeof(line2));
        } else {
            strlcat(line1, plusStr, sizeof(line1));
        }
      }

      // --- UPDATED: Moved starting coordinate from 165 to 145 ---
      tft.drawString(line1, 145, y + 16);
      
      if (strlen(line2) > 0) {
        tft.drawString(line2, 0, y + 30); 
      }
      tft.drawLine(0, y + 45, 480, y + 45, hex24to565(0x222222));
    }
    row++;
  }

  // ==========================================
  // 4. UNIFIED NAVIGATION FOOTER
  // ==========================================
  tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
  tft.drawLine(0, 294, 480, 294, TFT_WHITE); 

  if (probe_current_page > 0 && total_sniffed_probes > 0) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("<- PREV", 20, 300);
  }
  
  tft.setTextColor(TFT_RED);
  tft.drawString("BACK", 215, 300); 

  if (((probe_current_page + 1) * PROBES_PER_PAGE) < total_sniffed_probes) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("NEXT ->", 360, 300);
  }
}

void initProbeTracker() {
  // 1. Initialize all device slots
  for (int i = 0; i < MAX_PROBE_SLOTS; i++) {
    memset(probeList[i].mac, 0, 6);
    probeList[i].hits = 0;
    probeList[i].first_seen = 0;
    probeList[i].last_seen = 0;
    probeList[i].ssid_count = 0;
    probeList[i].first_ssid_idx = -1; 
    probeList[i].generation = 0;
    probeList[i].needs_lookup = false;
    probeList[i].rssi = -100;           
    probeList[i].smoothedDistance = 0.0; 
    
    // --- INITIALIZE FINGERPRINTING & GROUP DATA ---
    probeList[i].pnl_hash = 0;
    probeList[i].hardware_hash = 0;
    probeList[i].mac_rotations = 1;
    // ---------------------------------------------------

    strncpy(probeList[i].vendor, "Unknown", 25);
  }

  // 2. Initialize the global SSID memory pool
  for (int i = 0; i < TOTAL_SSID_POOL; i++) {
    ssidPool[i].text[0] = '\0';
    ssidPool[i].next_node_idx = -1;
  }
}

void drawFoxhuntScreen() {
    last_displayed_rssi = -999; // Force redraw on every full screen draw
    last_drawn_min = 0;         // NEW: Force bounds redraw 
    last_drawn_max = 0;         // NEW: Force bounds redraw
    tft.fillScreen(TFT_BLACK);
    
    // ==========================================
    // ZONE MAP (non-overlapping):
    // Y=0-30:    Header (static)
    // Y=35-55:   MAC address (static)
    // Y=58-75:   Vendor (static, truncated)
    // Y=80-100:  "SIGNAL:" label (static)
    // Y=100-130: RSSI value (DYNAMIC — owned by loop() updater)
    // Y=130-195: Spatial dashboard (DYNAMIC — owned by loop() updater)
    // Y=220-275: Alert banner (DYNAMIC — owned by loop() updater)
    // Y=285-320: Footer (static)
    // ==========================================
    
    // 1. HEADER (static)
    tft.fillRect(0, 0, 480, 30, 
                 (currentRadioMode == RADIO_BLE) ? TFT_PURPLE : TFT_RED);
    tft.setTextColor(TFT_WHITE);
    tft.setTextDatum(MC_DATUM);
    tft.setFreeFont(&UbuntuMono_Regular11pt7b);
    const char* huntLabel = "WIFI FOXHUNT";
    if (currentRadioMode == RADIO_BLE) huntLabel = "BLE FOXHUNT";
    else if (currentRadioMode == RADIO_AP) huntLabel = "AP FOXHUNT";
    tft.drawString(huntLabel, 240, 15);

    // 2. TARGET MAC (static)
    tft.setFreeFont(&UbuntuMono_Regular9pt7b);
    tft.setTextColor(TFT_CYAN);
    char targetStr[64];
    snprintf(targetStr, sizeof(targetStr), 
             "TARGET: %02X:%02X:%02X:%02X:%02X:%02X",
             foxhunt_target_mac[0], foxhunt_target_mac[1],
             foxhunt_target_mac[2], foxhunt_target_mac[3],
             foxhunt_target_mac[4], foxhunt_target_mac[5]);
    tft.drawString(targetStr, 240, 40);

    // 3. VENDOR (static, truncated to prevent width overflow)
    tft.setTextColor(TFT_LIGHTGREY);
    char safeVendor[21];
    strncpy(safeVendor, foxhunt_target_vendor, 20);
    safeVendor[20] = '\0';
    tft.drawString(safeVendor, 240, 58); // Nudged up slightly for perfect spacing

    // 4. TARGET CHANNEL (Replaces the phantom "SIGNAL" label)
    if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
        tft.setTextColor(TFT_ORANGE); 
        char chStr[16];
        snprintf(chStr, sizeof(chStr), "CH: %02d", target_channel);
        tft.drawString(chStr, 240, 76);
    }

    // 6. FOOTER (static)
    tft.drawLine(0, 285, 480, 285, TFT_WHITE);
    tft.drawRoundRect(190, 292, 100, 24, 3, TFT_RED);
    tft.setTextColor(TFT_WHITE);
    tft.setFreeFont(&UbuntuMono_Regular9pt7b);
    tft.setTextDatum(MC_DATUM);
    tft.drawString("ABORT", 240, 304);
    tft.setTextDatum(TL_DATUM); // Reset datum
}

double getChannelMetric(ChannelRecord r, SortMode mode) {
  if (mode == SORT_TOTAL) return (double)(r.tx_bytes + r.rx_bytes);
  if (mode == SORT_TX) return (double)r.tx_bytes; // Downlink
  if (mode == SORT_RX) return (double)r.rx_bytes; // Uplink
  if (mode == SORT_AVG) return (r.packets > 0) ? (double)(r.sum_bytes / r.packets) : 0;
  if (mode == SORT_CV) {
    if (r.packets == 0) return 0;
    double mean = (double)r.sum_bytes / r.packets;
    double variance = ((double)r.sum_sq_bytes / r.packets) - (mean * mean);
    if (variance <= 0 || mean == 0) return 0;
    return (sqrt(variance) / mean) * 100.0;
  }
  // Repurposing SORT_DIST to sort by Power (Avg RSSI)
  if (mode == SORT_DIST) return (double)r.avg_rssi; 
  
  return (double)(r.tx_bytes + r.rx_bytes); // Failsafe fallback
}

void forceSessionSort() {
  if (currentRadioMode == RADIO_WIFI) {
    for (int i = 1; i < sessionMacCount; i++) {
      MacRecord key = sessionData[i];
      double key_val = getSortMetric(key, currentSortMode);
      int j = i - 1;
      if (sort_descending) {
        while (j >= 0 && getSortMetric(sessionData[j], currentSortMode) < key_val) {
          sessionData[j + 1] = sessionData[j];
          j = j - 1;
        }
      } else {
        while (j >= 0 && getSortMetric(sessionData[j], currentSortMode) > key_val && key_val > 0.0) {
          sessionData[j + 1] = sessionData[j];
          j = j - 1;
        }
      }
      sessionData[j + 1] = key;
    }
  } 
  else if (currentRadioMode == RADIO_BLE) {
    for (int i = 1; i < sessionBleCount; i++) {
      BLERecord key = sessionBleData[i];
      double key_val = getBleSortMetric(key, currentBleSortMode);
      int j = i - 1;
      if (sort_descending) {
        while (j >= 0 && getBleSortMetric(sessionBleData[j], currentBleSortMode) < key_val) {
          sessionBleData[j + 1] = sessionBleData[j];
          j = j - 1;
        }
      } else {
        while (j >= 0 && getBleSortMetric(sessionBleData[j], currentBleSortMode) > key_val && key.hits > 0) {
          sessionBleData[j + 1] = sessionBleData[j];
          j = j - 1;
        }
      }
      sessionBleData[j + 1] = key;
    }
  } 
  else if (currentRadioMode == RADIO_AP) {
    for (int i = 1; i < sessionApCount; i++) {
      ApRecord key = sessionApData[i];
      double key_val = getSortMetric(key, currentSortMode);
      int j = i - 1;
      if (sort_descending) {
        while (j >= 0 && getSortMetric(sessionApData[j], currentSortMode) < key_val) {
          sessionApData[j + 1] = sessionApData[j];
          j = j - 1;
        }
      } else {
        while (j >= 0 && getSortMetric(sessionApData[j], currentSortMode) > key_val && key_val > 0.0) {
          sessionApData[j + 1] = sessionApData[j];
          j = j - 1;
        }
      }
      sessionApData[j + 1] = key;
    }
  }
  else if (currentRadioMode == RADIO_CHANNELS) {
    for (int i = 1; i < sessionChannelCount; i++) {
      ChannelRecord key = sessionChannelData[i];
      double key_val = getChannelMetric(key, currentSortMode);
      int j = i - 1;
      if (sort_descending) {
        while (j >= 0 && getChannelMetric(sessionChannelData[j], currentSortMode) < key_val) {
          sessionChannelData[j + 1] = sessionChannelData[j];
          j = j - 1;
        }
      } else {
        // Prevent sorting zero-data to the top in ascending mode
        while (j >= 0 && getChannelMetric(sessionChannelData[j], currentSortMode) > key_val && key_val > 0.0) {
          sessionChannelData[j + 1] = sessionChannelData[j];
          j = j - 1;
        }
      }
      sessionChannelData[j + 1] = key;
    }
  }
}

void drawPersistentTopN() {
    tft.setFreeFont(&UbuntuMono_B9pt7b);
    tft.setTextDatum(TL_DATUM);

    int top_count = 0;
    if (currentRadioMode == RADIO_WIFI) top_count = sessionMacCount;
    else if (currentRadioMode == RADIO_BLE) top_count = sessionBleCount;
    else if (currentRadioMode == RADIO_AP) top_count = sessionApCount;
    else if (currentRadioMode == RADIO_CHANNELS) top_count = sessionChannelCount;

    if (top_count > 10) top_count = 10;

    // 1. Static state trackers for delta-drawing (REMOVED HEAP-FRAG STRINGS)
    static char lastLabels[10][32] = {0}; 
    static int lastTopCount = 0;
    static uint8_t lastRadioMode = 255; // 255 forces an initial redraw on boot

    // 2. Force a full block wipe ONLY when changing radio modes
    bool forceRedraw = (currentRadioMode != lastRadioMode) || force_ui_refresh;
    if (forceRedraw) {
        tft.fillRect(0, 18, 480, HEADER_HEIGHT - 27, TFT_BLACK);
        for(int i = 0; i < 10; i++) {
            lastLabels[i][0] = '\0'; // Clear the cache array
        }
        lastRadioMode = currentRadioMode;
        force_ui_refresh = false; // Consume the flag so it only runs once
    }

    for (int i = 0; i < top_count; i++) {
        // Grid Math
        int col = i % 2;           
        int row = i / 2;           
        
        int x_pos = 5 + (col * 240);       
        int y_pos = 18 + (row * 16);  

        char display_name[28] = "Unknown"; // Buffer for the raw text

        if (currentRadioMode == RADIO_WIFI) {
            strncpy(display_name, sessionData[i].vendor, 26);
            display_name[26] = '\0';
        } 
        else if (currentRadioMode == RADIO_BLE) {
            if (strlen((char*)sessionBleData[i].name) > 0) {
                strncpy(display_name, (char*)sessionBleData[i].name, 26);
                display_name[26] = '\0';
            } else {
                snprintf(display_name, sizeof(display_name), "%02X:%02X:%02X:%02X:%02X:%02X", 
                         sessionBleData[i].mac[0], sessionBleData[i].mac[1], sessionBleData[i].mac[2], 
                         sessionBleData[i].mac[3], sessionBleData[i].mac[4], sessionBleData[i].mac[5]);
            }
        }
        else if (currentRadioMode == RADIO_AP) {
            // Uses sessionApData, display_name, and wider truncation bounds
            if (strcmp(sessionApData[i].ssid, "<HIDDEN>") == 0 || strcmp(sessionApData[i].ssid, "<UNKNOWN>") == 0) {
                snprintf(display_name, sizeof(display_name), "%s", sessionApData[i].ssid);
            } else if (sessionApData[i].has_clone) {
                char temp_ssid[22]; 
                strncpy(temp_ssid, sessionApData[i].ssid, 21); // 21 chars max for list
                temp_ssid[21] = '\0';
                snprintf(display_name, sizeof(display_name), "%s~%02X%02X", 
                         temp_ssid, sessionApData[i].bssid[4], sessionApData[i].bssid[5]);
            } else {
                strncpy(display_name, sessionApData[i].ssid, 26); // 26 chars max for list
                display_name[26] = '\0';
            }
        }
        else if (currentRadioMode == RADIO_CHANNELS) {
            float rho = 0.0;
            if (sessionChannelData[i].ema_variance > 0.01) {
                rho = sessionChannelData[i].ema_cov / sessionChannelData[i].ema_variance;
            }
            const char* stateStr = "STATIC";
            if (sessionChannelData[i].packets < 5) stateStr = "CALC...";
            else if (rho > 0.6) stateStr = "DRIFT";
            else if (rho > 0.2) stateStr = "ACTIVE";

            snprintf(display_name, sizeof(display_name), "CH:%02d [%s]", sessionChannelData[i].channel, stateStr);
        }

        // Final assembly of index + display name
        char label[32];
        snprintf(label, sizeof(label), "%d.%s", i + 1, display_name);

        // 3. Delta Check: Only draw if the string changed or a mode swap forced it
        if (forceRedraw || strcmp(label, lastLabels[i]) != 0) {
            if (!forceRedraw) {
                // Wipe just this specific 235x16 cell to prevent trailing characters 
                // from a previous, longer string ghosting on the screen.
                tft.fillRect(x_pos, y_pos, 235, 16, TFT_BLACK);
            }
            
            tft.setTextColor(TFT_WHITE, TFT_BLACK);
            tft.drawString(label, x_pos, y_pos);
            
            // Store the new label for future delta checks
            strncpy(lastLabels[i], label, sizeof(lastLabels[i]) - 1);
            lastLabels[i][sizeof(lastLabels[i]) - 1] = '\0';
        }
    }

    // 4. Stale Data Cleanup: If the list shrank, wipe the abandoned grid cells
    for (int i = top_count; i < lastTopCount; i++) {
        int col = i % 2;
        int row = i / 2;
        int x_pos = 5 + (col * 240);
        int y_pos = 18 + (row * 16);
        
        tft.fillRect(x_pos, y_pos, 235, 16, TFT_BLACK);
        lastLabels[i][0] = '\0'; // Clear the tracker
    }

    lastTopCount = top_count;
}

void drawTemporalLegend() {
    int displayCount = 0;
    if (currentRadioMode == RADIO_WIFI) displayCount = sortMacCount;
    else if (currentRadioMode == RADIO_BLE) displayCount = sortBleCount;
    else if (currentRadioMode == RADIO_AP) displayCount = sortApCount;
    else if (currentRadioMode == RADIO_CHANNELS) displayCount = sortChannelCount;

    // Bail early if there's nothing to draw
    if (!(displayCount > 0 || ((currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_CHANNELS) && sortOtherBytes > 0))) {
        return; 
    }

    // 1. CALCULATE AND DRAW "OTHER" IN THE TOP MENU BANNER
    int otherCount = 0;
    // REDUCED: The threshold for "Other" is now > 6
    if (displayCount > 6) {
        otherCount = displayCount - 6;
    }

    tft.setFreeFont(&UbuntuMono_Regular9pt7b);
    tft.setTextDatum(TL_DATUM); 
    tft.setTextColor(COLOR_HOT_CHEST, TFT_BLACK);
    
    // FIX 1: Start the wipe at y=0 to catch the top ascenders of the font.
    // Height expanded to 20 to fully encapsulate the 9pt7b bounding box.
    tft.fillRect(315, 0, 95, 20, TFT_BLACK);
    
    char otherStr[16];
    // FIX 2: Force a 2-digit format so the string is always the exact same length
    snprintf(otherStr, sizeof(otherStr), "OTHER:%d", otherCount);
    
    // The text draws starting at y=1, safely inside the wiped area!
    tft.drawString(otherStr, 315, 1);

    // 2. DRAW THE MAIN 6-DEVICE LEGEND (Now in the bottom position)
    int start_y = HEADER_HEIGHT - 6;
    // Wipe exactly the space between the header line and the chart
    tft.fillRect(0, start_y, 480, chart_start_y - start_y, TFT_BLACK);
    
    tft.setFreeFont(&UbuntuMono_Regular11pt7b);

    int renderCount = 0;
    if (currentRadioMode == RADIO_WIFI) renderCount = sortMacCount;
    else if (currentRadioMode == RADIO_BLE) renderCount = sortBleCount;
    else if (currentRadioMode == RADIO_AP) renderCount = sortApCount;
    else if (currentRadioMode == RADIO_CHANNELS) renderCount = sortChannelCount;

    // REDUCED: Only loop up to 6 items max
    for(int i = 0; i < 6 && i < renderCount; i++) {
        char short_text[25]; // Safe size for 20-char strings + null terminator

        if (currentRadioMode == RADIO_WIFI) {
            strncpy(short_text, sortData[i].vendor, 19);
            short_text[19] = '\0';
        } 
        else if (currentRadioMode == RADIO_BLE) {
            if (strlen(sortBleData[i].name) > 0) {
                strncpy(short_text, sortBleData[i].name, 19);
                short_text[19] = '\0';
            } else {
                snprintf(short_text, sizeof(short_text), "%02X:%02X:%02X:%02X:%02X:%02X", 
                         sortBleData[i].mac[0], sortBleData[i].mac[1], sortBleData[i].mac[2], 
                         sortBleData[i].mac[3], sortBleData[i].mac[4], sortBleData[i].mac[5]);
            }
        } 
        else if (currentRadioMode == RADIO_AP) {
            // Uses sortApData, short_text, and tighter truncation bounds
            if (strcmp(sortApData[i].ssid, "<HIDDEN>") == 0 || strcmp(sortApData[i].ssid, "<UNKNOWN>") == 0) {
                snprintf(short_text, sizeof(short_text), "%s", sortApData[i].ssid);
            } else if (sortApData[i].has_clone) {
                char temp_ssid[16]; 
                strncpy(temp_ssid, sortApData[i].ssid, 14); // 14 chars max for legend
                temp_ssid[14] = '\0';
                snprintf(short_text, sizeof(short_text), "%s~%02X%02X", 
                         temp_ssid, sortApData[i].bssid[4], sortApData[i].bssid[5]);
            } else {
                strncpy(short_text, sortApData[i].ssid, 19); // 19 chars max for legend
                short_text[19] = '\0';
            }
        }
        else if (currentRadioMode == RADIO_CHANNELS) {
            snprintf(short_text, sizeof(short_text), "CH %02d", sortChannelData[i].channel);
        }

        tft.setTextColor(colors[i]);
        
        // Grid Math (3 rows x 2 columns)
        int x_pos = 5 + (i % 2) * 240; 
        int y_pos = start_y + (i / 2) * 20; 

        // UPDATED: Eliminated dynamic String object for pure char array
        char label[32];
        snprintf(label, sizeof(label), "%d.%s", i + 1, short_text);
        
        tft.drawString(label, x_pos, y_pos);
    }
    
    // Draw the white separator line between the new bottom legend and the waterfall chart
    tft.drawLine(0, chart_start_y, 480, chart_start_y, COLOR_HOT_CHEST);
}

// --- L2 QSORT COMPARATORS ---
int compareLeakAge(const void* a, const void* b) {
    LeakHistoryEntry* lA = (LeakHistoryEntry*)a;
    LeakHistoryEntry* lB = (LeakHistoryEntry*)b;
    
    // Push empty slots to the bottom
    if (lA->leak.meta.timestamp == 0 && lB->leak.meta.timestamp == 0) return 0;
    if (lA->leak.meta.timestamp == 0) return 1;
    if (lB->leak.meta.timestamp == 0) return -1;
    
    if (sort_descending) return (lB->leak.meta.timestamp > lA->leak.meta.timestamp) ? 1 : (lB->leak.meta.timestamp < lA->leak.meta.timestamp) ? -1 : 0;
    return (lA->leak.meta.timestamp > lB->leak.meta.timestamp) ? 1 : (lA->leak.meta.timestamp < lB->leak.meta.timestamp) ? -1 : 0;
}

int compareLeakLength(const void* a, const void* b) {
    LeakHistoryEntry* lA = (LeakHistoryEntry*)a;
    LeakHistoryEntry* lB = (LeakHistoryEntry*)b;
    
    if (lA->leak.meta.timestamp == 0 && lB->leak.meta.timestamp == 0) return 0;
    if (lA->leak.meta.timestamp == 0) return 1;
    if (lB->leak.meta.timestamp == 0) return -1;
    
    if (sort_descending) return (lB->leak.meta.frame_length > lA->leak.meta.frame_length) ? 1 : (lB->leak.meta.frame_length < lA->leak.meta.frame_length) ? -1 : 0;
    return (lA->leak.meta.frame_length > lB->leak.meta.frame_length) ? 1 : (lA->leak.meta.frame_length < lB->leak.meta.frame_length) ? -1 : 0;
}

int compareLeakHits(const void* a, const void* b) {
    LeakHistoryEntry* lA = (LeakHistoryEntry*)a;
    LeakHistoryEntry* lB = (LeakHistoryEntry*)b;
    
    if (lA->leak.meta.timestamp == 0 && lB->leak.meta.timestamp == 0) return 0;
    if (lA->leak.meta.timestamp == 0) return 1;
    if (lB->leak.meta.timestamp == 0) return -1;
    
    if (sort_descending) return (lB->hitCount > lA->hitCount) ? 1 : (lB->hitCount < lA->hitCount) ? -1 : 0;
    return (lA->hitCount > lB->hitCount) ? 1 : (lA->hitCount < lB->hitCount) ? -1 : 0;
}

// --- BULLETPROOF SORTING ENGINE ---
void processL2Data() {
    if (currentLeakSort == SORT_LEAK_AGE) {
        qsort(leakHistory, MAX_LEAK_SLOTS, sizeof(LeakHistoryEntry), compareLeakAge);
    } else if (currentLeakSort == SORT_LEAK_LENGTH) {
        qsort(leakHistory, MAX_LEAK_SLOTS, sizeof(LeakHistoryEntry), compareLeakLength);
    } else if (currentLeakSort == SORT_LEAK_HITS) {
        qsort(leakHistory, MAX_LEAK_SLOTS, sizeof(LeakHistoryEntry), compareLeakHits);
    }
}

bool handleTouchInputs(uint16_t t_x, uint16_t t_y) {
  bool trigger_render = false; // 1. Create local tracking variable

    // ==========================================
    // 1. CHART SCREEN TOUCH LOGIC
    // ==========================================
    if (currentState == SCREEN_CHART) {
      // TOP RIGHT: Menu Button
      if (t_x > 400 && t_y < 40) {
        currentState = SCREEN_MENU;
        pause_sniffing = true;
        esp_wifi_set_promiscuous(false);
        drawMenu();
        delay(300);
      }
      
      // BOTTOM FOOTER: Live Data Controls
      else if (t_y > 260) {
        
        // ==========================================
        // ZONE 1 (Left 0-145): SORT METRIC
        // ==========================================
        if (t_x < 145) {
          // 1. Wipe the inside
          tft.fillRect(3, 299, 139, 17, TFT_BLACK);
          
          // 2. Toggle the variable
          if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
            if (currentSortMode == SORT_TOTAL) currentSortMode = SORT_TX;
            else if (currentSortMode == SORT_TX) currentSortMode = SORT_RX;
            else if (currentSortMode == SORT_RX) currentSortMode = SORT_AVG;
            else if (currentSortMode == SORT_AVG) currentSortMode = SORT_CV;
            else if (currentSortMode == SORT_CV) currentSortMode = SORT_DIST;
            else if (currentSortMode == SORT_DIST) currentSortMode = SORT_AGE;
            else currentSortMode = SORT_TOTAL;
          } 
          else if (currentRadioMode == RADIO_CHANNELS) {
            if (currentSortMode == SORT_TOTAL) currentSortMode = SORT_TX;     
            else if (currentSortMode == SORT_TX) currentSortMode = SORT_RX;   
            else if (currentSortMode == SORT_RX) currentSortMode = SORT_AVG;  
            else if (currentSortMode == SORT_AVG) currentSortMode = SORT_CV;  
            else if (currentSortMode == SORT_CV) currentSortMode = SORT_DIST; 
            else if (currentSortMode == SORT_DIST) currentSortMode = SORT_AGE; 
            else currentSortMode = SORT_TOTAL;                                 
          }
          else if (currentRadioMode == RADIO_BLE) {
            if (currentBleSortMode == SORT_BLE_HITS) currentBleSortMode = SORT_BLE_DIST;
            else if (currentBleSortMode == SORT_BLE_DIST) currentBleSortMode = SORT_BLE_AGE;
            else currentBleSortMode = SORT_BLE_HITS;
          }
          // --- ADDED LAYER 2 LIVE TOGGLE ---
          else if (currentRadioMode == RADIO_LAYER2) {
            if (currentLeakSort == SORT_LEAK_AGE) currentLeakSort = SORT_LEAK_LENGTH;
            else if (currentLeakSort == SORT_LEAK_LENGTH) currentLeakSort = SORT_LEAK_HITS;
            else currentLeakSort = SORT_LEAK_AGE;
          }
          
          // 3. Redraw
          drawChartFooter();
          trigger_render = true; // Trigger the engine to re-sort and redraw the bars
          delay(200); 
        }
        
        // ==========================================
        // ZONE 2 (Center 145-290): SORT DIRECTION
        // ==========================================
        else if (t_x >= 145 && t_x <= 290) {
          tft.fillRect(148, 299, 139, 17, TFT_BLACK);
          sort_descending = !sort_descending;
          drawChartFooter(); 
          delay(200);
        }
        
        // ==========================================
        // ZONE 3 (Right 290-435): LOG/LINEAR SCALE
        // ==========================================
        else if (t_x > 290 && t_x <= 435) {
          tft.fillRect(293, 299, 139, 17, TFT_BLACK);
          useLogScale = !useLogScale;
          drawChartFooter(); 
          delay(200);
        }
      }
    }

    // ==========================================
    // 2. MENU SCREEN TOUCH LOGIC
    // ==========================================
    else if (currentState == SCREEN_MENU) {
      
      // FOXHUNT BUTTON TOUCH ZONE
      if (t_x > 50 && t_x < 250 && t_y > 90 && t_y < 130) {
          
          bool foxhunt_available = false;
          if (currentRadioMode == RADIO_WIFI) foxhunt_available = (target_locked && sessionMacCount > 0);
          else if (currentRadioMode == RADIO_BLE) foxhunt_available = (sessionBleCount > 0);
          else if (currentRadioMode == RADIO_AP) foxhunt_available = (sessionApCount > 0);

          if (!foxhunt_available) return false; 
          
          is_selecting_target = true;
          currentState = SCREEN_DEVICE_LIST;
          drawDeviceList();
          delay(400);
      }
      // Probe Request Tracker Button
      else if (t_x > 300 && t_x < 450 && t_y > 140 && t_y < 180) {
        currentState = SCREEN_PROBE_TRACKER;
        probe_current_page = 0;
        drawProbeTracker();
        delay(300); 
      }
      // AP Scanner / CH Select Button
      else if (t_x > 50 && t_x < 250 && t_y > 190 && t_y < 230) {
        if (currentRadioMode == RADIO_WIFI) {
          currentState = SCREEN_AP_SCAN;
          drawApScanner();
          delay(300);
        } else if (currentRadioMode == RADIO_AP || currentRadioMode == RADIO_LAYER2) {
          if (!target_locked) {
              target_locked = true;
              target_channel = 1;
          } else {
              target_channel++;
              if (target_channel > 13) {
                  target_locked = false;
                  target_channel = 0;
              }
          }
          
          memset(traffic_history, 0, sizeof(traffic_history)); 
          absolute_max_traffic = 10;
          resetMonitorState(); 
          
          drawMenu(); 
          delay(150); 
        }
      }
      // ==========================================
      // UNIFIED SNIFFED DEVICES / LEAK LIST BUTTON
      // ==========================================
      else if (t_x > 50 && t_x < 250 && t_y > 240 && t_y < 280) {
        currentState = SCREEN_DEVICE_LIST;
        device_current_page = 0;
        
        // Force an immediate sort before drawing so the array is ready
        if (currentRadioMode == RADIO_LAYER2) processL2Data();
        else forceSessionSort();
        
        drawDeviceList();
        delay(300);
      }
      // ==========================================
      // RADIO MODE TOGGLE TOUCH LOGIC (X:300-450, Y:190-230)
      // ==========================================
      else if (t_x > 300 && t_x < 450 && t_y > 190 && t_y < 230) {
        
        target_locked = false; 
        memset(traffic_history, 0, sizeof(traffic_history)); 
        absolute_max_traffic = 10;                           

        RadioMode nextMode;
        if (currentRadioMode == RADIO_WIFI) nextMode = RADIO_BLE;
        else if (currentRadioMode == RADIO_BLE) nextMode = RADIO_AP;
        else if (currentRadioMode == RADIO_AP) nextMode = RADIO_CHANNELS;
        else if (currentRadioMode == RADIO_CHANNELS) nextMode = RADIO_LAYER2;
        else nextMode = RADIO_WIFI;

        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.setTextDatum(MC_DATUM); 
        
        if (nextMode == RADIO_WIFI) {
          tft.fillRect(300, 190, 150, 40, TFT_BLUE);
          tft.drawRect(300, 190, 150, 40, TFT_WHITE);
          tft.setTextColor(TFT_WHITE);
          tft.drawString("MODE: WI-FI", 375, 210);
        } else if (nextMode == RADIO_BLE) {
          tft.fillRect(300, 190, 150, 40, TFT_PURPLE);
          tft.drawRect(300, 190, 150, 40, TFT_WHITE);
          tft.setTextColor(TFT_WHITE);
          tft.drawString("MODE: BLE", 375, 210);
        } else if (nextMode == RADIO_AP) {
          tft.fillRect(300, 190, 150, 40, TFT_DARKGREEN);
          tft.drawRect(300, 190, 150, 40, TFT_WHITE);
          tft.setTextColor(TFT_WHITE);
          tft.drawString("MODE: NETWORKS", 375, 210);
        } else if (nextMode == RADIO_CHANNELS) {
          tft.fillRect(300, 190, 150, 40, TFT_ORANGE);
          tft.drawRect(300, 190, 150, 40, TFT_WHITE);
          tft.setTextColor(TFT_WHITE);
          tft.drawString("MODE: CHANNELS", 375, 210);
        } else if (nextMode == RADIO_LAYER2) {
          tft.fillRect(300, 190, 150, 40, TFT_MAROON);
          tft.drawRect(300, 190, 150, 40, TFT_WHITE);
          tft.setTextColor(TFT_WHITE);
          tft.drawString("MODE: LAYER 2", 375, 210);
        }

        bool foxhunt_available = false;
        
        if (nextMode == RADIO_BLE) {
            if (sessionBleCount > 0) foxhunt_available = true;
        } else if (nextMode == RADIO_AP) {
            if (sessionApCount > 0) foxhunt_available = true;
        } else if (nextMode == RADIO_WIFI) {
            if (target_locked == true && sessionMacCount > 0) foxhunt_available = true;
        }

        if (foxhunt_available) {
            tft.fillRoundRect(50, 90, 200, 40, 3, TFT_RED); 
            tft.drawRoundRect(50, 90, 200, 40, 3, TFT_WHITE);
            tft.setTextColor(TFT_WHITE);
            tft.drawString("FOXHUNT", 150, 110);
        } else {
            uint16_t deadGrey = hex24to565(0x222222);
            tft.fillRect(50, 90, 200, 50, deadGrey); 
            tft.drawRect(50, 90, 200, 40, TFT_DARKGREY);
            tft.setTextColor(TFT_DARKGREY);
            tft.drawString("FOXHUNT", 150, 110);
            
            tft.setTextColor(hex24to565(0x444444));
            tft.drawString("(no targets yet)", 150, 125);
        }
        
        tft.setTextDatum(TL_DATUM); 

        // ==========================================
        // THE UNION SCRUB FIX
        // Because leakHistory shares a union with Wi-Fi/BLE session data, 
        // we MUST scrub it clean when switching to Layer 2. If we don't, the 
        // L2 sorting engine will choke on Wi-Fi garbage bytes!
        // ==========================================
        if (nextMode == RADIO_LAYER2) {
            memset(leakHistory, 0, sizeof(LeakHistoryEntry) * MAX_LEAK_SLOTS);
        }

        switchRadioMode(nextMode);
        delay(200);
      }
      // ==========================================
      // EXIT BUTTON TOUCH LOGIC
      // ==========================================
      else if (t_x > 300 && t_x < 450 && t_y > 240 && t_y < 280) {
        currentState = SCREEN_CHART;
        tft.fillScreen(TFT_BLACK);
        drawChartHeader();
        drawChartFooter();
        
        force_ui_refresh = true; 
        
        if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_CHANNELS || currentRadioMode == RADIO_LAYER2) {
            esp_wifi_set_promiscuous(true); 
        }
        
        if ((currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_LAYER2) && target_locked) {
          esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);
        } else if (currentRadioMode != RADIO_BLE) {
          esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);
        }
        
        current_x = 0;
        delay(300);
      }
    }

    // ==========================================
    // 3. OSINT PROBE TRACKER TOUCH LOGIC
    // ==========================================
    else if (currentState == SCREEN_PROBE_TRACKER) {
      
      // HEADER TOUCH (SORT CONTROLS)
      if (t_y <= 30) {
        if (t_x >= 275 && t_x < 410) {
          if (currentProbeSortMode == PROBE_SORT_HITS) currentProbeSortMode = PROBE_SORT_DIST;
          else if (currentProbeSortMode == PROBE_SORT_DIST) currentProbeSortMode = PROBE_SORT_SSIDS;
          else if (currentProbeSortMode == PROBE_SORT_SSIDS) currentProbeSortMode = PROBE_SORT_AGE;
          else currentProbeSortMode = PROBE_SORT_HITS;
          
          probe_current_page = 0; 
          drawProbeTracker();
          delay(200);
        }
        else if (t_x >= 410) {
          probe_sort_descending = !probe_sort_descending;
          probe_current_page = 0;
          drawProbeTracker();
          delay(200);
        }
      }
      
      // FOOTER TOUCH (NAVIGATION)
      else if (t_y > 285) {
        if (t_x < 160 && probe_current_page > 0) {
          probe_current_page--;
          drawProbeTracker();
          delay(250);
        }
        else if (t_x > 320 && ((probe_current_page + 1) * PROBES_PER_PAGE) < total_sniffed_probes) {
          probe_current_page++;
          drawProbeTracker();
          delay(250);
        }
        else if (t_x >= 160 && t_x <= 320) {
          currentState = SCREEN_MENU;
          drawMenu(); 
          delay(300);
        }
      }
    }

    // ==========================================
    // 4. AP SCANNER TOUCH LOGIC
    // ==========================================
    else if (currentState == SCREEN_AP_SCAN) {
      
      // 1. SNIFF ALL BUTTON (Free Airspace)
      if (t_y > 40 && t_y < 65) {
        target_locked = false;
        WiFi.scanDelete();
        esp_wifi_set_promiscuous(true);
        resetMonitorState();
        currentState = SCREEN_CHART;
        tft.fillScreen(TFT_BLACK);
        drawChartHeader();
        drawChartFooter();
        delay(300);
      }
      
      // 2. AP SELECTION LIST ROWS (y: 80 to 290)
      else if (t_y >= 80 && t_y < 290) {
        
        int clicked_row = (t_y - 80) / 35; 
        
        int actual_index = (ap_current_page * APS_PER_PAGE) + clicked_row;
        int n = WiFi.scanComplete();

        if (actual_index < n) {
          memcpy(target_bssid, WiFi.BSSID(actual_index), 6);
          target_channel = WiFi.channel(actual_index);
          target_rssi = WiFi.RSSI(actual_index);

          uint8_t* bssid = WiFi.BSSID(actual_index);
          String raw_ssid = WiFi.SSID(actual_index);

          bool has_clone = false;
          if (raw_ssid.length() > 0) {
            for (int j = 0; j < n; ++j) {
              if (actual_index != j && WiFi.SSID(j) == raw_ssid) {
                has_clone = true;
                break;
              }
            }
          }

          if (raw_ssid.length() == 0) {
            snprintf(target_ssid, sizeof(target_ssid), "<HIDDEN>~%02X%02X", bssid[4], bssid[5]);
          } else if (has_clone) {
            char temp_ssid[13];
            strncpy(temp_ssid, raw_ssid.c_str(), 12);
            temp_ssid[12] = '\0';
            snprintf(target_ssid, sizeof(target_ssid), "%s~%02X%02X", temp_ssid, bssid[4], bssid[5]);
          } else {
            char temp_ssid[18]; 
            strncpy(temp_ssid, raw_ssid.c_str(), 17);
            temp_ssid[17] = '\0';
            snprintf(target_ssid, sizeof(target_ssid), "%s", temp_ssid);
          }

          target_locked = true;

          WiFi.scanDelete();
          esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);
          esp_wifi_set_promiscuous(true);

          resetMonitorState();
          currentState = SCREEN_CHART;
          tft.fillScreen(TFT_BLACK);
          drawChartHeader();
          drawChartFooter();
          delay(300);
        }
      }

      // 3. PAGINATION & BACK FOOTER
      else if (t_y >= 290) {
        int total_aps = WiFi.scanComplete();
        
        if (t_x < 160 && ap_current_page > 0) {
          ap_current_page--;
          drawApScanner();
          delay(250);
        }
        else if (t_x > 320 && ((ap_current_page + 1) * APS_PER_PAGE) < total_aps) {
          ap_current_page++;
          drawApScanner();
          delay(250);
        }
        else if (t_x >= 160 && t_x <= 320) {
          currentState = SCREEN_MENU;
          ap_current_page = 0; 
          drawMenu(); 
          delay(300);
        }
      }
    }

    // ==========================================
    // 5. FOXHUNT SCREEN TOUCH LOGIC
    // ==========================================
    else if (currentState == SCREEN_FOXHUNT) {
      if (t_x > 190 && t_x < 290 && t_y > 290) {
        is_foxhunting = false;
        is_selecting_target = false;
        foxhunt_bounds_seeded = false; 
        
        target_locked = false; 
        current_ch_idx = 0;    
        esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);

        currentState = SCREEN_MENU; 
        drawMenu();
        delay(300);
      }
    }
    
    // ==========================================
    // 6. SEEN DEVICES / LEAK LIST TOUCH LOGIC
    // ==========================================
    else if (currentState == SCREEN_DEVICE_LIST) {
      
      // ==========================================
      // A. HEADER TOUCH LOGIC (SORT CONTROLS)
      // ==========================================
      if (t_y <= 30) {
        // ZONE 1: TOGGLE SORT METRIC (X: 275 to 405)
        if (t_x >= 275 && t_x < 405) {
          
          if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
            if (currentSortMode == SORT_TOTAL) currentSortMode = SORT_TX;
            else if (currentSortMode == SORT_TX) currentSortMode = SORT_RX;
            else if (currentSortMode == SORT_RX) currentSortMode = SORT_AVG;
            else if (currentSortMode == SORT_AVG) currentSortMode = SORT_CV;
            else if (currentSortMode == SORT_CV) currentSortMode = SORT_DIST;
            else if (currentSortMode == SORT_DIST) currentSortMode = SORT_AGE;
            else currentSortMode = SORT_TOTAL;
          } 
          else if (currentRadioMode == RADIO_CHANNELS) {
            if (currentSortMode == SORT_TOTAL) currentSortMode = SORT_TX;      
            else if (currentSortMode == SORT_TX) currentSortMode = SORT_RX;    
            else if (currentSortMode == SORT_RX) currentSortMode = SORT_AVG;   
            else if (currentSortMode == SORT_AVG) currentSortMode = SORT_CV;   
            else if (currentSortMode == SORT_CV) currentSortMode = SORT_DIST;  
            else currentSortMode = SORT_TOTAL;                                 
          }
          else if (currentRadioMode == RADIO_BLE) {
            if (currentBleSortMode == SORT_BLE_HITS) currentBleSortMode = SORT_BLE_DIST;
            else if (currentBleSortMode == SORT_BLE_DIST) currentBleSortMode = SORT_BLE_AGE;
            else currentBleSortMode = SORT_BLE_HITS;
          }
          // --- ADDED LAYER 2 SORT TOGGLE ---
          else if (currentRadioMode == RADIO_LAYER2) {
            if (currentLeakSort == SORT_LEAK_AGE) currentLeakSort = SORT_LEAK_LENGTH;
            else if (currentLeakSort == SORT_LEAK_LENGTH) currentLeakSort = SORT_LEAK_HITS;
            else currentLeakSort = SORT_LEAK_AGE;
          }
          
          device_current_page = 0; 
          
          // Force sort array before rendering list
          if (currentRadioMode == RADIO_LAYER2) processL2Data();
          else forceSessionSort(); 
          
          drawDeviceList();
          delay(200);
        }
        // ZONE 2: TOGGLE SORT DIRECTION (X: 410 to 480)
        else if (t_x >= 410) {
          sort_descending = !sort_descending;
          device_current_page = 0; 
          
          // Force sort array before rendering list
          if (currentRadioMode == RADIO_LAYER2) processL2Data();
          else forceSessionSort();
          
          drawDeviceList();
          delay(200);
        }
      }

      // ==========================================
      // B. FOOTER NAVIGATION (Y >= 294)
      // ==========================================
      else if (t_y >= 294) { 
        // --- ADDED LAYER 2 PAGINATION MATH ---
        int items_per_page = (currentRadioMode == RADIO_LAYER2) ? 3 : 7;
        int total_devices = 0;
        
        if (currentRadioMode == RADIO_WIFI) total_devices = sessionMacCount;
        else if (currentRadioMode == RADIO_BLE) total_devices = sessionBleCount;
        else if (currentRadioMode == RADIO_AP) total_devices = sessionApCount;
        else if (currentRadioMode == RADIO_CHANNELS) total_devices = sessionChannelCount;
        else if (currentRadioMode == RADIO_LAYER2) {
            for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
                if (leakHistory[i].hitCount > 0) total_devices++;
            }
        }

        // 1. PREV PAGE
        if (t_x < 160 && device_current_page > 0) {
          device_current_page--;
          drawDeviceList();
          delay(250);
        }
        // 2. NEXT PAGE
        else if (t_x > 320 && ((device_current_page + 1) * items_per_page) < total_devices) {
          device_current_page++;
          drawDeviceList();
          delay(250);
        }
        // 3. BACK TO MENU
        else if (t_x >= 160 && t_x <= 320) {
          currentState = SCREEN_MENU;
          device_current_page = 0; 
          drawMenu(); 
          delay(300);
        }
      }
      
      // ==========================================
      // C. LIST ROW SELECTION (The "Hot" Devices)
      // ==========================================
      else if (t_y >= 62 && t_y < 294) { 
        
        // --- ADDED LAYER 2 GUARD (No foxhunting for leaks yet) ---
        if (currentRadioMode == RADIO_LAYER2) return false;

        int tapped_screen_row = (t_y - 62) / 33;
        int total_devices = 0;
        
        if (currentRadioMode == RADIO_WIFI) total_devices = sessionMacCount;
        else if (currentRadioMode == RADIO_BLE) total_devices = sessionBleCount;
        else if (currentRadioMode == RADIO_AP) total_devices = sessionApCount;

        int tapped_array_index = (device_current_page * 7) + tapped_screen_row;

        if (tapped_screen_row < 7 && tapped_array_index < total_devices) {
          if (is_selecting_target) {
            is_selecting_target = false;
            is_foxhunting = true;
            smoothed_rssi = -100.0f;
            last_displayed_rssi = -999;      

            if (currentRadioMode == RADIO_WIFI) {
               memcpy(foxhunt_target_mac, sessionData[tapped_array_index].mac, 6);
              strncpy(foxhunt_target_vendor, sessionData[tapped_array_index].vendor, sizeof(foxhunt_target_vendor) - 1);
              foxhunt_target_vendor[sizeof(foxhunt_target_vendor) - 1] = '\0'; 
    
              foxhunt_rssi_min = sessionData[tapped_array_index].rssi_min;
              foxhunt_rssi_max = sessionData[tapped_array_index].rssi_max;
              foxhunt_bounds_seeded = (sessionData[tapped_array_index].packets > 6);
    
            } else if (currentRadioMode == RADIO_AP) {
              memcpy(foxhunt_target_mac, sessionApData[tapped_array_index].bssid, 6);
              strncpy(foxhunt_target_vendor, sessionApData[tapped_array_index].ssid, sizeof(foxhunt_target_vendor) - 1);
              foxhunt_target_vendor[sizeof(foxhunt_target_vendor) - 1] = '\0'; 
              
              foxhunt_rssi_min = sessionApData[tapped_array_index].rssi_min;
              foxhunt_rssi_max = sessionApData[tapped_array_index].rssi_max;
              foxhunt_bounds_seeded = (sessionApData[tapped_array_index].packets > 6);

              target_locked = true; 
              target_channel = sessionApData[tapped_array_index].channel;
              esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);

            } else if (currentRadioMode == RADIO_BLE) {
              memcpy(foxhunt_target_mac, sessionBleData[tapped_array_index].mac, 6);
              strncpy(foxhunt_target_vendor, sessionBleData[tapped_array_index].name, 25);
              if (foxhunt_target_vendor[0] == '\0') {
                strncpy(foxhunt_target_vendor, "<Unnamed BLE>", 25);
              }
              foxhunt_target_vendor[25] = '\0'; 
              
              foxhunt_rssi_min = -100;
              foxhunt_rssi_max = -100;
              foxhunt_bounds_seeded = false;
              
              target_locked = false;
            }

            currentState = SCREEN_FOXHUNT;
            
            if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
                esp_wifi_set_promiscuous(true);
            }
            pause_sniffing = false;

            drawFoxhuntScreen(); 
            delay(200);
          }
        }
      }

    }
    
    // (Notice SCREEN_LEAK_LIST block is completely deleted!)
    
    return trigger_render; 
}

void updateFoxhuntRadar() {
    // --- WAVE HOUND ANIMATION ENGINE ---
    static unsigned long last_anim_tick = 0;
    static int sequence_index = 0; // Tracks where we are in the script
    static unsigned long current_delay = 300; // Tracks how long the current frame should stay on screen

    // Define the custom animation script (0 = sniff, 1 = sniff/wag, 2 = look up)
    // This yields 8 standard loops, followed by 1 loop where the head raises
    const int ANIM_SEQUENCE[] = {0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2};
    const int SEQUENCE_LENGTH = 20;

    // Animate using the dynamic delay interval
    if (millis() - last_anim_tick > current_delay) {
        last_anim_tick = millis();
        
        int current_val = (int)smoothed_rssi;
        uint16_t houndColor = TFT_WHITE;
        int step_time = 300;

        // Tactical Color Feedback & Speed based on signal strength (Hot/Cold logic)
        if (current_val > -60) {
            houndColor = COLOR_HOT_CHEST;  // Hot / Close
            step_time = 100;               // Fast walk
        } else if (current_val > -75) {
            houndColor = COLOR_WARM;       // Warm / Medium
            step_time = 300;               // Normal walk
        } else {
            houndColor = COLOR_COLD;       // Cold / Far
            step_time = 600;               // Slow walk
        }

        int dog_x = HOUND_CENTER_X - (HOUND_WIDTH / 2); 
        int dog_y = HOUND_BASELINE_Y - HOUND_HEIGHT; 

        // Look up the actual frame (0, 1, or 2) from our sequence array
        int current_frame = ANIM_SEQUENCE[sequence_index];

        // Render the frame to the display
        tft.drawBitmap(dog_x, dog_y, houndAnimation[current_frame], HOUND_WIDTH, HOUND_HEIGHT, houndColor, TFT_BLACK);
        
        // NOW determine how long THIS newly drawn frame should stay on screen
        if (current_frame == 2) {
            current_delay = 1000;      // Always lock to 1-second pause when looking up
        } else {
            current_delay = step_time; // Apply the dynamically calculated walking speed
        }
        
        // Advance to the next step in the sequence, looping back to 0 at the end
        sequence_index = (sequence_index + 1) % SEQUENCE_LENGTH; 
    }
    // -----------------------------------

    static unsigned long last_radar_update = 0;

    if (millis() - last_radar_update > 300) {
        int current_display_val = (int)smoothed_rssi;

        // 1. RSSI VALUE — Massive Font (owns Y=88 to Y=132)
        if (current_display_val != last_displayed_rssi) {
            tft.fillRect(0, 88, 480, 44, TFT_BLACK); // Expanded clear box for giant text
            tft.setTextDatum(MC_DATUM);
            tft.setFreeFont(&UbuntuMono_B9pt7b);
            
            // THE MULTIPLIER: Scales 9pt to ~27pt
            tft.setTextSize(3); 

            // Color-code by signal strength
            if      (current_display_val > -60) tft.setTextColor(COLOR_HOT_CHEST);
            else if (current_display_val > -75) tft.setTextColor(COLOR_WARM);
            else                                tft.setTextColor(COLOR_COLD);

            char rssiStr[32];
            snprintf(rssiStr, sizeof(rssiStr), "%d dBm", current_display_val);
            tft.drawString(rssiStr, 240, 110);
            
            // THE RESET: Crucial to prevent UI corruption!
            tft.setTextSize(1); 
            tft.setTextDatum(TL_DATUM);
            last_displayed_rssi = current_display_val;
        }

        // ==========================================
        // 2. THE DYNAMIC BOUNDS UPDATER (Gutted)
        // ==========================================
        if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_BLE) {
            if (foxhunt_rssi_min != last_drawn_min || foxhunt_rssi_max != last_drawn_max) {
                
                tft.fillRect(0, 135, 480, 60, TFT_BLACK); // Clean wipe
                tft.setFreeFont(&UbuntuMono_Regular9pt7b);
                tft.setTextDatum(MC_DATUM);

                char boundStr[64];
                snprintf(boundStr, sizeof(boundStr), 
                         "FLOOR: %d dBm  |  CEILING: %d dBm", foxhunt_rssi_min, foxhunt_rssi_max);
                tft.setTextColor(TFT_GREEN);
                tft.drawString(boundStr, 240, 165); // Centered vertically in the 60px wipe box

                tft.setTextDatum(TL_DATUM);

                last_drawn_min = foxhunt_rssi_min;
                last_drawn_max = foxhunt_rssi_max;
            }
        }
        // ==========================================

        last_radar_update = millis();
    }
}

void runProbeCorrelationEngine() {
    static unsigned long last_correlation_run = 0;
    
    if (millis() - last_correlation_run > 5000) { 
        last_correlation_run = millis();
        
        for (int i = 0; i < MAX_PROBE_SLOTS; i++) {
            if (probeList[i].generation == 0) continue; 
            if ((probeList[i].mac[0] & 0x02) == 0) continue; // Only process randomized MACs

            for (int j = i + 1; j < MAX_PROBE_SLOTS; j++) {
                 if (probeList[j].generation == 0) continue;
                 if ((probeList[j].mac[0] & 0x02) == 0) continue; 

                 // --- THE MERGE TRIGGER ---
                 if (isSameDevice(i, j)) {
                     
                     // 1. Update Rotations & Hits
                     probeList[i].mac_rotations += probeList[j].mac_rotations;
                     probeList[i].hits += probeList[j].hits;
                     
                     // 2. Adopt the most recent MAC address and timestamps
                     if (probeList[j].last_seen > probeList[i].last_seen) {
                         probeList[i].last_seen = probeList[j].last_seen;
                         memcpy(probeList[i].mac, probeList[j].mac, 6); // Stay current with the target's rotation
                     }
                     
                     // 3. Merge the Behavioral PNL Fingerprint
                     probeList[i].pnl_hash |= probeList[j].pnl_hash;

                     // ==========================================
                     // 4. THE STACK-BUFFERED MERGE PROTOCOL
                     // ==========================================
                     // MAX_MERGE_SSIDS matches EMERGENCY_CUTOFF so no valid SSIDs
                     // should be truncated. If j_ssid_count hits the cap, remaining
                     // nodes are freed in 4b without migration — acceptable data loss
                     // from a corrupted chain that exceeded the per-device limit.
                     const int MAX_MERGE_SSIDS = EMERGENCY_CUTOFF;
                     char j_ssids[MAX_MERGE_SSIDS][33];
                     uint8_t j_ssid_count = 0;
                     int node = probeList[j].first_ssid_idx;
                     
                     // 4a. Pre-collect J's SSIDs onto the stack
                     while (node != -1 && j_ssid_count < MAX_MERGE_SSIDS) {
                         if (strlen(ssidPool[node].text) > 0) {
                             strncpy(j_ssids[j_ssid_count], ssidPool[node].text, 32);
                             j_ssids[j_ssid_count][32] = '\0';
                             j_ssid_count++;
                         }
                         node = ssidPool[node].next_node_idx;
                     }

                     // 4b. THE BURN PROTOCOL: Free J's pool nodes FIRST to reclaim SRAM
                     int node_to_wipe = probeList[j].first_ssid_idx;
                     int fail_safe = 0; 
                     while (node_to_wipe != -1 && fail_safe < TOTAL_SSID_POOL) {
                         int next = ssidPool[node_to_wipe].next_node_idx;
                         ssidPool[node_to_wipe].text[0] = '\0'; 
                         ssidPool[node_to_wipe].next_node_idx = -1; 
                         node_to_wipe = next;
                         fail_safe++;
                     }
                     
                     // 4c. Wipe J's array slot completely (The Sentinel Burn)
                     memset(&probeList[j], 0, sizeof(ProbeRecordShared));
                     
                     // Restore the critical sentinels that cannot be 0
                     probeList[j].first_ssid_idx = -1; 
                     probeList[j].rssi = -100;         
                     strncpy(probeList[j].vendor, "Unknown", 25);

                     // 4d. Re-allocate unique SSIDs from the stack into I
                     for (int s = 0; s < j_ssid_count; s++) {
                         bool already_exists = false;
                         bool added = false;
                         probeList[i].first_ssid_idx = addSsidToPool(j_ssids[s], 
                                                                     probeList[i].first_ssid_idx, 
                                                                     already_exists, added, 
                                                                     probeList[i].ssid_count);
                         if (added) probeList[i].ssid_count++;
                     }
                 }
            }
        }
    }
}

// ==========================================
// CORE 1: RAM-ONLY QUEUE CONSUMER
// ==========================================
void logLeakToSerial(const Layer2Capture& leak, const char* src_vendor,
                      const char* dst_vendor, const char* ssid) {

    // Render correctly regardless of IP version, reusing meta.ip_version
    // as the single source of truth (same field the on-screen L2 display
    // already keys off of).
    char srcIpStr[48], dstIpStr[48];

    if (leak.meta.ip_version == 6) {
        char srcIpRaw[48], dstIpRaw[48];
        getIpString(6, leak.meta.src_ip, srcIpRaw, sizeof(srcIpRaw));
        getIpString(6, leak.meta.dst_ip, dstIpRaw, sizeof(dstIpRaw));
        compress_ipv6(srcIpRaw, srcIpStr, sizeof(srcIpStr));
        compress_ipv6(dstIpRaw, dstIpStr, sizeof(dstIpStr));
    } else {
        getIpString(leak.meta.ip_version, leak.meta.src_ip, srcIpStr, sizeof(srcIpStr));
        getIpString(leak.meta.ip_version, leak.meta.dst_ip, dstIpStr, sizeof(dstIpStr));
    }

    Serial.printf(
        "🚨 LEAK [%s] | BSSID(SSID): %02X:%02X:%02X:%02X:%02X:%02X (%s) | "
        "Src MAC: %02X:%02X:%02X:%02X:%02X:%02X (%s) [%s:%u] -> "
        "Dst MAC: %02X:%02X:%02X:%02X:%02X:%02X (%s) [%s:%u] | "
        "Ch: %u | Text: %s\n",
        leak.meta.is_high_value ? "HIGH-VALUE" : "STANDARD",
        leak.meta.bssid[0], leak.meta.bssid[1], leak.meta.bssid[2],
        leak.meta.bssid[3], leak.meta.bssid[4], leak.meta.bssid[5],
        ssid,
        leak.meta.src_mac[0], leak.meta.src_mac[1], leak.meta.src_mac[2],
        leak.meta.src_mac[3], leak.meta.src_mac[4], leak.meta.src_mac[5],
        src_vendor,
        srcIpStr, leak.meta.src_port,
        leak.meta.dst_mac[0], leak.meta.dst_mac[1], leak.meta.dst_mac[2],
        leak.meta.dst_mac[3], leak.meta.dst_mac[4], leak.meta.dst_mac[5],
        dst_vendor,
        dstIpStr, leak.meta.dst_port,
        leak.meta.channel,
        leak.text
    );
}

void processLeakQueue() {
    if (leakQueue == NULL) return;

    Layer2Capture incomingLeak;
    bool ui_needs_update = false;

    while (xQueueReceive(leakQueue, &incomingLeak, 0) == pdTRUE) {

        // ==========================================
        // 0. TOKEN EXPANSION
        //    Run outside the ISR
        // ==========================================
        if (strcmp(incomingLeak.text, "ICMPV6_NS") == 0) {

            char src_str[40] = {0};
            char tgt_str[40] = {0};

            getIpString(
                6,
                incomingLeak.meta.src_ip,
                src_str,
                sizeof(src_str)
            );

            getIpString(
                6,
                incomingLeak.meta.dst_ip,
                tgt_str,
                sizeof(tgt_str)
            );

            snprintf(
                incomingLeak.text,
                sizeof(incomingLeak.text),
                "ICMPv6 ND: Who has %s? Tell %s",
                tgt_str,
                src_str
            );
        }

        // ==========================================
        // 1. TERMINAL HISTORY DEDUPLICATION
        //
        //    This is intentionally independent from
        //    persistent leakHistory eviction.
        // ==========================================
        bool foundTerminalMatch = false;
        int matchIndex = -1;

        for (int i = 0; i < MAX_TERMINAL_LINES; i++) {

            if (terminal_history[i].meta.timestamp > 0 &&
                memcmp(
                    terminal_history[i].meta.src_mac,
                    incomingLeak.meta.src_mac,
                    6
                ) == 0 &&
                strcmp(
                    terminal_history[i].text,
                    incomingLeak.text
                ) == 0) {

                foundTerminalMatch = true;
                matchIndex = i;
                break;
            }
        }

        if (foundTerminalMatch) {

            // Existing terminal entry: increment hits
            terminal_hits[matchIndex]++;

            // Refresh last-seen timestamp
            terminal_history[matchIndex].meta.timestamp =
                incomingLeak.meta.timestamp;

            // Move the refreshed entry to the front
            if (matchIndex > 0) {

                Layer2Capture tempCap =
                    terminal_history[matchIndex];

                uint16_t tempHits =
                    terminal_hits[matchIndex];

                uint32_t tempFirst =
                    terminal_first_seen[matchIndex];

                for (int t = matchIndex; t > 0; t--) {
                    terminal_history[t] =
                        terminal_history[t - 1];

                    terminal_hits[t] =
                        terminal_hits[t - 1];

                    terminal_first_seen[t] =
                        terminal_first_seen[t - 1];
                }

                terminal_history[0] = tempCap;
                terminal_hits[0] = tempHits;
                terminal_first_seen[0] = tempFirst;
            }

            ui_needs_update = true;

        } else {

            // New terminal entry.
            // Shift existing entries toward the back.
            for (int t = MAX_TERMINAL_LINES - 1; t > 0; t--) {

                terminal_history[t] =
                    terminal_history[t - 1];

                terminal_hits[t] =
                    terminal_hits[t - 1];

                terminal_first_seen[t] =
                    terminal_first_seen[t - 1];
            }

            terminal_history[0] = incomingLeak;
            terminal_hits[0] = 1;
            terminal_first_seen[0] =
                incomingLeak.meta.timestamp;

            ui_needs_update = true;
        }


        // ==========================================
        // 2. PERSISTENT LIST DEDUPLICATION
        // ==========================================
        bool isDuplicate = false;

        for (int i = 0; i < MAX_LEAK_SLOTS; i++) {

            if (leakHistory[i].leak.meta.timestamp > 0 &&
                memcmp(
                    leakHistory[i].leak.meta.src_mac,
                    incomingLeak.meta.src_mac,
                    6
                ) == 0 &&
                strcmp(
                    leakHistory[i].leak.text,
                    incomingLeak.text
                ) == 0) {

                // Existing persistent entry.
                // Do NOT run the eviction engine.
                leakHistory[i].hitCount++;

                // Refresh last-seen timestamp.
                leakHistory[i].leak.meta.timestamp =
                    incomingLeak.meta.timestamp;

                isDuplicate = true;
                ui_needs_update = true;

                break;
            }
        }


                if (!isDuplicate) {

            // ==========================================
            // 3. RESOLVE VENDORS + LOG — UNCONDITIONAL
            //    Runs for every genuinely new capture,
            //    regardless of eviction outcome.
            // ==========================================
            MacRecord tempRec;
            char resolved_src_vendor[16] = "Unknown";
            char resolved_dst_vendor[16] = "Unknown";

            memset(&tempRec, 0, sizeof(MacRecord));
            memcpy(tempRec.mac, incomingLeak.meta.src_mac, 6);
            resolveMacVendor(&tempRec);
            strncpy(resolved_src_vendor, tempRec.vendor, sizeof(resolved_src_vendor) - 1);
            resolved_src_vendor[sizeof(resolved_src_vendor) - 1] = '\0';

            memset(&tempRec, 0, sizeof(MacRecord));
            memcpy(tempRec.mac, incomingLeak.meta.dst_mac, 6);
            resolveMacVendor(&tempRec);
            strncpy(resolved_dst_vendor, tempRec.vendor, sizeof(resolved_dst_vendor) - 1);
            resolved_dst_vendor[sizeof(resolved_dst_vendor) - 1] = '\0';

            char safeSsid[33] = "Unknown";
            for (int ap = 0; ap < MAX_BSSID_CACHE; ap++) {
                if (bssidCache[ap].last_seen == 0) continue;
                if (memcmp(incomingLeak.meta.bssid, bssidCache[ap].bssid, 6) == 0) {
                    strncpy(safeSsid, bssidCache[ap].ssid, sizeof(safeSsid) - 1);
                    safeSsid[sizeof(safeSsid) - 1] = '\0';
                    break;
                }
            }

            logLeakToSerial(incomingLeak, resolved_src_vendor, resolved_dst_vendor, safeSsid);

            // ==========================================
            // 4. SMART EVICTION ENGINE
            //    Only decides whether it also gets a
            //    permanent slot in leakHistory.
            // ==========================================
            int targetIndex = -1;

            for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
                if (leakHistory[i].leak.meta.timestamp == 0) {
                    targetIndex = i;
                    break;
                }
            }

            if (targetIndex == -1) {
                int victim_idx = 0;
                int min_score = INT_MAX;
                uint32_t oldest_time = UINT32_MAX;

                for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
                    int score = leakHistory[i].leak.retained_len;
                    if (score == 0) score = strlen(leakHistory[i].leak.text);
                    if (leakHistory[i].leak.meta.is_high_value) score += 300;

                    if (score < min_score) {
                        min_score = score;
                        victim_idx = i;
                        oldest_time = leakHistory[i].first_seen;
                    } else if (score == min_score) {
                        if (leakHistory[i].first_seen < oldest_time) {
                            victim_idx = i;
                            oldest_time = leakHistory[i].first_seen;
                        }
                    }
                }

                int incoming_score = incomingLeak.retained_len;
                if (incoming_score == 0) incoming_score = strlen(incomingLeak.text);
                if (incomingLeak.meta.is_high_value) incoming_score += 10000;

                if (incoming_score > min_score) {
                    targetIndex = victim_idx;
                }
            }

            // ==========================================
            // 5. INSERT — GATED, using vendors already resolved above
            // ==========================================
            if (targetIndex != -1) {
                leakHistory[targetIndex].leak = incomingLeak;
                leakHistory[targetIndex].hitCount = 1;
                leakHistory[targetIndex].first_seen = incomingLeak.meta.timestamp;
                leakHistory[targetIndex].flow_hash = incomingLeak.meta.flow_hash;
                strcpy(leakHistory[targetIndex].src_vendor, resolved_src_vendor);
                strcpy(leakHistory[targetIndex].dst_vendor, resolved_dst_vendor);

                ui_needs_update = true;
            }
        }
    }


    // ==========================================
    // 8. BATCHED UI REFRESH
    // ==========================================
    if (ui_needs_update &&
        currentState == SCREEN_DEVICE_LIST &&
        currentRadioMode == RADIO_LAYER2) {

        processL2Data();
        drawDeviceList();
    }
}

/*
void processLeakQueue() {
    if (leakQueue == NULL) return;

    Layer2Capture incomingLeak; 
    bool ui_needs_update = false; 
    
    while (xQueueReceive(leakQueue, &incomingLeak, 0) == pdTRUE) {
        
        // ==========================================
        // 0. TOKEN EXPANSION (Run outside the ISR!)
        // ==========================================
        if (strcmp(incomingLeak.text, "ICMPV6_NS") == 0) {
            char src_str[40] = {0};
            char tgt_str[40] = {0};
            
            getIpString(6, incomingLeak.meta.src_ip, src_str, sizeof(src_str));
            getIpString(6, incomingLeak.meta.dst_ip, tgt_str, sizeof(tgt_str));
            
            snprintf(incomingLeak.text, sizeof(incomingLeak.text), 
                     "ICMPv6 ND: Who has %s? Tell %s", tgt_str, src_str);
        }

        // --- ADVANCED TERMINAL DEDUPLICATION (LRU CACHE) ---
        bool foundTerminalMatch = false;
        int matchIndex = -1;

        for (int i = 0; i < MAX_TERMINAL_LINES; i++) {
            if (terminal_history[i].meta.timestamp > 0 && 
                memcmp(terminal_history[i].meta.src_mac, incomingLeak.meta.src_mac, 6) == 0 &&
                strcmp(terminal_history[i].text, incomingLeak.text) == 0) {
                foundTerminalMatch = true;
                matchIndex = i;
                break;
            }
        }

        if (foundTerminalMatch) {
            terminal_hits[matchIndex]++;
            terminal_history[matchIndex].meta.timestamp = incomingLeak.meta.timestamp; 

            if (matchIndex > 0) {
                Layer2Capture tempCap = terminal_history[matchIndex];
                uint16_t tempHits = terminal_hits[matchIndex];
                uint32_t tempFirst = terminal_first_seen[matchIndex]; 

                for (int t = matchIndex; t > 0; t--) {
                    terminal_history[t] = terminal_history[t-1];
                    terminal_hits[t] = terminal_hits[t-1];
                    terminal_first_seen[t] = terminal_first_seen[t-1]; 
                }
                
                terminal_history[0] = tempCap;
                terminal_hits[0] = tempHits;
                terminal_first_seen[0] = tempFirst; 
            }
            ui_needs_update = true;
        } else {
            for (int t = MAX_TERMINAL_LINES - 1; t > 0; t--) {
                terminal_history[t] = terminal_history[t-1];
                terminal_hits[t] = terminal_hits[t-1]; 
                terminal_first_seen[t] = terminal_first_seen[t-1]; 
            }
            terminal_history[0] = incomingLeak;
            terminal_hits[0] = 1; 
            terminal_first_seen[0] = incomingLeak.meta.timestamp; 
            ui_needs_update = true;
        }
        
        bool isDuplicate = false;
                
        // 1. Deduplication (Sync to Session)
        for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
            if (leakHistory[i].leak.meta.timestamp > 0 && 
                memcmp(leakHistory[i].leak.meta.src_mac, incomingLeak.meta.src_mac, 6) == 0 &&
                strcmp(leakHistory[i].leak.text, incomingLeak.text) == 0) {
                
                leakHistory[i].hitCount++;
                leakHistory[i].leak.meta.timestamp = incomingLeak.meta.timestamp; 
                
                isDuplicate = true;
                ui_needs_update = true;
                break;
            }
        }

        // ==========================================
        // 2. SMART EVICTION ENGINE (Length + Value Weighted)
        // ==========================================
        if (!isDuplicate) {
            int targetIndex = -1;

            // Fast Pass: Look for a completely empty slot first
            for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
                if (leakHistory[i].leak.meta.timestamp == 0) {
                    targetIndex = i;
                    break;
                }
            }

            // The Arena: Fight for survival if list is full
            if (targetIndex == -1) {
                int victim_idx = 0;
                int min_score = 999999;
                uint32_t oldest_time = 0xFFFFFFFF;

                for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
                    int score = leakHistory[i].leak.retained_len;
                    if (score == 0) score = strlen(leakHistory[i].leak.text);

                    if (leakHistory[i].leak.meta.is_high_value) score += 10000;

                    if (score < min_score) {
                        min_score = score;
                        victim_idx = i;
                        oldest_time = leakHistory[i].first_seen;
                    } 
                    else if (score == min_score) {
                        if (leakHistory[i].leak.meta.timestamp < oldest_time) {
                            victim_idx = i;
                            oldest_time = leakHistory[i].leak.meta.timestamp;
                        }
                    }
                }

                int incoming_score = incomingLeak.retained_len;
                if (incoming_score == 0) incoming_score = strlen(incomingLeak.text);
                if (incomingLeak.meta.is_high_value) incoming_score += 10000;

                // The Gatekeeper Check
                if (incoming_score >= min_score) {
                    targetIndex = victim_idx;
                }
            }

            // 3. Resolve BOTH MAC vendors safely into local buffers
            MacRecord tempRec;
            char resolved_src_vendor[16] = "Unknown";
            char resolved_dst_vendor[16] = "Unknown";
            
            memset(&tempRec, 0, sizeof(MacRecord));      
            memcpy(tempRec.mac, incomingLeak.meta.src_mac, 6); 
            resolveMacVendor(&tempRec); 
            strncpy(resolved_src_vendor, tempRec.vendor, 15);
            resolved_src_vendor[15] = '\0'; 
            
            memset(&tempRec, 0, sizeof(MacRecord));      
            memcpy(tempRec.mac, incomingLeak.meta.dst_mac, 6); 
            resolveMacVendor(&tempRec); 
            strncpy(resolved_dst_vendor, tempRec.vendor, 15);
            resolved_dst_vendor[15] = '\0'; 

            // Insert into the target slot if it survived the Gatekeeper
            if (targetIndex != -1) {
                leakHistory[targetIndex].leak = incomingLeak;
                leakHistory[targetIndex].hitCount = 1;
                leakHistory[targetIndex].first_seen = incomingLeak.meta.timestamp;
                leakHistory[targetIndex].flow_hash = incomingLeak.meta.flow_hash;
                strcpy(leakHistory[targetIndex].src_vendor, resolved_src_vendor);
                strcpy(leakHistory[targetIndex].dst_vendor, resolved_dst_vendor);
                
                ui_needs_update = true;
            }

            // ==========================================
            // DYNAMIC SSID LOOKUP FOR SERIAL MONITOR
            // ==========================================
            char safeSsid[33] = "Unknown"; 
            for (int ap = 0; ap < MAX_BSSID_CACHE; ap++) {
                if (bssidCache[ap].last_seen == 0) continue;
                if (memcmp(incomingLeak.meta.bssid, bssidCache[ap].bssid, 6) == 0) {
                    strncpy(safeSsid, bssidCache[ap].ssid, 32);
                    safeSsid[32] = '\0';
                    break;
                }
            }

            Serial.printf("🚨 LEAK [%s] | BSSID(SSID): %02X:%02X:%02X:%02X:%02X:%02X (%s) | Src MAC: %02X:%02X:%02X:%02X:%02X:%02X (%s) [%u.%u.%u.%u:%u] -> Dst MAC: %02X:%02X:%02X:%02X:%02X:%02X (%s) [%u.%u.%u.%u:%u] | Ch: %u | Text: %s\n",
              incomingLeak.meta.is_high_value ? "HIGH-VALUE" : "STANDARD",
              incomingLeak.meta.bssid[0], incomingLeak.meta.bssid[1], incomingLeak.meta.bssid[2], 
              incomingLeak.meta.bssid[3], incomingLeak.meta.bssid[4], incomingLeak.meta.bssid[5],
              safeSsid,
              incomingLeak.meta.src_mac[0], incomingLeak.meta.src_mac[1], incomingLeak.meta.src_mac[2], 
              incomingLeak.meta.src_mac[3], incomingLeak.meta.src_mac[4], incomingLeak.meta.src_mac[5],
              resolved_src_vendor,
              incomingLeak.meta.src_ip[0], incomingLeak.meta.src_ip[1], incomingLeak.meta.src_ip[2], incomingLeak.meta.src_ip[3],
              incomingLeak.meta.src_port,
              incomingLeak.meta.dst_mac[0], incomingLeak.meta.dst_mac[1], incomingLeak.meta.dst_mac[2], 
              incomingLeak.meta.dst_mac[3], incomingLeak.meta.dst_mac[4], incomingLeak.meta.dst_mac[5],
              resolved_dst_vendor,
              incomingLeak.meta.dst_ip[0], incomingLeak.meta.dst_ip[1], incomingLeak.meta.dst_ip[2], incomingLeak.meta.dst_ip[3],
              incomingLeak.meta.dst_port,
              incomingLeak.meta.channel,
              incomingLeak.text
            );
        }
    }
    
    // ==========================================
    // 4. BATCHED UI REFRESH
    // ==========================================
    if (ui_needs_update && currentState == SCREEN_DEVICE_LIST && currentRadioMode == RADIO_LAYER2) {
        processL2Data(); 
        drawDeviceList();  
    }
}

void processLeakQueue() {
    if (leakQueue == NULL) return;

    Layer2Capture incomingLeak; // Uses the unified struct
    bool ui_needs_update = false; // Prevents UI flicker during packet bursts
    
    // Process all available items in the queue without blocking (tick delay = 0)
    while (xQueueReceive(leakQueue, &incomingLeak, 0) == pdTRUE) {
        
        // ==========================================
        // 0. TOKEN EXPANSION (Run outside the ISR!)
        // ==========================================
        if (strcmp(incomingLeak.text, "ICMPV6_NS") == 0) {
            char src_str[40] = {0};
            char tgt_str[40] = {0};
            
            getIpString(6, incomingLeak.meta.src_ip, src_str, sizeof(src_str));
            getIpString(6, incomingLeak.meta.dst_ip, tgt_str, sizeof(tgt_str));
            
            snprintf(incomingLeak.text, sizeof(incomingLeak.text), 
                     "ICMPv6 ND: Who has %s? Tell %s", tgt_str, src_str);
        }

        // --- NEW: ADVANCED TERMINAL DEDUPLICATION (LRU CACHE) ---
        bool foundTerminalMatch = false;
        int matchIndex = -1;

        // Scan all 5 visible terminal slots for a match
        for (int i = 0; i < MAX_TERMINAL_LINES; i++) {
            if (terminal_history[i].meta.timestamp > 0 && 
                memcmp(terminal_history[i].meta.src_mac, incomingLeak.meta.src_mac, 6) == 0 &&
                strcmp(terminal_history[i].text, incomingLeak.text) == 0) {
                foundTerminalMatch = true;
                matchIndex = i;
                break;
            }
        }

        if (foundTerminalMatch) {
            // 1. Increment hits and update LAST seen time
            terminal_hits[matchIndex]++;
            terminal_history[matchIndex].meta.timestamp = incomingLeak.meta.timestamp; 

            // 2. Bubble this active flow back up to the top (index 0)
            if (matchIndex > 0) {
                Layer2Capture tempCap = terminal_history[matchIndex];
                uint16_t tempHits = terminal_hits[matchIndex];
                uint32_t tempFirst = terminal_first_seen[matchIndex]; // Grab the original first_seen

                // Shift everything ABOVE the match down by one slot
                for (int t = matchIndex; t > 0; t--) {
                    terminal_history[t] = terminal_history[t-1];
                    terminal_hits[t] = terminal_hits[t-1];
                    terminal_first_seen[t] = terminal_first_seen[t-1]; // Shift first_seen
                }
                
                // Put the actively hitting packet back at the top
                terminal_history[0] = tempCap;
                terminal_hits[0] = tempHits;
                terminal_first_seen[0] = tempFirst; // Restore original first_seen to the top
            }
            ui_needs_update = true;
        } else {
            // It's a brand new packet. Shift everything down.
            for (int t = MAX_TERMINAL_LINES - 1; t > 0; t--) {
                terminal_history[t] = terminal_history[t-1];
                terminal_hits[t] = terminal_hits[t-1]; 
                terminal_first_seen[t] = terminal_first_seen[t-1]; 
            }
            terminal_history[0] = incomingLeak;
            terminal_hits[0] = 1; 
            terminal_first_seen[0] = incomingLeak.meta.timestamp; // Initialize first_seen!
            ui_needs_update = true;
        }
        
        bool isDuplicate = false;
                
        // 1. Deduplication (Sync to Session)
        // Using your original robust identity check: Same MAC + Same Text
        for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
            if (leakHistory[i].leak.meta.timestamp > 0 && 
                memcmp(leakHistory[i].leak.meta.src_mac, incomingLeak.meta.src_mac, 6) == 0 &&
                strcmp(leakHistory[i].leak.text, incomingLeak.text) == 0) {
                
                leakHistory[i].hitCount++;
                leakHistory[i].leak.meta.timestamp = incomingLeak.meta.timestamp; 
                
                // (Note: We no longer memmove() to bubble-up here because 
                // the processL2Data sorting engine handles the ordering!)
                
                isDuplicate = true;
                ui_needs_update = true;
                break;
            }
        }

        // 2. New Leak: Find an empty slot or Evict the oldest (LRU)
        if (!isDuplicate) {
            int targetIndex = -1;
            uint32_t oldestTime = 0xFFFFFFFF;
            
            // Scan for empty slot or find the oldest to evict
            for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
                if (leakHistory[i].leak.meta.timestamp == 0) {
                    targetIndex = i; // Found an empty slot!
                    break;
                }
                if (leakHistory[i].leak.meta.timestamp < oldestTime) {
                    oldestTime = leakHistory[i].leak.meta.timestamp;
                    targetIndex = i; // Track the oldest slot just in case
                }
            }

            // Insert into the target slot (Memory stays flat, no shifting!)
            if (targetIndex != -1) {
                leakHistory[targetIndex].leak = incomingLeak;
                leakHistory[targetIndex].hitCount = 1;
                leakHistory[targetIndex].first_seen = incomingLeak.meta.timestamp;
                leakHistory[targetIndex].flow_hash = incomingLeak.meta.flow_hash;

                // 3. Resolve BOTH MAC vendors
                MacRecord tempRec;
                
                memset(&tempRec, 0, sizeof(MacRecord));      
                memcpy(tempRec.mac, incomingLeak.meta.src_mac, 6); 
                resolveMacVendor(&tempRec); 
                strncpy(leakHistory[targetIndex].src_vendor, tempRec.vendor, 15);
                leakHistory[targetIndex].src_vendor[15] = '\0'; 
                
                memset(&tempRec, 0, sizeof(MacRecord));      
                memcpy(tempRec.mac, incomingLeak.meta.dst_mac, 6); 
                resolveMacVendor(&tempRec); 
                strncpy(leakHistory[targetIndex].dst_vendor, tempRec.vendor, 15);
                leakHistory[targetIndex].dst_vendor[15] = '\0'; 
                
                ui_needs_update = true;
            }

            // ==========================================
            // DYNAMIC SSID LOOKUP FOR SERIAL MONITOR
            // ==========================================
            char safeSsid[33] = "Unknown"; // 32 chars + null terminator
            for (int ap = 0; ap < MAX_BSSID_CACHE; ap++) {
                if (bssidCache[ap].last_seen == 0) continue;
                if (memcmp(incomingLeak.meta.bssid, bssidCache[ap].bssid, 6) == 0) {
                    strncpy(safeSsid, bssidCache[ap].ssid, 32);
                    safeSsid[32] = '\0';
                    break;
                }
            }

            Serial.printf("🚨 LEAK [%s] | BSSID(SSID): %02X:%02X:%02X:%02X:%02X:%02X (%s) | Src MAC: %02X:%02X:%02X:%02X:%02X:%02X (%s) [%u.%u.%u.%u:%u] -> Dst MAC: %02X:%02X:%02X:%02X:%02X:%02X (%s) [%u.%u.%u.%u:%u] | Ch: %u | Text: %s\n",
              incomingLeak.meta.is_high_value ? "HIGH-VALUE" : "STANDARD",
              incomingLeak.meta.bssid[0], incomingLeak.meta.bssid[1], incomingLeak.meta.bssid[2], 
              incomingLeak.meta.bssid[3], incomingLeak.meta.bssid[4], incomingLeak.meta.bssid[5],
              safeSsid,
              incomingLeak.meta.src_mac[0], incomingLeak.meta.src_mac[1], incomingLeak.meta.src_mac[2], 
              incomingLeak.meta.src_mac[3], incomingLeak.meta.src_mac[4], incomingLeak.meta.src_mac[5],
              leakHistory[targetIndex].src_vendor, // <--- INJECTED SRC VENDOR
              incomingLeak.meta.src_ip[0], incomingLeak.meta.src_ip[1], incomingLeak.meta.src_ip[2], incomingLeak.meta.src_ip[3],
              incomingLeak.meta.src_port,
              incomingLeak.meta.dst_mac[0], incomingLeak.meta.dst_mac[1], incomingLeak.meta.dst_mac[2], 
              incomingLeak.meta.dst_mac[3], incomingLeak.meta.dst_mac[4], incomingLeak.meta.dst_mac[5],
              leakHistory[targetIndex].dst_vendor, // <--- INJECTED DST VENDOR
              incomingLeak.meta.dst_ip[0], incomingLeak.meta.dst_ip[1], incomingLeak.meta.dst_ip[2], incomingLeak.meta.dst_ip[3],
              incomingLeak.meta.dst_port,
              incomingLeak.meta.channel,
              incomingLeak.text
            );
        }
    }
    
    // ==========================================
    // 4. BATCHED UI REFRESH
    // ==========================================
    // Trigger render outside the while loop to prevent screen stutter
    if (ui_needs_update && currentState == SCREEN_DEVICE_LIST && currentRadioMode == RADIO_LAYER2) {
        processL2Data(); // Sort the array based on the current user setting
        drawDeviceList();  // Asynchronously paint the unified screen
    }
}
*/

bool updateRadioHopper() {
    bool trigger_render = false; // Local render trigger

    // THE FIX: Added SCREEN_LEAK_LIST so the radio continues scanning the spectrum
    if (currentState == SCREEN_CHART || currentState == SCREEN_FOXHUNT || currentState == SCREEN_LEAK_LIST) {
        static unsigned long lastTimer = 0;

        tft.setTextWrap(false);

        // ==========================================
        // RADIO-AWARE TIMERS
        // ==========================================
        // Both Wi-Fi and AP modes need the Channel Hopper!
        if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_CHANNELS || currentRadioMode == RADIO_LAYER2) {
            if (!target_locked) {
                if (millis() - lastTimer > HOP_INTERVAL) {
                    lastTimer = millis();
                    current_ch_idx++;

                    if (current_ch_idx >= NUM_CHANNELS) {
                        current_ch_idx = 0;
                        trigger_render = true; // Replaces should_render = true
                    }

                    esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);

                    // Only draw the channel indicator if we are on the main chart!
                    if (currentState == SCREEN_CHART) {
                        // 1. Reduced width from 75 to 62 to prevent clipping the " | "
                        tft.fillRect(5, 0, 62, 20, TFT_BLACK);
                        
                        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
                        tft.setTextDatum(TL_DATUM);
                        
                        tft.setTextColor(COLOR_HOT_CHEST);

                        char chStr[16];
                        sprintf(chStr, "CH: %02d", CHANNELS[current_ch_idx]);
                        
                        // 2. Changed y from 0 to 1 to match drawChartHeader() exactly
                        tft.drawString(chStr, 5, 1);
                    }
                }
            }
            else {
                // High-speed drain for Foxhunting / Target Locking
                if (millis() - lastTimer > LOCKED_UPDATE_INTERVAL) {
                    lastTimer = millis();
                    trigger_render = true; // Replaces should_render = true
                }
            }
        } 
        else if (currentRadioMode == RADIO_BLE) {
            // BLE MODE WATERFALL
            if (millis() - lastTimer > BLE_UPDATE_INTERVAL) { 
                lastTimer = millis();
                trigger_render = true; // Replaces should_render = true
                
                // Only draw the BLE sniffing indicator if we are on the main chart!
                if (currentState == SCREEN_CHART) {
                    tft.fillRect(5, 0, 200, 20, TFT_BLACK); 
                    tft.setFreeFont(&UbuntuMono_Regular9pt7b);
                    tft.setTextDatum(TL_DATUM);
                    tft.setTextColor(COLOR_HOT_CHEST);
                    tft.drawString("SNIFFING BLE DEVICES", 5, 4);
                }
            }
        }
    }
    
    return trigger_render;
}

void processWifiData() {
    // Snapshot the live buffer for the real-time UI/sorting
    memcpy((void*)sortData, (void*)liveData, sizeof(liveData));
    sortMacCount = liveMacCount;
    sortOtherBytes = liveOtherBytes;

    // Drain the "Other Bytes" bucket into the historical session
    sessionOtherBytes += liveOtherBytes;
    
    // Sync the Live Buffer into the Historical Session
    for (int i = 0; i < liveMacCount; i++) {
        bool found = false;
        float rawDistance = calculateRfDistance(liveData[i].rssi, 0, RADIO_WIFI_24GHZ);
        
        // A. Inner j loop — session sync + bounds refresh
        for (int j = 0; j < sessionMacCount; j++) {
            if (memcmp(sessionData[j].mac, (void*)liveData[i].mac, 6) == 0) {
                sessionData[j].packets += liveData[i].packets;
                sessionData[j].tx_bytes += liveData[i].tx_bytes;
                sessionData[j].rx_bytes += liveData[i].rx_bytes;
                sessionData[j].sum_bytes += liveData[i].sum_bytes;
                sessionData[j].sum_sq_bytes += liveData[i].sum_sq_bytes;
                sessionData[j].rssi = liveData[i].rssi;
                
                if (liveData[i].rate > 0) sessionData[j].rate = liveData[i].rate;
                sessionData[j].last_seen = liveData[i].last_seen;
                
                // Only stretch the session bounds if the liveData window actually
                // captured a valid physical transmission (!= 0 and != -100).
                if (liveData[i].rssi_min != 0) {
                    if (liveData[i].rssi_min < sessionData[j].rssi_min || sessionData[j].rssi_min == 0) {
                        sessionData[j].rssi_min = liveData[i].rssi_min;
                    }
                }
                if (liveData[i].rssi_max != -100) {
                    if (liveData[i].rssi_max > sessionData[j].rssi_max || sessionData[j].rssi_max == 0) {
                        sessionData[j].rssi_max = liveData[i].rssi_max;
                    }
                }

                if (rawDistance > 0) {
                    sessionData[j].smoothedDistance = (0.2 * rawDistance) + (0.8 * sessionData[j].smoothedDistance);
                }

                found = true;
                break;
            }
        }

        // B. If it's a completely new MAC, claim a new slot OR Evict
        if (!found) {
            int targetIndex = 0;

            if (sessionMacCount < MAX_MACS) {
                targetIndex = sessionMacCount;
                sessionMacCount++;
            } else {
                // Execute LRU Eviction!
                uint32_t oldestTime = 0xFFFFFFFF; 
                for (int k = 0; k < MAX_MACS; k++) {
                    if (sessionData[k].last_seen < oldestTime) {
                        oldestTime = sessionData[k].last_seen;
                        targetIndex = k;
                    }
                }
                // Dump the evicted device's stats so global totals remain accurate!
                sessionOtherBytes += (sessionData[targetIndex].tx_bytes + sessionData[targetIndex].rx_bytes);
            }

            memcpy((void*)&sessionData[targetIndex], (void*)&liveData[i], sizeof(MacRecord));
            sessionData[targetIndex].smoothedDistance = (rawDistance > 0) ? rawDistance : 0.0;
        }
    } 

    // Wipe the live buffer clean so the interrupt can refill it
    memset((void*)liveData, 0, sizeof(liveData));
    liveMacCount = 0;
    liveOtherBytes = 0;

    // --- FAST INSERTION SORT: WI-FI SNAPSHOT ---
    for (int i = 1; i < sortMacCount; i++) {
        MacRecord key = sortData[i];
        double key_val = getSortMetric(key, currentSortMode); 
        int j = i - 1;

        if (sort_descending) {
            while (j >= 0 && getSortMetric(sortData[j], currentSortMode) < key_val) {
                sortData[j + 1] = sortData[j];
                j = j - 1;
            }
        } else {
            while (j >= 0 && getSortMetric(sortData[j], currentSortMode) > key_val && key_val > 0.0) {
                sortData[j + 1] = sortData[j];
                j = j - 1;
            }
        }
        sortData[j + 1] = key;
    }

    // --- FAST INSERTION SORT: WI-FI SESSION ---
    for (int i = 1; i < sessionMacCount; i++) {
        MacRecord key = sessionData[i];
        double key_val = getSortMetric(key, currentSortMode); 
        int j = i - 1;

        if (sort_descending) {
            while (j >= 0 && getSortMetric(sessionData[j], currentSortMode) < key_val) {
                sessionData[j + 1] = sessionData[j];
                j = j - 1;
            }
        } else {
            while (j >= 0 && getSortMetric(sessionData[j], currentSortMode) > key_val && key_val > 0.0) {
                sessionData[j + 1] = sessionData[j];
                j = j - 1;
            }
        }
        sessionData[j + 1] = key;
    }

    // Calculate "Other" for the live waterfall chart
    sortOtherBytes = liveOtherBytes; 
    for(int i = 6; i < sortMacCount; i++) {
        sortOtherBytes += (sortData[i].tx_bytes + sortData[i].rx_bytes);
    }

    // Attempt Vendor Resolution
    for(int i = 0; i < 10 && i < sortMacCount; i++) resolveMacVendor(&sortData[i]);
    for(int i = 0; i < 10 && i < sessionMacCount; i++) resolveMacVendor(&sessionData[i]);
}

void processBleData() {
    memcpy(sortBleData, (void*)liveBleData, sizeof(liveBleData));
    sortBleCount = liveBleCount;

    for (int i = 0; i < liveBleCount; i++) {
        bool found = false;
        float rawDistance = calculateRfDistance(liveBleData[i].rssi, liveBleData[i].txPower, RADIO_BLE_24GHZ);
        
        for (int j = 0; j < sessionBleCount; j++) {
            if (memcmp(sessionBleData[j].mac, (void*)(uint8_t*)liveBleData[i].mac, 6) == 0) {
                sessionBleData[j].hits += liveBleData[i].hits;
                sessionBleData[j].rssi = liveBleData[i].rssi;
                sessionBleData[j].txPower = liveBleData[i].txPower; 
                sessionBleData[j].lastSeen = liveBleData[i].lastSeen;

                if (rawDistance > 0) {
                    sessionBleData[j].smoothedDistance = (0.2 * rawDistance) + (0.8 * sessionBleData[j].smoothedDistance);
                }

                if (liveBleData[i].name[0] != '\0') {
                    strncpy((char*)sessionBleData[j].name, (char*)liveBleData[i].name, 24);
                    sessionBleData[j].name[24] = '\0'; 
                }
                
                if (liveBleData[i].trackerType != TRACKER_NONE) sessionBleData[j].trackerType = liveBleData[i].trackerType;
                if (liveBleData[i].appearanceId != 0) sessionBleData[j].appearanceId = liveBleData[i].appearanceId;
                if (liveBleData[i].serviceId != 0) sessionBleData[j].serviceId = liveBleData[i].serviceId;

                found = true;
                break;
            }
        }

        if (!found) {
            int targetIndex = 0;

            if (sessionBleCount < MAX_BLE_DEVICES) {
                targetIndex = sessionBleCount;
                sessionBleCount++;
            } else {
                uint32_t oldestTime = 0xFFFFFFFF; 
                for (int k = 0; k < MAX_BLE_DEVICES; k++) {
                    if (sessionBleData[k].lastSeen < oldestTime) {
                        oldestTime = sessionBleData[k].lastSeen;
                        targetIndex = k;
                    }
                }
            }

            memcpy((void*)&sessionBleData[targetIndex], (void*)&liveBleData[i], sizeof(BLERecord));
            sessionBleData[targetIndex].smoothedDistance = (rawDistance > 0) ? rawDistance : 0.0;
        }
    }

    memset((void*)liveBleData, 0, sizeof(liveBleData));
    liveBleCount = 0;

    // --- FAST INSERTION SORT: BLE SNAPSHOT ---
    for (int i = 1; i < sortBleCount; i++) {
        BLERecord key = sortBleData[i];
        double key_val = getBleSortMetric(key, currentBleSortMode);
        int j = i - 1;

        if (sort_descending) {
            while (j >= 0 && getBleSortMetric(sortBleData[j], currentBleSortMode) < key_val) {
                sortBleData[j + 1] = sortBleData[j];
                j = j - 1;
            }
        } else {
            while (j >= 0 && getBleSortMetric(sortBleData[j], currentBleSortMode) > key_val && key.hits > 0) {
                sortBleData[j + 1] = sortBleData[j];
                j = j - 1;
            }
        }
        sortBleData[j + 1] = key;
    }

    // --- FAST INSERTION SORT: BLE SESSION ---
    for (int i = 1; i < sessionBleCount; i++) {
        BLERecord key = sessionBleData[i];
        double key_val = getBleSortMetric(key, currentBleSortMode);
        int j = i - 1;

        if (sort_descending) {
            while (j >= 0 && getBleSortMetric(sessionBleData[j], currentBleSortMode) < key_val) {
                sessionBleData[j + 1] = sessionBleData[j];
                j = j - 1;
            }
        } else {
            while (j >= 0 && getBleSortMetric(sessionBleData[j], currentBleSortMode) > key_val && key.hits > 0) {
                sessionBleData[j + 1] = sessionBleData[j];
                j = j - 1;
            }
        }
        sessionBleData[j + 1] = key;
    }
}

void processApData() {
    //memcpy((void*)sortApData, (void*)liveApData, sizeof(liveApData));
    //sortApCount = liveApCount;
    sortApCount = 0;
    for (int i = 0; i < liveApCount; i++) {
        // Only push APs to the temporal legend/waterfall if they moved actual data in this cycle
        if (liveApData[i].tx_bytes + liveApData[i].rx_bytes > 0) {
            // Safely cast away volatile using memcpy for the single struct
            memcpy((void*)&sortApData[sortApCount], (void*)&liveApData[i], sizeof(ApRecord));
            sortApCount++;
        }
    }
    
    for (int i = 0; i < liveApCount; i++) {
        bool found = false;
        float rawDistance = calculateRfDistance(liveApData[i].rssi, 0, RADIO_WIFI_24GHZ);

        for (int j = 0; j < sessionApCount; j++) {
            if (memcmp(sessionApData[j].bssid, (void*)liveApData[i].bssid, 6) == 0) {
                sessionApData[j].packets += liveApData[i].packets;
                sessionApData[j].tx_bytes += liveApData[i].tx_bytes;
                sessionApData[j].rx_bytes += liveApData[i].rx_bytes;
                sessionApData[j].sum_bytes += liveApData[i].sum_bytes;
                sessionApData[j].sum_sq_bytes += liveApData[i].sum_sq_bytes;
                
                sessionApData[j].last_seen = liveApData[i].last_seen;
                sessionApData[j].rssi = liveApData[i].rssi;
                if (liveApData[i].rssi_min < sessionApData[j].rssi_min || sessionApData[j].rssi_min == 0) {
                    sessionApData[j].rssi_min = liveApData[i].rssi_min;
                }
                if (liveApData[i].rssi_max > sessionApData[j].rssi_max || sessionApData[j].rssi_max == 0) {
                    sessionApData[j].rssi_max = liveApData[i].rssi_max;
                }
                sessionApData[j].channel = liveApData[i].channel;
                if (sessionApData[j].country[0] == '\0' && liveApData[i].country[0] != '\0') {
                    sessionApData[j].country[0] = liveApData[i].country[0];
                    sessionApData[j].country[1] = liveApData[i].country[1];
                    sessionApData[j].country[2] = '\0';
                }
                
                if (liveApData[i].max_rate > sessionApData[j].max_rate) {
                    sessionApData[j].max_rate = liveApData[i].max_rate;
                }
                
                if (rawDistance > 0) {
                    sessionApData[j].smoothedDistance = (0.2 * rawDistance) + (0.8 * sessionApData[j].smoothedDistance);
                }
                
                if (strcmp(sessionApData[j].ssid, "<UNKNOWN>") == 0 && strcmp((char*)liveApData[i].ssid, "<UNKNOWN>") != 0) {
                    strlcpy((char*)sessionApData[j].ssid, (char*)liveApData[i].ssid, sizeof(sessionApData[j].ssid));
                }
                sessionApData[j].has_clone = liveApData[i].has_clone;
                found = true; break;
            }
        }
        
        if (!found) {
            int targetIndex = -1;

            if (sessionApCount < MAX_AP_RECORDS) {
                targetIndex = sessionApCount;
                sessionApCount++;
            } else {
                unsigned long now = millis();
                int stalest_idx = 0;
                int weakest_idx = 0;
                unsigned long oldest_time = 0xFFFFFFFF;
                int lowest_rssi = 127;

                for (int k = 0; k < MAX_AP_RECORDS; k++) {
                    if (sessionApData[k].last_seen < oldest_time) {
                        oldest_time = sessionApData[k].last_seen;
                        stalest_idx = k;
                    }
                    if (sessionApData[k].rssi < lowest_rssi) {
                        lowest_rssi = sessionApData[k].rssi;
                        weakest_idx = k;
                    }
                }

                if ((now - oldest_time) > 60000) targetIndex = stalest_idx;
                else if (liveApData[i].rssi > lowest_rssi) targetIndex = weakest_idx;
            }

            if (targetIndex != -1) {
                memcpy((void*)&sessionApData[targetIndex], (void*)&liveApData[i], sizeof(ApRecord));
                sessionApData[targetIndex].smoothedDistance = (rawDistance > 0) ? rawDistance : 0.0;
            }
        }
    }
    
    // Clear the traffic counters, but PRESERVE THE DICTIONARY!
    for (int i = 0; i < liveApCount; i++) {
        liveApData[i].packets = 0;
        liveApData[i].tx_bytes = 0;
        liveApData[i].rx_bytes = 0;
        liveApData[i].sum_bytes = 0;
        liveApData[i].sum_sq_bytes = 0;
    }
    
    // --- FAST INSERTION SORT: AP SNAPSHOT ---
    for (int i = 1; i < sortApCount; i++) {
        ApRecord key = sortApData[i];
        double key_val = getSortMetric(key, currentSortMode);
        int j = i - 1;
        
        if (sort_descending) {
            while (j >= 0 && getSortMetric(sortApData[j], currentSortMode) < key_val) {
                sortApData[j + 1] = sortApData[j];
                j = j - 1;
            }
        } else {
            while (j >= 0 && getSortMetric(sortApData[j], currentSortMode) > key_val && key_val > 0.0) {
                sortApData[j + 1] = sortApData[j];
                j = j - 1;
            }
        }
        sortApData[j + 1] = key;
    }

    // --- FAST INSERTION SORT: AP SESSION ---
    for (int i = 1; i < sessionApCount; i++) {
        ApRecord key = sessionApData[i];
        double key_val = getSortMetric(key, currentSortMode);
        int j = i - 1;

        if (sort_descending) {
            while (j >= 0 && getSortMetric(sessionApData[j], currentSortMode) < key_val) {
                sessionApData[j + 1] = sessionApData[j];
                j = j - 1;
            }
        } else {
            while (j >= 0 && getSortMetric(sessionApData[j], currentSortMode) > key_val && key_val > 0.0) {
                sessionApData[j + 1] = sessionApData[j];
                j = j - 1;
            }
        }
        sessionApData[j + 1] = key;
    }
    
    sortOtherBytes = 0; 
    for(int i = 8; i < sortApCount; i++) {
        sortOtherBytes += (sortApData[i].tx_bytes + sortApData[i].rx_bytes);
    }
}

void processChannelData() {
    memcpy((void*)sortChannelData, (void*)liveChannelData, sizeof(liveChannelData));
    sortChannelCount = liveChannelCount;
    
    for (int i = 0; i < liveChannelCount; i++) {
        bool found = false;
        for (int j = 0; j < sessionChannelCount; j++) {
            if (sessionChannelData[j].channel == liveChannelData[i].channel) {
                sessionChannelData[j].packets += liveChannelData[i].packets;
                sessionChannelData[j].tx_bytes += liveChannelData[i].tx_bytes;
                sessionChannelData[j].rx_bytes += liveChannelData[i].rx_bytes;
                sessionChannelData[j].sum_bytes += liveChannelData[i].sum_bytes;
                sessionChannelData[j].sum_sq_bytes += liveChannelData[i].sum_sq_bytes;
                sessionChannelData[j].last_seen = liveChannelData[i].last_seen;
                
                sessionChannelData[j].avg_rssi = liveChannelData[i].avg_rssi;
                sessionChannelData[j].ema_variance = liveChannelData[i].ema_variance;
                sessionChannelData[j].prev_rssi = liveChannelData[i].prev_rssi;
                sessionChannelData[j].ema_cov = liveChannelData[i].ema_cov;
                
                found = true; break;
            }
        }
        
        if (!found && sessionChannelCount < MAX_CHANNEL_RECORDS) {
            memcpy((void*)&sessionChannelData[sessionChannelCount], (void*)&liveChannelData[i], sizeof(ChannelRecord));
            sessionChannelCount++;
        }
    }
    
    for (int i = 0; i < liveChannelCount; i++) {
        liveChannelData[i].packets = 0;
        liveChannelData[i].tx_bytes = 0;
        liveChannelData[i].rx_bytes = 0;
        liveChannelData[i].sum_bytes = 0;
        liveChannelData[i].sum_sq_bytes = 0;
    }
    
    // --- DYNAMIC INSERTION SORT: CHANNEL SNAPSHOT ---
    for (int i = 1; i < sortChannelCount; i++) {
        ChannelRecord key = sortChannelData[i];
        double key_val = getChannelMetric(key, currentSortMode);
        int j = i - 1;
        
        if (sort_descending) {
            while (j >= 0 && getChannelMetric(sortChannelData[j], currentSortMode) < key_val) {
                sortChannelData[j + 1] = sortChannelData[j];
                j = j - 1;
            }
        } else {
            while (j >= 0 && getChannelMetric(sortChannelData[j], currentSortMode) > key_val && key_val != 0) {
                sortChannelData[j + 1] = sortChannelData[j];
                j = j - 1;
            }
        }
        sortChannelData[j + 1] = key;
    }

    // --- DYNAMIC INSERTION SORT: CHANNEL SESSION ---
    for (int i = 1; i < sessionChannelCount; i++) {
        ChannelRecord key = sessionChannelData[i];
        double key_val = getChannelMetric(key, currentSortMode);
        int j = i - 1;
        
        if (sort_descending) {
            while (j >= 0 && getChannelMetric(sessionChannelData[j], currentSortMode) < key_val) {
                sessionChannelData[j + 1] = sessionChannelData[j];
                j = j - 1;
            }
        } else {
            while (j >= 0 && getChannelMetric(sessionChannelData[j], currentSortMode) > key_val && key_val != 0) {
                sessionChannelData[j + 1] = sessionChannelData[j];
                j = j - 1;
            }
        }
        sessionChannelData[j + 1] = key;
    }
            
    sortOtherBytes = 0; 
    for(int i = 6; i < sortChannelCount; i++) {
        sortOtherBytes += (sortChannelData[i].tx_bytes + sortChannelData[i].rx_bytes);
    }
}

void drawWaterfallChart() {
    // 1. Gate the legends
    if (currentRadioMode != RADIO_LAYER2) {
        drawTemporalLegend();
        drawPersistentTopN();
    }

    int chart_area_height = CHART_BOTTOM - chart_start_y;
    
    // FIX 3: Use the exact same 3/4 split for ALL modes to keep the bottom graph height identical
    int split_y = chart_start_y + (chart_area_height * 3) / 4; 
    
    int ERASER_WIDTH = 44;

    // 3. Adjust the eraser to ONLY clear the bottom pane in L2 mode
    int clear_start_y = (currentRadioMode == RADIO_LAYER2) ? (split_y + 1) : (chart_start_y + 1);
    int clear_height = CHART_BOTTOM - clear_start_y;
    
    // Pure wipe logic (using dynamic clear_start_y and clear_height)
    if (current_x + ERASER_WIDTH <= 480) {
        tft.fillRect(current_x, clear_start_y, ERASER_WIDTH, clear_height, TFT_BLACK);
    } else {
        int w1 = 480 - current_x;
        tft.fillRect(current_x, clear_start_y, w1, clear_height, TFT_BLACK);
        tft.fillRect(0, clear_start_y, ERASER_WIDTH - w1, clear_height, TFT_BLACK);
    }

    // X-Axis Time Ticks
    if (current_x % 60 == 0) {
        tft.drawLine(current_x, split_y - 3, current_x, split_y + 3, COLOR_HOT_CHEST);
        tft.drawLine(current_x + 1, split_y - 3, current_x + 1, split_y + 3, COLOR_HOT_CHEST);
    } else {
        tft.drawPixel(current_x, split_y, COLOR_HOT_CHEST);
        tft.drawPixel(current_x + 1, split_y, COLOR_HOT_CHEST);
    }

    int current_y = split_y - 1; 
    uint32_t current_total_metric = 0;

    // --- CHART PLOTTING ---
    if (currentRadioMode == RADIO_WIFI) {
        uint32_t total_bytes = sortOtherBytes;
        for(int i = 0; i < 6 && i < sortMacCount; i++) total_bytes += (sortData[i].tx_bytes + sortData[i].rx_bytes);
        current_total_metric = total_bytes; 

        if (total_bytes > 0) {
            double log_total = 0;
            if (useLogScale) {
                for(int j = 0; j < 6 && j < sortMacCount; j++) {
                    uint32_t device_total = sortData[j].tx_bytes + sortData[j].rx_bytes;
                    log_total += log10((double)device_total + 1.0);
                }
                log_total += log10((double)sortOtherBytes + 1.0);
            }

            for(int i = 0; i < 6 && i < sortMacCount; i++) {
                double fraction;
                uint32_t current_device_bytes = sortData[i].tx_bytes + sortData[i].rx_bytes;

                if (useLogScale) fraction = log10((double)current_device_bytes + 1.0) / log_total;
                else fraction = (double)current_device_bytes / (double)total_bytes;

                int bar_height = (int)(fraction * (split_y - chart_start_y - 1));
                if (bar_height > (split_y - chart_start_y - 1)) bar_height = split_y - chart_start_y - 1;

                tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);
                current_y -= bar_height;
            }

            if (sortOtherBytes > 0 && current_y > chart_start_y) {
                tft.drawLine(current_x, current_y, current_x, chart_start_y + 1, colors[8]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, chart_start_y + 1, colors[8]);
            } else if (sortOtherBytes == 0 && current_y > chart_start_y && sortMacCount > 0) {
                tft.drawLine(current_x, current_y, current_x, chart_start_y + 1, colors[sortMacCount - 1]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, chart_start_y + 1, colors[sortMacCount - 1]);
            }
        }
    }
    else if (currentRadioMode == RADIO_BLE) {
        uint32_t total_hits = 0;
        uint32_t other_hits = 0;
        int ble_count = (sortBleCount > 6) ? 6 : sortBleCount;

        for(int i = 0; i < ble_count; i++) total_hits += sortBleData[i].hits;
        if (sortBleCount > 6) {
            for (int i = 6; i < sortBleCount; i++) other_hits += sortBleData[i].hits;
            total_hits += other_hits; 
        }
        current_total_metric = total_hits; 

        if (total_hits > 0) {
            double log_total = 0;
            if (useLogScale) {
                for(int j = 0; j < ble_count; j++) log_total += log10((double)sortBleData[j].hits + 1.0);
                if (other_hits > 0) log_total += log10((double)other_hits + 1.0);
            }

            for(int i = 0; i < ble_count; i++) {
                double fraction;
                if (useLogScale) fraction = log10((double)sortBleData[i].hits + 1.0) / log_total;
                else fraction = (double)sortBleData[i].hits / (double)total_hits;
                
                int bar_height = (int)(fraction * (split_y - chart_start_y - 1));
                if (bar_height > (split_y - chart_start_y - 1)) bar_height = split_y - chart_start_y - 1;

                tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);
                current_y -= bar_height;
            }
            
            if (other_hits > 0 && current_y > chart_start_y) {
                tft.drawLine(current_x, current_y, current_x, chart_start_y + 1, colors[8]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, chart_start_y + 1, colors[8]);
            } else if (other_hits == 0 && current_y > chart_start_y && ble_count > 0) {
                tft.drawLine(current_x, current_y, current_x, chart_start_y + 1, colors[ble_count - 1]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, chart_start_y + 1, colors[ble_count - 1]);
            }
        }
    }
    else if (currentRadioMode == RADIO_AP) {
        uint32_t total_bytes = sortOtherBytes;
        for(int i = 0; i < 6 && i < sortApCount; i++) total_bytes += (sortApData[i].tx_bytes + sortApData[i].rx_bytes);
        current_total_metric = total_bytes; 

        if (total_bytes > 0) {
            double log_total = 0;
            if (useLogScale) {
                for(int j = 0; j < 6 && j < sortApCount; j++) {
                    uint32_t device_total = sortApData[j].tx_bytes + sortApData[j].rx_bytes;
                    log_total += log10((double)device_total + 1.0);
                }
                log_total += log10((double)sortOtherBytes + 1.0);
            }

            for(int i = 0; i < 6 && i < sortApCount; i++) {
                double fraction;
                uint32_t current_device_bytes = sortApData[i].tx_bytes + sortApData[i].rx_bytes;
                
                if (useLogScale) fraction = log10((double)current_device_bytes + 1.0) / log_total;
                else fraction = (double)current_device_bytes / (double)total_bytes;

                int bar_height = (int)(fraction * (split_y - chart_start_y - 1));
                if (bar_height > (split_y - chart_start_y - 1)) bar_height = split_y - chart_start_y - 1;

                tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);
                current_y -= bar_height;
            }

            if (sortOtherBytes > 0 && current_y > chart_start_y) {
                tft.drawLine(current_x, current_y, current_x, chart_start_y + 1, colors[8]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, chart_start_y + 1, colors[8]);
            } else if (sortOtherBytes == 0 && current_y > chart_start_y && sortApCount > 0) {
                tft.drawLine(current_x, current_y, current_x, chart_start_y + 1, colors[sortApCount - 1]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, chart_start_y + 1, colors[sortApCount - 1]);
            }
        }
    }
    else if (currentRadioMode == RADIO_CHANNELS) {
        uint32_t total_bytes = sortOtherBytes;
        for(int i = 0; i < 6 && i < sortChannelCount; i++) total_bytes += (sortChannelData[i].tx_bytes + sortChannelData[i].rx_bytes);
        current_total_metric = total_bytes; 

        if (total_bytes > 0) {
            double log_total = 0;
            if (useLogScale) {
                for(int j = 0; j < 6 && j < sortChannelCount; j++) {
                    uint32_t c_total = sortChannelData[j].tx_bytes + sortChannelData[j].rx_bytes;
                    log_total += log10((double)c_total + 1.0);
                }
                log_total += log10((double)sortOtherBytes + 1.0);
            }

            for(int i = 0; i < 6 && i < sortChannelCount; i++) {
                double fraction;
                uint32_t current_c_bytes = sortChannelData[i].tx_bytes + sortChannelData[i].rx_bytes;
                
                if (useLogScale) fraction = log10((double)current_c_bytes + 1.0) / log_total;
                else fraction = (double)current_c_bytes / (double)total_bytes;

                int bar_height = (int)(fraction * (split_y - chart_start_y - 1));
                if (bar_height > (split_y - chart_start_y - 1)) bar_height = split_y - chart_start_y - 1;

                tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);
                current_y -= bar_height;
            }

            if (sortOtherBytes > 0 && current_y > chart_start_y) {
                tft.drawLine(current_x, current_y, current_x, chart_start_y + 1, colors[8]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, chart_start_y + 1, colors[8]);
            } else if (sortOtherBytes == 0 && current_y > chart_start_y && sortChannelCount > 0) {
                tft.drawLine(current_x, current_y, current_x, chart_start_y + 1, colors[sortChannelCount - 1]);
                tft.drawLine(current_x + 1, current_y, current_x + 1, chart_start_y + 1, colors[sortChannelCount - 1]);
            }
        }
    }
    static uint32_t last_rendered_leak_timestamp = 0;
    if (currentRadioMode == RADIO_LAYER2) {
        current_total_metric = l2_bytes_render;
        
        // Redraw only if the newest packet in the buffer has changed
        if (terminal_history[0].meta.timestamp != last_rendered_leak_timestamp && terminal_history[0].meta.timestamp > 0) {
            last_rendered_leak_timestamp = terminal_history[0].meta.timestamp;

            int terminal_start_y = 26;
            tft.fillRect(0, terminal_start_y, 480, split_y - terminal_start_y - 1, TFT_BLACK);
            
            tft.setFreeFont(&UbuntuMono_Regular8pt7b);
            tft.setTextDatum(TL_DATUM);
            
            int cursor_y = terminal_start_y + 4;

// --- PASS 1: figure out which packets actually fit, newest-first ---
int drawIdx[MAX_TERMINAL_LINES];
int drawCount = 0;
{
    int scan_y = cursor_y;
    for (int i = 0; i < MAX_TERMINAL_LINES; i++) {
        if (terminal_history[i].meta.timestamp == 0) continue;

        int pLen = strnlen(terminal_history[i].text, MAX_LEAK_STR_LEN);
        int payload_lines = (pLen > 0) ? ((pLen - 1) / 57) + 1 : 1;
        if (payload_lines > 9) payload_lines = 9;
        int needed = 42 + (payload_lines * 14) + 5; // 3 meta rows + payload + margin

        if (scan_y + needed > split_y) break;
        scan_y += needed;
        drawIdx[drawCount++] = i;
    }
}

// --- PASS 2: draw them oldest-of-the-kept-set first, for the scroll effect ---
for (int k = drawCount - 1; k >= 0; k--) {
    int i = drawIdx[k]; 

                // ==========================================
// LIVE VENDOR LOOKUP — RAM CACHE ONLY
//
// IMPORTANT:
// No leakHistory dependency.
// No SD access.
// No vendor resolution.
// This is strictly an ephemeral fast-path lookup.
// ==========================================

char srcVend[9] = "";
char dstVend[9] = "";

if (!lookupVendorCache(
        terminal_history[i].meta.src_mac,
        srcVend,
        sizeof(srcVend))) {

    strlcpy(srcVend, "Unknown", sizeof(srcVend));
}

if (!lookupVendorCache(
        terminal_history[i].meta.dst_mac,
        dstVend,
        sizeof(dstVend))) {

    strlcpy(dstVend, "Unknown", sizeof(dstVend));
}

                // --- INLINE FORMATTERS ---
// 1. Compact Length (Max 4 chars)
char lenStr[8];
uint16_t fLen = terminal_history[i].meta.frame_length;
if (fLen < 1000) snprintf(lenStr, sizeof(lenStr), "%dB", fLen);
else snprintf(lenStr, sizeof(lenStr), "%dK", fLen / 1000);

// 2. Safe IPv6 Buffers (40 bytes to prevent overflow)
char srcIpRaw[40] = {0}, dstIpRaw[40] = {0};
getIpString(terminal_history[i].meta.ip_version, terminal_history[i].meta.src_ip, srcIpRaw, sizeof(srcIpRaw));
getIpString(terminal_history[i].meta.ip_version, terminal_history[i].meta.dst_ip, dstIpRaw, sizeof(dstIpRaw));

// 3. IPv6 Compression (RFC 5952 longest-run collapse, replaces old sequential strstr/memmove approach)
char srcIpStr[40] = {0}, dstIpStr[40] = {0};
if (terminal_history[i].meta.ip_version == 6) {
    compress_ipv6(srcIpRaw, srcIpStr, sizeof(srcIpStr));
    compress_ipv6(dstIpRaw, dstIpStr, sizeof(dstIpStr));
} else {
    strncpy(srcIpStr, srcIpRaw, sizeof(srcIpStr) - 1);
    strncpy(dstIpStr, dstIpRaw, sizeof(dstIpStr) - 1);
}

                // 4. Fast Live Age Calculator (Seconds Resolution)
                char firstSeenStr[8], lastSeenStr[8], ageCombo[18];
                uint32_t now_ms = millis();
                uint32_t first_sec = (now_ms - terminal_first_seen[i]) / 1000;
                uint32_t last_sec = (now_ms - terminal_history[i].meta.timestamp) / 1000;
                
                if (first_sec < 60) snprintf(firstSeenStr, sizeof(firstSeenStr), "%ds", first_sec);
                else if (first_sec < 3600) snprintf(firstSeenStr, sizeof(firstSeenStr), "%dm", first_sec / 60);
                else snprintf(firstSeenStr, sizeof(firstSeenStr), "%dh", first_sec / 3600);
                
                if (last_sec < 60) snprintf(lastSeenStr, sizeof(lastSeenStr), "%ds", last_sec);
                else if (last_sec < 3600) snprintf(lastSeenStr, sizeof(lastSeenStr), "%dm", last_sec / 60);
                else snprintf(lastSeenStr, sizeof(lastSeenStr), "%dh", last_sec / 3600);
                
                snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr);

                // 5. Fetch Live SSID (Using persistent cache to bypass the union)
                char safeSsid[13] = "Unknown";
                for (int ap = 0; ap < MAX_BSSID_CACHE; ap++) {
                    if (bssidCache[ap].last_seen == 0) continue; // Skip empty slots
                    
                    if (memcmp(terminal_history[i].meta.bssid, bssidCache[ap].bssid, 6) == 0) {
                        strncpy(safeSsid, bssidCache[ap].ssid, 12);
                        safeSsid[12] = '\0';
                        break;
                    }
                }

                // --- ROW 1: [xHit] MAC(Vend)>MAC(Vend)|Len|C ---
                tft.setTextColor(TFT_CYAN);
                char line1[80];
                snprintf(line1, sizeof(line1), "[x%d]%02X%02X%02X%02X%02X%02X(%s)>%02X%02X%02X%02X%02X%02X(%s)|%s|C%d", 
                         terminal_hits[i],
                         terminal_history[i].meta.src_mac[0], terminal_history[i].meta.src_mac[1], terminal_history[i].meta.src_mac[2],
                         terminal_history[i].meta.src_mac[3], terminal_history[i].meta.src_mac[4], terminal_history[i].meta.src_mac[5],
                         srcVend,
                         terminal_history[i].meta.dst_mac[0], terminal_history[i].meta.dst_mac[1], terminal_history[i].meta.dst_mac[2],
                         terminal_history[i].meta.dst_mac[3], terminal_history[i].meta.dst_mac[4], terminal_history[i].meta.dst_mac[5],
                         dstVend, lenStr, terminal_history[i].meta.channel);
                tft.drawString(line1, 4, cursor_y);
                cursor_y += 14; 

                // --- ROW 2: BSSID(SSID)|DIR|SUBTYPE|PROTO|PORTS ---
                tft.setTextColor(TFT_YELLOW);
                char portStr[24] = "";
                if (terminal_history[i].meta.protocol == 6 || terminal_history[i].meta.protocol == 17) {
                    snprintf(portStr, sizeof(portStr), "|%d>%d", terminal_history[i].meta.src_port, terminal_history[i].meta.dst_port);
                }
                char line2[80];
                snprintf(line2, sizeof(line2), "%02X%02X%02X%02X%02X%02X(%s)|%s|%s|%s%s",
                         terminal_history[i].meta.bssid[0], terminal_history[i].meta.bssid[1], terminal_history[i].meta.bssid[2],
                         terminal_history[i].meta.bssid[3], terminal_history[i].meta.bssid[4], terminal_history[i].meta.bssid[5],
                         safeSsid,
                         getDirectionStr(terminal_history[i].meta.direction), 
                         getSubtypeStr(terminal_history[i].meta.frame_subtype),
                         getProtocolStr(terminal_history[i].meta.protocol), portStr);
                tft.drawString(line2, 4, cursor_y);
                cursor_y += 14;

                // --- ROW 3: IP>IP|first/last ---
                tft.setTextColor(TFT_ORANGE);
                char line3[90];
                snprintf(line3, sizeof(line3), "%s>%s|%s",
                         srcIpStr, dstIpStr, ageCombo);
                tft.drawString(line3, 4, cursor_y);
                cursor_y += 14; 

                // --- ROW 4 & 5: PAYLOAD ---
tft.setTextColor(TFT_GREEN);

int pLen = strnlen(terminal_history[i].text, MAX_LEAK_STR_LEN);
const int maxChars = 57; // (460-4)/8
int n_lines = (pLen > 0) ? ((pLen - 1) / maxChars) + 1 : 1;
if (n_lines > 9) n_lines = 9;

char sanitized[MAX_LEAK_STR_LEN + 1] = {0};
memcpy(sanitized, terminal_history[i].text, pLen);
for (int c = 0; c < pLen; c++) {
    if (sanitized[c] < 32 || sanitized[c] > 126) sanitized[c] = '.';
}

for (int line = 0; line < n_lines; line++) {
    char lineBuf[60] = {0};
    int offset = line * maxChars;
    int remaining = pLen - offset;
    int chunk = (remaining < maxChars) ? remaining : maxChars;
    strncpy(lineBuf, sanitized + offset, chunk);
    tft.drawString(lineBuf, 4, cursor_y);
    cursor_y += 14;
}
tft.drawLine(0, cursor_y + 2, 480, cursor_y + 2, COLOR_HOT_CHEST);
cursor_y += 5;
            }
        }
    }

    // --- BOTTOM PANE: SCALING ENGINE ---
    static RadioMode last_seen_mode = currentRadioMode;
    static uint8_t last_seen_bssid[6] = {0}; 
    
    static uint32_t true_max = 10;
    static uint16_t peak_h_index = 0;
    
    bool did_rescale = false; 

    if (currentRadioMode != last_seen_mode || memcmp(target_bssid, last_seen_bssid, 6) != 0) {
        true_max = 10;
        peak_h_index = 0;
        absolute_max_traffic = 10; 
        
        last_seen_mode = currentRadioMode;
        memcpy(last_seen_bssid, target_bssid, 6); 

        memset(traffic_history, 0, sizeof(traffic_history));
        did_rescale = true; 
    }

    int h_index = current_x / 2;
    traffic_history[h_index] = current_total_metric; 

    if (current_total_metric > absolute_max_traffic) {
        true_max = current_total_metric;
        peak_h_index = h_index;
        absolute_max_traffic = current_total_metric + (current_total_metric / 5); 
        did_rescale = true; 
    } else {
        if (current_total_metric > true_max) {
            true_max = current_total_metric;
            peak_h_index = h_index;
        }
        
        if (h_index == peak_h_index && current_total_metric < true_max) {
            true_max = 0;
            for (int i = 0; i < 240; i++) {
                if (traffic_history[i] > true_max) {
                    true_max = traffic_history[i];
                    peak_h_index = i;
                }
            }
            
            uint32_t next_scale = true_max + (true_max / 5);
            if (next_scale < 10) next_scale = 10; 
            
            if (next_scale < absolute_max_traffic) {
                absolute_max_traffic = next_scale;
                did_rescale = true; 
            }
        }
    }

    if (did_rescale) {
        tft.fillRect(0, split_y + 1, 480, CHART_BOTTOM - split_y, TFT_BLACK);
        tft.drawLine(0, split_y, 480, split_y, COLOR_HOT_CHEST);

        for (int c = 0; c < 240; c++) {
            int px = c * 2;
            if (px % 60 == 0) {
                tft.drawLine(px, split_y + 1, px, split_y + 3, COLOR_HOT_CHEST);
                tft.drawLine(px + 1, split_y + 1, px + 1, split_y + 3, COLOR_HOT_CHEST);
            }

            if (traffic_history[c] > 0) {
                int h = (int)(((double)traffic_history[c] / (double)absolute_max_traffic) * (CHART_BOTTOM - split_y - 1));
                if (h > CHART_BOTTOM - split_y - 4) h = CHART_BOTTOM - split_y - 4; 
                
                tft.drawLine(px, CHART_BOTTOM, px, CHART_BOTTOM - h, COLOR_HOT_CHEST);
                tft.drawLine(px + 1, CHART_BOTTOM, px + 1, CHART_BOTTOM - h, COLOR_HOT_CHEST);
            }
        }
    } else {
        if (current_total_metric > 0) {
            int h = (int)(((double)current_total_metric / (double)absolute_max_traffic) * (CHART_BOTTOM - split_y - 1));
            if (h > CHART_BOTTOM - split_y - 4) h = CHART_BOTTOM - split_y - 4; 
            
            tft.drawLine(current_x, CHART_BOTTOM, current_x, CHART_BOTTOM - h, COLOR_HOT_CHEST);
            tft.drawLine(current_x + 1, CHART_BOTTOM, current_x + 1, CHART_BOTTOM - h, COLOR_HOT_CHEST);
        }
    }

    // --- OVERLAYS ---
    // Gate the sweeping vertical lines to ONLY draw in the area below clear_start_y
    tft.drawFastVLine(current_x + 2, clear_start_y, clear_height, COLOR_HOT_CHEST);
    
    if (current_x + ERASER_WIDTH <= 480) {
        tft.drawFastVLine(current_x + ERASER_WIDTH - 1, clear_start_y, clear_height, COLOR_HOT_CHEST);
        tft.drawFastHLine(current_x, split_y, ERASER_WIDTH, COLOR_HOT_CHEST);
    } else {
        int w1 = 480 - current_x;
        tft.drawFastVLine(ERASER_WIDTH - w1 - 1, clear_start_y, clear_height, COLOR_HOT_CHEST);
        tft.drawFastHLine(current_x, split_y, w1, COLOR_HOT_CHEST);
        tft.drawFastHLine(0, split_y, ERASER_WIDTH - w1, COLOR_HOT_CHEST);
    }

    if (current_x <= 480 - ERASER_WIDTH || did_rescale) {
        int text_x = current_x + 6; 
        if (text_x > 480 - 40) text_x = 480 - 40; 

        tft.setFreeFont(&UbuntuMono_Regular8pt7b);
        tft.setTextDatum(TL_DATUM);
        tft.setTextColor(COLOR_HOT_CHEST);

        // Gate the top pane percentages AND the time scale so they don't overwrite L2 text
        if (currentRadioMode != RADIO_LAYER2) {
            tft.drawString("100%", text_x, chart_start_y + 4);
            int mid_y = chart_start_y + ((split_y - chart_start_y) / 2);
            tft.drawString("50%", text_x, mid_y - 6);
            
            if (currentRadioMode == RADIO_BLE || target_locked) tft.drawString("|=1m", text_x, split_y - 15); 
            else tft.drawString("|=2m", text_x, split_y - 15);
        }

        char maxStr[16];
        if (currentRadioMode == RADIO_BLE) {
            snprintf(maxStr, sizeof(maxStr), "%lu", absolute_max_traffic);
        } else {
            if (absolute_max_traffic < 1024) snprintf(maxStr, sizeof(maxStr), "%lu", absolute_max_traffic);
            else if (absolute_max_traffic < 1048576) snprintf(maxStr, sizeof(maxStr), "%luK", absolute_max_traffic / 1024);
            else if (absolute_max_traffic < 1073741824) snprintf(maxStr, sizeof(maxStr), "%luM", absolute_max_traffic / 1048576);
            else snprintf(maxStr, sizeof(maxStr), "%.1fG", (float)absolute_max_traffic / 1073741824.0);
        }
        
        tft.drawString(maxStr, text_x, split_y + 4);
        tft.drawString("0", text_x, CHART_BOTTOM - 12);
    }

    current_x += 2;
    if (current_x >= 480) current_x = 0;
}

void setup() {
  Serial.begin(115200);
  pinMode(15, OUTPUT); digitalWrite(15, HIGH);
  pinMode(21, OUTPUT); digitalWrite(21, HIGH);
  pinMode(5, OUTPUT);  digitalWrite(5, HIGH);

  Serial.printf("[MEM] Static footprint:  %u bytes\n", static_non_union);
Serial.printf("[MEM] Free heap at boot: %u bytes\n", esp_get_free_heap_size());
Serial.printf("[MEM] Free SRAM minimum: %u bytes\n", esp_get_minimum_free_heap_size());
Serial.printf("[MEM] sizeof(LiveCaptureEvent) = %u bytes\n", sizeof(LiveCaptureEvent));   // <-- add here
Serial.printf("[MEM] sizeof(Layer2Capture)    = %u bytes\n", sizeof(Layer2Capture));     // <-- and this one too
Serial.printf(
    "Layer2Capture=%u bytes | leakQueue storage ~%u bytes\n",
    (unsigned)sizeof(Layer2Capture),
    (unsigned)(sizeof(Layer2Capture) * LEAK_QUEUE_DEPTH)
);
initProbeTracker();

// ==========================================
// 1. CREATE THE LAYER 2 QUEUES + TRANSIENT BUFFERS
// ==========================================

// Allocate the two reusable full-payload buffers on the heap.
// These are NOT part of the persistent session union.
ptr_isr_evt = (LiveCaptureEvent*)malloc(sizeof(LiveCaptureEvent));
ptr_core1_evt = (LiveCaptureEvent*)malloc(sizeof(LiveCaptureEvent));

if (ptr_isr_evt == nullptr || ptr_core1_evt == nullptr) {
    Serial.println("FATAL: Failed to allocate transient buffers on heap!");
    while (true) delay(100);
}

// Post-parser queue: ONLY Layer2Capture objects.
leakQueue = xQueueCreate(LEAK_QUEUE_DEPTH, sizeof(Layer2Capture));

if (leakQueue == NULL) {
    Serial.println("[!] FATAL: Failed to create leakQueue!");
}

// Pre-parser queue: ONLY full-payload LiveCaptureEvent objects.
liveDumpQueue = xQueueCreate(
    LIVE_DUMP_QUEUE_DEPTH,
    sizeof(LiveCaptureEvent)
);

if (liveDumpQueue == NULL) {
    Serial.println("[!] FATAL: Failed to create liveDumpQueue!");
}

  // -----------------------------------------------------------

  // ==========================================
  // 2. INITIALIZE DISPLAY
  // ==========================================
  delay(1000);
  tft.init();
  tft.setTouch(calData);
  tft.setRotation(1);
  tft.fillScreen(TFT_BLACK);
  drawChartHeader();
  drawChartFooter();

  // ==========================================
  // 3. INITIALIZE SD CARD (Crucial to do this BEFORE the sniffer starts!)
  // ==========================================
  Serial.println("\n--- Initializing SD Card ---");
  if (!sd.begin(SdSpiConfig(5, SHARED_SPI, SD_SCK_MHZ(4)))) {
    Serial.println("[!] SD Card Mount Failed!");
    sd.initErrorPrint(&Serial);
  } else {
    Serial.println("[*] SD Card mounted successfully.");
    FsFile file = sd.open("/oui_db.txt", O_READ);
    if (!file) {
      Serial.println("[!] Failed to open /oui_db.txt! Check filename.");
    } else {
      Serial.printf("[*] SUCCESS! oui_db.txt found. Size: %llu bytes\n", file.fileSize());
      file.close();
    }
  }
  Serial.println("----------------------------\n");

  // ==========================================
  // 4. SPAWN CORE 1 TASKS (UI & SD Logging)
  // ==========================================
  // We will uncomment this in the next step once we write the task function!
  /*
  xTaskCreatePinnedToCore(
      sdLoggerTask,    // Task function
      "SD_Logger",     // Task name
      8192,            // Stack size (Bytes)
      NULL,            // Parameters
      1,               // Priority (1 is standard for Core 1)
      NULL,            // Task handle
      1                // Pin to Core 1
  );
  */

  // ==========================================
  // 5. TURN ON THE WATER (Start Sniffer)
  // ==========================================
  // The plumbing is fully ready. Open the valve.
  WiFi.mode(WIFI_STA);
  esp_wifi_set_promiscuous(true);
  esp_wifi_set_promiscuous_rx_cb(&sniffer_callback);
  esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);
  Serial.println("[*] Sniffer ISR active.");
}

void loop() {
  // ==========================================
  // BACKGROUND DATA ENGINES (Run every tick)
  // ==========================================
  processPendingVendors();
  runProbeCorrelationEngine(); 
  processLiveDumpQueue();
  processLeakQueue();
  
  uint16_t t_x = 0, t_y = 0;
  bool should_render = false;

  // 1. Check Touch inputs (State Controller)
  if (tft.getTouch(&t_x, &t_y)) {
      should_render = handleTouchInputs(t_x, t_y);
  }
    
  // 2. Run the Channel Hopper
  should_render |= updateRadioHopper();

  // 3. CONTINUOUS DELTA-DRAW: Foxhunt Animation Engine
  // (Must run every loop so the dog keeps walking even if signal is lost)
  if (currentState == SCREEN_FOXHUNT) {
      updateFoxhuntRadar();
  }

  // 4. EVENT-DRIVEN GATE: Heavy Math & Full UI Redraws
  if (should_render) {
    pause_sniffing = true; // Lock the radio buffers

    // --- MATH ENGINES ---
    if (currentRadioMode == RADIO_WIFI) processWifiData();
    else if (currentRadioMode == RADIO_BLE) processBleData();
    else if (currentRadioMode == RADIO_AP) processApData();
    else if (currentRadioMode == RADIO_CHANNELS) processChannelData();
    // --- ADDED LAYER 2 MATH GATE ---
    else if (currentRadioMode == RADIO_LAYER2) {
        // Snapshot the bytes for the UI and reset the ISR counter
        l2_bytes_render = l2_bytes_tick;
        l2_bytes_tick = 0;
        // IF THIS PRINTS '0', THE ISR IS BROKEN. 
        // IF THIS PRINTS '4000', THE CHART GRAPHICS ARE BROKEN.
        Serial.printf("L2 Tick Vol: %u\n", l2_bytes_render);
    }

    pause_sniffing = false; // Unlock immediately!

    // --- FULL REDRAW GRAPHICS ENGINES ---
    if (currentState == SCREEN_CHART) {
        drawWaterfallChart();
    } else if (currentState == SCREEN_DEVICE_LIST) {
        drawDeviceList();
    } else if (currentState == SCREEN_AP_SCAN) {
        drawApScanner();
    } else if (currentState == SCREEN_PROBE_TRACKER) {
        drawProbeTracker();
    } 
    // Do NOT add SCREEN_LEAK_LIST here. It updates itself asynchronously!
    
    Serial.printf("Free Heap: %d bytes\n", ESP.getFreeHeap());
  }
  // ==========================================
    // ASYNCHRONOUS DIAGNOSTICS (Runs every 3 seconds)
    // ==========================================
    static uint32_t last_debug_print = 0;
if (millis() - last_debug_print > 3000) {

    uint32_t isr_att       = leak_isr_attempts;
    uint32_t isr_drop     = leak_isr_dropped;

    uint32_t f_seen       = leak_funnel_seen;
    uint32_t f_suppressed = leak_funnel_suppressed;
    uint32_t f_shipped    = leak_funnel_shipped;
    uint32_t ld_drop      = live_dump_dropped;

    Serial.printf(
        "[DIAG] Funnel: Seen=%u | Suppressed=%u | Shipped=%u\n",
        f_seen,
        f_suppressed,
        f_shipped
    );

    Serial.printf(
        "[DIAG] Drops: liveDumpQueue=%u | "
        "leakQueue ISR=%u/%u | Core1=%u/%u\n",
        ld_drop,
        isr_drop,
        isr_att,
        leak_core1_dropped,
        leak_core1_attempts
    );

    Serial.printf(
        "[DIAG] Free Heap: %d bytes\n",
        ESP.getFreeHeap()
    );

    leak_funnel_seen       = 0;
    leak_funnel_suppressed = 0;
    leak_funnel_shipped    = 0;
    live_dump_dropped      = 0;

    leak_isr_attempts      = 0;
    leak_isr_dropped       = 0;
    leak_core1_attempts    = 0;
    leak_core1_dropped     = 0;

    if (currentState == SCREEN_CHART &&
        currentRadioMode == RADIO_LAYER2) {

        drawTelemetryHeader();
    }

    last_debug_print = millis();
}
}

/*
void setup() {
  Serial.begin(115200);
  pinMode(15, OUTPUT); digitalWrite(15, HIGH);
  pinMode(21, OUTPUT); digitalWrite(21, HIGH);
  pinMode(5, OUTPUT);  digitalWrite(5, HIGH);

  Serial.printf("[MEM] Static footprint:  %u bytes\n", static_non_union);
  Serial.printf("[MEM] Free heap at boot: %u bytes\n", esp_get_free_heap_size());
  Serial.printf("[MEM] Free SRAM minimum: %u bytes\n", 
              esp_get_minimum_free_heap_size());

  initProbeTracker();

  // ==========================================
  // CREATE THE LEAKY LAYER 2 QUEUE
  // ==========================================
  leakQueue = xQueueCreate(10, sizeof(CleartextLeak));
  if (leakQueue == NULL) {
      Serial.println("[!] FATAL: Failed to create leakQueue! Out of heap.");
  } else {
      Serial.println("[*] leakQueue created successfully.");
  }
  // ==========================================

  delay(1000);
  tft.init();
  tft.setTouch(calData);
  tft.setRotation(1);
  tft.fillScreen(TFT_BLACK);
  drawChartHeader();
  drawChartFooter();

  // The water is turned on here, so the queue MUST exist by this point!
  WiFi.mode(WIFI_STA);
  esp_wifi_set_promiscuous(true);
  esp_wifi_set_promiscuous_rx_cb(&sniffer_callback);
  esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);

  Serial.println("\n--- Initializing SD Card ---");
  if (!sd.begin(SdSpiConfig(5, SHARED_SPI, SD_SCK_MHZ(4)))) {
    Serial.println("[!] SD Card Mount Failed!");
    sd.initErrorPrint(&Serial);
  } else {
    Serial.println("[*] SD Card mounted successfully.");
    FsFile file = sd.open("/oui_db.txt", O_READ);
    if (!file) {
      Serial.println("[!] Failed to open /oui_db.txt! Check filename.");
    } else {
      Serial.printf("[*] SUCCESS! oui_db.txt found. Size: %llu bytes\n", file.fileSize());
      file.close();
    }
  }
  Serial.println("----------------------------\n");
}
*/
