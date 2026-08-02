#include <Arduino.h>
#include <WiFi.h>
#include "esp_wifi.h"
#include <TFT_eSPI.h>
#include <SPI.h>
#include "SdFat.h"
#include <NimBLEDevice.h>
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
// LEAKY LAYER 2 GLOBALS
// ==========================================
#define MAX_LEAK_STR_LEN 256

struct CleartextLeak {
    uint32_t timestamp;           // 4 bytes 
    uint16_t src_port;            // 2 bytes
    uint16_t dst_port;            // 2 bytes
    uint8_t ip_version;   // 0 = none, 4 = IPv4, 6 = IPv6
    uint8_t src_ip[16];   // Holds 4 bytes for IPv4, or 16 bytes for IPv6
    uint8_t dst_ip[16];
    uint8_t src_mac[6];           // 6 bytes
    uint8_t dst_mac[6];           // 6 bytes
    uint8_t frame_subtype;        // 1 byte  (e.g., 0x08 for QoS Data)
    uint8_t direction;            // 1 byte  (0=AdHoc, 1=STA->AP, 2=AP->STA, 3=WDS)
    uint8_t channel;              // 1 byte
    uint8_t protocol;             // 1 byte  (e.g., 17 for UDP, 6 for TCP)
    bool is_high_value;           // 1 byte
    char text[MAX_LEAK_STR_LEN];  // N bytes 
}; // (Total adds up perfectly with 1 byte of tail padding depending on string length)

struct LeakHistoryEntry {
    CleartextLeak leak;   // 4-byte aligned
    uint32_t first_seen;  // 4 bytes 
    uint16_t hitCount;    // 2 bytes
    char src_vendor[9];   // 9 bytes (8 chars + null)
    char dst_vendor[9];   // 9 bytes (8 chars + null)
};

#define MAX_LEAK_SLOTS 10
LeakHistoryEntry leakHistory[MAX_LEAK_SLOTS];

// The FreeRTOS Queue to pass data from Core 0 (Sniffer) to Core 1 (Display)
QueueHandle_t leakQueue = NULL;

// De-duplication Hash Ring (Uses exactly 129 bytes of RAM)
uint32_t leak_hash_history[32] = {0};
uint8_t leak_hash_idx = 0;

// Pagination for the Cleartext Leaks UI
uint8_t leak_current_page = 0;

#define SEC_COOLDOWN_MS 5000 // 5 seconds (adjust to your preference)
#define ALERT_CACHE_SIZE 8

struct CryptoAlertCache {
    uint8_t mac_src[6];
    uint8_t mac_dst[6];
    uint32_t last_alert_ms;
};

static CryptoAlertCache crypto_cache[ALERT_CACHE_SIZE];
static uint8_t crypto_cache_idx = 0;

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
        default: return "Reserved";
    }
}

const char* getDirectionStr(uint8_t dir) {
    // dir is derived from (payload[1] & 0x03)
    // Bit 0 = To DS (Upload), Bit 1 = From DS (Download)
    switch(dir) {
        case 0: return "STA<->STA"; // To_DS = 0, From_DS = 0
        case 1: return "STA->AP";   // To_DS = 1, From_DS = 0
        case 2: return "AP->STA";   // To_DS = 0, From_DS = 1
        case 3: return "WDS";       // To_DS = 1, From_DS = 1
        default: return "???";
    }
}

const char* getProtocolStr(uint8_t proto) {
    if (proto == 17) return "UDP";
    if (proto == 6) return "TCP";
    return "RAW";
}

void getIpString(uint8_t version, const uint8_t* ip_bytes, char* out_str, size_t max_len) {
    if (version == 4) {
        snprintf(out_str, max_len, "%d.%d.%d.%d", 
                 ip_bytes[0], ip_bytes[1], ip_bytes[2], ip_bytes[3]);
    } else if (version == 6) {
        // Simplified IPv6 formatting (avoids complex zero-compression logic for speed)
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
enum RadioMode { RADIO_WIFI, RADIO_BLE, RADIO_AP, RADIO_CHANNELS };
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
void drawLeakAlertToTFT(uint8_t* mac, const char* vendor, const char* payload, bool is_high_value); // Good practice to add this one too!

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

// Dynamically determine the true union boundary
constexpr size_t max_size_1 = (ble_size > wifi_size) ? ble_size : wifi_size;
constexpr size_t max_size_2 = (ap_size > channel_size) ? ap_size : channel_size;
constexpr size_t union_size = (max_size_1 > max_size_2) ? max_size_1 : max_size_2;

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
// TFT LEAK ALERT RENDERER
// ==========================================
void drawLeakAlertToTFT(uint8_t* mac, const char* vendor, const char* payload, bool is_high_value) {
    // Save the current text settings if needed
    
    // Draw a prominent alert box
    int box_y = 60; // Adjust based on your chart location
    int box_h = 120;
    
    // Use a red border for high-value targets (HTTP/mDNS), yellow for general leaks
    uint16_t borderColor = is_high_value ? TFT_RED : TFT_YELLOW;
    
    tft.fillRoundRect(10, box_y, 460, box_h, 8, TFT_DARKGREY);
    tft.drawRoundRect(10, box_y, 460, box_h, 8, borderColor);
    
    // Title
    tft.setTextColor(borderColor, TFT_DARKGREY);
    tft.setTextDatum(TC_DATUM);
    tft.drawString("CLEARTEXT LEAK DETECTED", 240, box_y + 10, 2);
    
    // MAC & Vendor
    tft.setTextColor(TFT_WHITE, TFT_DARKGREY);
    tft.setTextDatum(TL_DATUM);
    char macStr[64];
    sprintf(macStr, "SRC: %02X:%02X:%02X:%02X:%02X:%02X (%s)", 
            mac[0], mac[1], mac[2], mac[3], mac[4], mac[5], vendor);
    tft.drawString(macStr, 20, box_y + 35, 2);
    
    // Payload snippet (truncate if too long for screen)
    tft.setTextColor(TFT_GREEN, TFT_DARKGREY);
    char short_payload[60];
    strncpy(short_payload, payload, 59);
    short_payload[59] = '\0'; // Ensure null termination
    tft.drawString(short_payload, 20, box_y + 60, 2);
}

// ==========================================
// CORE 1: LEAK MONITOR TASK
// ==========================================
void leakMonitorTask(void *pvParameters) {
    CleartextLeak leak;
    MacRecord tempRec; // Temporary record for the SD card lookup

    while (true) {
        // Wait indefinitely for a leak to arrive in the queue
        if (xQueueReceive(leakQueue, &leak, portMAX_DELAY)) {
            
            // 1. Prepare the MacRecord and resolve the vendor
            memset(&tempRec, 0, sizeof(MacRecord)); // Clear out old data
            
            // Copy the MAC from the leak into your MacRecord struct
            // CHANGE '.mac' IF YOUR STRUCT USES A DIFFERENT NAME
            memcpy(tempRec.mac, leak.src_mac, 6); 
            
            // Pass the pointer to your resolver
            resolveMacVendor(&tempRec); 
            
            // 2. Dump full details to Serial for debugging
            Serial.println("\n====================================");
            Serial.printf("🚨 CLEARTEXT LEAK 🚨 [%s]\n", leak.is_high_value ? "HIGH VALUE" : "STANDARD");
            
            // CHANGE '.vendor' IF YOUR STRUCT USES A DIFFERENT NAME
            Serial.printf("MAC: %02X:%02X:%02X:%02X:%02X:%02X | Vendor: %s\n",
                          leak.src_mac[0], leak.src_mac[1], leak.src_mac[2],
                          leak.src_mac[3], leak.src_mac[4], leak.src_mac[5], 
                          tempRec.vendor);
                          
            Serial.println("Payload:");
            Serial.println(leak.text);
            Serial.println("====================================\n");

            // 3. Render to the TFT Display
            drawLeakAlertToTFT(leak.src_mac, tempRec.vendor, leak.text, leak.is_high_value);
        }
    }
}

// ==========================================
// CLEARTEXT EXTRACTOR 
// ==========================================
// ---------------------------------------------------------
// CLEARTEXT EXTRACTOR (Aggregator)
// Scans the entire payload, scraping all printable strings.
// Replaces binary gaps and newlines with spaces.
// ---------------------------------------------------------
bool extractCleartext(const uint8_t* payload, uint16_t payload_len, char* output_buffer) {
    uint16_t out_idx = 0;
    uint16_t consecutive_printable = 0;
    uint16_t max_consecutive = 0;

    for (uint16_t i = 0; i < payload_len; i++) {
        char c = (char)payload[i];
        
        // Check for printable ASCII or standard whitespace
        if ((c >= 32 && c <= 126) || c == '\n' || c == '\t' || c == '\r') {
            if (out_idx < (MAX_LEAK_STR_LEN - 1)) {
                // Flatten newlines and tabs to spaces for clean TFT rendering
                if (c == '\n' || c == '\r' || c == '\t') {
                    c = ' ';
                }
                output_buffer[out_idx++] = c;
            }
            
            consecutive_printable++;
            if (consecutive_printable > max_consecutive) {
                max_consecutive = consecutive_printable;
            }
        } else {
            // Binary byte hit. Reset the streak counter.
            consecutive_printable = 0;
            
            // Insert a single space to cleanly separate different text chunks
            if (out_idx > 0 && output_buffer[out_idx - 1] != ' ' && out_idx < (MAX_LEAK_STR_LEN - 1)) {
                output_buffer[out_idx++] = ' ';
            }
        }
        
        // If we filled the buffer, stop scanning
        if (out_idx >= (MAX_LEAK_STR_LEN - 1)) break;
    }
    
    output_buffer[out_idx] = '\0'; 
    
    // Return true only if we found at least one chunk of 10+ characters
    return (max_consecutive >= 10);
}
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

        // 3. Format it
        snprintf(out_text, max_len, "NetBIOS: %s [%s]", cleanName, serviceType);
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
    
    // Loop one extra time with a virtual 0-byte to force the final string to process
    for (int i = 0; i <= length; i++) {
        char c = (i < length) ? payload[i] : 0; 
        
        if (c >= 32 && c <= 126) { // Printable ASCII
            if (cur_l == 0) cur_s = i;
            cur_l++;
        } else {
            // Python equivalent of re.findall(rb"[ -~]{5,}")
            if (cur_l >= 5) { 
                char temp[64] = {0};
                int copy_len = std::min(cur_l, 63);
                memcpy(temp, &payload[cur_s], copy_len);
                
                // 1. Filter out boilerplate MAILSLOT / BROWSE headers
                if (!strstr(temp, "MAILSLOT") && !strstr(temp, "BROWSE")) {
                    
                    // 2. Filter out raw A-P encoded blobs (length >= 16 of just A-P)
                    bool is_ap_blob = (cur_l >= 16);
                    for (int j = 0; j < copy_len && is_ap_blob; j++) {
                        if (temp[j] < 'A' || temp[j] > 'P') is_ap_blob = false;
                    }
                    
                    // 3. Deduplicate (ensure we haven't already added this exact name)
                    if (!is_ap_blob && !strstr(out_text, temp)) {
                        if (written < max_len) {
                            // Append it to our growing string with a separator!
                            written += snprintf(out_text + written, max_len - written, " [%s]", temp);
                            found_any = true;
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
// DHCPv4 (IPv4) PARSER
// Extracts Message Type, Primary DNS, and highest-value text 
// Priority: FQDN > Hostname > Domain > Vendor > Fallback ASCII
// ---------------------------------------------------------
bool parse_dhcp_v4(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length <= 240) return false;
    
    // Check for standard DHCP Magic Cookie
    if (payload[236] == 0x63 && payload[237] == 0x82 && 
        payload[238] == 0x53 && payload[239] == 0x63) {
        
        int offset = 240;
        
        const char* msg_type_str = "UNK";
        const char* text_prefix = nullptr;
        const uint8_t* text_ptr = nullptr;
        int text_len = 0;
        int current_priority = 99; 
        
        const uint8_t* dns_ptr = nullptr;

        // --- PASS 1: Extract Options ---
        while (offset < length && payload[offset] != 255) { // 255 is End Option
            uint8_t opt_type = payload[offset];
            if (opt_type == 0) { offset++; continue; } // Pad Option
            
            if (offset + 1 >= length) break;
            uint8_t opt_len = payload[offset + 1];
            if (offset + 2 + opt_len > length) break; // Truncated packet
            
            int opt_data_offset = offset + 2;
            int opt_data_len = opt_len;
            int this_priority = 99;
            const char* this_prefix = nullptr;

            // 1. Message Type (Option 53)
            if (opt_type == 53 && opt_len == 1) {
                switch (payload[opt_data_offset]) {
                    case 1: msg_type_str = "DISCOVER"; break;
                    case 2: msg_type_str = "OFFER"; break;
                    case 3: msg_type_str = "REQUEST"; break;
                    case 4: msg_type_str = "DECLINE"; break;
                    case 5: msg_type_str = "ACK"; break;
                    case 6: msg_type_str = "NAK"; break;
                    case 7: msg_type_str = "RELEASE"; break;
                    case 8: msg_type_str = "INFORM"; break;
                }
            }
            // 2. DNS Servers (Option 6)
            else if (opt_type == 6 && opt_len >= 4) {
                dns_ptr = &payload[opt_data_offset]; // Grab the first IP
            }
            // 3. Text Fields (Ranked by Priority)
            else if (opt_type == 81 && opt_len > 3) {
                this_priority = 1; this_prefix = "FQDN:"; 
                opt_data_offset += 3; opt_data_len -= 3; // Skip RCODE
            }
            else if (opt_type == 12) { this_priority = 2; this_prefix = "Host:"; }
            else if (opt_type == 15) { this_priority = 3; this_prefix = "Domain:"; }
            else if (opt_type == 60) { this_priority = 4; this_prefix = "Vendor:"; }
            
            // Save if it's the most valuable text we've seen so far
            if (this_priority < current_priority && opt_data_len > 0) {
                current_priority = this_priority;
                text_prefix = this_prefix;
                text_ptr = &payload[opt_data_offset];
                text_len = opt_data_len;
            }
            
            offset += 2 + opt_len;
        }

        // --- PASS 2: ASCII Fallback ---
        // If we found NO text options, scan remainder for generic ASCII strings
        if (text_ptr == nullptr) {
            int best_start = 0, best_len = 0, cur_start = 0, cur_len = 0;
            for (int i = 240; i < length; i++) {
                char c = payload[i];
                if (c >= 32 && c <= 126) { 
                    if (cur_len == 0) cur_start = i;
                    cur_len++;
                    if (cur_len > best_len) { best_len = cur_len; best_start = cur_start; }
                } else { cur_len = 0; }
            }
            if (best_len >= 6) {
                text_prefix = "Str:";
                text_ptr = &payload[best_start];
                text_len = best_len;
            }
        }

        // --- STRING ASSEMBLY ---
        // If we found ANYTHING of value, compile the final string
        if (text_ptr != nullptr || dns_ptr != nullptr) {
            int written = snprintf(out_text, max_len, "DHCP [%s]", msg_type_str);
            
            if (text_ptr != nullptr && written < max_len) {
                written += snprintf(out_text + written, max_len - written, " %s %.*s", 
                                    text_prefix, text_len, text_ptr);
            }
            
            if (dns_ptr != nullptr && written < max_len) {
                snprintf(out_text + written, max_len - written, " DNS: %d.%d.%d.%d", 
                         dns_ptr[0], dns_ptr[1], dns_ptr[2], dns_ptr[3]);
            }
            return true;
        }
    }
    return false;
}

// ---------------------------------------------------------
// DHCPv6 (IPv6) PARSER
// Extracts Message Type and highest-value text (FQDN > Vendor > ASCII)
// ---------------------------------------------------------
bool parse_dhcp_v6(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length < 4) return false; // Needs 1 byte msg type, 3 byte transaction ID
    
    // 1. Message Type
    uint8_t msg_type = payload[0];
    const char* msg_type_str = "UNK";
    switch (msg_type) {
        case 1: msg_type_str = "SOLICIT"; break;
        case 2: msg_type_str = "ADVERT"; break;
        case 3: msg_type_str = "REQUEST"; break;
        case 4: msg_type_str = "CONFIRM"; break;
        case 5: msg_type_str = "RENEW"; break;
        case 7: msg_type_str = "REPLY"; break;
        case 8: msg_type_str = "RELEASE"; break;
        case 11: msg_type_str = "INFO-REQ"; break;
    }

    int offset = 4;
    int current_priority = 99;
    const char* text_prefix = nullptr;
    int best_text_start = 0;
    int best_text_len = 0;

    // --- PASS 1: Extract Options ---
    while (offset + 4 <= length) {
        // DHCPv6 uses 16-bit Type and 16-bit Length fields (Big Endian)
        uint16_t opt_code = (payload[offset] << 8) | payload[offset + 1];
        uint16_t opt_len = (payload[offset + 2] << 8) | payload[offset + 3];
        offset += 4;
        
        if (offset + opt_len > length) break; // Truncated packet
        
        int this_priority = 99;
        const char* this_prefix = nullptr;

        if (opt_code == 39) { this_priority = 1; this_prefix = "FQDN:"; }
        else if (opt_code == 16) { this_priority = 2; this_prefix = "Vendor:"; }

        // If it's a high-value option, find the longest ASCII substring inside it
        if (this_priority < current_priority) {
            int cur_s = 0, cur_l = 0, max_s = 0, max_l = 0;
            for (int i = 0; i < opt_len; i++) {
                char c = payload[offset + i];
                if (c >= 32 && c <= 126) {
                    if (cur_l == 0) cur_s = offset + i;
                    cur_l++;
                    if (cur_l > max_l) { max_l = cur_l; max_s = cur_s; }
                } else { cur_l = 0; }
            }
            
            if (max_l >= 3) { // Require at least 3 chars
                current_priority = this_priority;
                text_prefix = this_prefix;
                best_text_start = max_s;
                best_text_len = max_l;
            }
        }
        offset += opt_len; // Jump to next option
    }

    // --- PASS 2: ASCII Fallback ---
    if (text_prefix == nullptr) {
        int cur_s = 0, cur_l = 0, max_s = 0, max_l = 0;
        for (int i = 4; i < length; i++) { // Sweep entire packet after header
            char c = payload[i];
            if (c >= 32 && c <= 126) {
                if (cur_l == 0) cur_s = i;
                cur_l++;
                if (cur_l > max_l) { max_l = cur_l; max_s = cur_s; }
            } else { cur_l = 0; }
        }
        if (max_l >= 6) {
            text_prefix = "Str:";
            best_text_start = max_s;
            best_text_len = max_l;
        }
    }

    // --- STRING ASSEMBLY ---
    if (text_prefix != nullptr) {
        snprintf(out_text, max_len, "DHCPv6 [%s] %s %.*s", 
                 msg_type_str, text_prefix, best_text_len, &payload[best_text_start]);
        return true;
    }

    return false;
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

// ---------------------------------------------------------
// SSDP VERBOSE PARSER (Port 1900)
// Extracts First Line, HOST, NT/ST, SERVER, USN, LOCATION, CACHE
// Requires MAX_LEAK_STR_LEN to be at least 256
// ---------------------------------------------------------
bool parse_ssdp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length < 15) return false;

    // Small stack buffers for each header (limits prevent buffer overflows)
    char first_line[32] = {0};
    char host[24] = {0};
    char target_key[4] = "TGT";
    char target_val[64] = {0};
    char server[64] = {0};
    char usn[64] = {0};
    char location[64] = {0};
    char cache_control[24] = {0};

    const char* p = (const char*)payload;
    const char* end = p + length;

    // 1. Grab First Line (e.g., "NOTIFY * HTTP/1.1")
    const char* line_end = (const char*)memchr(p, '\n', end - p);
    if (!line_end) line_end = end;
    int len = line_end - p;
    if (len > 0 && *(line_end - 1) == '\r') len--;
    memcpy(first_line, p, std::min(len, 31));
    p = line_end + 1;

    // 2. Parse Headers
    while (p < end) {
        line_end = (const char*)memchr(p, '\n', end - p);
        if (!line_end) line_end = end;
        len = line_end - p;
        if (len > 0 && *(line_end - 1) == '\r') len--;

        if (len > 0) {
            const char* colon = (const char*)memchr(p, ':', len);
            if (colon) {
                int k_len = colon - p;
                const char* v = colon + 1;
                int v_len = len - (k_len + 1);
                
                // Trim leading spaces from the value
                while (v_len > 0 && *v == ' ') { v++; v_len--; }

                // Case-insensitive header matching
                if (k_len == 4 && strncasecmp(p, "HOST", 4) == 0) {
                    memcpy(host, v, std::min(v_len, 23));
                } else if (k_len == 2 && (strncasecmp(p, "NT", 2) == 0 || strncasecmp(p, "ST", 2) == 0)) {
                    memcpy(target_key, p, 2); target_key[2] = '\0';
                    memcpy(target_val, v, std::min(v_len, 63));
                } else if ((k_len == 6 && strncasecmp(p, "SERVER", 6) == 0) || 
                           (k_len == 10 && strncasecmp(p, "USER-AGENT", 10) == 0)) {
                    if (server[0] == '\0') memcpy(server, v, std::min(v_len, 63));
                } else if (k_len == 3 && strncasecmp(p, "USN", 3) == 0) {
                    memcpy(usn, v, std::min(v_len, 63));
                } else if ((k_len == 8 && strncasecmp(p, "LOCATION", 8) == 0) || 
                           (k_len >= 14 && strncasecmp(p, "SECURELOCATION", 14) == 0)) {
                    if (location[0] == '\0') memcpy(location, v, std::min(v_len, 63));
                } else if (k_len == 13 && strncasecmp(p, "CACHE-CONTROL", 13) == 0) {
                    memcpy(cache_control, v, std::min(v_len, 23));
                }
            }
        }
        p = line_end + 1;
    }

    // 3. UI Optimization: Strip redundant UPnP prefixes
    char* clean_target = target_val;
    if (strncmp(target_val, "urn:schemas-upnp-org:device:", 28) == 0) clean_target += 28;
    else if (strncmp(target_val, "urn:schemas-upnp-org:service:", 29) == 0) clean_target += 29;

    // 4. Assemble the multiline string exactly as requested
    int written = snprintf(out_text, max_len, "%s", first_line);
    if (host[0]) written += snprintf(out_text + written, max_len - written, " | HOST=%s", host);
    if (clean_target[0]) written += snprintf(out_text + written, max_len - written, " | %s=%s", target_key, clean_target);
    
    if (server[0]) written += snprintf(out_text + written, max_len - written, "\n    SERVER=%s", server);
    if (usn[0]) written += snprintf(out_text + written, max_len - written, "\n    USN=%s", usn);
    
    if (location[0] || cache_control[0]) {
        written += snprintf(out_text + written, max_len - written, "\n   ");
        if (location[0]) written += snprintf(out_text + written, max_len - written, " LOCATION=%s", location);
        if (location[0] && cache_control[0]) written += snprintf(out_text + written, max_len - written, " |");
        if (cache_control[0]) written += snprintf(out_text + written, max_len - written, " CACHE-CONTROL=%s", cache_control);
    }

    return true;
}

// ---------------------------------------------------------
// LLMNR PARSER (Port 5355)
// Extracts Windows local network name resolution queries
// ---------------------------------------------------------
bool parse_llmnr(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    if (length < 12) return false; // Standard DNS header is 12 bytes

    uint16_t flags = (payload[2] << 8) | payload[3];
    bool is_response = (flags & 0x8000) != 0; // Check the QR bit (Query vs Response)
    uint16_t qdcount = (payload[4] << 8) | payload[5];

    // We primarily care about the Question section (what name are they looking for?)
    if (qdcount > 0) {
        char qname[80] = {0};
        
        // We can safely reuse the DNS name decoder we wrote for mDNS!
        decode_dns_name(payload, length, 12, qname, sizeof(qname));
        
        if (qname[0] != '\0') {
            const char* type_str = is_response ? "Reply" : "Query";
            snprintf(out_text, max_len, "LLMNR [%s] Tgt: %s", type_str, qname);
            return true;
        }
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
bool parse_generic_json(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    const char* p = (const char*)payload;
    const char* end = p + length;
    
    // 1. Find the first '{' and last '}'
    const char* json_start = nullptr;
    const char* json_end = nullptr;
    
    for (int i = 0; i < length; i++) {
        if (!json_start && p[i] == '{') json_start = &p[i];
        if (p[i] == '}') json_end = &p[i];
    }
    
    if (!json_start || !json_end || json_end <= json_start) return false;
    
    // Narrow our scope to just the JSON portion
    uint16_t json_len = (json_end - json_start) + 1;
    
    char model[64] = {0};
    char ip[32] = {0};
    char name[64] = {0};
    
    // 2. Surgically extract our target keys (ignores nesting!)
    bool has_model = extract_json_val(json_start, json_len, "model", model, sizeof(model));
    bool has_ip = extract_json_val(json_start, json_len, "ip", ip, sizeof(ip));
    bool has_name = extract_json_val(json_start, json_len, "name", name, sizeof(name));
    
    int written = 0;
    
    // 3. Build the summary if we found any common keys
    if (has_model || has_ip || has_name) {
        written = snprintf(out_text, max_len, "JSON:");
        if (has_model) written += snprintf(out_text + written, max_len - written, " model=%s", model);
        if (has_ip) written += snprintf(out_text + written, max_len - written, " ip=%s", ip);
        if (has_name) written += snprintf(out_text + written, max_len - written, " name=%s", name);
        return true;
    }
    
    // 4. Fallback: If no common keys, grab the first 3 key names we see
    written = snprintf(out_text, max_len, "JSON Keys: ");
    int keys_found = 0;
    const char* curr = json_start;
    
    while (curr < json_end && keys_found < 3 && written < max_len - 5) {
        // Look for "
        const char* q_start = (const char*)memchr(curr, '"', json_end - curr);
        if (!q_start) break;
        
        const char* q_end = (const char*)memchr(q_start + 1, '"', json_end - (q_start + 1));
        if (!q_end) break;
        
        // Check if a colon follows shortly after the closing quote
        const char* colon_check = q_end + 1;
        while (colon_check < json_end && (*colon_check == ' ' || *colon_check == '\t')) colon_check++;
        
        if (colon_check < json_end && *colon_check == ':') {
            // It's a key! Let's print it.
            int key_len = std::min((int)(q_end - (q_start + 1)), 16); // limit key length for screen
            written += snprintf(out_text + written, max_len - written, "%s%.*s", 
                                (keys_found > 0) ? ", " : "", 
                                key_len, q_start + 1);
            keys_found++;
        }
        curr = colon_check + 1;
    }
    
    if (keys_found > 0) return true;
    
    return false;
}

// ---------------------------------------------------------
// ARP PARSER (Extracts IP to MAC mappings)
// ---------------------------------------------------------
bool parse_arp(const uint8_t* payload, uint16_t length, char* out_text, size_t max_len) {
    // ARP packet length over 802.11 LLC is typically 28 bytes
    if (length < 28) return false;
    
    // Hardware Type (2), Protocol Type (2), Hw Size (1), Proto Size (1), Opcode (2)
    uint16_t opcode = (payload[6] << 8) | payload[7];
    
    if (opcode != 1 && opcode != 2) return false; // 1 = Request, 2 = Reply
    
    // IP addresses are at offsets 14 and 24 in standard ARP
    uint8_t src_ip[4];
    memcpy(src_ip, &payload[14], 4);
    
    uint8_t dst_ip[4];
    memcpy(dst_ip, &payload[24], 4);

    if (opcode == 2) {
        snprintf(out_text, max_len, "ARP Reply: MAC is %d.%d.%d.%d", 
                 src_ip[0], src_ip[1], src_ip[2], src_ip[3]);
    } else {
        snprintf(out_text, max_len, "ARP Req: Who has %d.%d.%d.%d?", 
                 dst_ip[0], dst_ip[1], dst_ip[2], dst_ip[3]);
    }
    
    return true;
}

// ==========================================
// TKIP/WEP RATE LIMITER (ISR SAFE)
// ==========================================
// Returns true if we should push this alert to the queue
bool should_alert_crypto(const uint8_t* src, const uint8_t* dst, uint32_t current_ms) {
    for (int i = 0; i < ALERT_CACHE_SIZE; i++) {
        if (memcmp(crypto_cache[i].mac_src, src, 6) == 0 &&
            memcmp(crypto_cache[i].mac_dst, dst, 6) == 0) {
            
            if (current_ms - crypto_cache[i].last_alert_ms > SEC_COOLDOWN_MS) {
                crypto_cache[i].last_alert_ms = current_ms;
                return true;
            }
            return false; // Still in cooldown
        }
    }
    // New flow: overwrite the oldest slot
    memcpy(crypto_cache[crypto_cache_idx].mac_src, src, 6);
    memcpy(crypto_cache[crypto_cache_idx].mac_dst, dst, 6);
    crypto_cache[crypto_cache_idx].last_alert_ms = current_ms;
    
    crypto_cache_idx = (crypto_cache_idx + 1) % ALERT_CACHE_SIZE;
    return true;
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

  // 1. Filter out everything except Data Frames (Type 0x08)
  if ((payload[0] & 0x0C) != 0x08) return;

  // ==========================================
  // LEAKY LAYER 2 CLEARTEXT EXTRACTOR
  // ==========================================
  if (currentRadioMode == RADIO_WIFI) {
      
      // TRICK 1: The Protected Bit Filter
      bool is_protected = (payload[1] & 0x40) != 0;
      
      if (!is_protected) {
          uint8_t header_len = (payload[0] & 0x80) ? 26 : 24;

          // --- NEW: METADATA EXTRACTION ---
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
              uint16_t ether_type = 0; // NEW: For routing ARP
              uint8_t tcp_flags = 0;   // NEW: For catching TCP SYN/RST connection attempts
              
              // Variables to hold our extracted IPs before they go to the queue
              uint8_t captured_ip_version = 0;
              uint8_t captured_src_ip[16] = {0};
              uint8_t captured_dst_ip[16] = {0};
              
              // 1. Skip LLC/SNAP Header (8 bytes) if present. 
              if (body_len > 8 && frame_body[0] == 0xAA && frame_body[1] == 0xAA) {
                  ether_type = (frame_body[6] << 8) | frame_body[7]; // <--- GRAB ETHERTYPE HERE  
                  frame_body += 8;
                  body_len -= 8;
              }

              // 2. Check for IPv4 (First nibble is 4)
              if (body_len > 20 && (frame_body[0] & 0xF0) == 0x40) {
                  captured_ip_version = 4;
                  
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
              }
              // 2.5 Check for IPv6 (First nibble is 6)
              else if (body_len > 40 && (frame_body[0] & 0xF0) == 0x60) {
                  captured_ip_version = 6;
                  
                  // IPv6 Source IP is at offset 8, Destination IP is at offset 24
                  memcpy(captured_src_ip, &frame_body[8], 16);
                  memcpy(captured_dst_ip, &frame_body[24], 16);

                  uint8_t next_header = frame_body[6]; // IPv6 uses "Next Header" instead of Protocol
                  uint8_t ip_header_len = 40; // Fixed size for base IPv6 header

                  // Note: This assumes no extension headers for maximum speed.
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
                  } else {
                      // Unknown protocol or contains extension headers. Just strip the fixed IP header.
                      frame_body += ip_header_len;
                      body_len -= ip_header_len;
                  }
              }

              char temp_text[MAX_LEAK_STR_LEN] = {0};
              bool custom_extracted = false;

            // --- 0. ARP (EtherType 0x0806) ---
            if (ether_type == 0x0806) {
                custom_extracted = parse_arp(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }
            // --- 1. DHCPv4 Extraction (Ports 67, 68) ---
            if (captured_dst_port == 67 || captured_dst_port == 68) {
                custom_extracted = parse_dhcp_v4(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }            
            // --- 2. DHCPv6 Extraction (Ports 546, 547) ---
            else if (captured_dst_port == 546 || captured_dst_port == 547) {
                custom_extracted = parse_dhcp_v6(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }
            // --- 3. NetBIOS Name Service (Port 137) ---
            else if (captured_dst_port == 137 || captured_src_port == 137) {
                custom_extracted = parse_netbios(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }
            // --- 3.5 NetBIOS Datagram / Browser (Port 138) ---
            else if (captured_dst_port == 138 || captured_src_port == 138) {
                custom_extracted = parse_nbds(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }
            // --- 4. DNS and mDNS (Ports 53, 5353) ---
            else if (captured_dst_port == 53 || captured_dst_port == 5353) {
                custom_extracted = parse_dns_mdns(frame_body, body_len, captured_dst_port, temp_text, MAX_LEAK_STR_LEN);
            }
            // --- 5. SSDP / UPnP (Port 1900) ---
            else if (captured_dst_port == 1900) {
                custom_extracted = parse_ssdp(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }
            // --- 6. LLMNR (Port 5355) ---
            else if (captured_dst_port == 5355) {
                custom_extracted = parse_llmnr(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }
            // --- 7. Dropbox LAN Sync (Port 17500) ---
            else if (captured_dst_port == 17500 || captured_src_port == 17500) {
                custom_extracted = parse_dropbox(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }
            // --- 8. SNMP (Ports 161, 162) ---
            else if (captured_dst_port == 161 || captured_dst_port == 162) {
                custom_extracted = parse_snmp(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }
            // --- 9. Static Port Fingerprints (No payload parsing required) ---
            else if (captured_dst_port == 3478 || captured_src_port == 3478) {
                snprintf(temp_text, MAX_LEAK_STR_LEN, "STUN: WebRTC/VoIP NAT Traversal");
                custom_extracted = true;
            }
            else if (captured_dst_port == 3544 || captured_src_port == 3544) {
                snprintf(temp_text, MAX_LEAK_STR_LEN, "Teredo: Windows IPv6 Tunnel");
                custom_extracted = true;
            }
            else if (captured_dst_port == 5350 || captured_src_port == 5350) {
                snprintf(temp_text, MAX_LEAK_STR_LEN, "PCP: Port Control Protocol");
                custom_extracted = true;
            }
            else if (captured_dst_port == 5351 || captured_src_port == 5351) {
                snprintf(temp_text, MAX_LEAK_STR_LEN, "NAT-PMP: Apple Port Mapping");
                custom_extracted = true;
            }
            // --- 10. TCP Cleartext and Connection Flags ---
            else if (captured_protocol == 6) {
                // 1. Try to scrape text from the payload
                if (body_len > 0 && extractCleartext(frame_body, body_len, temp_text)) {
                    custom_extracted = true;
                } 
                // 2. If no text, check if it's a new connection (SYN)
                else if (tcp_flags & 0x02) { 
                    snprintf(temp_text, MAX_LEAK_STR_LEN, "TCP SYN (Port %d)", captured_dst_port); 
                    custom_extracted = true; 
                } 
                // 3. Or a connection reset (RST)
                else if (tcp_flags & 0x04) { 
                    snprintf(temp_text, MAX_LEAK_STR_LEN, "TCP RST (Port %d)", captured_dst_port); 
                    custom_extracted = true; 
                } 
                // 4. (Optional) Log binary data packets
                else if (body_len > 0) {
                    snprintf(temp_text, MAX_LEAK_STR_LEN, "TCP Data: %d->%d (%d bytes)", captured_src_port, captured_dst_port, body_len);
                    custom_extracted = true;
                }
            }
            // --- 11. Catch-All Generic JSON Parser ---
            else {
                custom_extracted = parse_generic_json(frame_body, body_len, temp_text, MAX_LEAK_STR_LEN);
            }

            // --- 12. ICMPv6 Neighbor Discovery ---
            // If JSON didn't catch it, check if it's ICMPv6
            if (!custom_extracted && captured_ip_version == 6 && captured_protocol == 58) {
                // Ensure we have enough of the body to read the ICMPv6 Target IP (starts at byte 8)
                if (body_len >= 24) { 
                    uint8_t icmp_type = frame_body[0];
                    if (icmp_type == 135) { // 135 = Neighbor Solicitation
                        // Filter out Router Noise (Assuming 2 is AP->STA in your direction mapping)
                        if (captured_direction != 2) { 
                            strncpy(temp_text, "ICMPV6_NS", MAX_LEAK_STR_LEN);
                            // Overwrite captured_dst_ip with the Target IP being queried
                            memcpy(captured_dst_ip, &frame_body[8], 16);
                            custom_extracted = true;
                        }
                    }
                }
            }

            // --- 13. CATCH-ALL FOR UNKNOWN CLEARTEXT ---
            // If absolutely nothing else caught it, scan the raw bytes for text
            if (!custom_extracted && body_len > 0) {
                uint16_t printable_count = 0;
                uint16_t consecutive = 0;
                uint16_t text_idx = 0;
                
                for (uint16_t i = 0; i < body_len && text_idx < (MAX_LEAK_STR_LEN - 4); i++) {
                    char c = frame_body[i];
                    
                    if (c >= 32 && c <= 126) { // Printable ASCII range
                        consecutive++;
                        if (consecutive == 4) {
                            // Hit threshold! Retroactively copy the 3 previous chars
                            temp_text[text_idx++] = frame_body[i-3];
                            temp_text[text_idx++] = frame_body[i-2];
                            temp_text[text_idx++] = frame_body[i-1];
                            temp_text[text_idx++] = c;
                            printable_count += 4;
                        } else if (consecutive > 4) {
                            // Already past threshold, just keep adding
                            temp_text[text_idx++] = c;
                            printable_count++;
                        }
                    } else {
                        // Not a printable character
                        if (consecutive >= 4) {
                            // Add a visual separator (equivalent to Python's " | ".join())
                            temp_text[text_idx++] = ' ';
                            temp_text[text_idx++] = '|';
                            temp_text[text_idx++] = ' ';
                        }
                        consecutive = 0; // Reset streak
                    }
                }
                
                // If we found enough text, null terminate and trigger the queue push
                if (printable_count > 10) {
                    temp_text[text_idx] = '\0';
                    custom_extracted = true;
                }
            }
            
            // =========================================================
            // PUSH CLEARTEXT TO QUEUE (WITH DEDUPLICATION)
            // =========================================================
            if (custom_extracted) {
                
                // 1. ISR-Safe Flow Key De-Duplication (The Hash Ring)
                uint32_t text_hash = 5381;
                for (int c = 0; temp_text[c] != '\0'; c++) {
                    text_hash = ((text_hash << 5) + text_hash) + temp_text[c];
                }
                
                bool is_duplicate = false;
                for (int h = 0; h < 32; h++) {
                    if (leak_hash_history[h] == text_hash) {
                        is_duplicate = true;
                        break;
                    }
                }
                
                if (!is_duplicate) {
                    // Save hash to ring buffer
                    leak_hash_history[leak_hash_idx] = text_hash;
                    leak_hash_idx = (leak_hash_idx + 1) % 32;
                    
                    CleartextLeak leak;
                    memset(&leak, 0, sizeof(CleartextLeak));
                    
                    // 2. High-Value Triage (Optional: highlights on screen)
                    if (strstr(temp_text, "M-SEARCH") || strstr(temp_text, "HTTP/1.") || 
                        strstr(temp_text, "spotify") || strstr(temp_text, "cast")) {
                        leak.is_high_value = true;
                    }

                    // 3. Populate Payload and MACs
                    strncpy(leak.text, temp_text, MAX_LEAK_STR_LEN - 1);
                    memcpy(leak.src_mac, payload + 10, 6);
                    memcpy(leak.dst_mac, payload + 4, 6);
                    
                    // 4. Populate Extracted Metadata
                    leak.timestamp = xTaskGetTickCount() * portTICK_PERIOD_MS;
                    leak.src_port = captured_src_port;
                    leak.dst_port = captured_dst_port;
                    leak.ip_version = captured_ip_version;
                    memcpy(leak.src_ip, captured_src_ip, 16);
                    memcpy(leak.dst_ip, captured_dst_ip, 16);
                    leak.frame_subtype = captured_subtype;
                    leak.direction = captured_direction;
                    leak.channel = captured_channel;
                    leak.protocol = captured_protocol;
                    
                    // 5. Fire off to the Main Task
                    if (leakQueue != NULL) {
                        xQueueSendFromISR(leakQueue, &leak, NULL);
                    }
                }
            }
          }
        } else {
          // ==========================================
          // INSECURE ENCRYPTION DETECTION (TKIP/WEP)
          // ==========================================
          uint8_t header_len = (payload[0] & 0x80) ? 26 : 24;
          
          // Ensure we have enough bytes to read the IV header
          if (len > header_len + 4) {
              uint8_t* iv_ptr = payload + header_len;
              
              // Bit 5 (0x20) of the Key ID octet indicates an Extended (8-byte) IV
              bool is_ext_iv = (iv_ptr[3] & 0x20) != 0;
              
              // REQ 2: Extract TID (Traffic Identifier) if QoS bit is set
              char tid_str[16] = {0};
              if (payload[0] & 0x80) { 
                  // QoS Control field is at payload[24]. Lowest 4 bits = TID.
                  uint8_t tid = payload[24] & 0x0F;
                  snprintf(tid_str, sizeof(tid_str), "[TID:%d] ", tid);
              }
              
              bool triggered = false;
              char temp_text[MAX_LEAK_STR_LEN] = {0};

              if (is_ext_iv) {
                  // Heuristic: CCMP reserves Byte 2 as 0x00. TKIP uses it for a TSC-derived WEP seed.
                  if (iv_ptr[2] != 0x00) {
                      snprintf(temp_text, MAX_LEAK_STR_LEN, "%sWPA/TKIP Encryption Detected (INSECURE)", tid_str);
                      triggered = true;
                  }
              } else {
                  // A 4-byte IV without the Ext-IV bit set is standard WEP
                  snprintf(temp_text, MAX_LEAK_STR_LEN, "%sWEP Encryption Detected (INSECURE)", tid_str);
                  triggered = true;
              }

              // Apply the deduplication cooldown based on MAC addresses
              if (triggered) {
                  uint32_t now_ms = xTaskGetTickCount() * portTICK_PERIOD_MS;
                  
                  // Grab MAC addresses directly from the frame (Dst is offset 4, Src is offset 10)
                  if (should_alert_crypto(payload + 10, payload + 4, now_ms)) {
                      
                      CleartextLeak leak;
                      memset(&leak, 0, sizeof(CleartextLeak));
                      
                      // Using the correct struct member names
                      strncpy(leak.text, temp_text, MAX_LEAK_STR_LEN - 1);
                      memcpy(leak.src_mac, payload + 10, 6);
                      memcpy(leak.dst_mac, payload + 4, 6);
                      
                      // Fill in the Layer 2 metadata we know for encrypted frames
                      leak.timestamp = now_ms;
                      leak.frame_subtype = (payload[0] & 0xF0) >> 4;
                      leak.direction = payload[1] & 0x03;
                      leak.channel = pkt->rx_ctrl.channel;
                      
                      // IP/Ports remain 0 since this frame is encrypted
                      
                      if (leakQueue != NULL) {
                          xQueueSendFromISR(leakQueue, &leak, NULL);
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
  // CLEAR TEXT LEAKS BUTTON (Right Column, Top)
  // ==========================================
  // Placed directly above SNIFFED PROBES
  tft.fillRect(300, 90, 150, 40, TFT_DARKCYAN); 
  tft.drawRect(300, 90, 150, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("SNIFFED LEAKS", 375, 110);

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
  if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
    // Active State
    tft.fillRect(50, 190, 200, 40, TFT_BLACK);
    tft.drawRect(50, 190, 200, 40, TFT_WHITE);
    tft.setTextColor(TFT_WHITE);
    
    if (currentRadioMode == RADIO_WIFI) {
        tft.drawString("SELECT AP", 150, 210);
    } else if (currentRadioMode == RADIO_AP) {
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

  // 5. EXIT BUTTON
  tft.fillRect(300, 240, 150, 40, TFT_RED);
  tft.drawRect(300, 240, 150, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("EXIT", 375, 260);
  
  // THE FIX: Reset datum to Top-Left for the rest of the UI ONLY at the very end!
  tft.setTextDatum(TL_DATUM); 
}

void drawChartHeader() {
  tft.drawLine(0, HEADER_HEIGHT - 8, 480, HEADER_HEIGHT - 8, COLOR_HOT_CHEST);

  // MENU BUTTON
  // 1. Draw the Button Outline
  tft.drawRoundRect(420, 1, 55, 16, 2, TFT_WHITE);
  // 2. Set the Font State
  tft.setTextColor(TFT_WHITE);
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);  
  // 3. Center the Text Automatically
  tft.setTextDatum(MC_DATUM);     // Set datum to Middle-Center
  tft.drawString("MENU", 447, 7); 
  // 4. Reset state for the rest of your UI
  tft.setTextDatum(TL_DATUM);     // Put datum back to Top-Left

  // BANNER
  tft.setTextWrap(false); 
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);

  char bannerStr[64];

  // ==========================================
  // THE 3-STATE HEADER LOGIC
  // ==========================================
  tft.setTextColor(COLOR_HOT_CHEST); // Default color for the header
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

  // Draw the final formulated string
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
  // 1. Draw the top bounding line (separating it from the waterfall)
  //tft.drawLine(0, 295, 480, 295, TFT_WHITE);

  // 2. Clear the footer area to prevent text from overlapping when updated
  tft.fillRect(0, 296, 480, 24, TFT_BLACK);

  // 3. Set up the typography
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextColor(TFT_WHITE);
  tft.setTextDatum(MC_DATUM); 

  // ==========================================
  // ZONE 1: SORT METRIC (Center X = 72)
  // ==========================================
  // Draw the button outline
  tft.drawRoundRect(2, 302, 141, 17, 3, TFT_WHITE); 

  char metricStr[32] = "SORT: ERR"; // Failsafe fallback
  
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
    // --- NEW SPECTRUM STRINGS ---
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
  
  // Draw the text with the newly assigned color
  tft.drawString(metricStr, 72, 308);
  
  // Reset the color back to WHITE so it doesn't bleed into Zone 2 or 3
  tft.setTextColor(TFT_WHITE);
  // ==========================================
  // ZONE 2: SORT DIRECTION (Center X = 217)
  // ==========================================
  // Draw the button outline (X: 147, Y: 298, W: 141, H: 19, Radius: 3)
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
  // Draw the button outline (X: 292, Y: 298, W: 141, H: 19, Radius: 3)
  tft.drawRoundRect(292, 302, 141, 17, 3, TFT_WHITE); 

  if (useLogScale) {
    tft.setTextColor(TFT_YELLOW); 
    tft.drawString("SCALE: LOG", 362, 309);
  } else {
    tft.drawString("SCALE: LIN", 362, 309);
  }
    
  // ==========================================
  // ZONE 4: BATTERY PLACEHOLDER
  // ==========================================
  tft.drawRect(445, 304, 22, 12, TFT_WHITE); // Battery Outline
  tft.fillRect(467, 307, 3, 6, TFT_WHITE);   // Positive Terminal Nub
  tft.fillRect(447, 306, 18, 8, TFT_GREEN);  // Fake "Full Charge" Indicator
  
  // 4. Reset datum so the rest of your UI doesn't draw off-center
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
  // DYNAMIC PAGINATION MATH
  // ==========================================
  int items_per_page = 7; 
  int total_devices = 0;
  
  if (currentRadioMode == RADIO_WIFI) total_devices = sessionMacCount;
  else if (currentRadioMode == RADIO_BLE) total_devices = sessionBleCount;
  else if (currentRadioMode == RADIO_AP) total_devices = sessionApCount;
  else if (currentRadioMode == RADIO_CHANNELS) total_devices = sessionChannelCount;

  // ==========================================
  // DRAW TOP BANNER (WITH FOXHUNT OVERRIDE)
  // ==========================================
  tft.setTextColor(TFT_WHITE);
  tft.setFreeFont(&UbuntuMono_B9pt7b);
  
  if (is_selecting_target) {
    // TACTICAL MODE HEADER (Red Alert)
    tft.fillRect(0, 0, 480, 24, TFT_RED); 
    char huntStr[64];
    const char* modeName = (currentRadioMode == RADIO_WIFI) ? "WI-FI" : (currentRadioMode == RADIO_BLE) ? "BLE" : "NETWORKS";
    snprintf(huntStr, sizeof(huntStr), " FOXHUNT TARGET (%s)", modeName);
    tft.drawString(huntStr, 5, 5);
  } else {
    // NORMAL MODE HEADER (Dynamic Colors)
    uint16_t headerColor = TFT_BLUE;
    const char* modeStr = "WI-FI";
    
    if (currentRadioMode == RADIO_BLE) {
        headerColor = TFT_PURPLE;
        modeStr = "BLE";
    } else if (currentRadioMode == RADIO_AP) {
        headerColor = TFT_DARKGREEN;
        modeStr = "NETWORKS";
    } else if (currentRadioMode == RADIO_CHANNELS) {
        headerColor = TFT_ORANGE;
        modeStr = "CHANNELS";
    }
    
    tft.fillRect(0, 0, 480, 24, headerColor);
    char headerStr[64];
    snprintf(headerStr, sizeof(headerStr), " SNIFFED %s (%d)", modeStr, total_devices);
    tft.drawString(headerStr, 5, 5); 
  } 

  // ==========================================
  // DYNAMIC SORT BUTTONS (RIGHT-ALIGNED IN HEADER)
  // ==========================================
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  char metricStr[32] = "SORT:ERR";
  uint16_t metricColor = TFT_RED;
  
  if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
    // 1. STANDARD WI-FI / AP METRICS
    if (currentSortMode == SORT_TOTAL) { strcpy(metricStr, "SORT:TOTAL"); metricColor = TFT_WHITE; }
    else if (currentSortMode == SORT_TX) { strcpy(metricStr, "SORT:TX"); metricColor = TFT_CYAN; }
    else if (currentSortMode == SORT_RX) { strcpy(metricStr, "SORT:RX"); metricColor = TFT_MAGENTA; }
    else if (currentSortMode == SORT_AVG) { strcpy(metricStr, "SORT:AVG"); metricColor = TFT_YELLOW; }
    else if (currentSortMode == SORT_CV) { strcpy(metricStr, "SORT:CV%"); metricColor = TFT_ORANGE; }
    else if (currentSortMode == SORT_DIST) { strcpy(metricStr, "SORT:DIST"); metricColor = TFT_GREEN; }
    else if (currentSortMode == SORT_AGE) { strcpy(metricStr, "SORT:AGE"); metricColor = TFT_BLUE; }
  } 
  else if (currentRadioMode == RADIO_CHANNELS) {
    // 2. CUSTOM SPECTRUM METRICS
    if (currentSortMode == SORT_TOTAL) { strcpy(metricStr, "SORT:TOTAL"); metricColor = TFT_WHITE; }
    else if (currentSortMode == SORT_TX) { strcpy(metricStr, "SORT:DN"); metricColor = TFT_CYAN; }
    else if (currentSortMode == SORT_RX) { strcpy(metricStr, "SORT:UP"); metricColor = TFT_MAGENTA; }
    else if (currentSortMode == SORT_AVG) { strcpy(metricStr, "SORT:AVG"); metricColor = TFT_YELLOW; }
    else if (currentSortMode == SORT_CV) { strcpy(metricStr, "SORT:CV%"); metricColor = TFT_ORANGE; }
    else if (currentSortMode == SORT_DIST) { strcpy(metricStr, "SORT:PWR"); metricColor = TFT_GREEN; }
  } 
  else if (currentRadioMode == RADIO_BLE) {
    // 3. BLE METRICS
    if (currentBleSortMode == SORT_BLE_HITS) { strcpy(metricStr, "SORT:HITS"); metricColor = TFT_WHITE; }
    else if (currentBleSortMode == SORT_BLE_DIST) { strcpy(metricStr, "SORT:DIST"); metricColor = TFT_GREEN; }
    else if (currentBleSortMode == SORT_BLE_AGE) { strcpy(metricStr, "SORT:AGE"); metricColor = TFT_BLUE; }
  }

  // Draw Metric Button Outline and Text
  tft.fillRoundRect(275, 2, 130, 20, 3, TFT_BLACK); 
  tft.drawRoundRect(275, 2, 130, 20, 3, TFT_WHITE);
  tft.setTextColor(metricColor);
  tft.drawString(metricStr, 282, 4);

  // Draw Direction Button Outline and Text
  tft.fillRoundRect(410, 2, 65, 20, 3, TFT_BLACK); 
  tft.drawRoundRect(410, 2, 65, 20, 3, TFT_WHITE);
  
  if (sort_descending) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("DESC", 423, 4);
  } else {
    tft.setTextColor(TFT_GREEN);
    tft.drawString("ASC", 427, 4);
  }
  
  // Reset for the rest of the list
  tft.setTextColor(TFT_WHITE);

  if (total_devices == 0) {
    tft.setFreeFont(&UbuntuMono_Regular9pt7b);
    tft.drawString("No devices captured yet.", 5, 45);
  } else {
    int start_idx = device_current_page * items_per_page;
    if (start_idx >= total_devices) {
      device_current_page = 0;
      start_idx = 0;
    }
    int end_idx = start_idx + items_per_page;
    if (end_idx > total_devices) end_idx = total_devices;

    // ==========================================
    // DRAW THE UNIFIED DUAL COLUMN HEADERS
    // ==========================================
    tft.setTextColor(TFT_GREEN);
    if (currentRadioMode == RADIO_WIFI) {
      tft.setFreeFont(&UbuntuMono_B9pt7b);
      tft.drawString("     VENDOR                 MAC            RSSI TOTAL", 5, 26); 
      tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
      // --- UPDATED WIFI HEADER WITH Per(s) ---
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

    // --- HEADER SEPARATOR LINE ---
    tft.drawLine(0, 57, 480, 57, TFT_WHITE); 

    // ==========================================
    // DRAW THE DATA ROWS
    // ==========================================
    int row = 0;
    for (int i = start_idx; i < end_idx; i++) {
      
      int y = 62 + (row * 33); 
      
      if (currentRadioMode == RADIO_WIFI) {
        // ==========================================
        // WIFI MODE - UI LAYOUT
        // ==========================================
        char line1[90]; char line2[90];
        resolveMacVendor(&sessionData[i]);

        char macStr[18];
        snprintf(macStr, sizeof(macStr), "%02X:%02X:%02X:%02X:%02X:%02X",
                 sessionData[i].mac[0], sessionData[i].mac[1], sessionData[i].mac[2],
                 sessionData[i].mac[3], sessionData[i].mac[4], sessionData[i].mac[5]);

        char safeVendor[20]; 
        // The background queue already resolved this string, just format it for the column width
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

        // --- NEW: CALCULATE PERIODICITY (Keep-Alive Interval) ---
        int keep_alive_s = 0;
        if (sessionData[i].packets > 1) {
            unsigned long duration_ms = sessionData[i].last_seen - sessionData[i].first_seen;
            keep_alive_s = (duration_ms / sessionData[i].packets) / 1000;
            if (keep_alive_s > 99) keep_alive_s = 99; // Cap at 99 to protect double-digit UI bounds
        }
        // --------------------------------------------------------

        snprintf(line1, sizeof(line1), "%3d. %-18.18s %17s %4d %-5.5s", 
                 (i + 1), safeVendor, macStr, sessionData[i].rssi, totStr);

        // --- UPDATED WIFI LINE 2 WITH %02d REPLACING INDENT ---
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
        // ==========================================
        // BLE MODE - JIT TRANSLATION & DISPLAY
        // ==========================================
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

        // --- ZERO-ALLOCATION STRING BUILDER ---
        const char* appStr = resolveBleAppearance(sessionBleData[i].appearanceId);
        const char* srvStr = resolveBleServiceUuid(sessionBleData[i].serviceId);
        
        char tagStr[64] = {0}; // Stack buffer initialized to empty string
        
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

        // Fallback if tagStr is still empty
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
        
        // IMPORTANT: Ensure your cleanOsintString function signature expects a char* now, not a std::string!
        cleanOsintString(tagStr); 

        char macStr[18];
        snprintf(macStr, sizeof(macStr), "%02X:%02X:%02X:%02X:%02X:%02X", 
                 sessionBleData[i].mac[0], sessionBleData[i].mac[1], sessionBleData[i].mac[2], 
                 sessionBleData[i].mac[3], sessionBleData[i].mac[4], sessionBleData[i].mac[5]);

        snprintf(line1, sizeof(line1), "%2d.%-18.18s %13s %4d %4.0fm %5u", 
                 (i + 1), safeName, ageCombo, sessionBleData[i].rssi, 
                 sessionBleData[i].smoothedDistance, sessionBleData[i].hits);

        char line2[90];
        // Dropped the .c_str() since tagStr is now a native char array
        snprintf(line2, sizeof(line2), "%17s  %-33.33s", macStr, tagStr);

        tft.setFreeFont(&UbuntuMono_B9pt7b);
        tft.drawString(line1, 5, y);
        tft.setTextColor(TFT_LIGHTGREY);
        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.drawString(line2, 5, y + 15);
        tft.setTextColor(TFT_WHITE);

      } else if (currentRadioMode == RADIO_AP) {
        // ==========================================
        // AP MODE - NETWORKS SNIFF LIST
        // ==========================================
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
        // ==========================================
        // CHANNELS MODE - NETWORKS SNIFF LIST
        // ==========================================
        char line1[90];
        char line2[90];

        // 1. GLOBAL VOLUME STATISTICS (Bytes)
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

        // 2. EMA TIME-SERIES STATISTICS (RSSI & RF Physics)
        float avg_rssi = sessionChannelData[i].avg_rssi;
        double std_dev_rssi = sqrt(sessionChannelData[i].ema_variance);
        
        // Calculate Autocorrelation (rho)
        float rho = 0.0;
        if (sessionChannelData[i].ema_variance > 0.01) { 
            rho = sessionChannelData[i].ema_cov / sessionChannelData[i].ema_variance;
        }

        char stateStr[10];
        if (sessionChannelData[i].packets < 5) strcpy(stateStr, "CALC.."); 
        else if (rho > 0.6) strcpy(stateStr, "DRIFT");   
        else if (rho > 0.2) strcpy(stateStr, "ACTIVE");  
        else strcpy(stateStr, "STATIC");                 

        // 3. STRING FORMATTING
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
      row++;
    }
  }

  // --- SAFE NAVIGATION FOOTER ---
  tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
  tft.drawLine(0, 294, 480, 294, TFT_WHITE); 

  if (device_current_page > 0 && total_devices > 0) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("<- PREV", 20, 300);
  }
  
  tft.setTextColor(TFT_RED);
  tft.drawString("BACK", 215, 300); 

  if (((device_current_page + 1) * items_per_page) < total_devices) {
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

void drawLeakList() {
  tft.fillScreen(TFT_BLACK);
  tft.setTextSize(1);

  // ==========================================
  // 1. DYNAMIC HEADER BANNER
  // ==========================================
  int active_leaks = 0;
  for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
    if (leakHistory[i].hitCount > 0) {
      active_leaks++;
    }
  }

  tft.setFreeFont(&UbuntuMono_B9pt7b);
  tft.setTextDatum(TL_DATUM);
  tft.setTextColor(TFT_WHITE);
  uint16_t leakHeaderColor = TFT_DARKCYAN; 
  tft.fillRect(0, 0, 480, 24, leakHeaderColor);
  
  char headerStr[64];
  snprintf(headerStr, sizeof(headerStr), "SNIFFED LEAKS (%d)", active_leaks);
  tft.drawString(headerStr, 0, 5); 

  // ==========================================
  // 2. MULTI-LINE COLUMN HEADERS
  // ==========================================
  tft.setTextColor(TFT_CYAN);
  tft.setFreeFont(&UbuntuMono_Regular8pt7b);
  tft.drawString("SRC VENDOR:MAC:PORT  ->  DST VENDOR:MAC:PORT     HITS", 0, 25); 
  
  tft.setFreeFont(&UbuntuMono_Regular8pt7b); 
  tft.drawString("Cleartext payload", 0, 38); 
  tft.drawLine(0, 53, 480, 53, TFT_WHITE); 

  // ==========================================
  // 3. DATA ROWS (5-Line Data Injection)
  // ==========================================
  int LEAKS_PER_PAGE = 3; 
  int start_idx = leak_current_page * LEAKS_PER_PAGE;
  int end_idx = start_idx + LEAKS_PER_PAGE;

  int row = 0;
  for (int i = start_idx; i < end_idx && i < MAX_LEAK_SLOTS; i++) {
    if (leakHistory[i].hitCount == 0) continue;

    // Row height increased to 74px (5 lines total)
    int y = 60 + (row * 74); 
    auto& lk = leakHistory[i].leak; // shorthand

    // ---------------------------------------------------
    // METADATA LINE 1: MACs, Vendors, Channel, Hits, Time
    // ---------------------------------------------------
    tft.setFreeFont(&UbuntuMono_Regular8pt7b); 
    tft.setTextColor(TFT_GREEN);  

    char meta1[80];
    
    // Convert ms to seconds for a more readable, compact display
    uint32_t first_sec = leakHistory[i].first_seen / 1000;
    uint32_t last_sec = lk.timestamp / 1000;

    // Conditionally format the time so we don't waste horizontal space
    if (leakHistory[i].hitCount == 1) {
        snprintf(meta1, sizeof(meta1), "%02X%02X%02X%02X%02X%02X(%-6.6s)>%02X%02X%02X%02X%02X%02X(%-6.6s) [C%d H1 %u]",
                 lk.src_mac[0], lk.src_mac[1], lk.src_mac[2], lk.src_mac[3], lk.src_mac[4], lk.src_mac[5],
                 leakHistory[i].src_vendor,
                 lk.dst_mac[0], lk.dst_mac[1], lk.dst_mac[2], lk.dst_mac[3], lk.dst_mac[4], lk.dst_mac[5],
                 leakHistory[i].dst_vendor,
                 lk.channel, first_sec);
    } else {
        snprintf(meta1, sizeof(meta1), "%02X%02X%02X%02X%02X%02X(%-6.6s)>%02X%02X%02X%02X%02X%02X(%-6.6s) [C%d H%d %u-%u]",
                 lk.src_mac[0], lk.src_mac[1], lk.src_mac[2], lk.src_mac[3], lk.src_mac[4], lk.src_mac[5],
                 leakHistory[i].src_vendor,
                 lk.dst_mac[0], lk.dst_mac[1], lk.dst_mac[2], lk.dst_mac[3], lk.dst_mac[4], lk.dst_mac[5],
                 leakHistory[i].dst_vendor,
                 lk.channel, leakHistory[i].hitCount, first_sec, last_sec);
    }
             
    tft.drawString(meta1, 0, y); 

    // ---------------------------------------------------
    // METADATA LINE 2: Direction, Protocol, Ports, SSID
    // ---------------------------------------------------
    tft.setTextColor(TFT_CYAN);
    
    // Determine Protocol String
    const char* protoStr = "RAW";
    if (lk.protocol == 6) protoStr = "TCP";
    else if (lk.protocol == 17) protoStr = "UDP";
    else if (lk.protocol == 1) protoStr = "ICMP";
    else if (lk.protocol == 58) protoStr = "ICMPv6";

    // Determine Direction and extract BSSID for SSID Lookup
    const char* dirStr = "UNK";
    uint8_t target_bssid[6] = {0};
    bool can_lookup_ssid = false;

    if (lk.direction == 0) { 
        dirStr = "STA>STA"; 
    } else if (lk.direction == 1) { 
        dirStr = "STA>AP"; 
        memcpy(target_bssid, lk.dst_mac, 6); 
        can_lookup_ssid = true;
    } else if (lk.direction == 2) { 
        dirStr = "AP>STA"; 
        memcpy(target_bssid, lk.src_mac, 6); 
        can_lookup_ssid = true;
    } else if (lk.direction == 3) { 
        dirStr = "WDS"; 
    }

    // Fast RAM lookup for SSID
    char ssidStr[16] = "<Unknown>";
    if (can_lookup_ssid) {
        for (int b = 0; b < MAX_BSSID_CACHE; b++) {
            if (memcmp(bssidCache[b].bssid, target_bssid, 6) == 0) {
                strncpy(ssidStr, bssidCache[b].ssid, 15);
                ssidStr[15] = '\0';
                break;
            }
        }
    }

    // Format Line 2
    char meta2[80];
    if (lk.src_port > 0 || lk.dst_port > 0) {
        snprintf(meta2, sizeof(meta2), "[%s] Sub:%02X | %s %d->%d | SSID:%s", 
                 dirStr, lk.frame_subtype, protoStr, lk.src_port, lk.dst_port, ssidStr);
    } else {
        snprintf(meta2, sizeof(meta2), "[%s] Sub:%02X | %s (No Ports) | SSID:%s", 
                 dirStr, lk.frame_subtype, protoStr, ssidStr);
    }
    
    tft.drawString(meta2, 0, y + 14);

    // ---------------------------------------------------
    // LINES 3, 4, 5: Cleartext Payload (Truncated)
    // ---------------------------------------------------
    tft.setTextColor(TFT_WHITE);
    
    const int maxChars = 60; 
    int payloadLen = strlen(lk.text);
    char line3[maxChars + 1] = {0}; 
    char line4[maxChars + 1] = {0};
    char line5[maxChars + 1] = {0}; 

    if (payloadLen <= (maxChars * 3)) {
        strncpy(line3, lk.text, maxChars);
        if (payloadLen > maxChars) strncpy(line4, lk.text + maxChars, maxChars);
        if (payloadLen > (maxChars * 2)) strncpy(line5, lk.text + (maxChars * 2), maxChars);
    } else {
        strncpy(line3, lk.text, maxChars);
        strncpy(line4, lk.text + maxChars, maxChars);
        
        int usableLine5Chars = maxChars - 4; 
        strncpy(line5, lk.text + (maxChars * 2), usableLine5Chars);
        snprintf(line5 + usableLine5Chars, 5, "+%d", payloadLen - ((maxChars*2) + usableLine5Chars));
    }

    if (strlen(line3) > 0) tft.drawString(line3, 0, y + 28); 
    if (strlen(line4) > 0) tft.drawString(line4, 0, y + 42); 
    if (strlen(line5) > 0) tft.drawString(line5, 0, y + 56);
    
    // Draw row separator
    tft.drawLine(0, y + 70, 480, y + 70, hex24to565(0x222222));
    
    row++;
  }
  // ==========================================
  // 4. UNIFIED NAVIGATION FOOTER
  // ==========================================
  tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
  tft.drawLine(0, 294, 480, 294, TFT_WHITE); 

  if (leak_current_page > 0 && active_leaks > 0) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("<- PREV", 20, 300);
  }
  
  tft.setTextColor(TFT_RED);
  tft.drawString("BACK", 215, 300); 

  if (((leak_current_page + 1) * LEAKS_PER_PAGE) < active_leaks) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("NEXT ->", 360, 300);
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
            else if (currentSortMode == SORT_DIST) currentSortMode = SORT_AGE; // <-- ADD THIS LINE
            else currentSortMode = SORT_TOTAL;                                 // Loops back to TOTAL
          }
          else if (currentRadioMode == RADIO_BLE) {
            if (currentBleSortMode == SORT_BLE_HITS) currentBleSortMode = SORT_BLE_DIST;
            else if (currentBleSortMode == SORT_BLE_DIST) currentBleSortMode = SORT_BLE_AGE;
            else currentBleSortMode = SORT_BLE_HITS;
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
          // 1. Wipe the inside
          tft.fillRect(148, 299, 139, 17, TFT_BLACK);
          
          // 2. Toggle the variable
          sort_descending = !sort_descending;
          
          // 3. Redraw
          drawChartFooter(); 
          delay(200);
        }
        
        // ==========================================
        // ZONE 3 (Right 290-435): LOG/LINEAR SCALE
        // ==========================================
        else if (t_x > 290 && t_x <= 435) {
          // 1. Wipe the inside
          tft.fillRect(293, 299, 139, 17, TFT_BLACK);
          
          // 2. Toggle the variable
          useLogScale = !useLogScale;
          
          // 3. Redraw
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

          // 1. THE GATE
          if (!foxhunt_available) {
              return false; // The button is cold. Ignore the touch entirely.
          }
          
          // 2. THE EXECUTION
          is_selecting_target = true;
          currentState = SCREEN_DEVICE_LIST;
          drawDeviceList();
          
          // 3. THE DEBOUNCE
          delay(400); // Wait 400ms before accepting new touches
      }
      // SNIFFED LEAKS Button Touch Zone
      else if (t_x > 300 && t_x < 450 && t_y > 90 && t_y < 130) {
        currentState = SCREEN_LEAK_LIST; // Make sure to add this to your state enum!
        drawLeakList();
        delay(300); 
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
        } else if (currentRadioMode == RADIO_AP) {
          // Tap to cycle channels! 1-13, then back to unlocked (ALL)
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
          
          // Wipe the slate clean so the chart only shows APs on the new channel
          memset(traffic_history, 0, sizeof(traffic_history)); 
          absolute_max_traffic = 10;
          resetMonitorState(); 
          
          drawMenu(); // Redraw the button immediately to show the new channel number
          delay(150); // Snappy debounce for fast tapping
        }
      }
      // Sniffed Devices Button
      else if (t_x > 50 && t_x < 250 && t_y > 240 && t_y < 280) {
        currentState = SCREEN_DEVICE_LIST;
        device_current_page = 0;
        drawDeviceList();
        delay(300);
      }
      // ==========================================
      // RADIO MODE TOGGLE TOUCH LOGIC (X:300-450, Y:190-230)
      // ==========================================
      else if (t_x > 300 && t_x < 450 && t_y > 190 && t_y < 230) {
        
        target_locked = false; // Always break target locks on mode change
        memset(traffic_history, 0, sizeof(traffic_history)); // Clear the absolute chart memory
        absolute_max_traffic = 10;                           // Reset the absolute scaling ceiling

        // 1. Determine the next mode BEFORE we switch hardware
        RadioMode nextMode;
        if (currentRadioMode == RADIO_WIFI) nextMode = RADIO_BLE;
        else if (currentRadioMode == RADIO_BLE) nextMode = RADIO_AP;
        else if (currentRadioMode == RADIO_AP) nextMode = RADIO_CHANNELS;
        else nextMode = RADIO_WIFI;

        // 2. INSTANT PARTIAL REDRAW (Zero Screen Flicker!)
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
        } else {
          tft.fillRect(300, 190, 150, 40, TFT_ORANGE);
          tft.drawRect(300, 190, 150, 40, TFT_WHITE);
          tft.setTextColor(TFT_WHITE);
          tft.drawString("MODE: CHANNELS", 375, 210);
        }

        // ==========================================
        // PARTIAL REDRAW FOR FOXHUNT BUTTON
        // ==========================================
        bool foxhunt_available = false;
        
        if (nextMode == RADIO_BLE) {
            if (sessionBleCount > 0) foxhunt_available = true;
        } else if (nextMode == RADIO_AP) {
            if (sessionApCount > 0) foxhunt_available = true;
        } else if (nextMode == RADIO_WIFI) {
            if (target_locked == true && sessionMacCount > 0) foxhunt_available = true;
        }

        if (foxhunt_available) {
            // Draw active red button
            tft.fillRoundRect(50, 90, 200, 40, 3, TFT_RED); 
            tft.drawRoundRect(50, 90, 200, 40, 3, TFT_WHITE);
            tft.setTextColor(TFT_WHITE);
            tft.drawString("FOXHUNT", 150, 110);
        } else {
            // Overwrite with grey dead space
            uint16_t deadGrey = hex24to565(0x222222);
            tft.fillRect(50, 90, 200, 50, deadGrey); // Height expanded to 50 to erase old hint text
            tft.drawRect(50, 90, 200, 40, TFT_DARKGREY);
            tft.setTextColor(TFT_DARKGREY);
            tft.drawString("FOXHUNT", 150, 110);
            
            tft.setTextColor(hex24to565(0x444444));
            tft.drawString("(no targets yet)", 150, 125);
        }
        // ==========================================
        
        tft.setTextDatum(TL_DATUM); // Reset datum for the rest of your UI

        // 3. Let the ESP32 hang here for 500ms doing the heavy hardware swap
        switchRadioMode(nextMode);
        
        // Debounce
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
        
        // --- FLUSH THE DELTA-DRAW CACHE ---
        force_ui_refresh = true; 
        
        // THE FIX: Wake the Wi-Fi radio back up if we are in ANY Wi-Fi based mode!
        if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_CHANNELS) {
            esp_wifi_set_promiscuous(true); 
        }
        
        // --- UPDATED: Allow AP mode to restore its target channel, and sync the hopper if unlocked ---
        if ((currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) && target_locked) {
          esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);
        } else if (currentRadioMode != RADIO_BLE) {
          esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);
        }
        // -----------------------------------------------------------------------------
        
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
        // ZONE 1: Sort Metric (X: 275 to 410)
        if (t_x >= 275 && t_x < 410) {
          if (currentProbeSortMode == PROBE_SORT_HITS) currentProbeSortMode = PROBE_SORT_DIST;
          else if (currentProbeSortMode == PROBE_SORT_DIST) currentProbeSortMode = PROBE_SORT_SSIDS;
          else if (currentProbeSortMode == PROBE_SORT_SSIDS) currentProbeSortMode = PROBE_SORT_AGE;
          else currentProbeSortMode = PROBE_SORT_HITS;
          
          probe_current_page = 0; // Snap list back to page 1 upon resorting
          drawProbeTracker();
          delay(200);
        }
        // ZONE 2: Sort Direction (X: 410 to 480)
        else if (t_x >= 410) {
          probe_sort_descending = !probe_sort_descending;
          probe_current_page = 0;
          drawProbeTracker();
          delay(200);
        }
      }
      
      // FOOTER TOUCH (NAVIGATION)
      else if (t_y > 285) {
        // PREV PAGE (Left Third)
        if (t_x < 160 && probe_current_page > 0) {
          probe_current_page--;
          drawProbeTracker();
          delay(250);
        }
        // NEXT PAGE (Right Third)
        else if (t_x > 320 && ((probe_current_page + 1) * PROBES_PER_PAGE) < total_sniffed_probes) {
          probe_current_page++;
          drawProbeTracker();
          delay(250);
        }
        // BACK TO MENU (Center Third)
        else if (t_x >= 160 && t_x <= 320) {
          currentState = SCREEN_MENU;
          drawMenu(); 
          delay(300);
        }
      }
    }

    // ==========================================
    // 3. AP SCANNER TOUCH LOGIC
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
      // THE FIX: Stretched the hot zone down to 290 to cover the 6th row
      else if (t_y >= 80 && t_y < 290) {
        
        int clicked_row = (t_y - 80) / 35; 
        
        int actual_index = (ap_current_page * APS_PER_PAGE) + clicked_row;
        int n = WiFi.scanComplete();

        if (actual_index < n) {
          memcpy(target_bssid, WiFi.BSSID(actual_index), 6);
          target_channel = WiFi.channel(actual_index);
          target_rssi = WiFi.RSSI(actual_index);

          // ==========================================
          // TACTICAL SUFFIX INJECTION
          // ==========================================
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
          // ==========================================

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
      // THE FIX: Pushed down from 280 to 290 so it doesn't overlap row 6
      else if (t_y >= 290) {
        int total_aps = WiFi.scanComplete();
        
        // PREV PAGE
        if (t_x < 160 && ap_current_page > 0) {
          ap_current_page--;
          drawApScanner();
          delay(250);
        }
        // NEXT PAGE
        else if (t_x > 320 && ((ap_current_page + 1) * APS_PER_PAGE) < total_aps) {
          ap_current_page++;
          drawApScanner();
          delay(250);
        }
        // BACK TO MENU
        else if (t_x >= 160 && t_x <= 320) {
          currentState = SCREEN_MENU;
          ap_current_page = 0; 
          drawMenu(); 
          delay(300);
        }
      }
    }

    // 3. FOXHUNT SCREEN TOUCH LOGIC
    else if (currentState == SCREEN_FOXHUNT) {
      // Abort Button (Bottom Center)
      if (t_x > 190 && t_x < 290 && t_y > 290) {
        is_foxhunting = false;
        is_selecting_target = false;
        foxhunt_bounds_seeded = false; // Clear stale bounds
        
        // --- ADD THESE 3 LINES ---
        target_locked = false; // Release the lock
        current_ch_idx = 0;    // Reset the hopper index cleanly
        esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);
        // -------------------------

        currentState = SCREEN_MENU; // Route back to MENU
        drawMenu();
        delay(300);
      }
    }
    
    // 4. SEEN DEVICES TOUCH LOGIC
    else if (currentState == SCREEN_DEVICE_LIST) {
      
      // ==========================================
      // A. HEADER TOUCH LOGIC (SORT CONTROLS)
      // ==========================================
      if (t_y <= 30) {
        // ZONE 1: TOGGLE SORT METRIC (X: 275 to 405)
        if (t_x >= 275 && t_x < 405) {
          
          if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
            // Standard Wi-Fi/AP Toggle Cycle
            if (currentSortMode == SORT_TOTAL) currentSortMode = SORT_TX;
            else if (currentSortMode == SORT_TX) currentSortMode = SORT_RX;
            else if (currentSortMode == SORT_RX) currentSortMode = SORT_AVG;
            else if (currentSortMode == SORT_AVG) currentSortMode = SORT_CV;
            else if (currentSortMode == SORT_CV) currentSortMode = SORT_DIST;
            else if (currentSortMode == SORT_DIST) currentSortMode = SORT_AGE;
            else currentSortMode = SORT_TOTAL;
          } 
          else if (currentRadioMode == RADIO_CHANNELS) {
            // Custom Channels Toggle Cycle (Loops back after PWR)
            if (currentSortMode == SORT_TOTAL) currentSortMode = SORT_TX;      // DN
            else if (currentSortMode == SORT_TX) currentSortMode = SORT_RX;    // UP
            else if (currentSortMode == SORT_RX) currentSortMode = SORT_AVG;   // AVG Bytes
            else if (currentSortMode == SORT_AVG) currentSortMode = SORT_CV;   // CV% Bytes
            else if (currentSortMode == SORT_CV) currentSortMode = SORT_DIST;  // PWR (Avg RSSI)
            else currentSortMode = SORT_TOTAL;                                 // Skip AGE, loop back to TOTAL
          }
          else if (currentRadioMode == RADIO_BLE) {
            // BLE Toggle Cycle
            if (currentBleSortMode == SORT_BLE_HITS) currentBleSortMode = SORT_BLE_DIST;
            else if (currentBleSortMode == SORT_BLE_DIST) currentBleSortMode = SORT_BLE_AGE;
            else currentBleSortMode = SORT_BLE_HITS;
          }
          
          device_current_page = 0; 
          forceSessionSort(); 
          drawDeviceList();
          delay(200);
        }
        // ZONE 2: TOGGLE SORT DIRECTION (X: 410 to 480)
        else if (t_x >= 410) {
          sort_descending = !sort_descending;
          device_current_page = 0; // Snap list back to page 1 upon resorting
          forceSessionSort();
          drawDeviceList();
          delay(200);
        }
      }

      // ==========================================
      // B. FOOTER NAVIGATION (Y >= 294)
      // ==========================================
      else if (t_y >= 294) { 
        int items_per_page = 7;
        int total_devices = 0;
        
        if (currentRadioMode == RADIO_WIFI) total_devices = sessionMacCount;
        else if (currentRadioMode == RADIO_BLE) total_devices = sessionBleCount;
        else if (currentRadioMode == RADIO_AP) total_devices = sessionApCount;
        else if (currentRadioMode == RADIO_CHANNELS) total_devices = sessionChannelCount;

        // 1. PREV PAGE (X: 0 to 160)
        if (t_x < 160 && device_current_page > 0) {
          device_current_page--;
          drawDeviceList();
          delay(250);
        }
        // 2. NEXT PAGE (X: 320 to 480)
        else if (t_x > 320 && ((device_current_page + 1) * items_per_page) < total_devices) {
          device_current_page++;
          drawDeviceList();
          delay(250);
        }
        // 3. BACK TO MENU (X: 160 to 320)
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
      else if (t_y >= 62 && t_y < 294) { // Protected area ends at 294
        
        int tapped_screen_row = (t_y - 62) / 33;
        int total_devices = 0;
        
        if (currentRadioMode == RADIO_WIFI) total_devices = sessionMacCount;
        else if (currentRadioMode == RADIO_BLE) total_devices = sessionBleCount;
        else if (currentRadioMode == RADIO_AP) total_devices = sessionApCount;

        int tapped_array_index = (device_current_page * 7) + tapped_screen_row;

        if (tapped_screen_row < 7 && tapped_array_index < total_devices) {
          if (is_selecting_target) {
            // --- TARGET ACQUIRED: LAUNCH FOXHUNT ---
            is_selecting_target = false;
            is_foxhunting = true;
            smoothed_rssi = -100.0f;
            last_displayed_rssi = -999;      // Force frame 1 redraw

            if (currentRadioMode == RADIO_WIFI) {
               memcpy(foxhunt_target_mac, sessionData[tapped_array_index].mac, 6);
    
              // The struct already contains the resolved name, "<Randomized>", or "Unknown Device"
              strncpy(foxhunt_target_vendor, sessionData[tapped_array_index].vendor, sizeof(foxhunt_target_vendor) - 1);
              foxhunt_target_vendor[sizeof(foxhunt_target_vendor) - 1] = '\0'; // Safe null termination
    
              foxhunt_rssi_min = sessionData[tapped_array_index].rssi_min;
              foxhunt_rssi_max = sessionData[tapped_array_index].rssi_max;
              foxhunt_bounds_seeded = (sessionData[tapped_array_index].packets > 6);
    
            } else if (currentRadioMode == RADIO_AP) {
              // Allows Foxhunting routers from the AP list!
              memcpy(foxhunt_target_mac, sessionApData[tapped_array_index].bssid, 6);
              strncpy(foxhunt_target_vendor, sessionApData[tapped_array_index].ssid, sizeof(foxhunt_target_vendor) - 1);
              foxhunt_target_vendor[sizeof(foxhunt_target_vendor) - 1] = '\0'; // Safe null termination
              
              foxhunt_rssi_min = sessionApData[tapped_array_index].rssi_min;
              foxhunt_rssi_max = sessionApData[tapped_array_index].rssi_max;
              foxhunt_bounds_seeded = (sessionApData[tapped_array_index].packets > 6);

              // THE INSTANT LOCK STRATEGY (Routers are Stationary)
              target_locked = true; 
              target_channel = sessionApData[tapped_array_index].channel;
              esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);

            } else if (currentRadioMode == RADIO_BLE) {
              memcpy(foxhunt_target_mac, sessionBleData[tapped_array_index].mac, 6);
              strncpy(foxhunt_target_vendor, sessionBleData[tapped_array_index].name, 25);
              if (foxhunt_target_vendor[0] == '\0') {
                strncpy(foxhunt_target_vendor, "<Unnamed BLE>", 25);
              }
              foxhunt_target_vendor[25] = '\0'; // Safe null termination
              
              // BLE has no spatial bounds yet. Sentinels set to -100 to match globals.
              foxhunt_rssi_min = -100;
              foxhunt_rssi_max = -100;
              foxhunt_bounds_seeded = false;
              
              // BLE does not use the channel hopper
              target_locked = false;
            }

            currentState = SCREEN_FOXHUNT;
            
            // ==========================================
            // --- THE AWAKENING FIX ---
            // Wake the radio back up before drawing the radar!
            if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
                esp_wifi_set_promiscuous(true);
            }
            pause_sniffing = false;
            // ==========================================

            drawFoxhuntScreen(); 
            delay(200);
          }
        }
      }

    }
    // ==========================================
    // 5. SNIFFED LEAKS TOUCH LOGIC
    // ==========================================
    else if (currentState == SCREEN_LEAK_LIST) {
      
      // PREV PAGE (Bottom Left)
      if (t_y > 290 && t_x < 160) {
        if (leak_current_page > 0) { 
          leak_current_page--;
          drawLeakList();
          delay(200); // debounce touch
        }
      }
      // BACK TO MENU (Center Button)
      else if (t_y > 290 && t_x >= 160 && t_x <= 320) {
        currentState = SCREEN_MENU;
        drawMenu();
        delay(300);
      }
      // NEXT PAGE (Bottom Right)
      else if (t_y > 290 && t_x > 320) {
        // Assuming ~3 entries per page with your custom 3-line formatting,
        // and 10 MAX_LEAK_SLOTS, your maximum page index is 3 (pages 0, 1, 2, 3).
        int maxPages = 3; 
        
        if (leak_current_page < maxPages) {
          leak_current_page++;
          drawLeakList();
          delay(200); // debounce touch
        }
      }
    }
    return trigger_render; // 3. Return the decision back to loop()

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
void processLeakQueue() {
    CleartextLeak incomingLeak;
    
    // Process all available items in the queue without blocking (tick delay = 0)
    while (xQueueReceive(leakQueue, &incomingLeak, 0) == pdTRUE) {
        
        // ==========================================
        // 0. TOKEN EXPANSION (Run outside the ISR!)
        // ==========================================
        if (strcmp(incomingLeak.text, "ICMPV6_NS") == 0) {
            char src_str[40] = {0};
            char tgt_str[40] = {0};
            
            getIpString(6, incomingLeak.src_ip, src_str, sizeof(src_str));
            getIpString(6, incomingLeak.dst_ip, tgt_str, sizeof(tgt_str));
            
            snprintf(incomingLeak.text, sizeof(incomingLeak.text), 
                     "ICMPv6 ND: Who has %s? Tell %s", tgt_str, src_str);
        }
        
        bool isDuplicate = false;
        
        // 1. Check if this exact payload from this MAC is already in RAM
        for (int i = 0; i < MAX_LEAK_SLOTS; i++) {
            if (leakHistory[i].hitCount > 0 && 
                memcmp(leakHistory[i].leak.src_mac, incomingLeak.src_mac, 6) == 0 &&
                strcmp(leakHistory[i].leak.text, incomingLeak.text) == 0) {
                
                leakHistory[i].hitCount++;
                leakHistory[i].leak.timestamp = incomingLeak.timestamp; 
                isDuplicate = true;
                
                // BUBBLE UP: Move this active leak back to the top (Index 0)
                if (i > 0) {
                    auto tempLeak = leakHistory[i];
                    memmove(&leakHistory[1], &leakHistory[0], sizeof(leakHistory[0]) * i);
                    leakHistory[0] = tempLeak;
                }
                break;
            }
        }

        // 2. If it's a new leak, insert it at the top of the history list
        if (!isDuplicate) {
            memmove(&leakHistory[1], &leakHistory[0], sizeof(leakHistory[0]) * (MAX_LEAK_SLOTS - 1));

            leakHistory[0].leak = incomingLeak;
            leakHistory[0].hitCount = 1;
            leakHistory[0].first_seen = incomingLeak.timestamp;

            // 3. Resolve BOTH MAC vendors
            MacRecord tempRec;
            
            memset(&tempRec, 0, sizeof(MacRecord));      
            memcpy(tempRec.mac, incomingLeak.src_mac, 6); 
            resolveMacVendor(&tempRec); 
            strncpy(leakHistory[0].src_vendor, tempRec.vendor, 8);
            leakHistory[0].src_vendor[8] = '\0'; 
            
            memset(&tempRec, 0, sizeof(MacRecord));      
            memcpy(tempRec.mac, incomingLeak.dst_mac, 6); 
            resolveMacVendor(&tempRec); 
            strncpy(leakHistory[0].dst_vendor, tempRec.vendor, 8);
            leakHistory[0].dst_vendor[8] = '\0'; 
        }
    }
}

bool updateRadioHopper() {
    bool trigger_render = false; // Local render trigger

    if (currentState == SCREEN_CHART || currentState == SCREEN_FOXHUNT) {
        static unsigned long lastTimer = 0;

        tft.setTextWrap(false);

        // ==========================================
        // RADIO-AWARE TIMERS
        // ==========================================
        // Both Wi-Fi and AP modes need the Channel Hopper!
        if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_CHANNELS) {
            if (!target_locked) {
                if (millis() - lastTimer > HOP_INTERVAL) {
                    lastTimer = millis();
                    current_ch_idx++;

                    if (current_ch_idx >= NUM_CHANNELS) {
                        current_ch_idx = 0;
                        trigger_render = true; // Replaces should_render = true
                    }

                    esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);

                    // THE FIX: Only draw the channel indicator if we are on the main chart!
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
                
                // THE FIX: Only draw the BLE sniffing indicator if we are on the main chart!
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
    drawTemporalLegend();
    drawPersistentTopN();

    int chart_area_height = CHART_BOTTOM - chart_start_y;
    int split_y = chart_start_y + (chart_area_height * 3) / 4; 
    int ERASER_WIDTH = 44;
    
    // Pure wipe logic
    if (current_x + ERASER_WIDTH <= 480) {
        tft.fillRect(current_x, chart_start_y + 1, ERASER_WIDTH, CHART_BOTTOM - chart_start_y, TFT_BLACK);
    } else {
        int w1 = 480 - current_x;
        tft.fillRect(current_x, chart_start_y + 1, w1, CHART_BOTTOM - chart_start_y, TFT_BLACK);
        tft.fillRect(0, chart_start_y + 1, ERASER_WIDTH - w1, CHART_BOTTOM - chart_start_y, TFT_BLACK);
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
    tft.drawFastVLine(current_x + 2, chart_start_y + 1, CHART_BOTTOM - chart_start_y, COLOR_HOT_CHEST);
    
    if (current_x + ERASER_WIDTH <= 480) {
        tft.drawFastVLine(current_x + ERASER_WIDTH - 1, chart_start_y + 1, CHART_BOTTOM - chart_start_y, COLOR_HOT_CHEST);
        tft.drawFastHLine(current_x, split_y, ERASER_WIDTH, COLOR_HOT_CHEST);
    } else {
        int w1 = 480 - current_x;
        tft.drawFastVLine(ERASER_WIDTH - w1 - 1, chart_start_y + 1, CHART_BOTTOM - chart_start_y, COLOR_HOT_CHEST);
        tft.drawFastHLine(current_x, split_y, w1, COLOR_HOT_CHEST);
        tft.drawFastHLine(0, split_y, ERASER_WIDTH - w1, COLOR_HOT_CHEST);
    }

    if (current_x <= 480 - ERASER_WIDTH || did_rescale) {
        int text_x = current_x + 6; 
        if (text_x > 480 - 40) text_x = 480 - 40; 

        tft.setFreeFont(&UbuntuMono_Regular8pt7b);
        tft.setTextDatum(TL_DATUM);

        tft.setTextColor(COLOR_HOT_CHEST);
        tft.drawString("100%", text_x, chart_start_y + 4);
        int mid_y = chart_start_y + ((split_y - chart_start_y) / 2);
        tft.drawString("50%", text_x, mid_y - 6);

        if (currentRadioMode == RADIO_BLE || target_locked) tft.drawString("|=1m", text_x, split_y - 15); 
        else tft.drawString("|=2m", text_x, split_y - 15);

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

  initProbeTracker();

  // ==========================================
  // 1. CREATE THE LEAKY LAYER 2 QUEUE
  // ==========================================
  leakQueue = xQueueCreate(10, sizeof(CleartextLeak));
  if (leakQueue == NULL) {
      Serial.println("[!] FATAL: Failed to create leakQueue! Out of heap.");
  } else {
      Serial.println("[*] leakQueue created successfully.");
  }

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

void loop() {
  // ==========================================
  // BACKGROUND DATA ENGINES (Run every tick)
  // ==========================================
  processPendingVendors();
  runProbeCorrelationEngine(); 
  processLeakQueue();           // <--- ADD IT RIGHT HERE
  
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
    } else if (currentState == SCREEN_LEAK_LIST) {
        drawLeakList(); // <--- ALSO ADD YOUR NEW SCREEN HERE!
    }
    
    Serial.printf("Free Heap: %d bytes\n", ESP.getFreeHeap());
  }
}