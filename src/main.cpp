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
char foxhunt_target_vendor[26] = "Unknown";

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
   SCREEN_DEVICE_LIST, SCREEN_PROBE_TRACKER, SCREEN_FOXHUNT };
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
  int8_t rssi_min;    // NEW: spatial floor for foxhunt adaptive threshold
  int8_t rssi_max;    // NEW: spatial ceiling for foxhunt adaptive threshold
  char ssid[26];      // Trimmed from 28 — UI truncates at 18 chars anyway
  char country[3];
};
// Still exactly 80 bytes

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
const int CHART_BOTTOM = 295;
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
#define OUI_CACHE_SIZE 300 // Shrunk from 300 to clear SRAM

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

// Everything that lives outside the union
constexpr size_t union_size = sizeof(MacRecord) * MAX_MACS; // The union's footprint
                                                             // (sized by largest member)

constexpr size_t static_non_union =
    union_size * 3 +                                        // live + sort + session
    (sizeof(OUICache)          * OUI_CACHE_SIZE)      +
    (sizeof(ProbeRecordShared) * MAX_PROBE_SLOTS)     +
    (sizeof(SSIDNode)          * TOTAL_SSID_POOL)     +
    (sizeof(BeaconEntry)       * MAX_BEACON_DICT);

constexpr size_t osint_layer_size =
    (sizeof(ProbeRecordShared) * MAX_PROBE_SLOTS) +
    (sizeof(SSIDNode)          * TOTAL_SSID_POOL) +
    (sizeof(BeaconEntry)       * MAX_BEACON_DICT);

// Compile-time safety check to prevent silent memory corruption
constexpr size_t max_wifi_size = sizeof(MacRecord) * MAX_MACS;
static_assert(max_wifi_size >= sizeof(BLERecord) * MAX_BLE_DEVICES, 
              "FATAL: BLE array exceeds union boundary.");
static_assert(max_wifi_size >= sizeof(ApRecord) * MAX_AP_RECORDS, 
              "FATAL: AP array exceeds union boundary.");
static_assert(max_wifi_size >= sizeof(ChannelRecord) * MAX_CHANNEL_RECORDS, 
              "FATAL: Channel array exceeds union boundary.");
              // Persistent OSINT layer budget check
static_assert(osint_layer_size < 20480, 
    "FATAL: Persistent OSINT layer exceeds 20KB budget.");
// Total known static allocation
constexpr size_t SRAM_BUDGET = 327680;  // 320KB — conservative application budget
                                         // leaving ~200KB for WiFi/BLE/stack/heap

static_assert(static_non_union <= SRAM_BUDGET,
    "FATAL: Static allocations exceed conservative SRAM budget. "
    "Reduce array sizes.");

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
/*
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

  // 3. REAL-TIME TACTICAL STRETCHING (Option B)
  if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
      if (foxhunt_rssi_min == 0 || packet_rssi < foxhunt_rssi_min) {
          foxhunt_rssi_min = packet_rssi;
      }
      if (foxhunt_rssi_max == -100 || packet_rssi > foxhunt_rssi_max) {
          foxhunt_rssi_max = packet_rssi;
          foxhunt_bounds_seeded = true;
      }
  }
}
*/
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
            strncpy((char*)liveApData[ap_index].ssid, extracted_ssid, 25);
            liveApData[ap_index].ssid[25] = '\0';
          }
        }

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
    // THE SMART BOUNCER & IE PARSER (Replaces old Filter)
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
          strcpy(final_ssid, "<Wld>");
        } 
        else if (tag_len <= 32) {
          if (payload[offset + 2] == 0x00) {
            strcpy(final_ssid, "<Nul>");
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
              strcpy(final_ssid, "<Nul>");
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
              snprintf(ie_vendor, sizeof(ie_vendor), "%s (IE)", TAG_221_DATABASE[v].name);
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

  // --- NEW: CHASE TAIL SEQUENCE EXTRACTION (SUSPENDED FOR NOW)---
  // Sequence Control field is located at bytes 22 and 23 of the 802.11 MAC header (Little Endian)
  //uint16_t seq_ctrl = payload[22] | (payload[23] << 8);
  // Shift right 4 bits to strip the Fragment Number, then bitmask to isolate the 12-bit Sequence Number
  //uint16_t seq_num = (seq_ctrl >> 4) & 0x0FFF;
  // -------------------------------------------

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
    
    // --- NEW: INJECT FOXHUNT CHANNEL AND CHASE TAIL SEQUENCE ---
    // (Logs the hopper's current channel at the moment of discovery)
    //liveData[liveMacCount].channel = CHANNELS[current_ch_idx];     
    // -----------------------------------------------------------

    // Route the first packet to TX or RX
    if (is_tx) {
      liveData[liveMacCount].tx_bytes = len;
      liveData[liveMacCount].rx_bytes = 0;
    } else {
      liveData[liveMacCount].tx_bytes = 0;
      liveData[liveMacCount].rx_bytes = len;
    }
    
    liveData[liveMacCount].vendorFound = false;
    
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
  if (record->vendorFound) return;

  // 1. Check RAM Cache
  for (int i = 0; i < cacheCount; i++) {
    if (vendorCache[i].oui[0] == record->mac[0] &&
        vendorCache[i].oui[1] == record->mac[1] &&
        vendorCache[i].oui[2] == record->mac[2]) {
      
      // Dynamically fills the array and leaves 1 byte for the null terminator
      strncpy(record->vendor, vendorCache[i].vendor, sizeof(record->vendor) - 1);
      record->vendor[sizeof(record->vendor) - 1] = '\0'; 
      record->vendorFound = true;
      return; 
    }
  }

  // Generate fallback string in case lookup fails
  sprintf(record->vendor, "%02X:%02X:%02X:%02X:%02X:%02X",
          record->mac[0], record->mac[1], record->mac[2],
          record->mac[3], record->mac[4], record->mac[5]);

  char target[7];
  sprintf(target, "%02X%02X%02X", record->mac[0], record->mac[1], record->mac[2]);

  // 2. Binary Search the SD Card
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
        // MATCH FOUND: Find where the actual text starts by skipping leading spaces/tabs
        int text_start = 7;
        while(text_start < 32 && (line[text_start] == ' ' || line[text_start] == '\t')) {
          text_start++;
        }
        
        // Calculate safe length: remaining chars in 'line' OR max capacity of 'vendor', whichever is smaller
        int available_chars = 32 - text_start;
        int max_capacity = sizeof(record->vendor) - 1;
        int copy_len = (available_chars < max_capacity) ? available_chars : max_capacity;
        
        // Safely extract the text
        strncpy(record->vendor, &line[text_start], copy_len); 
        record->vendor[copy_len] = '\0';
        
        // Strip trailing spaces and hidden line-endings working backward
        for(int i = copy_len - 1; i >= 0; i--) {         
          if(record->vendor[i] == ' ' || record->vendor[i] == '\r' || record->vendor[i] == '\n') {
              record->vendor[i] = '\0';
          } else {
              break;
          }
        }
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

  record->vendorFound = true;

  // 3. Save to RAM Cache
  vendorCache[cacheHead].oui[0] = record->mac[0];
  vendorCache[cacheHead].oui[1] = record->mac[1];
  vendorCache[cacheHead].oui[2] = record->mac[2];
  
  // Updated to 26 chars max, null terminated at [26]
  strncpy(vendorCache[cacheHead].vendor, record->vendor, 26);
  vendorCache[cacheHead].vendor[26] = '\0';
  
  if (cacheCount < OUI_CACHE_SIZE) cacheCount++;
  cacheHead = (cacheHead + 1) % OUI_CACHE_SIZE;
}

std::string resolveBleCompanyId(std::string mfgData) {
  if (mfgData.length() < 2) return "";
  
  uint16_t companyId = (uint8_t)mfgData[1] << 8 | (uint8_t)mfgData[0];

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
  return ""; 
}

std::string resolveBleAppearance(uint16_t appearanceId) {
  // PASS 1: Search for the exact 16-bit ID (Category + Subcategory)
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

  // PASS 2: If the exact subcategory fails, mask off the bottom 6 bits 
  // to search for the generic Base Category instead.
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
  
  return ""; // Completely unknown Appearance ID
}

/**
 * Fast Binary Search for Corporate Trackers (0x16 Service Data)
 */
std::string resolveBleMemberUuid(uint16_t targetId) {
  int left = 0;
  int right = numMemberUuids - 1;

  while (left <= right) {
    int mid = left + (right - left) / 2;

    if (memberUuids[mid].id == targetId) return memberUuids[mid].name;
    
    if (memberUuids[mid].id < targetId) left = mid + 1;
    else right = mid - 1;
  }
  return ""; 
}

/**
 * Fast Binary Search for Standard Hardware Services (0x02/0x03)
 */
std::string resolveBleServiceUuid(uint16_t targetId) {
  int left = 0;
  int right = numServiceUuids - 1;

  while (left <= right) {
    int mid = left + (right - left) / 2;

    if (serviceUuids[mid].id == targetId) return serviceUuids[mid].name;
    
    if (serviceUuids[mid].id < targetId) left = mid + 1;
    else right = mid - 1;
  }
  return ""; 
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
  
  // (The premature TL_DATUM reset was deleted from here)

  // ==========================================
  // PROBE REQUEST BUTTON (Right Column)
  // ==========================================
  uint16_t purpleColor = hex24to565(0x4A148C);
  tft.fillRect(300, 140, 150, 40, purpleColor);
  tft.drawRect(300, 140, 150, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("SNIFFED PROBES", 375, 160);

  // ==========================================
  // 3. AP SCANNER BUTTON (Y: 190 - 230)
  // ==========================================
  if (currentRadioMode == RADIO_WIFI) {
    // Active State
    tft.fillRect(50, 190, 200, 40, TFT_BLACK);
    tft.drawRect(50, 190, 200, 40, TFT_WHITE);
    tft.setTextColor(TFT_WHITE);
   } else {
    // "Cold" Abyss State
    uint16_t deadGrey = hex24to565(0x222222);      // Almost black
    tft.fillRect(50, 190, 200, 40, deadGrey);
    tft.drawRect(50, 190, 200, 40, TFT_DARKGREY);
    tft.setTextColor(TFT_DARKGREY);
  }
  tft.drawString("SELECT AP", 150, 210);

  // 4. SEEN DEVICES BUTTON
  tft.fillRect(50, 240, 200, 40, TFT_BLACK);
  tft.drawRect(50, 240, 200, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("SNIFF LIST", 150, 260);

  // ==========================================
  // RADIO MODE TOGGLE (3-STATE)
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
  tft.drawLine(0, HEADER_HEIGHT, 480, HEADER_HEIGHT, TFT_WHITE);

  // MENU BUTTON
  // 1. Draw the Button Outline
  tft.drawRoundRect(420, 2, 55, 16, 2, TFT_WHITE);
  // 2. Set the Font State
  tft.setTextColor(TFT_WHITE);
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);  
  // 3. Center the Text Automatically
  tft.setTextDatum(MC_DATUM);     // Set datum to Middle-Center
  tft.drawString("MENU", 447, 9); 
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
  if (currentRadioMode == RADIO_BLE) {
    tft.setTextColor(TFT_ORANGE); 
    snprintf(bannerStr, sizeof(bannerStr), "SNIFFING BLE DEVICES");
  } 
  else if (currentRadioMode == RADIO_AP) {
    tft.setTextColor(TFT_GREEN); 
    // AP Mode also hops channels, so showing the active channel is highly useful!
    snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | SNIFFING NETWORKS", CHANNELS[current_ch_idx]);
  }
  else if (currentRadioMode == RADIO_CHANNELS) {
    tft.setTextColor(TFT_ORANGE); 
    snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | SNIFFING SPECTRUM", CHANNELS[current_ch_idx]);
  }
  else if (currentRadioMode == RADIO_WIFI) {
    tft.setTextColor(TFT_WHITE); 
    
    if (!target_locked) {
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | SNIFFING FREE AIRSPACE", CHANNELS[current_ch_idx]);
    } else {
      char safe_ssid[15];
      strncpy(safe_ssid, target_ssid, 14);
      safe_ssid[14] = '\0';
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | %s (%ddBm)", target_channel, safe_ssid, target_rssi);
    }
  }

  // Draw the final formulated string
  tft.drawString(bannerStr, 5, 4);
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
  tft.drawRoundRect(2, 298, 141, 19, 3, TFT_WHITE); 

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
  tft.drawRoundRect(147, 298, 141, 19, 3, TFT_WHITE); 

  if (sort_descending) {
    tft.drawString("ORDER: DESC", 217, 308);
  } else {
    tft.setTextColor(TFT_GREEN); 
    tft.drawString("ORDER: ASC", 217, 308);
    tft.setTextColor(TFT_WHITE); 
  }

  // ==========================================
  // ZONE 3: SCALE MODE (Center X = 362)
  // ==========================================
  // Draw the button outline (X: 292, Y: 298, W: 141, H: 19, Radius: 3)
  tft.drawRoundRect(292, 298, 141, 19, 3, TFT_WHITE); 

  if (useLogScale) {
    tft.setTextColor(TFT_YELLOW); 
    tft.drawString("SCALE: LOG", 362, 308);
  } else {
    tft.drawString("SCALE: LIN", 362, 308);
  }
    
  // ==========================================
  // ZONE 4: BATTERY PLACEHOLDER
  // ==========================================
  tft.drawRect(445, 302, 22, 12, TFT_WHITE); // Battery Outline
  tft.fillRect(467, 305, 3, 6, TFT_WHITE);   // Positive Terminal Nub
  tft.fillRect(447, 304, 18, 8, TFT_GREEN);  // Fake "Full Charge" Indicator
  
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

void cleanOsintString(std::string &s) {
    // 1. Strip bulky corporate suffixes
    std::string suffixes[] = {", Inc.", " Inc.", " LLC", " Corp.", " Ltd."};
    for (const auto& suffix : suffixes) {
        size_t pos;
        while ((pos = s.find(suffix)) != std::string::npos) {
            s.erase(pos, suffix.length());
        }
    }

    // 2. Crush double spaces after colons (e.g. "Apple:  Find My" -> "Apple:Find My")
    // We check for double space first, then single space.
    size_t pos;
    while ((pos = s.find(":  ")) != std::string::npos) {
        s.replace(pos, 3, ":"); 
    }
    while ((pos = s.find(": ")) != std::string::npos) {
        s.replace(pos, 2, ":");
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

        bool is_randomized = (sessionData[i].mac[0] & 0x02) != 0;
        char safeVendor[20]; 
        
        if (strstr(sessionData[i].vendor, "(IE)") != nullptr) {
            snprintf(safeVendor, sizeof(safeVendor), "%-18.18s", sessionData[i].vendor);
        } else if (is_randomized) {
            snprintf(safeVendor, sizeof(safeVendor), "%-18.18s", "<Randomized>");
        } else if (sessionData[i].vendor[2] == ':' || strlen(sessionData[i].vendor) == 0) {
            snprintf(safeVendor, sizeof(safeVendor), "%-18.18s", "Unknown Device");
        } else {
            snprintf(safeVendor, sizeof(safeVendor), "%-18.18s", sessionData[i].vendor);
        }

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
        char line1[90]; char safeName[20];
        
        if (sessionBleData[i].name[0] == '\0') {
            snprintf(safeName, sizeof(safeName), "%-18.18s", "<Unnamed>");
        } else {
            snprintf(safeName, sizeof(safeName), "%-18.18s", sessionBleData[i].name);
        }

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

        std::string appStr = resolveBleAppearance(sessionBleData[i].appearanceId);
        std::string srvStr = resolveBleServiceUuid(sessionBleData[i].serviceId);
        std::string tagStr = "";
        
        if (strlen(trackerStr) > 0 && sessionBleData[i].namePriority != 1) {
            tagStr += trackerStr;
        }
        if (appStr != "") {
            tagStr += (tagStr.length() > 0 ? "|" : "") + appStr;
        }
        if (srvStr != "") {
            tagStr += (tagStr.length() > 0 ? "|" : "") + srvStr;
        }

        if (tagStr == "") {
            if (sessionBleData[i].payload[0] != '\0') {
                if (sessionBleData[i].trackerType == TRACKER_APPLE_IBEACON) {
                    tagStr = "iBeacon | " + std::string(sessionBleData[i].payload);
                } else {
                    tagStr = sessionBleData[i].payload; 
                }
            } else {
                tagStr = "No Data"; 
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
        snprintf(line2, sizeof(line2), "%17s  %-33.33s", macStr, tagStr.c_str());

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

std::string decodeEddystoneURL(const std::string& sData) {
    // Eddystone frame type 0x10 specifically means "URL"
    if (sData.length() < 3 || sData[0] != 0x10) return "Eddystone: (Not URL)";

    std::string url = "";
    
    // 1. Decode the Prefix Scheme (Byte 2)
    switch (sData[2]) {
        case 0x00: url += "http://www."; break;
        case 0x01: url += "https://www."; break;
        case 0x02: url += "http://"; break;
        case 0x03: url += "https://"; break;
        default: return "Unknown URI Scheme";
    }

    // 2. Decode the Body and Suffixes (Bytes 3+)
    const char* suffixes[] = {
        ".com/", ".org/", ".edu/", ".net/", ".info/", ".biz/", ".gov/",
        ".com", ".org", ".edu", ".net", ".info", ".biz", ".gov"
    };

    for (size_t i = 3; i < sData.length(); i++) {
        uint8_t c = sData[i];
        if (c <= 0x0D) {
            url += suffixes[c]; // Inject the decompressed suffix
        } else {
            url += (char)c;     // Just standard ASCII text
        }
    }
    return url;
}

class BLEPassiveCallbacks: public BLEAdvertisedDeviceCallbacks {
  void onResult(BLEAdvertisedDevice* advertisedDevice) {
    if (pause_sniffing) return; 

    // ==========================================
    // BLE FOXHUNT ISR FEEDER
    // Runs immediately on every advertisement from the target device.
    // Replaces the deferred render-pipeline update (every 2 seconds)
    // with per-packet updates, matching WiFi foxhunt responsiveness.
    // ==========================================
    if (is_foxhunting) {
        const uint8_t* rawMac = advertisedDevice->getAddress().getNative();
        if (memcmp(rawMac, foxhunt_target_mac, 6) == 0) {
            updateFoxhuntSignal(advertisedDevice->getRSSI());
        }
    }
    // ==========================================

    std::string macStr = advertisedDevice->getAddress().toString();
    
    // ==========================================
    // ON-THE-FLY RAW HEX DUMP (No SRAM Storage)
    // ==========================================
    uint8_t* rawPayload = advertisedDevice->getPayload();
    size_t payloadLen = advertisedDevice->getPayloadLength();

    Serial.printf("RAW [%02d bytes] MAC: %s | ", payloadLen, advertisedDevice->getAddress().toString().c_str());
    
    for (size_t p = 0; p < payloadLen; p++) {
        Serial.printf("%02X ", rawPayload[p]);
    }
    Serial.println();
    // ==========================================
    
    int rssi = advertisedDevice->getRSSI();
    int txPower = advertisedDevice->haveTXPower() ? advertisedDevice->getTXPower() : 0;
    int sdCount = advertisedDevice->getServiceDataCount();

    // ==========================================
    // PARALLEL OSINT EXTRACTION & SIG LOOKUPS
    // ==========================================
    std::string newName = "";
    uint8_t newNamePriority = 0;
    uint8_t newTrackerType = TRACKER_NONE; 
    uint16_t newAppearanceId = 0;          
    uint16_t newServiceId = 0;

    // ==========================================
    // STEP 1: Name & Manufacturer Data (0xFF)
    // ==========================================
    if (advertisedDevice->haveName()) {
      newName = advertisedDevice->getName();
    } 
    
    if (advertisedDevice->haveManufacturerData()) {
      std::string mfg = advertisedDevice->getManufacturerData();
      if (mfg.length() >= 2) {
        uint16_t companyId = (uint8_t)mfg[1] << 8 | (uint8_t)mfg[0];
        std::string resolvedCompany = resolveBleCompanyId(mfg);
        
        if (companyId == 0x004C && mfg.length() >= 3 && mfg[2] == 0x12) newTrackerType = TRACKER_APPLE_FINDMY;
        else if (companyId == 0x004C && mfg.length() >= 3 && mfg[2] == 0x02) newTrackerType = TRACKER_APPLE_IBEACON;
        else if (companyId == 0x00E0 && mfg.length() >= 3 && mfg[2] == 0xFC) newTrackerType = TRACKER_GOOGLE_FASTPAIR;
        else if (companyId == 0x000D) newTrackerType = TRACKER_TILE;
        else if (companyId == 0x0075 && mfg.length() >= 3 && mfg[2] == 0x42) newTrackerType = TRACKER_SAMSUNG_SMARTTAG;
        else if (companyId == 0x0006 && mfg.length() >= 3 && mfg[2] == 0x09) newTrackerType = TRACKER_MS_SWIFTPAIR;
        
        if (newName == "" && resolvedCompany != "") {
            if (newTrackerType == TRACKER_APPLE_FINDMY) newName = "Apple Find My";
            else if (newTrackerType == TRACKER_APPLE_IBEACON) newName = "Apple iBeacon";
            else if (newTrackerType == TRACKER_GOOGLE_FASTPAIR) newName = "Google FastPair";
            else if (newTrackerType == TRACKER_SAMSUNG_SMARTTAG) newName = "Samsung SmartTag";
            else if (newTrackerType == TRACKER_TILE) newName = "Tile Tracker";
            else if (newTrackerType == TRACKER_MS_SWIFTPAIR) newName = "MS Swift Pair";
            else {
                if (mfg.length() >= 3) {
                    char fallbackName[25];
                    snprintf(fallbackName, sizeof(fallbackName), "%s:0x%02X", 
                             resolvedCompany.substr(0, 12).c_str(), (uint8_t)mfg[2]);
                    newName = fallbackName;
                } else {
                    newName = resolvedCompany.substr(0, 24);
                }
            }
            newNamePriority = 1;
        }
      }
    }

    // ==========================================
    // STEP 2: Corporate Trackers & Eddystone (0x16)
    // ==========================================
    for (int k = 0; k < sdCount; k++) {
      NimBLEUUID sdUUID = advertisedDevice->getServiceDataUUID(k);
      
      if (sdUUID.bitSize() == 16) {
        uint16_t uuid16 = sdUUID.getNative()->u16.value;
        
        if (uuid16 == 0xFEAA) {
          newTrackerType = TRACKER_EDDYSTONE;
          if (newName == "") {
              newName = decodeEddystoneURL(advertisedDevice->getServiceData(k)).substr(0, 24);
          }
          break; 
        }

        if (newServiceId == 0) {
            newServiceId = uuid16; 
        }
      } 
    }

    // ==========================================
    // STEP 3: Appearance (0x19)
    // ==========================================
    if (advertisedDevice->haveAppearance()) {
      newAppearanceId = advertisedDevice->getAppearance();
    } 

    // ==========================================
    // STEP 4: Standard Services (0x02/0x03)
    // ==========================================
    if (advertisedDevice->haveServiceUUID()) {
      NimBLEUUID sUUID = advertisedDevice->getServiceUUID();
      if (sUUID.bitSize() == 16 && newServiceId == 0) {
        newServiceId = sUUID.getNative()->u16.value;
      }
    }

    // ==========================================
    // ARRAY MATCHING & STRUCT UPDATES
    // ==========================================
    const uint8_t* rawMac = advertisedDevice->getAddress().getNative();
    bool found = false;
    
    for (int i = 0; i < liveBleCount; i++) {
      if (memcmp((void*)(uint8_t*)liveBleData[i].mac, rawMac, 6) == 0) {
        liveBleData[i].hits++;
        liveBleData[i].lastSeen = millis();
        liveBleData[i].rssi = rssi;
        liveBleData[i].txPower = txPower; 

        if (newName != "") {
          strncpy((char*)liveBleData[i].name, newName.c_str(), 24);
          liveBleData[i].name[24] = '\0';
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

      strncpy((char*)liveBleData[liveBleCount].name, newName.c_str(), 24);
      liveBleData[liveBleCount].name[24] = '\0';

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
/*
void switchRadioMode(RadioMode targetMode) {
  pause_sniffing = true; 

  // ==========================================
  // THE UNION WIPE (Clears overlapping memory)
  // Always wipe using the LARGEST array (Wi-Fi)
  // ==========================================
  memset((void*)sessionData, 0, sizeof(sessionData));
  memset((void*)sortData, 0, sizeof(sortData));
  memset((void*)liveData, 0, sizeof(liveData));
  
  // Reset ALL Trackers regardless of mode
  sessionMacCount = 0;
  sortMacCount = 0;
  liveMacCount = 0;
  sessionOtherBytes = 0;
  liveOtherBytes = 0;

  sessionBleCount = 0;
  sortBleCount = 0;
  liveBleCount = 0;

  if (targetMode == RADIO_WIFI) {
    // 1. SOFT PAUSE BLE
    if (pBLEScan != nullptr) {
      pBLEScan->stop();
    }

    // 2. WAKE UP WI-FI
    esp_wifi_set_promiscuous(true);
    
  } else if (targetMode == RADIO_BLE) {
    // 1. SOFT PAUSE WI-FI 
    esp_wifi_set_promiscuous(false);

    // 2. COLD BOOT BLE (Only executes the very first time you switch!)
    if (!ble_initialized) {
      BLEDevice::init("");
      pBLEScan = BLEDevice::getScan();
      pBLEScan->setAdvertisedDeviceCallbacks(new BLEPassiveCallbacks(), true);
      pBLEScan->setActiveScan(false); 
      pBLEScan->setInterval(100);     
      pBLEScan->setWindow(99);        
      ble_initialized = true;
    }
    
    // 3. RESUME BLE
    pBLEScan->start(0, nullptr, false);
  }

  currentRadioMode = targetMode;
  pause_sniffing = false; 
}
*/

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
      strncpy(probeList[target_slot].vendor, known_vendor, 25);
      probeList[target_slot].needs_lookup = false; 
    } else {
      // We have no idea who this is. Tell Core 1 to check the SD Card.
      strncpy(probeList[target_slot].vendor, "Resolving...", 25);
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
  // 1. OSINT Probe Tracker Resolution Logic
  for (int i = 0; i < MAX_PROBE_SLOTS; i++) {
    if (probeList[i].needs_lookup) {
      MacRecord dummy;
      
      // A. Lock briefly just to copy the target MAC safely
      pause_sniffing = true;
      memcpy(dummy.mac, probeList[i].mac, 6);
      pause_sniffing = false; // Unlock immediately! Let the radio sniff.
      
      dummy.vendorFound = false;
      resolveMacVendor(&dummy); // Slow SD Card read happens safely on Core 1
      
      // B. Lock again to write the result
      pause_sniffing = true;
      
      // CRITICAL: Did Core 0 evict this slot while we were reading the SD card?
      if (memcmp(probeList[i].mac, dummy.mac, 6) == 0) {
        // The MAC matches! It is safe to write the vendor.
        strncpy(probeList[i].vendor, dummy.vendor, 24);
        probeList[i].vendor[24] = '\0';
        probeList[i].needs_lookup = false; 
      }
      // If the MAC doesn't match, we simply throw away the SD card result.
      // Core 0 already flagged the new MAC with needs_lookup=true, so we will catch it on the next loop.
      
      pause_sniffing = false; // Unlock
      break; 
    }
  }

  // 2. Main Wi-Fi Device List Asynchronous Resolution
  if (currentRadioMode == RADIO_WIFI) {
    for (int i = 0; i < sessionMacCount; i++) {
      if (sessionData[i].needs_lookup) {
        resolveMacVendor(&sessionData[i]);
        sessionData[i].needs_lookup = false; // Clear the flag
        break; // <-- Prevents wall-clock UI blocking
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

  delay(1000);
  tft.init();
  tft.setTouch(calData);
  tft.setRotation(1);
  tft.fillScreen(TFT_BLACK);
  drawChartHeader();
  drawChartFooter();

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


void loop() {
  processPendingVendors();
  uint16_t t_x = 0, t_y = 0;
  bool should_render = false;
  bool pressed = tft.getTouch(&t_x, &t_y);

  if (pressed) {

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
          should_render = true; // Trigger the engine to re-sort and redraw the bars
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
              return; // The button is cold. Ignore the touch entirely.
          }
          
          // 2. THE EXECUTION
          is_selecting_target = true;
          currentState = SCREEN_DEVICE_LIST;
          drawDeviceList();
          
          // 3. THE DEBOUNCE
          delay(400); // Wait 400ms before accepting new touches
      }
      // Probe Request Tracker Button
      else if (t_x > 300 && t_x < 450 && t_y > 140 && t_y < 180) {
        currentState = SCREEN_PROBE_TRACKER;
        probe_current_page = 0;
        drawProbeTracker();
        delay(300); 
      }
      // AP Scanner Button
      else if (t_x > 50 && t_x < 250 && t_y > 190 && t_y < 230) {
        if (currentRadioMode == RADIO_WIFI) {
          currentState = SCREEN_AP_SCAN;
          drawApScanner();
          delay(300);
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
        
        // THE FIX: Wake the Wi-Fi radio back up if we are in ANY Wi-Fi based mode!
          if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_CHANNELS) {
              esp_wifi_set_promiscuous(true); 
          }
        
        // Channel tuning for locked targets
        if (currentRadioMode == RADIO_WIFI && target_locked) {
          esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);
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
              
              // ==========================================
              // Smart Vendor Fallback
              // ==========================================
              if (sessionData[tapped_array_index].vendorFound) {
                  // Valid OUI match
                  strncpy(foxhunt_target_vendor, sessionData[tapped_array_index].vendor, 25);
              } else {
                  // Bitwise check for Locally Administered (Randomized) MAC addresses
                  if ((foxhunt_target_mac[0] & 0x02) == 0x02) {
                      strncpy(foxhunt_target_vendor, "<Randomized>", 25);
                  } else {
                      strncpy(foxhunt_target_vendor, "Unknown Device", 25);
                  }
              }
              foxhunt_target_vendor[25] = '\0'; // Safe null termination
              // ==========================================
              
              foxhunt_rssi_min = sessionData[tapped_array_index].rssi_min;
              foxhunt_rssi_max = sessionData[tapped_array_index].rssi_max;
              foxhunt_bounds_seeded = (sessionData[tapped_array_index].packets > 6);
              
              // THE CLEANUP: 
              // We are already locked to the AP's channel. target_locked is ALREADY true.
              // There is absolutely nothing we need to do to the channel hopper here!

            } else if (currentRadioMode == RADIO_AP) {
              // Allows Foxhunting routers from the AP list!
              memcpy(foxhunt_target_mac, sessionApData[tapped_array_index].bssid, 6);
              strncpy(foxhunt_target_vendor, sessionApData[tapped_array_index].ssid, 25);
              foxhunt_target_vendor[25] = '\0'; // Safe null termination
              
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
  } // <-- End of main if (pressed)

  // ==========================================
  // REAL-TIME FOXHUNT RADAR UPDATER
  // ==========================================
  if (currentState == SCREEN_FOXHUNT) {

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

  if (currentState == SCREEN_CHART || currentState == SCREEN_FOXHUNT) {
    static unsigned long lastTimer = 0;
    //bool should_render = false; // Local render trigger MOVED TO TOP

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
            should_render = true;
          }

          esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);

          // THE FIX: Only draw the channel indicator if we are on the main chart!
          if (currentState == SCREEN_CHART) {
              // Only black out the "CH: XX" part of the banner (80 pixels)
              tft.fillRect(5, 4, 80, 15, TFT_BLACK);
              tft.setFreeFont(&UbuntuMono_Regular9pt7b);
              tft.setTextDatum(TL_DATUM);
              
              // Match the colors we set in drawChartHeader!
              if (currentRadioMode == RADIO_AP) tft.setTextColor(TFT_GREEN);
              else if (currentRadioMode == RADIO_CHANNELS) tft.setTextColor(TFT_ORANGE);
              else tft.setTextColor(TFT_WHITE);

              char chStr[16];
              sprintf(chStr, "CH: %02d", CHANNELS[current_ch_idx]);
              tft.drawString(chStr, 5, 4);
          }
        }
      }
      else {
        // High-speed drain for Foxhunting / Target Locking
        if (millis() - lastTimer > LOCKED_UPDATE_INTERVAL) {
          lastTimer = millis();
          should_render = true;
        }
      }
    } 
    else if (currentRadioMode == RADIO_BLE) {
      // BLE MODE WATERFALL
      if (millis() - lastTimer > BLE_UPDATE_INTERVAL) { 
        lastTimer = millis();
        should_render = true; 
        
        // THE FIX: Only draw the BLE sniffing indicator if we are on the main chart!
        if (currentState == SCREEN_CHART) {
            tft.fillRect(5, 4, 200, 15, TFT_BLACK); 
            tft.setFreeFont(&UbuntuMono_Regular9pt7b);
            tft.setTextDatum(TL_DATUM);
            tft.setTextColor(TFT_ORANGE);
            tft.drawString("SNIFFING BLE DEVICES", 5, 4);
        }
      }
    }

    if (should_render) {
      pause_sniffing = true; 
      
     if (currentRadioMode == RADIO_WIFI) {
        // ==========================================
        // 1. WI-FI DATA PROCESSING PIPELINE
        // ==========================================
        
        // Snapshot the live buffer for the real-time UI/sorting
        // (Using void* casts to safely bypass volatile memory warnings)
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
                
                if (liveData[i].rate > 0) {
                    sessionData[j].rate = liveData[i].rate;
                }
                sessionData[j].last_seen = liveData[i].last_seen;
                
                // THE FIX: The Empty Window Gate
                // Only stretch the session bounds if the liveData window actually
                // captured a valid physical transmission (!= 0 and != -100).
                // The `|| sessionData[j]... == 0` ensures it breaks out of the initial C++ ghost state.
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
                    sessionData[j].smoothedDistance = 
                        (0.2 * rawDistance) + (0.8 * sessionData[j].smoothedDistance);
                }

                found = true;
                break;
            }
          }

          // B. If it's a completely new MAC, claim a new slot OR Evict
          if (!found) {
            int targetIndex = 0;

            if (sessionMacCount < MAX_MACS) {
              // 1. We have empty space, use it!
              targetIndex = sessionMacCount;
              sessionMacCount++;
            } else {
              // 2. Memory is full, execute LRU Eviction!
              uint32_t oldestTime = 0xFFFFFFFF; 
              for (int k = 0; k < MAX_MACS; k++) {
                if (sessionData[k].last_seen < oldestTime) {
                  oldestTime = sessionData[k].last_seen;
                  targetIndex = k;
                }
              }
              
              // 3. Overflow Bucket: Dump the evicted device's stats so global totals remain accurate!
              sessionOtherBytes += (sessionData[targetIndex].tx_bytes + sessionData[targetIndex].rx_bytes);
            }

            // --- POPULATE THE TARGET SLOT ---
            // 4. Bulk copy the entire raw packet struct into the target index
            memcpy((void*)&sessionData[targetIndex], (void*)&liveData[i], sizeof(MacRecord));
            
            // 5. Inject the math we calculated at the top of the pipeline
            sessionData[targetIndex].smoothedDistance = (rawDistance > 0) ? rawDistance : 0.0;
          }
        } // <-- Ends the 'for (int i...)' loop safely!

        // Wipe the live buffer clean so the interrupt can refill it
        memset((void*)liveData, 0, sizeof(liveData));
        liveMacCount = 0;
        liveOtherBytes = 0;

        // ==========================================
        // 2. SORTING & UI PREPARATION
        // ==========================================
        
        // --- FAST INSERTION SORT: WI-FI SNAPSHOT ---
        for (int i = 1; i < sortMacCount; i++) {
          MacRecord key = sortData[i];
          
          // Dynamically grab the correct math based on the touch button!
          double key_val = getSortMetric(key, currentSortMode); 
          int j = i - 1;

          if (sort_descending) {
            while (j >= 0 && getSortMetric(sortData[j], currentSortMode) < key_val) {
              sortData[j + 1] = sortData[j];
              j = j - 1;
            }
          } else {
            // Preserved safety catch: keeps 0-value items at the bottom!
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
          
          // Dynamically grab the correct math based on the touch button!
          double key_val = getSortMetric(key, currentSortMode); 
          int j = i - 1;

          if (sort_descending) {
            while (j >= 0 && getSortMetric(sessionData[j], currentSortMode) < key_val) {
              sessionData[j + 1] = sessionData[j];
              j = j - 1;
            }
          } else {
            // Preserved safety catch: keeps 0-value items at the bottom!
            while (j >= 0 && getSortMetric(sessionData[j], currentSortMode) > key_val && key_val > 0.0) {
              sessionData[j + 1] = sessionData[j];
              j = j - 1;
            }
          }
          sessionData[j + 1] = key;
        }

        // ==========================================
        // Calculate "Other" for the live waterfall chart
        // ==========================================
        // 1. Start with any packets that overflowed the buffer entirely
        sortOtherBytes = liveOtherBytes; 
        
        // 2. Add the TOTAL BYTES of everything from index 8 onwards, 
        //    regardless of what metric the array is currently sorted by!
        for(int i = 8; i < sortMacCount; i++) {
          sortOtherBytes += (sortData[i].tx_bytes + sortData[i].rx_bytes);
        }

        // 3. Attempt Vendor Resolution for ONLY the top 8 visible devices
        for(int i = 0; i < 8 && i < sortMacCount; i++) {
          resolveMacVendor(&sortData[i]);
        }
      }
      else if (currentRadioMode == RADIO_BLE) {
        // ==========================================
        // 2. BLE DATA PROCESSING PIPELINE
        // ==========================================
        // Snapshot the live data for the waterfall
        memcpy(sortBleData, (void*)liveBleData, sizeof(liveBleData));
        sortBleCount = liveBleCount;

        for (int i = 0; i < liveBleCount; i++) {
          // --- INJECT FOXHUNT TRACKER ---
          // Notice the explicit (void*) cast added to the MAC
          bool found = false;
          float rawDistance = calculateRfDistance(liveBleData[i].rssi, liveBleData[i].txPower, RADIO_BLE_24GHZ);
          
          for (int j = 0; j < sessionBleCount; j++) {
            
            // CRITICAL FIX 1: Use memcmp for raw byte arrays, NOT strcmp!
            if (memcmp(sessionBleData[j].mac, (void*)(uint8_t*)liveBleData[i].mac, 6) == 0) {
                
                sessionBleData[j].hits += liveBleData[i].hits;
                sessionBleData[j].rssi = liveBleData[i].rssi;
                sessionBleData[j].txPower = liveBleData[i].txPower; // Keep the math engine fed with fresh data!

                // CRITICAL FIX 2: Propagate the fresh timestamp from the live buffer!
                sessionBleData[j].lastSeen = liveBleData[i].lastSeen;

                // EMA smooth the distance into the session record
                if (rawDistance > 0) {
                    sessionBleData[j].smoothedDistance =
                        (0.2 * rawDistance) + (0.8 * sessionBleData[j].smoothedDistance);
                }

                // --- NEW: HYBRID OSINT PROPAGATION ---
                
                // 1. Handle the dynamic Name string exactly as you did before
                if (liveBleData[i].name[0] != '\0') {
                    strncpy((char*)sessionBleData[j].name, (char*)liveBleData[i].name, 24);
                    sessionBleData[j].name[24] = '\0'; // Guarantee safe termination
                }
                
                // 2. Replace the massive string copies with tiny ID assignments
                if (liveBleData[i].trackerType != TRACKER_NONE) {
                    sessionBleData[j].trackerType = liveBleData[i].trackerType;
                }
                if (liveBleData[i].appearanceId != 0) {
                    sessionBleData[j].appearanceId = liveBleData[i].appearanceId;
                }
                if (liveBleData[i].serviceId != 0) {
                    sessionBleData[j].serviceId = liveBleData[i].serviceId;
                }

                found = true;
                break;
            }
          }

          // B. If it's a completely new device, claim a new slot OR Evict
          if (!found) {
            int targetIndex = 0;

            if (sessionBleCount < MAX_BLE_DEVICES) {
              // 1. We have empty space, use it!
              targetIndex = sessionBleCount;
              sessionBleCount++;
            } else {
              // 2. Memory is full, execute LRU Eviction!
              uint32_t oldestTime = 0xFFFFFFFF; 
              for (int k = 0; k < MAX_BLE_DEVICES; k++) {
                // Note: using camelCase lastSeen for BLE struct
                if (sessionBleData[k].lastSeen < oldestTime) {
                  oldestTime = sessionBleData[k].lastSeen;
                  targetIndex = k;
                }
              }
              // (No overflow bucket needed for BLE since we don't track packet byte sizes)
            }

            // --- POPULATE THE TARGET SLOT ---
            // 3. Bulk copy the entire raw packet struct into the target index
            memcpy((void*)&sessionBleData[targetIndex], (void*)&liveBleData[i], sizeof(BLERecord));
            
            // 4. Inject the math we calculated at the top of the pipeline
            sessionBleData[targetIndex].smoothedDistance = (rawDistance > 0) ? rawDistance : 0.0;
          }
        }

        // Dump the bucket for the next scanning wave
        memset((void*)liveBleData, 0, sizeof(liveBleData));
        liveBleCount = 0;

        // --- FAST INSERTION SORT: BLE SNAPSHOT (WATERFALL) ---
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
            // Safety catch: explicitly check 'hits' so empty memory slots stay at the bottom
            while (j >= 0 && getBleSortMetric(sortBleData[j], currentBleSortMode) > key_val && key.hits > 0) {
              sortBleData[j + 1] = sortBleData[j];
              j = j - 1;
            }
          }
          sortBleData[j + 1] = key;
        }

        // --- FAST INSERTION SORT: BLE SESSION (SEEN DEVICES) ---
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
        // ==========================================
        // 3. AP NETWORK DATA PROCESSING PIPELINE
        // ==========================================
                
        // 1. Snapshot the live data for the waterfall
        memcpy((void*)sortApData, (void*)liveApData, sizeof(liveApData));
        sortApCount = liveApCount;
        
        // 2. Sync to Historical Session
        for (int i = 0; i < liveApCount; i++) {
          bool found = false;
          float rawDistance = calculateRfDistance(liveApData[i].rssi, 0, RADIO_WIFI_24GHZ);

          // A. Try to update an existing AP
          for (int j = 0; j < sessionApCount; j++) {
            if (memcmp(sessionApData[j].bssid, (void*)liveApData[i].bssid, 6) == 0) {
              
              sessionApData[j].packets += liveApData[i].packets;
              sessionApData[j].tx_bytes += liveApData[i].tx_bytes;
              sessionApData[j].rx_bytes += liveApData[i].rx_bytes;
              sessionApData[j].sum_bytes += liveApData[i].sum_bytes;
              sessionApData[j].sum_sq_bytes += liveApData[i].sum_sq_bytes;
              
              sessionApData[j].last_seen = liveApData[i].last_seen;
              sessionApData[j].rssi = liveApData[i].rssi;
              if (liveApData[i].rssi_min < sessionApData[j].rssi_min || 
                  sessionApData[j].rssi_min == 0) {
                  sessionApData[j].rssi_min = liveApData[i].rssi_min;
              }
              if (liveApData[i].rssi_max > sessionApData[j].rssi_max || 
                  sessionApData[j].rssi_max == 0) {
                  sessionApData[j].rssi_max = liveApData[i].rssi_max;
              }
              sessionApData[j].channel = liveApData[i].channel;
              if (sessionApData[j].country[0] == '\0' && liveApData[i].country[0] != '\0') {
                  sessionApData[j].country[0] = liveApData[i].country[0];
                  sessionApData[j].country[1] = liveApData[i].country[1];
                  sessionApData[j].country[2] = '\0';
              }
              
              // Only overwrite the historical rate if the new one is faster
              if (liveApData[i].max_rate > sessionApData[j].max_rate) {
                  sessionApData[j].max_rate = liveApData[i].max_rate;
              }
              
              if (rawDistance > 0) {
                  sessionApData[j].smoothedDistance = 
                      (0.2 * rawDistance) + (0.8 * sessionApData[j].smoothedDistance);
              }
              
              if (strcmp(sessionApData[j].ssid, "<UNKNOWN>") == 0 && strcmp((char*)liveApData[i].ssid, "<UNKNOWN>") != 0) {
                strcpy((char*)sessionApData[j].ssid, (char*)liveApData[i].ssid);
              }
              
              found = true; break;
            }
          }
          
          // B. If it's a completely new AP, claim a new slot OR Evict
          if (!found) {
            int targetIndex = -1;

            if (sessionApCount < MAX_AP_RECORDS) {
              // Space available, claim the next slot
              targetIndex = sessionApCount;
              sessionApCount++;
            } else {
              // ==========================================
              // THE STALE & WEAK HYBRID EVICTION (Sync)
              // ==========================================
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

              // 1. The Ghost Hunt
              if ((now - oldest_time) > 60000) {
                targetIndex = stalest_idx;
              } 
              // 2. The Weakest Link
              else if (liveApData[i].rssi > lowest_rssi) {
                targetIndex = weakest_idx;
              }
            }

            // If we claimed a slot, pull the data from the live buffer!
            if (targetIndex != -1) {
               memcpy((void*)&sessionApData[targetIndex], (void*)&liveApData[i], sizeof(ApRecord));
               sessionApData[targetIndex].smoothedDistance = (rawDistance > 0) ? rawDistance : 0.0;
            }
          }
        }
        
        // 3. Clear the traffic counters, but PRESERVE THE DICTIONARY!
        for (int i = 0; i < liveApCount; i++) {
            liveApData[i].packets = 0;
            liveApData[i].tx_bytes = 0;
            liveApData[i].rx_bytes = 0;
            liveApData[i].sum_bytes = 0;
            liveApData[i].sum_sq_bytes = 0;
            
            // We intentionally do NOT reset max_rate, bssid, or ssid.
            // We also intentionally do NOT reset liveApCount to 0!
        }
        
        // 4. --- FAST INSERTION SORT: AP SNAPSHOT ---
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
            // Safety catch: keeps 0-value items at the bottom
            while (j >= 0 && getSortMetric(sortApData[j], currentSortMode) > key_val && key_val > 0.0) {
              sortApData[j + 1] = sortApData[j];
              j = j - 1;
            }
          }
          sortApData[j + 1] = key;
        }

        // --- FAST INSERTION SORT: AP SESSION (SEEN DEVICES) ---
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
        
        // 5. Calculate "Other" Bytes for the AP Waterfall
        sortOtherBytes = 0; 
        for(int i = 8; i < sortApCount; i++) {
          sortOtherBytes += (sortApData[i].tx_bytes + sortApData[i].rx_bytes);
        }
      }
      else if (currentRadioMode == RADIO_CHANNELS) {
        // ==========================================
        // 4. CHANNEL SPECTRUM PROCESSING PIPELINE
        // ==========================================
        // 1. Snapshot the live data for the waterfall
        memcpy((void*)sortChannelData, (void*)liveChannelData, sizeof(liveChannelData));
        sortChannelCount = liveChannelCount;
        
        // 2. Sync to Historical Session
        for (int i = 0; i < liveChannelCount; i++) {
          bool found = false;
          for (int j = 0; j < sessionChannelCount; j++) {
            if (sessionChannelData[j].channel == liveChannelData[i].channel) {
              // 1. Accumulate Volume
              sessionChannelData[j].packets += liveChannelData[i].packets;
              sessionChannelData[j].tx_bytes += liveChannelData[i].tx_bytes;
              sessionChannelData[j].rx_bytes += liveChannelData[i].rx_bytes;
              sessionChannelData[j].sum_bytes += liveChannelData[i].sum_bytes;
              sessionChannelData[j].sum_sq_bytes += liveChannelData[i].sum_sq_bytes;
              sessionChannelData[j].last_seen = liveChannelData[i].last_seen;
              
              // 2. Overwrite EMA State (Sync the physics model)
              sessionChannelData[j].avg_rssi = liveChannelData[i].avg_rssi;
              sessionChannelData[j].ema_variance = liveChannelData[i].ema_variance;
              sessionChannelData[j].prev_rssi = liveChannelData[i].prev_rssi;
              sessionChannelData[j].ema_cov = liveChannelData[i].ema_cov;
              
              found = true; break;
            }
          }
          
          // (Keep the memcpy block exactly as it is below this, 
          // because memcpy perfectly copies all the floats automatically for new channels!)
          
          if (!found && sessionChannelCount < MAX_CHANNEL_RECORDS) {
             memcpy((void*)&sessionChannelData[sessionChannelCount], (void*)&liveChannelData[i], sizeof(ChannelRecord));
             sessionChannelCount++;
          }
        }
        
        // 3. Clear traffic counters for the next hop
        for (int i = 0; i < liveChannelCount; i++) {
            liveChannelData[i].packets = 0;
            liveChannelData[i].tx_bytes = 0;
            liveChannelData[i].rx_bytes = 0;
            liveChannelData[i].sum_bytes = 0;
            liveChannelData[i].sum_sq_bytes = 0;
        }
        
        // 4. --- DYNAMIC INSERTION SORT: CHANNEL SNAPSHOT ---
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

        // --- DYNAMIC INSERTION SORT: CHANNEL SESSION (SEEN DEVICES) ---
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
                
        // 5. Calculate "Other" Bytes for channels beyond the top 8
        sortOtherBytes = 0; 
        for(int i = 8; i < sortChannelCount; i++) {
          sortOtherBytes += (sortChannelData[i].tx_bytes + sortChannelData[i].rx_bytes);
        }
      }

      // ==========================================
  // THE BACKGROUND CORRELATION & MERGE ENGINE
  // ==========================================
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
             // (Old Step 5 was successfully deleted from here)
         }
      }
    }
  }
  // ==========================================

      pause_sniffing = false;

      if (currentState == SCREEN_CHART) {

      int displayCount = 0;
      if (currentRadioMode == RADIO_WIFI) displayCount = sortMacCount;
      else if (currentRadioMode == RADIO_BLE) displayCount = sortBleCount;
      else if (currentRadioMode == RADIO_AP) displayCount = sortApCount;
      else if (currentRadioMode == RADIO_CHANNELS) displayCount = sortChannelCount;

      if (displayCount > 0 || ((currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP || currentRadioMode == RADIO_CHANNELS) && sortOtherBytes > 0)) {

        // 1. CALCULATE AND DRAW "OTHER" IN THE TOP MENU BANNER
        int otherCount = 0;
        if (displayCount > 8) {
          otherCount = displayCount - 8;
        }

        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.setTextDatum(TL_DATUM); 
        tft.setTextColor(colors[8]);
        tft.fillRect(315, 4, 95, 15, TFT_BLACK);
        char otherStr[16];
        sprintf(otherStr, "OTHER:%d", otherCount);
        tft.drawString(otherStr, 315, 4);

        // 2. DRAW THE MAIN 8-DEVICE LEGEND
        tft.fillRect(0, 18, 480, HEADER_HEIGHT - 18, TFT_BLACK);
        tft.setFreeFont(&UbuntuMono_Regular11pt7b);

        // Dynamically determine the ceiling for the loop based on the active mode
        int renderCount = 0;
        if (currentRadioMode == RADIO_WIFI) renderCount = sortMacCount;
        else if (currentRadioMode == RADIO_BLE) renderCount = sortBleCount;
        else if (currentRadioMode == RADIO_AP) renderCount = sortApCount;
        else if (currentRadioMode == RADIO_CHANNELS) renderCount = sortChannelCount;

        for(int i = 0; i < 8 && i < renderCount; i++) {
          char short_text[20];

          if (currentRadioMode == RADIO_WIFI) {
            strncpy(short_text, sortData[i].vendor, 19);
            short_text[19] = '\0';
          } 
          else if (currentRadioMode == RADIO_BLE) {
            // BLE: Use the snapshot broadcast Name. If empty, fallback to MAC address.
            if (strlen(sortBleData[i].name) > 0) {
              strncpy(short_text, sortBleData[i].name, 19);
              short_text[19] = '\0';
            } else {
              // Format the 6 raw bytes directly into the short_text buffer.
              snprintf(short_text, sizeof(short_text), "%02X:%02X:%02X:%02X:%02X:%02X", 
                       sortBleData[i].mac[0], sortBleData[i].mac[1], sortBleData[i].mac[2], 
                       sortBleData[i].mac[3], sortBleData[i].mac[4], sortBleData[i].mac[5]);
            }
          } 
          else if (currentRadioMode == RADIO_AP) {
            // 1. Determine if this SSID has a clone in the dictionary
            bool has_clone = false;
            if (strcmp(sortApData[i].ssid, "<HIDDEN>") != 0 && strcmp(sortApData[i].ssid, "<UNKNOWN>") != 0) {
              for (int j = 0; j < sortApCount; j++) {
                if (i != j && strcmp(sortApData[i].ssid, sortApData[j].ssid) == 0) {
                  has_clone = true;
                  break;
                }
              }
            }

            // 2. Format the output based on clone status
            if (strcmp(sortApData[i].ssid, "<HIDDEN>") == 0 || strcmp(sortApData[i].ssid, "<UNKNOWN>") == 0) {
               snprintf(short_text, sizeof(short_text), "%s", sortApData[i].ssid);
            } else if (has_clone) {
               char temp_ssid[13];
               strncpy(temp_ssid, sortApData[i].ssid, 12); 
               temp_ssid[12] = '\0';
               snprintf(short_text, sizeof(short_text), "%s~%02X%02X", 
                        temp_ssid, sortApData[i].bssid[4], sortApData[i].bssid[5]);
            } else {
               // Unique network! Give it more characters since we don't need the bracket suffix
               strncpy(short_text, sortApData[i].ssid, 19);
               short_text[19] = '\0';
            }
          }
          else if (currentRadioMode == RADIO_CHANNELS) {
             // Simply print the channel number (e.g., "CH 06")
             snprintf(short_text, sizeof(short_text), "CH %02d", sortChannelData[i].channel);
          }


          tft.setTextColor(colors[i]);
          int x_pos = 5 + (i % 2) * 240; 
          int y_pos = 22 + (i / 2) * 20;

          tft.drawString(short_text, x_pos, y_pos);
        }
      }

      // --- WATERFALL CHART PLOTTING MATH ---

      // 1. Establish the Dual-Pane boundaries
      int chart_area_height = CHART_BOTTOM - HEADER_HEIGHT;
      int split_y = HEADER_HEIGHT + (chart_area_height * 3) / 4; // The 75% line

      // ==========================================
      // 2. The ECG Scan Window (Wipes 44 pixels ahead)
      // ==========================================
      int ERASER_WIDTH = 44;
      
      // Pure wipe logic: Clears the void. Borders are drawn at the end to survive rescales.
      if (current_x + ERASER_WIDTH <= 480) {
          tft.fillRect(current_x, HEADER_HEIGHT + 1, ERASER_WIDTH, CHART_BOTTOM - HEADER_HEIGHT, TFT_BLACK);
      } else {
          int w1 = 480 - current_x;
          tft.fillRect(current_x, HEADER_HEIGHT + 1, w1, CHART_BOTTOM - HEADER_HEIGHT, TFT_BLACK);
          tft.fillRect(0, HEADER_HEIGHT + 1, ERASER_WIDTH - w1, CHART_BOTTOM - HEADER_HEIGHT, TFT_BLACK);
      }

      // 3. Draw the X-Axis Time Ticks & Separator Line
      if (current_x % 60 == 0) {
          tft.drawLine(current_x, split_y - 3, current_x, split_y + 3, TFT_WHITE);
          tft.drawLine(current_x + 1, split_y - 3, current_x + 1, split_y + 3, TFT_WHITE);
      } else {
          tft.drawPixel(current_x, split_y, TFT_DARKGREY);
          tft.drawPixel(current_x + 1, split_y, TFT_DARKGREY);
      }

      int current_y = split_y - 1; // Top chart builds UP from the split line
      uint32_t current_total_metric = 0; // Universal tracker for the bottom pane

      if (currentRadioMode == RADIO_WIFI) {
        // ==========================================
        // WI-FI PLOTTING (Bytes & Log Scale)
        // ==========================================
        uint32_t total_bytes = sortOtherBytes;
        for(int i = 0; i < 8 && i < sortMacCount; i++) {
          total_bytes += (sortData[i].tx_bytes + sortData[i].rx_bytes);
        }
        
        current_total_metric = total_bytes; 

        if (total_bytes > 0) {
          double log_total = 0;
          if (useLogScale) {
            for(int j = 0; j < 8 && j < sortMacCount; j++) {
              uint32_t device_total = sortData[j].tx_bytes + sortData[j].rx_bytes;
              log_total += log10((double)device_total + 1.0);
            }
            log_total += log10((double)sortOtherBytes + 1.0);
          }

          for(int i = 0; i < 8 && i < sortMacCount; i++) {
            double fraction;
            uint32_t current_device_bytes = sortData[i].tx_bytes + sortData[i].rx_bytes;

            if (useLogScale) fraction = log10((double)current_device_bytes + 1.0) / log_total;
            else fraction = (double)current_device_bytes / (double)total_bytes;

            int bar_height = (int)(fraction * (split_y - HEADER_HEIGHT - 1));
            if (bar_height > (split_y - HEADER_HEIGHT - 1)) bar_height = split_y - HEADER_HEIGHT - 1;

            tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);
            current_y -= bar_height;
          }

          if (sortOtherBytes > 0 && current_y > HEADER_HEIGHT) {
            tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[8]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[8]);
          } else if (sortOtherBytes == 0 && current_y > HEADER_HEIGHT && sortMacCount > 0) {
            tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[sortMacCount - 1]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[sortMacCount - 1]);
          }
        }
      }
      else if (currentRadioMode == RADIO_BLE) {
        // ==========================================
        // BLE PLOTTING (Hits / Traffic volume)
        // ==========================================
        uint32_t total_hits = 0;
        uint32_t other_hits = 0;
        int ble_count = (sortBleCount > 8) ? 8 : sortBleCount;

        for(int i = 0; i < ble_count; i++) total_hits += sortBleData[i].hits;

        if (sortBleCount > 8) {
          for (int i = 8; i < sortBleCount; i++) other_hits += sortBleData[i].hits;
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
            
            int bar_height = (int)(fraction * (split_y - HEADER_HEIGHT - 1));
            if (bar_height > (split_y - HEADER_HEIGHT - 1)) bar_height = split_y - HEADER_HEIGHT - 1;

            tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);
            current_y -= bar_height;
          }
          
          if (other_hits > 0 && current_y > HEADER_HEIGHT) {
            tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[8]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[8]);
          } else if (other_hits == 0 && current_y > HEADER_HEIGHT && ble_count > 0) {
            tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[ble_count - 1]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[ble_count - 1]);
          }
        }
      }
      else if (currentRadioMode == RADIO_AP) {
          // ==========================================
          // AP PLOTTING (Traffic Bytes)
          // ==========================================
          uint32_t total_bytes = sortOtherBytes;
          for(int i = 0; i < 8 && i < sortApCount; i++) total_bytes += (sortApData[i].tx_bytes + sortApData[i].rx_bytes);

          current_total_metric = total_bytes; 

          if (total_bytes > 0) {
            double log_total = 0;
            if (useLogScale) {
              for(int j = 0; j < 8 && j < sortApCount; j++) {
                uint32_t device_total = sortApData[j].tx_bytes + sortApData[j].rx_bytes;
                log_total += log10((double)device_total + 1.0);
              }
              log_total += log10((double)sortOtherBytes + 1.0);
            }

            for(int i = 0; i < 8 && i < sortApCount; i++) {
              double fraction;
              uint32_t current_device_bytes = sortApData[i].tx_bytes + sortApData[i].rx_bytes;
              
              if (useLogScale) fraction = log10((double)current_device_bytes + 1.0) / log_total;
              else fraction = (double)current_device_bytes / (double)total_bytes;

              int bar_height = (int)(fraction * (split_y - HEADER_HEIGHT - 1));
              if (bar_height > (split_y - HEADER_HEIGHT - 1)) bar_height = split_y - HEADER_HEIGHT - 1;

              tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
              tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);
              current_y -= bar_height;
            }

            if (sortOtherBytes > 0 && current_y > HEADER_HEIGHT) {
              tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[8]);
              tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[8]);
            } else if (sortOtherBytes == 0 && current_y > HEADER_HEIGHT && sortApCount > 0) {
              tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[sortApCount - 1]);
              tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[sortApCount - 1]);
            }
          }
      }
      else if (currentRadioMode == RADIO_CHANNELS) {
          // ==========================================
          // CHANNEL PLOTTING
          // ==========================================
          uint32_t total_bytes = sortOtherBytes;
          for(int i = 0; i < 8 && i < sortChannelCount; i++) total_bytes += (sortChannelData[i].tx_bytes + sortChannelData[i].rx_bytes);

          current_total_metric = total_bytes; 

          if (total_bytes > 0) {
            double log_total = 0;
            if (useLogScale) {
              for(int j = 0; j < 8 && j < sortChannelCount; j++) {
                uint32_t c_total = sortChannelData[j].tx_bytes + sortChannelData[j].rx_bytes;
                log_total += log10((double)c_total + 1.0);
              }
              log_total += log10((double)sortOtherBytes + 1.0);
            }

            for(int i = 0; i < 8 && i < sortChannelCount; i++) {
              double fraction;
              uint32_t current_c_bytes = sortChannelData[i].tx_bytes + sortChannelData[i].rx_bytes;
              
              if (useLogScale) fraction = log10((double)current_c_bytes + 1.0) / log_total;
              else fraction = (double)current_c_bytes / (double)total_bytes;

              int bar_height = (int)(fraction * (split_y - HEADER_HEIGHT - 1));
              if (bar_height > (split_y - HEADER_HEIGHT - 1)) bar_height = split_y - HEADER_HEIGHT - 1;

              tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
              tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);
              current_y -= bar_height;
            }

            if (sortOtherBytes > 0 && current_y > HEADER_HEIGHT) {
              tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[8]);
              tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[8]);
            } else if (sortOtherBytes == 0 && current_y > HEADER_HEIGHT && sortChannelCount > 0) {
              tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[sortChannelCount - 1]);
              tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[sortChannelCount - 1]);
            }
          }
      }

      // ==========================================
      // BOTTOM PANE: ABSOLUTE VOLUME GRAPH & SCALING
      // ==========================================
      // Local statics to track the epoch without polluting your globals
      static uint32_t current_sweep_peak = 0;
      static RadioMode last_seen_mode = currentRadioMode;
      
      // Safety reset: Wipe the epoch peak if you changed radio modes mid-sweep
      if (currentRadioMode != last_seen_mode) {
          current_sweep_peak = 0;
          last_seen_mode = currentRadioMode;
      }

      bool did_rescale = false; 
      int h_index = current_x / 2;
      traffic_history[h_index] = current_total_metric;

      // 1. Track the highest traffic peak for the current sweep
      if (current_total_metric > current_sweep_peak) {
          current_sweep_peak = current_total_metric;
      }

      // 2. INSTANT UP-SCALE (The Lazy Rescale)
      if (current_total_metric > absolute_max_traffic) {
          absolute_max_traffic = current_total_metric + (current_total_metric / 5); 
          did_rescale = true; 
          
          tft.fillRect(0, split_y + 1, 480, CHART_BOTTOM - split_y, TFT_BLACK);
          
          for (int c = 0; c < 240; c++) {
              int px = c * 2;

              // --- THE REPAIR: Redraw the bottom half of the tick marks ---
              if (px % 60 == 0) {
                  tft.drawLine(px, split_y + 1, px, split_y + 3, TFT_WHITE);
                  tft.drawLine(px + 1, split_y + 1, px + 1, split_y + 3, TFT_WHITE);
              }

              if (traffic_history[c] > 0) {
                  int h = (int)(((double)traffic_history[c] / (double)absolute_max_traffic) * (CHART_BOTTOM - split_y - 1));
                  
                  // Cap the bar height to protect the ticks (Stops at split_y + 4)
                  if (h > CHART_BOTTOM - split_y - 4) h = CHART_BOTTOM - split_y - 4; 
                  
                  tft.drawLine(px, CHART_BOTTOM, px, CHART_BOTTOM - h, TFT_GREEN);
                  tft.drawLine(px + 1, CHART_BOTTOM, px + 1, CHART_BOTTOM - h, TFT_GREEN);
              }
          }
      } else {
          // Normal plot operation
          if (current_total_metric > 0) {
              int h = (int)(((double)current_total_metric / (double)absolute_max_traffic) * (CHART_BOTTOM - split_y - 1));
              
              // Cap the bar height here as well
              if (h > CHART_BOTTOM - split_y - 4) h = CHART_BOTTOM - split_y - 4; 
              
              tft.drawLine(current_x, CHART_BOTTOM, current_x, CHART_BOTTOM - h, TFT_GREEN);
              tft.drawLine(current_x + 1, CHART_BOTTOM, current_x + 1, CHART_BOTTOM - h, TFT_GREEN);
          }
      }

      // ==========================================
      // FINAL OVERLAY: WINDOW BORDERS (Z-Order Top)
      // ==========================================
      // 1. Trailing Edge (Frames the back of the data)
      tft.drawFastVLine(current_x + 2, HEADER_HEIGHT + 1, CHART_BOTTOM - HEADER_HEIGHT, TFT_WHITE);
      
      // 2. Leading Edge (Frames the front of the void)
      // Drawn here so it sits cleanly on top of any full-screen rescale wipes!
      if (current_x + ERASER_WIDTH <= 480) {
          tft.drawFastVLine(current_x + ERASER_WIDTH - 1, HEADER_HEIGHT + 1, CHART_BOTTOM - HEADER_HEIGHT, TFT_WHITE);
      } else {
          int w1 = 480 - current_x;
          tft.drawFastVLine(ERASER_WIDTH - w1 - 1, HEADER_HEIGHT + 1, CHART_BOTTOM - HEADER_HEIGHT, TFT_WHITE);
      }
      
      // ==========================================
      // PUNCH-OUT Y-AXIS OVERLAY LABELS
      // ==========================================
      // Only execute if the sweeping line is currently in the window,
      // or if the bottom chart just wiped itself during a rescale.
      if (current_x <= 480 - ERASER_WIDTH || did_rescale) {
          int text_x = current_x + 6; 
          
          // Safety: If the window is near the right edge, don't draw labels off-screen
          if (text_x > 480 - 40) text_x = 480 - 40; 

          tft.setFreeFont(&UbuntuMono_Regular8pt7b);
          tft.setTextDatum(TL_DATUM);

          // Top Pane Labels
          tft.setTextColor(TFT_WHITE);
          tft.drawString("100%", text_x, HEADER_HEIGHT + 4);
          int mid_y = HEADER_HEIGHT + ((split_y - HEADER_HEIGHT) / 2);
          tft.drawString("50%", text_x, mid_y - 6);

          // Time Legend
          tft.setTextColor(TFT_DARKGREY);
          if (currentRadioMode == RADIO_BLE || target_locked) tft.drawString("|=1m", text_x, split_y - 15); 
          else tft.drawString("|=2m", text_x, split_y - 15);

          // Custom Text Formatter: Pure Base-2 alignment
          char maxStr[16];
          if (currentRadioMode == RADIO_BLE) {
              snprintf(maxStr, sizeof(maxStr), "%lu", absolute_max_traffic);
          } else {
              if (absolute_max_traffic < 1024) snprintf(maxStr, sizeof(maxStr), "%lu", absolute_max_traffic);
              else if (absolute_max_traffic < 1048576) snprintf(maxStr, sizeof(maxStr), "%luK", absolute_max_traffic / 1024);
              else if (absolute_max_traffic < 1073741824) snprintf(maxStr, sizeof(maxStr), "%luM", absolute_max_traffic / 1048576);
              else snprintf(maxStr, sizeof(maxStr), "%.1fG", (float)absolute_max_traffic / 1073741824.0);
          }
          
          // Bottom Pane Labels
          tft.setTextColor(TFT_GREEN);
          tft.drawString(maxStr, text_x, split_y + 4);
          tft.drawString("0", text_x, CHART_BOTTOM - 15);
      }

      // ==========================================
      // END OF SWEEP: EPOCH DOWN-SCALING
      // ==========================================
      current_x += 2;
      if (current_x >= 480) {
          current_x = 0;
          
          // Calculate what the ceiling SHOULD be based on the sweep that just ended
          uint32_t next_scale = current_sweep_peak + (current_sweep_peak / 5);
          if (next_scale < 10) next_scale = 10; // Floor safety prevents div-by-zero
          
          // If the traffic died down, shrink the scale so small spikes are visible again
          if (next_scale < absolute_max_traffic) {
              absolute_max_traffic = next_scale;
              
              // Wipe the bottom pane
              tft.fillRect(0, split_y + 1, 480, CHART_BOTTOM - split_y, TFT_BLACK);
              
              // Redraw the 240-column history array mapping it upward to the lowered ceiling
              for (int c = 0; c < 240; c++) {
                  int px = c * 2;

                  // --- THE REPAIR: Redraw the bottom half of the tick marks ---
                  if (px % 60 == 0) {
                      tft.drawLine(px, split_y + 1, px, split_y + 3, TFT_WHITE);
                      tft.drawLine(px + 1, split_y + 1, px + 1, split_y + 3, TFT_WHITE);
                  }

                  if (traffic_history[c] > 0) {
                      int h = (int)(((double)traffic_history[c] / (double)absolute_max_traffic) * (CHART_BOTTOM - split_y - 1));
                      
                      // Cap the bar height to protect the ticks (Stops at split_y + 4)
                      if (h > CHART_BOTTOM - split_y - 4) h = CHART_BOTTOM - split_y - 4; 
                      
                      tft.drawLine(px, CHART_BOTTOM, px, CHART_BOTTOM - h, TFT_GREEN);
                      tft.drawLine(px + 1, CHART_BOTTOM, px + 1, CHART_BOTTOM - h, TFT_GREEN);
                  }
              }
          }
          
          // Reset the peak tracker to prepare for the new sweep
          current_sweep_peak = 0;
      }
    }
  }
}
}