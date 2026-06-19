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
#include "UbuntuMono_B9pt7b.h"
#include "UbuntuMono_RI9pt7b.h"
#include <cmath>
#include <atomic> // Add this to your includes

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
const int APS_PER_PAGE = 5; // Number of APs that fit safely between the header and footer

int target_rssi = 0;

SdFs sd;

// ==========================================
// FOXHUNT STATE GLOBALS
// ==========================================
bool is_selecting_target = false; 
bool is_foxhunting = false;
uint8_t foxhunt_target_mac[6] = {0};
char foxhunt_target_vendor[25] = "Unknown";

// Foxhunt Math & Alert State
float smoothed_rssi = -100.0;
int baseline_rssi = -100;
unsigned long last_foxhunt_update = 0;
bool target_behind_alert = false;
unsigned long alert_start_time = 0;
const int RSSI_DROP_THRESHOLD = 12; // dBm drop to trigger body-block alert

// --- Forward Declarations for OSINT Probe Tracker ---
int addSsidToPool(const char* ssid, int head_idx, bool &already_exists, bool &added, uint8_t current_count);
void processProbeRequestShared(uint8_t* mac, const char* ssid, const char* known_vendor = "", int8_t rssi = -100);

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
  // 4-byte variables first
  unsigned long first_seen; 
  unsigned long last_seen;
  int first_ssid_idx;               
  float smoothedDistance;   // <--- NEW: 4-byte physics variable
  
  // 2-byte variables
  uint16_t hits;
  
  // 1-byte arrays and variables
  uint8_t mac[6];
  char vendor[25];
  uint8_t ssid_count;
  uint8_t generation = 0;
  bool needs_lookup = false;
  int8_t rssi;              // <--- NEW: 1-byte physics variable
};

// Fixed, static memory blocks
ProbeRecordShared probeList[MAX_PROBE_SLOTS];
SSIDNode ssidPool[TOTAL_SSID_POOL];
int nextFreeSsidIdx = 0;            // Points to the next unused slot in the pool

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
  char ssid[31];         // 31 chars locks the struct exactly at 80 bytes
};

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
const int MAX_MACS = 250;

// --- TARGET AP LOCK GLOBALS ---
uint8_t target_bssid[6] = {0};
int target_channel = 0;
bool target_locked = false;
char target_ssid[33] = {0}; // Store the name of the targeted network

const int HEADER_HEIGHT = 108; 
const int CHART_BOTTOM = 295;
int current_x = 0;

struct MacRecord {
  // 8-byte types
  uint64_t sum_bytes;
  uint64_t sum_sq_bytes;

  // 4-byte types 
  uint32_t first_seen; 
  uint32_t last_seen;  
  uint32_t packets;
  uint32_t tx_bytes;
  uint32_t rx_bytes;
  float smoothedDistance;  // <--- Moved up to group with 4-byte types

  // 1-byte types & Arrays
  uint8_t mac[6];
  char vendor[22];         // <--- Reduced to 22 bytes to hit the magic 72-byte struct limit
  int8_t rssi;
  uint8_t rate;
  bool vendorFound;
  bool needs_lookup;
};

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

// Compile-time safety check to prevent silent memory corruption
constexpr size_t max_wifi_size = sizeof(MacRecord) * MAX_MACS;
static_assert(max_wifi_size >= sizeof(BLERecord) * MAX_BLE_DEVICES, 
              "FATAL: BLE array exceeds union boundary.");
static_assert(max_wifi_size >= sizeof(ApRecord) * MAX_AP_RECORDS, 
              "FATAL: AP array exceeds union boundary.");
static_assert(max_wifi_size >= sizeof(ChannelRecord) * MAX_CHANNEL_RECORDS, 
              "FATAL: Channel array exceeds union boundary.");
// ==========================================
// OUI RAM CACHE (Ring Buffer)
// ==========================================
#define OUI_CACHE_SIZE 300 // Shrunk from 300 to clear SRAM

struct OUICache {
  uint8_t oui[3];
  char vendor[22]; // <--- Shrunk to match MacRecord and prevent string overflows
};

OUICache vendorCache[OUI_CACHE_SIZE];
int cacheCount = 0;
int cacheHead = 0;

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

// --- The Smart Endpoint Wi-Fi Sniffer Callback ---
void sniffer_callback(void* buf, wifi_promiscuous_pkt_type_t type) {
  if (pause_sniffing) return;
  wifi_promiscuous_pkt_t *pkt = (wifi_promiscuous_pkt_t *)buf;
  uint16_t len = pkt->rx_ctrl.sig_len;
  uint8_t* payload = pkt->payload;

  if (len < 24) return;

  // Extract MAC addresses immediately since we need them for both modes
  uint8_t* addr1 = payload + 4;  // Receiver
  uint8_t* addr2 = payload + 10; // Transmitter

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
              
              offset += 2 + tag_len; // Jump to the next tag
            }

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
            
            liveApData[ap_index].channel = true_channel; // <--- INJECT THE TRUE CHANNEL
            strcpy((char*)liveApData[ap_index].ssid, extracted_ssid); // <--- INJECT THE PARSED SSID
          }
        }

        // If the AP made it into the array, process the packet!
        if (ap_index != -1) {
          liveApData[ap_index].last_seen = millis();
          liveApData[ap_index].rssi = pkt->rx_ctrl.rssi; 
          liveApData[ap_index].tx_bytes += len; // Beacons are AP transmissions!
          liveApData[ap_index].packets += 1;
          liveApData[ap_index].sum_bytes += len;
          liveApData[ap_index].sum_sq_bytes += ((uint64_t)len * len);
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
    
    // 1. FIRST PASS: Parse the IE tags to build the profile
    while (offset < len - 4) {
      uint8_t tag_num = payload[offset];
      uint8_t tag_len = payload[offset + 1];
      
      if (offset + 2 + tag_len > len) break; // Memory safety boundary
      
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
          processProbeRequestShared(addr2, final_ssid, ie_vendor, pkt->rx_ctrl.rssi);
        } else {
          processProbeRequestShared(addr2, final_ssid, "", pkt->rx_ctrl.rssi); 
        }
        
      }
    }    
    return; // EXIT EARLY: Do not let Management frames hit the bandwidth math!
  }
  // ==========================================

  // 1. Filter out everything except Data Frames (Type 0x08)
  if ((payload[0] & 0x0C) != 0x08) return;

  uint8_t* mac3 = payload + 16; // Source / Destination

  // 2. The Target AP Lock Gate
  if (target_locked) {
    bool belongs_to_target = false;
    if (memcmp(addr1, target_bssid, 6) == 0) belongs_to_target = true;
    else if (memcmp(addr2, target_bssid, 6) == 0) belongs_to_target = true;
    else if (memcmp(mac3, target_bssid, 6) == 0) belongs_to_target = true;

    if (!belongs_to_target) return;
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

  for(int i = 0; i < liveMacCount; i++) {
    if(memcmp((void*)liveData[i].mac, client_mac, 6) == 0) {
      liveData[i].packets += 1;
      liveData[i].sum_bytes += len;
      liveData[i].sum_sq_bytes += ((uint64_t)len * len);
      liveData[i].rssi = pkt->rx_ctrl.rssi;
      //liveData[i].rate = getBitrateMbps(pkt);
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
      
      // Updated to 21 chars max, null terminated at [21]
      strncpy(record->vendor, vendorCache[i].vendor, 21);
      record->vendor[21] = '\0'; 
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
        while(line[text_start] == ' ' || line[text_start] == '\t') {
          text_start++;
        }
        
        // Safely extract from the true start of the word (Updated to 21)
        strncpy(record->vendor, &line[text_start], 21); 
        record->vendor[21] = '\0';
        
        // Strip trailing spaces working backward (Updated to start at 20)
        for(int i = 20; i >= 0; i--) {         
          if(record->vendor[i] == ' ') record->vendor[i] = '\0';
          else break;
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
  
  // Updated to 21 chars max, null terminated at [21]
  strncpy(vendorCache[cacheHead].vendor, record->vendor, 21);
  vendorCache[cacheHead].vendor[21] = '\0';
  
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
  // Using a red border to indicate an active tracking mode
  tft.drawRoundRect(50, 90, 200, 40, 3, TFT_RED); 
  tft.setTextColor(TFT_WHITE);
  tft.setTextDatum(MC_DATUM);
  tft.drawString("FOXHUNT", 150, 110); // Center of the 50-250 box

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
    tft.fillRect(300, 190, 150, 40, TFT_DARKGREEN); // New color for AP mode
  }
  else if (currentRadioMode == RADIO_CHANNELS) {
    tft.fillRect(300, 190, 150, 40, TFT_ORANGE); // New color for channel spectrum mode
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
  tft.drawString("SELECT TARGET AP", 240, 15);

  // THE FIX: Bumped the global list font to 11pt!
  tft.setFreeFont(&UbuntuMono_Regular11pt7b);
  tft.setTextDatum(TL_DATUM);
  tft.setTextColor(TFT_GREEN);
  tft.drawRect(0, 40, 480, 35, TFT_DARKGREY); // Matched height to 35px for symmetry
  tft.drawString("[*] SNIFF ALL (Free Airspace)", 5, 50);

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
      // Y-math updated to account for the larger header row
      int y = 80 + (row * 35); 

      // 1. Get the raw BSSID bytes and the SSID string
      uint8_t* bssid = WiFi.BSSID(i);
      String raw_ssid = WiFi.SSID(i);
      char tactical_ssid[26]; // Expanded buffer slightly for safety

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
        char temp_ssid[16]; // Allowed a few more characters since we dropped the MAC!
        strncpy(temp_ssid, raw_ssid.c_str(), 15);
        temp_ssid[15] = '\0';
        snprintf(tactical_ssid, sizeof(tactical_ssid), "%s~%02X%02X", temp_ssid, bssid[4], bssid[5]);
      } else {
        char temp_ssid[22]; 
        strncpy(temp_ssid, raw_ssid.c_str(), 21);
        temp_ssid[21] = '\0';
        snprintf(tactical_ssid, sizeof(tactical_ssid), "%s", temp_ssid);
      }

      // 4. Print the row using the new, cleaner format
      char apRowStr[80];
      // Removed the MAC string at the end and slightly expanded the SSID spacing
      snprintf(apRowStr, sizeof(apRowStr), "CH:%02d  %-22s %4ddBm",
               WiFi.channel(i),
               tactical_ssid,
               WiFi.RSSI(i));

      tft.drawString(apRowStr, 5, y + 10);
      tft.drawRect(0, y, 480, 35, TFT_DARKGREY);
      row++;
    }
  }

  // ==========================================
  // FOOTER & NAVIGATION (Always renders!)
  // ==========================================
  // Dropped footer back to 9pt so the buttons don't crowd each other
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);

  tft.drawLine(0, 285, 480, 285, TFT_WHITE);
  
  tft.setTextColor(TFT_RED);
  tft.drawString("BACK", 215, 295);

  if (n > APS_PER_PAGE) {
    tft.setTextColor(TFT_WHITE);

    if (ap_current_page > 0) {
      tft.drawString("<- PREV", 20, 295);
    }
    
    if (((ap_current_page + 1) * APS_PER_PAGE) < n) {
      tft.drawString("NEXT ->", 360, 295);
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
    // Slightly abbreviated to ensure buttons fit on the right
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
    // Removed "Total:" to free up space for the buttons
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
  // FIX: Updated X coordinate to 410 and Width to 65
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
      tft.drawString("    FIRST | LAST   DIST Mbps  AVG    CV%    TX | RX", 5, 41);
    } 
    else if (currentRadioMode == RADIO_AP) {
      tft.setFreeFont(&UbuntuMono_B9pt7b);
      tft.drawString("     SSID                 BSSID            RSSI TOTAL", 5, 26);       
      tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
      tft.drawString("    FIRST | LAST  DIST CH RATE  AVG  CV%    TX | RX", 5, 41);
    }
    else if (currentRadioMode == RADIO_CHANNELS) {
      tft.setFreeFont(&UbuntuMono_B9pt7b);
      // 'PWR(AVG|STD)' replaces the old raw RSSI column
      tft.drawString("     CHANNEL           PWR(AVG dBm|STD)         TOTAL", 5, 26);       
      tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
      // 'STATE' replaces the blank space
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
            // VIP ACCESS: Bypass the randomization mask
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

        snprintf(line1, sizeof(line1), "%3d. %-18.18s %17s %4d %-5.5s", 
                 (i + 1), safeVendor, macStr, sessionData[i].rssi, totStr);

        snprintf(line2, sizeof(line2), "    %13s %4.0fm %3d  %-5.5s %4.0f%%   %9s", 
                 ageCombo, sessionData[i].smoothedDistance, sessionData[i].rate, 
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

        snprintf(line1, sizeof(line1), "%3d. %-18.18s %17s %4d %-5.5s", 
                 (i + 1), safeSsid, bssidStr, sessionApData[i].rssi, totStr);

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
        if (sessionChannelData[i].ema_variance > 0.01) { // Prevent divide-by-zero
            rho = sessionChannelData[i].ema_cov / sessionChannelData[i].ema_variance;
        }

        // Translate rho into a human-readable diagnostic state
        char stateStr[10];
        if (sessionChannelData[i].packets < 5) strcpy(stateStr, "CALC.."); // Gathering data
        else if (rho > 0.6) strcpy(stateStr, "DRIFT");   // Mobile/Shifting interference
        else if (rho > 0.2) strcpy(stateStr, "ACTIVE");  // Standard bursting traffic
        else strcpy(stateStr, "STATIC");                 // Stationary/Thermal noise

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
        formatShortUnit(sessionChannelData[i].tx_bytes, txStr, sizeof(txStr)); // Downlink
        formatShortUnit(sessionChannelData[i].rx_bytes, rxStr, sizeof(rxStr)); // Uplink
        snprintf(trafficCombo, sizeof(trafficCombo), "%s|%s", txStr, rxStr); 

        // Format the combined Power String (e.g., "-65|±3")
        char pwrStr[16];
        if (sessionChannelData[i].packets == 0) strcpy(pwrStr, "N/A");
        else snprintf(pwrStr, sizeof(pwrStr), "%3.0f|~%-2.0f", avg_rssi, std_dev_rssi);
        //replace "~" with "±" if your font supports it, or keep as is for clarity on the small screen

        // --- PERFECTLY JUSTIFIED UI STRINGS ---
        // 14-char spacer to align Power, 11-char padding to align Total to the far right
        snprintf(line1, sizeof(line1), "%3d. CHANNEL %02d %14s %-11.11s   %-5.5s", 
                 (i + 1), sessionChannelData[i].channel, "", pwrStr, totStr);

        // Aligns Age, State, Byte Avg, Byte CV%, and Uplink/Downlink combo
        snprintf(line2, sizeof(line2), "    %13s %5s %-7.7s %-4.4s %3.0f%%   %9s", 
                 ageCombo, "", stateStr, avgStr, cv_percent, trafficCombo);

        // 4. DRAW TO SCREEN
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
    // The new, memory-efficient IDs
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
        
        // --- HIGH-VALUE OSINT INTERCEPTS ---
        if (companyId == 0x004C && mfg.length() >= 3 && mfg[2] == 0x12) newTrackerType = TRACKER_APPLE_FINDMY;
        else if (companyId == 0x004C && mfg.length() >= 3 && mfg[2] == 0x02) newTrackerType = TRACKER_APPLE_IBEACON;
        else if (companyId == 0x00E0 && mfg.length() >= 3 && mfg[2] == 0xFC) newTrackerType = TRACKER_GOOGLE_FASTPAIR;
        else if (companyId == 0x000D) newTrackerType = TRACKER_TILE;
        else if (companyId == 0x0075 && mfg.length() >= 3 && mfg[2] == 0x42) newTrackerType = TRACKER_SAMSUNG_SMARTTAG;
        else if (companyId == 0x0006 && mfg.length() >= 3 && mfg[2] == 0x09) newTrackerType = TRACKER_MS_SWIFTPAIR;
        
        // --- PRIORITY 1: TARGETED COMPANY NAME FALLBACK ---
        if (newName == "" && resolvedCompany != "") {
            
            // 1. If we successfully resolved the protocol, promote it to the Name slot!
            if (newTrackerType == TRACKER_APPLE_FINDMY) newName = "Apple Find My";
            else if (newTrackerType == TRACKER_APPLE_IBEACON) newName = "Apple iBeacon";
            else if (newTrackerType == TRACKER_GOOGLE_FASTPAIR) newName = "Google FastPair";
            else if (newTrackerType == TRACKER_SAMSUNG_SMARTTAG) newName = "Samsung SmartTag";
            else if (newTrackerType == TRACKER_TILE) newName = "Tile Tracker";
            else if (newTrackerType == TRACKER_MS_SWIFTPAIR) newName = "MS Swift Pair";
            
            // 2. If it is an unknown proprietary protocol, leave the hex diagnostic!
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
            newNamePriority = 1; // Secure the Priority Rank!
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
        
        // THE EDDYSTONE INTERCEPT
        if (uuid16 == 0xFEAA) {
          newTrackerType = TRACKER_EDDYSTONE;
          // If we don't have a name, promote the URL to the name column
          if (newName == "") {
              newName = decodeEddystoneURL(advertisedDevice->getServiceData(k)).substr(0, 24);
          }
          break; 
        }

        // If it's a generic 16-bit service data, save it so the UI can resolve the Member Name later
        if (newServiceId == 0) {
            newServiceId = uuid16; 
        }
      } 
    }

    // ==========================================
    // STEP 3: Appearance (0x19)
    // ==========================================
    // No more strings! Just grab the raw ID.
    if (advertisedDevice->haveAppearance()) {
      newAppearanceId = advertisedDevice->getAppearance();
    } 

    // ==========================================
    // STEP 4: Standard Services (0x02/0x03)
    // ==========================================
    // Grab the first 16-bit Service UUID we find
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

        // Safely update the Name string if a new one arrived
        if (newName != "") {
          strncpy((char*)liveBleData[i].name, newName.c_str(), 24);
          liveBleData[i].name[24] = '\0';
        }
        
        // Update IDs if we found new ones
        if (newTrackerType != TRACKER_NONE) liveBleData[i].trackerType = newTrackerType;
        if (newAppearanceId != 0) liveBleData[i].appearanceId = newAppearanceId;
        if (newServiceId != 0) liveBleData[i].serviceId = newServiceId;

        found = true;
        break;
      }
    }

    // Add New Device to the live buffer
    if (!found && liveBleCount < MAX_BLE_DEVICES) {
      memcpy((void*)(uint8_t*)liveBleData[liveBleCount].mac, rawMac, 6);

      strncpy((char*)liveBleData[liveBleCount].name, newName.c_str(), 24);
      liveBleData[liveBleCount].name[24] = '\0';

      // Drop the integers directly into the struct
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

void processProbeRequestShared(uint8_t* mac, const char* ssid, const char* known_vendor, int8_t rssi) {
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

    // The block you just asked about! Safely claiming the slot:
    memcpy(probeList[target_slot].mac, mac, 6);
    probeList[target_slot].hits = 0;
    probeList[target_slot].ssid_count = 0;
    probeList[target_slot].first_ssid_idx = -1;
    probeList[target_slot].first_seen = millis();
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
  probeList[target_slot].hits++;
  probeList[target_slot].last_seen = millis();
  probeList[target_slot].rssi = rssi;
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
  snprintf(headerStr, sizeof(headerStr), "SNIFFED PROBES (%d)", active_probes);
  tft.drawString(headerStr, 0, 5); // Flush Left

  // --- INJECT SORT UI BUTTONS ---
  char metricStr[32];
  uint16_t metricColor = TFT_YELLOW;

  if (currentProbeSortMode == PROBE_SORT_HITS) strcpy(metricStr, "SORT:HITS");
  else if (currentProbeSortMode == PROBE_SORT_DIST) strcpy(metricStr, "SORT:DIST");
  else if (currentProbeSortMode == PROBE_SORT_SSIDS) strcpy(metricStr, "SORT:#SSIDs");
  else if (currentProbeSortMode == PROBE_SORT_AGE) strcpy(metricStr, "SORT:AGE");

  // Draw Metric Button Outline and Text
  tft.fillRoundRect(275, 2, 130, 20, 3, TFT_BLACK); 
  tft.drawRoundRect(275, 2, 130, 20, 3, TFT_WHITE);
  tft.setTextColor(metricColor);
  tft.drawString(metricStr, 282, 4);

  // Draw Direction Button Outline and Text
  tft.fillRoundRect(410, 2, 65, 20, 3, TFT_BLACK); 
  tft.drawRoundRect(410, 2, 65, 20, 3, TFT_WHITE);
  
  if (probe_sort_descending) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("DESC", 423, 4);
  } else {
    tft.setTextColor(TFT_GREEN);
    tft.drawString("ASC", 427, 4);
  }
  
  // Reset for the rest of the list
  tft.setTextColor(TFT_WHITE);

  // ==========================================
  // 2. DUAL-LINE COLUMN HEADERS
  // ==========================================
  tft.setTextColor(TFT_GREEN);
  tft.setFreeFont(&UbuntuMono_B9pt7b);
  tft.drawString("ID VENDOR           FIRST|LAST    RSSI  DIST   HITS", 0, 26); // Flush Left
  tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
  tft.drawString("MAC ADDRESS       CAPTURED SSIDs", 0, 41); // Flush Left
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
      tft.setTextColor(TFT_GREEN);
      
      bool is_randomized = (probeList[i].mac[0] & 0x02) != 0;
      char safeVendor[20];
      
      if (strcmp(probeList[i].vendor, "Resolving...") == 0) {
          snprintf(safeVendor, sizeof(safeVendor), "%-15.15s", "Resolving...");
      } else if (strstr(probeList[i].vendor, "(IE)") != nullptr) {
          snprintf(safeVendor, sizeof(safeVendor), "%-15.15s", probeList[i].vendor);
      } else if (is_randomized) {
          snprintf(safeVendor, sizeof(safeVendor), "%-15.15s", "<Randomized>");
      } else if (probeList[i].vendor[2] == ':' || strcmp(probeList[i].vendor, "Unknown") == 0 || strlen(probeList[i].vendor) == 0) {
          snprintf(safeVendor, sizeof(safeVendor), "%-15.15s", "Unknown Device");
      } else {
          snprintf(safeVendor, sizeof(safeVendor), "%-15.15s", probeList[i].vendor);
      }

      char ageCombo[16];
      char firstSeenStr[8], lastSeenStr[8];
      getAgeString(probeList[i].first_seen, firstSeenStr, sizeof(firstSeenStr));
      getAgeString(probeList[i].last_seen, lastSeenStr, sizeof(lastSeenStr));
      snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr);

      char metaStr[80];
      // Changed to %02d to eliminate the blank space indent for numbers 1-9
      snprintf(metaStr, sizeof(metaStr), "%02d.%-15.15s %13s %4d %4.0fm %5u",
               i + 1, safeVendor, ageCombo, probeList[i].rssi, probeList[i].smoothedDistance, probeList[i].hits);
               
      tft.setFreeFont(&UbuntuMono_B9pt7b);
      tft.drawString(metaStr, 0, y); // Flush Left

      // --- LINES 2 & 3: MAC Address & Smart SSID Word Wrapper ---
      tft.setTextColor(TFT_WHITE);
      tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
      
      // Draw MAC Address on Line 2
      char macStr[32];
      snprintf(macStr, sizeof(macStr), "%02X:%02X:%02X:%02X:%02X:%02X", 
               probeList[i].mac[0], probeList[i].mac[1], probeList[i].mac[2],
               probeList[i].mac[3], probeList[i].mac[4], probeList[i].mac[5]);
      tft.drawString(macStr, 0, y + 16); // Flush Left

      char line1[64] = ""; 
      char line2[80] = ""; 
      int current_node = probeList[i].first_ssid_idx;
      int ssids_drawn = 0;
      int total_ssids = probeList[i].ssid_count;
      bool on_line2 = false;

      while (current_node != -1) {
        char next_str[36];
        snprintf(next_str, sizeof(next_str), "%s", ssidPool[current_node].text);
        
        char addition[40];
        if (ssids_drawn == 0) snprintf(addition, sizeof(addition), "%s", next_str); 
        else snprintf(addition, sizeof(addition), "|%s", next_str);

        // Fits on first SSID line? (Adjusted down to 32 chars since X was bumped to 185)
        if (!on_line2) {
            if (strlen(line1) + strlen(addition) <= 37) {
                strlcat(line1, addition, sizeof(line1));
                ssids_drawn++;
            } else {
                on_line2 = true; 
            }
        }

        if (on_line2) {
            if (strlen(line2) == 0) snprintf(addition, sizeof(addition), "%s", next_str);
            else snprintf(addition, sizeof(addition), "|%s", next_str);

            if (strlen(line2) + strlen(addition) <= 53) { 
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
      } else if (ssids_drawn < total_ssids) {
        char plusStr[8];
        snprintf(plusStr, sizeof(plusStr), "|+%d", (total_ssids - ssids_drawn));
        if (on_line2 || strlen(line1) > 32) {
            strlcat(line2, plusStr, sizeof(line2));
        } else {
            strlcat(line1, plusStr, sizeof(line1));
        }
      }

      // X=185 ensures a generous 15+ pixel gap after the flush-left MAC address
      tft.drawString(line1, 165, y + 16);
      
      if (strlen(line2) > 0) {
        tft.drawString(line2, 0, y + 30); // Flush Left
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

  // Mathematically identical to drawDeviceList()
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
    probeList[i].rssi = -100;           // <--- NEW
    probeList[i].smoothedDistance = 0.0; // <--- NEW
    strncpy(probeList[i].vendor, "Unknown", 25);
  }

  // 2. Initialize the global SSID memory pool
  for (int i = 0; i < TOTAL_SSID_POOL; i++) {
    ssidPool[i].text[0] = '\0';
    ssidPool[i].next_node_idx = -1;
  }
}

void drawFoxhuntScreen() {
  tft.fillScreen(TFT_BLACK);
  
  // 1. Header
  tft.fillRect(0, 0, 480, 30, TFT_DARKGREY);
  tft.setTextColor(TFT_WHITE);
  tft.setTextDatum(MC_DATUM);
  tft.setFreeFont(&UbuntuMono_Regular11pt7b);
  tft.drawString("TACTICAL FOXHUNT", 240, 15);

  // 2. Target Info
  tft.setTextColor(TFT_CYAN);
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  char targetStr[64];
  snprintf(targetStr, sizeof(targetStr), "TARGET: %02X:%02X:%02X:%02X:%02X:%02X", 
           foxhunt_target_mac[0], foxhunt_target_mac[1], foxhunt_target_mac[2], 
           foxhunt_target_mac[3], foxhunt_target_mac[4], foxhunt_target_mac[5]);
  tft.drawString(targetStr, 240, 60);
  tft.drawString(foxhunt_target_vendor, 240, 85);

  // 3. Massive RSSI Display
  tft.setTextColor(TFT_WHITE);
  char rssiStr[32];
  snprintf(rssiStr, sizeof(rssiStr), "SIG: %d dBm", (int)smoothed_rssi);
  tft.drawString(rssiStr, 240, 150);

  // 4. The Alert Banner (Overrides the middle of the screen)
  if (target_behind_alert) {
    tft.fillRect(50, 180, 380, 60, TFT_RED);
    tft.setTextColor(TFT_WHITE);
    // Draw a thick white border around the red box
    tft.drawRect(50, 180, 380, 60, TFT_WHITE); 
    tft.drawString("! TARGET BEHIND YOU !", 240, 210);
    
    // Clear alert after 3 seconds
    if (millis() - alert_start_time > 3000) {
      target_behind_alert = false;
      baseline_rssi = (int)smoothed_rssi; // Reset baseline to prevent continuous looping
    }
  }

  // 5. Footer (Exit Button)
  tft.drawLine(0, 285, 480, 285, TFT_WHITE);
  tft.drawRoundRect(190, 292, 100, 24, 3, TFT_RED);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("ABORT", 240, 304);
}

void updateFoxhuntSignal(int packet_rssi) {
  // 1. Set dynamic tuning parameters based on the active radio
  float current_alpha;
  int drop_threshold;
  
  if (currentRadioMode == RADIO_WIFI) {
    current_alpha = 0.2;       // Stable, slow-moving for high-noise Wi-Fi
    drop_threshold = 12;       // Requires a massive 12 dBm drop to trigger
  } else {
    current_alpha = 0.55;      // Twitchy, fast-moving for sparse BLE packets
    drop_threshold = 7;        // Only requires a 7 dBm drop to trigger alert
  }

  // 2. Initialize or Smooth the signal
  if (smoothed_rssi == -100.0) {
    smoothed_rssi = packet_rssi;
  } else {
    smoothed_rssi = (current_alpha * packet_rssi) + ((1.0 - current_alpha) * smoothed_rssi);
  }

  // 3. Track the Baseline (strongest recent signal)
  if ((int)smoothed_rssi > baseline_rssi) {
    baseline_rssi = (int)smoothed_rssi;
  }

  // 4. The Body-Block Trigger
  if ((baseline_rssi - (int)smoothed_rssi) >= drop_threshold) {
    if (!target_behind_alert) {
      target_behind_alert = true;
      alert_start_time = millis();
    }
  }
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
      // X: 50 to 250 | Y: 90 to 130
      if (t_x > 50 && t_x < 250 && t_y > 90 && t_y < 130) {
         is_selecting_target = true;         // Set the router flag
         currentState = SCREEN_DEVICE_LIST; // Route to the list
         drawDeviceList();                   // Draw the hijacked list (using your updated function)
         delay(200);
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

// 3. AP SCANNER TOUCH LOGIC
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
      
      // 2. AP SELECTION LIST ROWS (y: 80 to 255)
      else if (t_y >= 80 && t_y < 255) {
        
        // Match the Y-offset so Row 0 starts exactly at pixel 80
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

          // 1. Re-run the clone check for the network we just tapped
          bool has_clone = false;
          if (raw_ssid.length() > 0) {
            for (int j = 0; j < n; ++j) {
              if (actual_index != j && WiFi.SSID(j) == raw_ssid) {
                has_clone = true;
                break;
              }
            }
          }

          // 2. Build the tactical string directly into the global target_ssid variable
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
      else if (t_y >= 280) {
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
        target_locked = false;
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
            if (currentRadioMode == RADIO_WIFI) {
              memcpy(foxhunt_target_mac, sessionData[tapped_array_index].mac, 6);
              strncpy(foxhunt_target_vendor, sessionData[tapped_array_index].vendor, 25);
            } else if (currentRadioMode == RADIO_BLE) {
              memcpy(foxhunt_target_mac, sessionBleData[tapped_array_index].mac, 6);
              strncpy(foxhunt_target_vendor, sessionBleData[tapped_array_index].name, 25);
              if (foxhunt_target_vendor[0] == '\0') {
                strncpy(foxhunt_target_vendor, "<Unnamed BLE>", 25);
              }
            } else if (currentRadioMode == RADIO_AP) {
              // Allows Foxhunting routers from the AP list!
              memcpy(foxhunt_target_mac, sessionApData[tapped_array_index].bssid, 6);
              strncpy(foxhunt_target_vendor, sessionApData[tapped_array_index].ssid, 25);
            }

            is_selecting_target = false;
            is_foxhunting = true;
            smoothed_rssi = -100.0;
            baseline_rssi = -100;
            target_behind_alert = false;

            if (currentRadioMode == RADIO_WIFI || currentRadioMode == RADIO_AP) {
              target_locked = false; 
            }

            currentState = SCREEN_FOXHUNT;
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
    static unsigned long last_radar_update = 0;
    static int last_displayed_rssi = -999; // Track what is currently on the glass
    
    // Refresh loop
    if (millis() - last_radar_update > 300) {
      int current_display_val = (int)smoothed_rssi;

      // 1. ANTI-FLICKER: Only redraw the number if it actually changed!
      if (current_display_val != last_displayed_rssi) {
        tft.fillRect(100, 130, 280, 40, TFT_BLACK); 
        tft.setTextColor(TFT_WHITE);
        tft.setFreeFont(&UbuntuMono_Regular11pt7b); 
        tft.setTextDatum(MC_DATUM);
        
        char rssiStr[32];
        snprintf(rssiStr, sizeof(rssiStr), "SIG: %d dBm", current_display_val);
        tft.drawString(rssiStr, 240, 150);
        
        last_displayed_rssi = current_display_val;
      }

      // 2. Manage the Alert Banner State
      if (target_behind_alert) {
        tft.fillRect(50, 180, 380, 60, TFT_RED);
        tft.drawRect(50, 180, 380, 60, TFT_WHITE);
        tft.setTextColor(TFT_WHITE);
        tft.drawString("! TARGET BEHIND YOU !", 240, 210);
        
        // Auto-clear the alert after 3 seconds so the user can keep hunting
        if (millis() - alert_start_time > 3000) {
          target_behind_alert = false;
          baseline_rssi = current_display_val; // Reset baseline
          tft.fillRect(50, 180, 380, 60, TFT_BLACK); // Wipe the red box instantly
        }
      } 
      
      // 3. Baseline Decay (Runs every 2 seconds)
      static unsigned long last_decay_time = 0;
      if (millis() - last_decay_time > 2000) {
        baseline_rssi--; // Slowly degrade the baseline over time
        last_decay_time = millis();
      }
      
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
        
        tft.fillRect(5, 4, 200, 15, TFT_BLACK); 
        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.setTextDatum(TL_DATUM);
        tft.setTextColor(TFT_ORANGE);
        tft.drawString("SNIFFING BLE DEVICES", 5, 4);
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
          // --- INJECT FOXHUNT TRACKER ---
          if (is_foxhunting && memcmp((void*)liveData[i].mac, foxhunt_target_mac, 6) == 0) {
            updateFoxhuntSignal(liveData[i].rssi);
            if (!target_locked) {
              target_locked = true; 
            }
          }

          bool found = false;

          float rawDistance = calculateRfDistance(liveData[i].rssi, 0, RADIO_WIFI_24GHZ);
          
          // A. Try to update an existing device in the history
          for (int j = 0; j < sessionMacCount; j++) {
            if (memcmp(sessionData[j].mac, (void*)liveData[i].mac, 6) == 0) {
              // No more .bytes! Just update the deep metrics:
              sessionData[j].packets += liveData[i].packets;
              sessionData[j].tx_bytes += liveData[i].tx_bytes;
              sessionData[j].rx_bytes += liveData[i].rx_bytes;
              sessionData[j].sum_bytes += liveData[i].sum_bytes;
              sessionData[j].sum_sq_bytes += liveData[i].sum_sq_bytes;
              sessionData[j].rssi = liveData[i].rssi;
              // (Ignores 0-value parsing failures from advanced modern packets)
              if (liveData[i].rate > 0) {
                  sessionData[j].rate = liveData[i].rate;
              }
              sessionData[j].last_seen = liveData[i].last_seen;
              
              // EMA Distance Filter
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
          if (is_foxhunting && memcmp((void*)liveBleData[i].mac, foxhunt_target_mac, 6) == 0) {
            updateFoxhuntSignal(liveBleData[i].rssi);
          }
          
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
              sessionApData[j].channel = liveApData[i].channel;
              
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
      
      tft.fillRect(current_x + 2, HEADER_HEIGHT + 1, 4, CHART_BOTTOM - HEADER_HEIGHT, TFT_BLACK);

      int current_y = CHART_BOTTOM;

      if (currentRadioMode == RADIO_WIFI) {
        // ==========================================
        // WI-FI PLOTTING (Bytes & Log Scale)
        // ==========================================
        uint32_t total_bytes = sortOtherBytes;
        for(int i = 0; i < 8 && i < sortMacCount; i++) {
          total_bytes += (sortData[i].tx_bytes + sortData[i].rx_bytes);
        }

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

            if (useLogScale) {
              fraction = log10((double)current_device_bytes + 1.0) / log_total;
            } else {
              fraction = (double)current_device_bytes / (double)total_bytes;
            }

            int bar_height = (int)(fraction * (CHART_BOTTOM - HEADER_HEIGHT));
            if (bar_height > (CHART_BOTTOM - HEADER_HEIGHT)) bar_height = CHART_BOTTOM - HEADER_HEIGHT;

            tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);

            current_y -= bar_height;
          }

          if (sortOtherBytes > 0 && current_y > HEADER_HEIGHT) {
            tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[8]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[8]);
          }
          else if (sortOtherBytes == 0 && current_y > HEADER_HEIGHT && sortMacCount > 0) {
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
        uint32_t other_hits = 0; // NEW: Track hits outside the top 8
        int ble_count = (sortBleCount > 8) ? 8 : sortBleCount;

        // 1. Sum hits for the top 8 devices
        for(int i = 0; i < ble_count; i++) {
          total_hits += sortBleData[i].hits;
        }

        // 2. Sum hits for the "Other" category (devices 9+)
        if (sortBleCount > 8) {
          for (int i = 8; i < sortBleCount; i++) {
            other_hits += sortBleData[i].hits;
          }
          total_hits += other_hits; // Add to grand total for accurate fractions
        }

        if (total_hits > 0) {
          double log_total = 0;

          // 3. Log Scale Calculations (including 'Other')
          if (useLogScale) {
            for(int j = 0; j < ble_count; j++) {
              log_total += log10((double)sortBleData[j].hits + 1.0);
            }
            if (other_hits > 0) {
              log_total += log10((double)other_hits + 1.0);
            }
          }

          // 4. Draw the Top 8 bars
          for(int i = 0; i < ble_count; i++) {
            double fraction;
            
            // Respect the UI Log/Linear Toggle for BLE
            if (useLogScale) {
              fraction = log10((double)sortBleData[i].hits + 1.0) / log_total;
            } else {
              fraction = (double)sortBleData[i].hits / (double)total_hits;
            }
            
            int bar_height = (int)(fraction * (CHART_BOTTOM - HEADER_HEIGHT));
            if (bar_height > (CHART_BOTTOM - HEADER_HEIGHT)) bar_height = CHART_BOTTOM - HEADER_HEIGHT;

            tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);

            current_y -= bar_height;
          }
          
          // 5. Draw the Grey "Other" Category at the very top
          if (other_hits > 0 && current_y > HEADER_HEIGHT) {
            tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[8]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[8]);
          }
          // 6. Fill any remaining pixel gap at the top due to integer rounding (if no 'Other')
          else if (other_hits == 0 && current_y > HEADER_HEIGHT && ble_count > 0) {
            tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[ble_count - 1]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[ble_count - 1]);
          }
        }
      }
      else if (currentRadioMode == RADIO_AP) {
          // ==========================================
          // AP PLOTTING (Traffic Bytes & Log Scale)
          // ==========================================
          uint32_t total_bytes = sortOtherBytes;
          for(int i = 0; i < 8 && i < sortApCount; i++) {
            total_bytes += (sortApData[i].tx_bytes + sortApData[i].rx_bytes);
          }

          if (total_bytes > 0) {
            double log_total = 0;

            // Log Scale Calculations
            if (useLogScale) {
              for(int j = 0; j < 8 && j < sortApCount; j++) {
                uint32_t device_total = sortApData[j].tx_bytes + sortApData[j].rx_bytes;
                log_total += log10((double)device_total + 1.0);
              }
              log_total += log10((double)sortOtherBytes + 1.0);
            }

            // Draw the Top 8 bars
            for(int i = 0; i < 8 && i < sortApCount; i++) {
              double fraction;
              uint32_t current_device_bytes = sortApData[i].tx_bytes + sortApData[i].rx_bytes;
              
              if (useLogScale) {
                fraction = log10((double)current_device_bytes + 1.0) / log_total;
              } else {
                fraction = (double)current_device_bytes / (double)total_bytes;
              }

              int bar_height = (int)(fraction * (CHART_BOTTOM - HEADER_HEIGHT));
              if (bar_height > (CHART_BOTTOM - HEADER_HEIGHT)) bar_height = CHART_BOTTOM - HEADER_HEIGHT;

              tft.drawLine(current_x, current_y, current_x, current_y - bar_height, colors[i]);
              tft.drawLine(current_x + 1, current_y, current_x + 1, current_y - bar_height, colors[i]);

              current_y -= bar_height;
            }

            // Draw the Grey "Other" Category at the top
            if (sortOtherBytes > 0 && current_y > HEADER_HEIGHT) {
              tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[8]);
              tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[8]);
            }
            // Fill any remaining pixel gap
            else if (sortOtherBytes == 0 && current_y > HEADER_HEIGHT && sortApCount > 0) {
              tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[sortApCount - 1]);
              tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[sortApCount - 1]);
            }
          }
        }
        else if (currentRadioMode == RADIO_CHANNELS) {
          // ==========================================
          // CHANNEL PLOTTING (Log/Lin Scale)
          // ==========================================
          uint32_t total_bytes = sortOtherBytes;
          for(int i = 0; i < 8 && i < sortChannelCount; i++) {
            total_bytes += (sortChannelData[i].tx_bytes + sortChannelData[i].rx_bytes);
          }

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

              int bar_height = (int)(fraction * (CHART_BOTTOM - HEADER_HEIGHT));
              if (bar_height > (CHART_BOTTOM - HEADER_HEIGHT)) bar_height = CHART_BOTTOM - HEADER_HEIGHT;

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

      current_x += 2;
      if (current_x >= 478) current_x = 0;
    }
  }
}
}