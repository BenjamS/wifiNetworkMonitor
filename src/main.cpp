#include <Arduino.h>
#include <WiFi.h>
#include "esp_wifi.h"
#include <TFT_eSPI.h>
#include <SPI.h>
#include "SdFat.h"
#include <NimBLEDevice.h>
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

/**
 * Universal Log-Distance Path Loss Calculator
 * * @param rssi        The received signal strength (e.g., -75)
 * @param txPower     The broadcasted TX power in dBm (0 if unknown)
 * @param protocol    The RadioProtocol enum (BLE, Wi-Fi 2.4, Wi-Fi 5)
 * @param customLoss  (Optional) Override the path loss exponent. Default 0.0 uses standard presets.
 * @return            Estimated distance in meters
 */

int ap_current_page = 0;
const int APS_PER_PAGE = 8; // Number of APs that fit safely between the header and footer

int target_rssi = 0;

SdFs sd;

// --- Forward Declarations for OSINT Probe Tracker ---
int addSsidToPool(const char* ssid, int head_idx, bool &already_exists, bool &added, uint8_t current_count);
void processProbeRequestShared(uint8_t* mac, const char* ssid);

enum UIState { SCREEN_CHART, SCREEN_MENU, SCREEN_AP_SCAN,
   SCREEN_DEVICE_LIST, SCREEN_PROBE_TRACKER };
UIState currentState = SCREEN_CHART;

const int MAX_PROBE_SLOTS = 10;     // Max unique devices tracked
const int TOTAL_SSID_POOL = 60;     // Total unique SSID strings shared among all devices
const int EMERGENCY_CUTOFF = 5;    // Max SSIDs a single device can claim

struct SSIDNode {
  char text[33];
  int next_node_idx = -1;                // Index of the next SSID for this device (-1 if end)
};

struct ProbeRecordShared {
  // 4-byte variables first
  unsigned long last_seen;
  int first_ssid_idx;               
  
  // 2-byte variables
  uint16_t hits;
  
  // 1-byte arrays and variables
  uint8_t mac[6];
  char vendor[25];
  uint8_t ssid_count;
  uint8_t generation = 0;
  bool needs_lookup = false;
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
enum RadioMode { RADIO_WIFI, RADIO_BLE };
RadioMode currentRadioMode = RADIO_WIFI;

// ==========================================
// BLUETOOTH DATA STRUCTURE
// ==========================================
#define MAX_BLE_DEVICES 150

struct BLERecord {
  // --- 4-Byte Variables (Aligned at the top) ---
  int rssi;               
  int txPower;            
  uint32_t hits;          
  float smoothedDistance; 
  unsigned long firstSeen; 
  unsigned long lastSeen;

  // --- 1-Byte Arrays (Packed at the bottom) ---
  uint8_t mac[6];         
  char name[25];          
  char appearance[20];    
  char service[20];       
  char trackerData[20];   
};

// Perfectly aligned with your drawDeviceList() function!
const int BLE_UPDATE_INTERVAL = 2000;         // Refresh rate for BLE waterfall (ms)

// NimBLE Global Scanner Pointer
BLEScan* pBLEScan;

int device_current_page = 0;
const int DEVICES_PER_PAGE = 13; // 9pt font with 18px line spacing fits 13 devices perfectly

std::atomic<bool> pause_sniffing{false};
bool useLogScale = false;

bool sort_descending = true; // Default to loudest devices first

uint16_t calData[5] = { 288, 3501, 301, 3244, 7 };
TFT_eSPI tft = TFT_eSPI();

const int CHANNELS[] = {1, 6, 11};
const int NUM_CHANNELS = 3;
int current_ch_idx = 0;

const int HOP_INTERVAL = 1500;                // Time spent on each channel (ms)
const int LOCKED_UPDATE_INTERVAL = 2000;      // Refresh rate when locked to an AP (ms)
const int MAX_MACS = 250;

// --- TARGET AP LOCK GLOBALS ---
uint8_t target_bssid[6] = {0};
int target_channel = 0;
bool target_locked = false;
char target_ssid[33] = {0}; // Store the name of the targeted network

const int HEADER_HEIGHT = 110; 
const int CHART_BOTTOM = 320;
int current_x = 0;

struct MacRecord {
  // 8-byte variables first
  uint64_t sum_bytes;
  uint64_t sum_sq_bytes;

  // 4-byte variables
  uint32_t packets;
  unsigned long first_seen;
  unsigned long last_seen;
  uint32_t tx_bytes;
  uint32_t rx_bytes;

  // 1-byte arrays and variables
  uint8_t mac[6];
  char vendor[25];
  int8_t rssi;         
  uint8_t rate;        
  bool vendorFound; 
  bool needs_lookup;
  float smoothedDistance;
};

// ==========================================
// 1. LIVE BUFFER (Shared RAM: Wi-Fi or BLE)
// ==========================================
static union {
  volatile MacRecord liveData[MAX_MACS];
  volatile BLERecord liveBleData[MAX_BLE_DEVICES];
};
volatile uint16_t liveMacCount = 0;
volatile uint32_t liveOtherBytes = 0;
volatile uint16_t liveBleCount = 0;

// ==========================================
// 2. SORT BUFFER (Shared RAM: Wi-Fi or BLE)
// ==========================================
static union {
  MacRecord sortData[MAX_MACS];
  BLERecord sortBleData[MAX_BLE_DEVICES];
};
uint16_t sortMacCount = 0;
uint32_t sortOtherBytes = 0;
uint16_t sortBleCount = 0;

// ==========================================
// 3. SESSION BUFFER (Shared RAM: Wi-Fi or BLE)
// ==========================================
static union {
  MacRecord sessionData[MAX_MACS];
  BLERecord sessionBleData[MAX_BLE_DEVICES];
};
uint16_t sessionMacCount = 0;
uint32_t sessionOtherBytes = 0;
uint16_t sessionBleCount = 0;

// Compile-time safety check to prevent silent memory corruption
// (Throw compile error if max BLE devices > max wifi devices)
static_assert(sizeof(MacRecord) * MAX_MACS >= sizeof(BLERecord) * MAX_BLE_DEVICES, 
              "FATAL: BLE array exceeds union boundary. Increase MAX_MACS or reduce MAX_BLE_DEVICES.");
// ==========================================
// OUI RAM CACHE (Ring Buffer)
// ==========================================
#define OUI_CACHE_SIZE 300 // Shrunk from 300 to clear SRAM

struct OUICache {
  uint8_t oui[3];
  char vendor[25]; // Shrunk to match MacRecord and prevent string overflows
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
  hex24to565(0xCC5500), // [6] Rust/Orange  
  hex24to565(0x889FD7), // [7] Periwinkle Blue
  TFT_DARKGREY          // [8] "Other" category (unchanged)
  //hex24to565(0xE07EB6), // [6] Pink
  //hex24to565(0xDA815E), // [1] Rust/Orange
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

  // ==========================================
  // PROBE REQUEST BOUNCER
  // ==========================================
  // Check if Frame Control byte 0 is 0x40 (Subtype 4: Probe Request)
  if (payload[0] == 0x40) {
    
    // The Source Address (SA) starts at byte 10 in a Management Frame
    uint8_t* sa = &payload[10];

    // THE RANDOMIZATION FILTER:
    // Check the Locally Administered bit (second least-significant bit of the first byte).
    // If it's a 0, this is a globally unique physical MAC.
    if ((sa[0] & 0x02) == 0) { 
      
      // In Probe Requests, the Tagged Parameters start after the 24-byte MAC header.
      int offset = 24; 
      
      // Loop through the tags to find the SSID (Tag Number 0)
      while (offset < len - 4) { // -4 to ignore the FCS checksum at the end
        uint8_t tag_num = payload[offset];
        uint8_t tag_len = payload[offset + 1];

        // 0x00 is the SSID Tag
        if (tag_num == 0) {
          // Check the reported length first
          if (tag_len > 0 && tag_len <= 32) {
            char extracted_ssid[33];
            memcpy(extracted_ssid, &payload[offset + 2], tag_len);
            extracted_ssid[tag_len] = '\0'; // Ensure it's null-terminated

            // ==========================================
            // THE CLOAKING FILTER
            // Check the actual string length to catch null-byte padding!
            // ==========================================
            if (strlen(extracted_ssid) > 0) {
              // Pass the completely clean data to the Engine!
              processProbeRequestShared(sa, extracted_ssid);
            }
          }
          break; // Once we process the SSID, we can stop parsing this packet
        }
        // Jump to the next tag
        offset += 2 + tag_len;
      }
    }
    return; // EXIT EARLY: Do not let Management frames hit the bandwidth math!
  }
  // ==========================================

  // 1. Filter out everything except Data Frames (Type 0x08)
  if ((payload[0] & 0x0C) != 0x08) return;

  uint8_t* mac1 = payload + 4;  // Receiver
  uint8_t* mac2 = payload + 10; // Transmitter
  uint8_t* mac3 = payload + 16; // Source / Destination

  // 2. The Target AP Lock Gate
  if (target_locked) {
    bool belongs_to_target = false;
    if (memcmp(mac1, target_bssid, 6) == 0) belongs_to_target = true;
    else if (memcmp(mac2, target_bssid, 6) == 0) belongs_to_target = true;
    else if (memcmp(mac3, target_bssid, 6) == 0) belongs_to_target = true;

    if (!belongs_to_target) return;
  }

  // 3. Extract DS Flags to determine traffic direction
  uint8_t ds_flags = payload[1] & 0x03;
  bool to_ds   = (ds_flags & 0x01); // Bit 0: Client -> AP (Upload)
  bool from_ds = (ds_flags & 0x02); // Bit 1: AP -> Client (Download)

  // 4. Smart Endpoint Identification
  uint8_t* client_mac = mac2; // Default to Transmitter

  if (from_ds && !to_ds) {
    client_mac = mac1;
  }
  else if (to_ds && !from_ds) {
    client_mac = mac2;
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
  bool is_tx = (client_mac == mac2); 

  for(int i = 0; i < liveMacCount; i++) {
    if(memcmp((void*)liveData[i].mac, client_mac, 6) == 0) {
      liveData[i].packets += 1;
      liveData[i].sum_bytes += len;
      liveData[i].sum_sq_bytes += ((uint64_t)len * len);
      liveData[i].rssi = pkt->rx_ctrl.rssi;
      liveData[i].rate = getBitrateMbps(pkt);
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
  // 1. Lock the radio interrupt to prevent memory collisions
  pause_sniffing = true;
  
  // 2. Reset the waterfall chart cursor back to the left edge
  current_x = 0;

  // ==========================================
  // FLUSH SHARED ARRAYS (Wi-Fi sizes cover BLE too)
  // ==========================================
  memset((void*)liveData, 0, sizeof(liveData));
  liveMacCount = 0;
  liveOtherBytes = 0;
  liveBleCount = 0;

  memset(sortData, 0, sizeof(sortData));
  sortMacCount = 0;
  sortOtherBytes = 0;
  sortBleCount = 0;

  memset(sessionData, 0, sizeof(sessionData));
  sessionMacCount = 0;
  sessionOtherBytes = 0;
  sessionBleCount = 0;

  // 3. Unlock the radio interrupt
  pause_sniffing = false;
}

void resolveMacVendor(MacRecord* record) {
  if (record->vendorFound) return;

  // 1. Check RAM Cache
  for (int i = 0; i < cacheCount; i++) {
    if (vendorCache[i].oui[0] == record->mac[0] &&
        vendorCache[i].oui[1] == record->mac[1] &&
        vendorCache[i].oui[2] == record->mac[2]) {
      
      strncpy(record->vendor, vendorCache[i].vendor, 24);
      record->vendor[24] = '\0'; // Guarantee safe termination!
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
        
        // Safely extract from the true start of the word
        strncpy(record->vendor, &line[text_start], 24); 
        record->vendor[24] = '\0';
        
        // Strip trailing spaces working backward
        for(int i = 23; i >= 0; i--) {         
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
  
  strncpy(vendorCache[cacheHead].vendor, record->vendor, 24);
  vendorCache[cacheHead].vendor[24] = '\0';
  
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

  // 1. LOG SCALE TOGGLE
  if (useLogScale) {
    tft.fillRect(50, 90, 200, 40, TFT_GREEN);
    tft.setTextColor(TFT_BLACK);
  } else {
    tft.fillRect(50, 90, 200, 40, TFT_DARKGREY);
    tft.setTextColor(TFT_WHITE);
  }
  tft.drawRect(50, 90, 200, 40, TFT_WHITE);

  if (useLogScale) tft.drawString("MODE: LOG", 150, 110);
  else tft.drawString("MODE: LINEAR", 150, 110);

  // 2. SORT TOGGLE
  if (sort_descending) {
    tft.fillRect(50, 140, 200, 40, TFT_DARKGREY);
    tft.setTextColor(TFT_WHITE);
    tft.drawRect(50, 140, 200, 40, TFT_WHITE);
    tft.drawString("SORT: HIGHEST", 150, 160);
  } else {
    tft.fillRect(50, 140, 200, 40, TFT_DARKCYAN);
    tft.setTextColor(TFT_WHITE);
    tft.drawRect(50, 140, 200, 40, TFT_WHITE);
    tft.drawString("SORT: LOWEST", 150, 160);
  }

  // ==========================================
  // PROBE REQUEST BUTTON (Right Column)
  // ==========================================
  uint16_t purpleColor = hex24to565(0x4A148C);
  tft.fillRect(300, 140, 150, 40, purpleColor);
  tft.drawRect(300, 140, 150, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("PROBE REQUESTS", 375, 160);

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
  tft.drawString("SEEN DEVICES", 150, 260);

  // RADIO MODE TOGGLE
  if (currentRadioMode == RADIO_WIFI) {
    tft.fillRect(300, 190, 150, 40, TFT_BLUE);
    tft.setTextColor(TFT_WHITE);
  } else {
    tft.fillRect(300, 190, 150, 40, TFT_PURPLE);
    tft.setTextColor(TFT_WHITE);
  }
  tft.drawRect(300, 190, 150, 40, TFT_WHITE);
  tft.drawString(currentRadioMode == RADIO_WIFI ? "MODE: WI-FI" : "MODE: BLE", 375, 210);

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
  tft.drawRoundRect(420, 2, 55, 14, 2, TFT_WHITE);
  // 2. Set the Font State
  tft.setTextColor(TFT_WHITE);
  // tft.setTextSize(1); // ONLY needed here if another function changed it to 2!
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);  
  // 3. Center the Text Automatically
  tft.setTextDatum(MC_DATUM);     // Set datum to Middle-Center
  // Center X = 420 + (55 / 2) = 447
  // Center Y = 2 + (14 / 2) = 9
  tft.drawString("MENU", 447, 9); 
   // 4. Reset state for the rest of your UI
  tft.setTextDatum(TL_DATUM);     // Put datum back to Top-Left

  // BANNER
  tft.setTextWrap(false); 
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);

  char bannerStr[64];

  if (currentRadioMode == RADIO_BLE) {
    tft.setTextColor(TFT_PURPLE); 
    snprintf(bannerStr, sizeof(bannerStr), "BLE MODE | SNIFFING...");
  } 
  else {
    tft.setTextColor(TFT_WHITE); 
    
    if (!target_locked) {
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | FREE AIRSPACE", CHANNELS[current_ch_idx]);
    } else {
      char safe_ssid[15];
      strncpy(safe_ssid, target_ssid, 14);
      safe_ssid[14] = '\0';
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | %s (%ddBm)", target_channel, safe_ssid, target_rssi);
    }
  }

  tft.drawString(bannerStr, 5, 4);
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

  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);
  tft.setTextColor(TFT_GREEN);
  tft.drawRect(0, 40, 480, 25, TFT_DARKGREY);
  tft.drawString("[*] SNIFF ALL (Free Airspace)", 5, 45);

  tft.setTextColor(TFT_WHITE);
  
  // ==========================================
  // LIST GENERATION
  // ==========================================
  if (n == 0) {
    tft.drawString("No networks found in airspace.", 5, 75);
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
      int y = 70 + (row * 25);

      char apRowStr[80];
      snprintf(apRowStr, sizeof(apRowStr), "CH:%02d  %-16s  %4ddBm  %s",
               WiFi.channel(i),
               WiFi.SSID(i).substring(0, 16).c_str(),
               WiFi.RSSI(i),
               WiFi.BSSIDstr(i).c_str());

      tft.drawString(apRowStr, 5, y + 5);
      tft.drawRect(0, y, 480, 25, TFT_DARKGREY);
      row++;
    }
  }

  // ==========================================
  // FOOTER & NAVIGATION (Always renders!)
  // ==========================================
  // Switch to your nice custom font so it matches the Device List exactly!
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);

  // Always draw the bounding line and BACK button
  tft.drawLine(0, 285, 480, 285, TFT_WHITE);
  
  tft.setTextColor(TFT_RED);
  tft.drawString("BACK", 215, 295);

  // Only draw NEXT/PREV if pagination is needed
  if (n > APS_PER_PAGE) {
    tft.setTextColor(TFT_WHITE);

    if (ap_current_page > 0) {
      tft.drawString("<- PREV", 20, 295);
    }
    
    if (((ap_current_page + 1) * APS_PER_PAGE) < n) {
      tft.drawString("NEXT ->", 360, 295);
    }
  }
} // <-- End of drawApScanner()

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
  int total_devices = (currentRadioMode == RADIO_WIFI) ? sessionMacCount : sessionBleCount;

  // Top Banner
  tft.fillRect(0, 0, 480, 24, (currentRadioMode == RADIO_WIFI) ? TFT_BLUE : TFT_PURPLE);
  tft.setTextColor(TFT_WHITE);

  // --- DRAW TOP BANNER ---
  tft.setFreeFont(&UbuntuMono_B9pt7b);
  char headerStr[64];
  snprintf(headerStr, sizeof(headerStr), " SEEN %s DEVICES (Total: %d) ", 
          (currentRadioMode == RADIO_WIFI) ? "WI-FI" : "BLE", total_devices);
  tft.drawString(headerStr, 5, 5); 

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
      tft.setFreeFont(&UbuntuMono_Regular9pt7b);
      tft.drawString("   VENDOR             First|Last    TX|RX(KB) Tot(KB)", 5, 26); 
      tft.setFreeFont(&UbuntuMono_RI9pt7b); 
      tft.drawString("    MAC                   RSSI Mbps  Avg(B)   CV%", 5, 41); 
    } else {
      tft.setFreeFont(&UbuntuMono_Regular9pt7b);
      tft.drawString("   NAME              First|Last      RSSI  DIST HITS", 5, 26); 
      tft.setFreeFont(&UbuntuMono_RI9pt7b); 
      tft.drawString("    MAC                 Vendor:Appearance|Service|", 5, 41); 
    }
    tft.setTextColor(TFT_WHITE); 

    // --- HEADER SEPARATOR LINE ---
    tft.drawLine(0, 57, 480, 57, TFT_WHITE); // Shifted up to 57

    // ==========================================
    // DRAW THE DATA ROWS
    // ==========================================
    int row = 0;
    for (int i = start_idx; i < end_idx; i++) {
      
      // Calculate row Y-position (Stays exactly the same)
      int y = 62 + (row * 33); 
      
      if (currentRadioMode == RADIO_WIFI) {
        
        resolveMacVendor(&sessionData[i]);

        char macStr[18];
        snprintf(macStr, sizeof(macStr), "%02X:%02X:%02X:%02X:%02X:%02X",
                 sessionData[i].mac[0], sessionData[i].mac[1], sessionData[i].mac[2],
                 sessionData[i].mac[3], sessionData[i].mac[4], sessionData[i].mac[5]);

        bool is_randomized = (sessionData[i].mac[0] & 0x02) != 0;

        // VENDOR: Squeezed to exactly 18 characters
        char short_vendor[20]; 
        if (is_randomized) {
          snprintf(short_vendor, sizeof(short_vendor), "%-18.18s", "<Randomized>");
        } else if (sessionData[i].vendor[2] == ':' || strlen(sessionData[i].vendor) == 0) {
          snprintf(short_vendor, sizeof(short_vendor), "%-18.18s", "Unknown Device");
        } else {
          snprintf(short_vendor, sizeof(short_vendor), "%-18.18s", sessionData[i].vendor);
        }

        double mean = 0.0;
        double cv_percent = 0.0;
        if (sessionData[i].packets > 0) {
          mean = (double)sessionData[i].sum_bytes / (double)sessionData[i].packets;
          double avg_sq_sum = (double)sessionData[i].sum_sq_bytes / (double)sessionData[i].packets;
          double variance = avg_sq_sum - (mean * mean);
          if (variance < 0) variance = 0; 
          double std_dev = sqrt(variance);
          if (mean > 0) cv_percent = (std_dev / mean) * 100.0;
        }

        uint32_t total_bytes = sessionData[i].tx_bytes + sessionData[i].rx_bytes;

        // AGE: Fixed-width 13 characters (e.g. "00h05m|01h20m")
        char firstSeenStr[8];
        char lastSeenStr[8];
        getAgeString(sessionData[i].first_seen, firstSeenStr, sizeof(firstSeenStr));
        getAgeString(sessionData[i].last_seen, lastSeenStr, sizeof(lastSeenStr));

        char ageCombo[16];
        snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr);

        // --- NEW: DYNAMIC TRAFFIC SCALING ---
        char txStr[8], rxStr[8], totStr[10];
        
        // Call the helpers we placed above drawDeviceList()
        formatShortUnit(sessionData[i].tx_bytes, txStr, sizeof(txStr));
        formatShortUnit(sessionData[i].rx_bytes, rxStr, sizeof(rxStr));
        formatTotalUnit(total_bytes, totStr, sizeof(totStr));

        // Packs into a rigid 9-character string like: "999K|2.4G"
        char trafficCombo[20];
        snprintf(trafficCombo, sizeof(trafficCombo), "%s|%s", txStr, rxStr);

        // --- THE 52-CHARACTER ALIGNMENT MAGIC ---
        // %3d.     : Index (4 chars)
        // %-18.18s : Left-justified Vendor (18 chars)
        // %13s     : Right-justified Age (13 chars)
        // %9s      : Right-justified TX|RX Combo (9 chars)
        // %5s      : Right-justified Total Unit (5 chars)
        // Plus 3 hardcoded spaces = 52 characters total.
        char line1[90];
        snprintf(line1, sizeof(line1), "%3d.%-18.18s %13s %9s %5s", 
                 (i + 1), short_vendor, ageCombo, trafficCombo, totStr);
        
        // --- Format Line 2: Indented 1 extra space to align under Vendor ---
        char line2[90]; 
        snprintf(line2, sizeof(line2), "     %s   %4d  %3d  %6.0f  %3.0f%%", 
                 macStr, sessionData[i].rssi, sessionData[i].rate, mean, cv_percent);

        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.drawString(line1, 5, y);
        tft.setTextColor(TFT_LIGHTGREY);
        tft.setFreeFont(&UbuntuMono_RI9pt7b);
        tft.drawString(line2, 5, y + 15); 
        tft.setTextColor(TFT_WHITE); 
      
      } else {
        // ==========================================
        // BLE MODE (Unchanged layout)
        // ==========================================
        char line1[90];
        char safeName[20];
        
        if (strlen(sessionBleData[i].name) == 0) {
            snprintf(safeName, sizeof(safeName), "%-19.19s", "<Unnamed>");
        } else {
            snprintf(safeName, sizeof(safeName), "%-19.19s", sessionBleData[i].name);
        }

        char firstSeenStr[8];
        char lastSeenStr[8];
        getAgeString(sessionBleData[i].firstSeen, firstSeenStr, sizeof(firstSeenStr));
        getAgeString(sessionBleData[i].lastSeen, lastSeenStr, sizeof(lastSeenStr));

        char ageCombo[16];
        snprintf(ageCombo, sizeof(ageCombo), "%s|%s", firstSeenStr, lastSeenStr);

        std::string tagStr = "";
        if (strlen(sessionBleData[i].trackerData) > 0) {
            tagStr += sessionBleData[i].trackerData;
        }
        if (strlen(sessionBleData[i].appearance) > 0) {
            tagStr += (tagStr.length() > 0 ? "|" : "") + std::string(sessionBleData[i].appearance);
        }
        if (strlen(sessionBleData[i].service) > 0) {
            tagStr += (tagStr.length() > 0 ? "|" : "") + std::string(sessionBleData[i].service);
        }

        if (tagStr == "") tagStr = "No Data";
        
        cleanOsintString(tagStr); // Ensure your helper function stays in play!

        if (tagStr.length() > 32) {
            tagStr = tagStr.substr(0, 29) + "...";
        }

        char macStr[18];
        snprintf(macStr, sizeof(macStr), "%02X:%02X:%02X:%02X:%02X:%02X", 
                 sessionBleData[i].mac[0], sessionBleData[i].mac[1], sessionBleData[i].mac[2], 
                 sessionBleData[i].mac[3], sessionBleData[i].mac[4], sessionBleData[i].mac[5]);

        snprintf(line1, sizeof(line1), "%d.%s %-13s %4d %4.0fm %4d", 
                 (i + 1), safeName, ageCombo, sessionBleData[i].rssi, 
                 sessionBleData[i].smoothedDistance, sessionBleData[i].hits);

        char line2[90];
        snprintf(line2, sizeof(line2), "    %s  %s", macStr, tagStr.c_str());

        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.drawString(line1, 5, y);
        tft.setTextColor(TFT_LIGHTGREY);
        tft.setFreeFont(&UbuntuMono_RI9pt7b);
        tft.drawString(line2, 5, y + 15);
        tft.setTextColor(TFT_WHITE); 
      }
      row++;
    }
  }

  // --- SAFE NAVIGATION FOOTER ---
  tft.setFreeFont(&UbuntuMono_Regular9pt7b); 
  tft.drawLine(0, 294, 480, 294, TFT_WHITE); // Shifted down to 294

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

/*
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
    // RAW PACKET HEX DUMP (DEBUG)
    // ==========================================
    uint8_t* payload = advertisedDevice->getPayload();
    size_t payloadLength = advertisedDevice->getPayloadLength();

    std::string rawDump = "RAW ADV [" + macStr + "] (" + std::to_string(payloadLength) + "b): ";
    
    for (size_t i = 0; i < payloadLength; i++) {
      char hex[4];
      snprintf(hex, sizeof(hex), "%02X ", payload[i]);
      rawDump += hex;
    }
    
    Serial.println(rawDump.c_str());
    // ==========================================
    
    int rssi = advertisedDevice->getRSSI();
    
    // Extract TX Power safely, defaulting to 0 if not present
    int txPower = advertisedDevice->haveTXPower() ? advertisedDevice->getTXPower() : 0;
    int sdCount = advertisedDevice->getServiceDataCount();

    #if 0
    // ==========================================
    // THE ULTIMATE BLE REALITY CHECK
    // ==========================================
    bool hasValuableData = false;
    std::string dumpStr = "MAC: " + macStr;

    if (advertisedDevice->haveTXPower()) {
      dumpStr += " | TX: " + std::to_string(txPower) + "dBm";
      hasValuableData = true;
    }

    if (advertisedDevice->haveAppearance()) {
      char appStr[16];
      snprintf(appStr, sizeof(appStr), " | App: 0x%04X", advertisedDevice->getAppearance());
      dumpStr += appStr;
      hasValuableData = true;
    }

    if (advertisedDevice->haveServiceUUID()) {
      dumpStr += " | UUID: " + advertisedDevice->getServiceUUID().toString();
      hasValuableData = true;
    }

    if (sdCount > 0) {
      dumpStr += " | Telemetry: ";
      for (int k = 0; k < sdCount; k++) { 
        NimBLEUUID sdUUID = advertisedDevice->getServiceDataUUID(k);
        std::string sData = advertisedDevice->getServiceData(k);
        
        dumpStr += "[" + sdUUID.toString() + "] ";
        for (size_t j = 0; j < sData.length(); j++) {
          char hex[4];
          snprintf(hex, sizeof(hex), "%02X ", (uint8_t)sData[j]);
          dumpStr += hex;
        }
      }
      hasValuableData = true;
    }

    // Manufacturer Specific Data (0xFF) HEX DUMP
    if (advertisedDevice->haveManufacturerData()) {
      dumpStr += " | Mfg (0xFF): ";
      std::string mfgData = advertisedDevice->getManufacturerData();
      
      for (size_t j = 0; j < mfgData.length(); j++) {
        char hex[4];
        snprintf(hex, sizeof(hex), "%02X ", (uint8_t)mfgData[j]);
        dumpStr += hex;
      }
      hasValuableData = true;
    }

    if (hasValuableData) {
      Serial.println(dumpStr.c_str());
    }
    #endif
    // ==========================================
    // PARALLEL OSINT EXTRACTION & SIG LOOKUPS
    // ==========================================
    std::string newName = "";
    std::string newTrackerData = "";
    std::string newAppearance = "";
    std::string newService = "";

    // ==========================================
    // STEP 1: Name & Manufacturer Data (0xFF)
    // ==========================================
    // 1A. Try to get the broadcasted Local Name first
    if (advertisedDevice->haveName()) {
      newName = advertisedDevice->getName();
    } 
    
    // 1B. ALWAYS check for Manufacturer Data, even if a Name was found!
    if (advertisedDevice->haveManufacturerData()) {
      std::string mfg = advertisedDevice->getManufacturerData();
      if (mfg.length() >= 2) {
        uint16_t companyId = (uint8_t)mfg[1] << 8 | (uint8_t)mfg[0];
        
        // Resolve the company name once to use in both catch-alls
        std::string resolvedCompany = resolveBleCompanyId(mfg);
        
        // --- HIGH-VALUE OSINT INTERCEPTS (Human Readable) ---
        if (companyId == 0x004C && mfg.length() >= 3 && mfg[2] == 0x12) newTrackerData = "Apple: Find My";
        else if (companyId == 0x004C && mfg.length() >= 3 && mfg[2] == 0x02) newTrackerData = "Apple: iBeacon";
        else if (companyId == 0x00E0 && mfg.length() >= 3 && mfg[2] == 0xFC) newTrackerData = "Google: Fast Pair";
        else if (companyId == 0x000D) newTrackerData = "Tile Tracker";
        else if (companyId == 0x0075 && mfg.length() >= 3 && mfg[2] == 0x42) newTrackerData = "Samsung: SmartTag";
        else if (companyId == 0x0075 && mfg.length() >= 3 && mfg[2] == 0x43) newTrackerData = "Samsung: SmartTag+";
        else if (companyId == 0x0006 && mfg.length() >= 3 && mfg[2] == 0x09) newTrackerData = "MS: Swift Pair";
        
        // --- THE GENERIC CATCH-ALL (Dynamic Hex Tagging) ---
        else {
            if (resolvedCompany != "") {
                if (mfg.length() >= 3) {
                    char trackerStr[20];
                    snprintf(trackerStr, sizeof(trackerStr), "%s:0x%02X", 
                             resolvedCompany.substr(0, 12).c_str(), (uint8_t)mfg[2]);
                    newTrackerData = trackerStr;
                } else {
                    newTrackerData = resolvedCompany.substr(0, 19);
                }
            }
        }

        // --- TARGETED COMPANY NAME FALLBACK ---
        // If the device hid its local name, but we know the company, promote the company to the Name column!
        if (newName == "" && resolvedCompany != "") {
            newName = resolvedCompany;
        }
      }
    }

    // ==========================================
    // STEP 2: Corporate Trackers & Eddystone (0x16 Service Data)
    // ==========================================
    for (int k = 0; k < sdCount; k++) {
      NimBLEUUID sdUUID = advertisedDevice->getServiceDataUUID(k);
      
      if (sdUUID.bitSize() == 16) {
        uint16_t uuid16 = sdUUID.getNative()->u16.value;
        
        // --- THE EDDYSTONE INTERCEPT ---
        if (uuid16 == 0xFEAA) {
          std::string url = decodeEddystoneURL(advertisedDevice->getServiceData(k));
          
          // If Step 1 already found a high-value corporate tag (like "Samsung: SmartTag"),
          // do NOT overwrite it. Instead, safely append the URL!
          if (newTrackerData != "" && newTrackerData.find("0x") == std::string::npos) {
              newTrackerData = newTrackerData + " | " + url; 
          } else {
              // It is safe to overwrite if the string is empty or just generic Hex
              newTrackerData = url; 
          }
          break; 
        }

        std::string memberName = resolveBleMemberUuid(uuid16);
        
        if (memberName != "") {
          // Only overwrite if Step 1 didn't find something more specific
          if (newTrackerData == "" || newTrackerData.find("0x") != std::string::npos) {
              newTrackerData = memberName;
          }
          break;
        } else if (newTrackerData == "") {
          char hexFallback[16];
          snprintf(hexFallback, sizeof(hexFallback), "0x%04X", uuid16);
          newTrackerData = hexFallback;
        }
      } 
      // 128-bit Service Data Fallback (Proprietary IoT / Beacons)
      else if (sdUUID.bitSize() == 128 && newTrackerData == "") {
        std::string fullUUID = sdUUID.toString();
        newTrackerData = "SD: " + fullUUID.substr(0, 8);
      }
    }

    // ==========================================
    // STEP 3: Appearance (0x19)
    // ==========================================
    if (advertisedDevice->haveAppearance()) {
      uint16_t appCode = advertisedDevice->getAppearance();
      newAppearance = resolveBleAppearance(appCode);
      
      if (newAppearance == "") {
        char hexFallback[16];
        snprintf(hexFallback, sizeof(hexFallback), "0x%04X", appCode);
        newAppearance = hexFallback;
      }
    } 

    // ==========================================
    // STEP 4: Standard Services (0x02/0x03)
    // ==========================================
    if (advertisedDevice->haveServiceUUID()) {
      NimBLEUUID sUUID = advertisedDevice->getServiceUUID();
      if (sUUID.bitSize() == 16) {
        uint16_t uuid16 = sUUID.getNative()->u16.value;
        newService = resolveBleServiceUuid(uuid16);
        
        if (newService == "") {
          char hexFallback[16];
          snprintf(hexFallback, sizeof(hexFallback), "0x%04X", uuid16);
          newService = hexFallback;
        }
      }
      // 128-bit Custom Hardware UUIDs
      else if (sUUID.bitSize() == 128) {
        std::string fullUUID = sUUID.toString();
        newService = "Custom: " + fullUUID.substr(0, 8);
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
        
        // Ensure the live buffer holds the latest txPower for the loop() to use!
        liveBleData[i].txPower = txPower; 

        // Update OSINT fields if new data arrived this advertisement
        if (newName != "") {
          strncpy((char*)liveBleData[i].name, newName.c_str(), 24);
          liveBleData[i].name[24] = '\0';
        }
        if (newTrackerData != "") {
          strncpy((char*)liveBleData[i].trackerData, newTrackerData.c_str(), 19);
          liveBleData[i].trackerData[19] = '\0';
        }
        if (newAppearance != "") {
          strncpy((char*)liveBleData[i].appearance, newAppearance.c_str(), 19);
          liveBleData[i].appearance[19] = '\0';
        }
        if (newService != "") {
          strncpy((char*)liveBleData[i].service, newService.c_str(), 19);
          liveBleData[i].service[19] = '\0';
        }

        found = true;
        break;
      }
    }

    // Add New Device to live buffer
    if (!found && liveBleCount < MAX_BLE_DEVICES) {
      memcpy((void*)(uint8_t*)liveBleData[liveBleCount].mac, rawMac, 6);

      strncpy((char*)liveBleData[liveBleCount].name, newName.c_str(), 24);
      liveBleData[liveBleCount].name[24] = '\0';

      strncpy((char*)liveBleData[liveBleCount].trackerData, newTrackerData.c_str(), 19);
      liveBleData[liveBleCount].trackerData[19] = '\0';

      strncpy((char*)liveBleData[liveBleCount].appearance, newAppearance.c_str(), 19);
      liveBleData[liveBleCount].appearance[19] = '\0';

      strncpy((char*)liveBleData[liveBleCount].service, newService.c_str(), 19);
      liveBleData[liveBleCount].service[19] = '\0';

      liveBleData[liveBleCount].rssi = rssi;
      liveBleData[liveBleCount].hits = 1;
      liveBleData[liveBleCount].txPower = txPower; // Loop needs this!
      
      // Removed the smoothedDistance initialization here.
      
      liveBleData[liveBleCount].firstSeen = millis();
      liveBleData[liveBleCount].lastSeen = millis();

      liveBleCount++;
    }
  }
};

// ADD THIS FLAG RIGHT ABOVE THE switchRadioMode FUNCTION
bool ble_initialized = false; 

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

void processProbeRequestShared(uint8_t* mac, const char* ssid) {
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
    
    // CRITICAL: Increment generation to invalidate any in-flight SD lookups for this slot (ABA fix)
    probeList[target_slot].generation++; 
    
    // ==========================================
    // DEFER THE SD CARD LOOKUP TO CORE 1
    // ==========================================
    strncpy(probeList[target_slot].vendor, "Resolving...", 25);
    probeList[target_slot].needs_lookup = true; 
    // ==========================================
  }

  probeList[target_slot].hits++;
  probeList[target_slot].last_seen = millis();

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

  // 1. Draw Header (Dark Purple/Magenta theme for OSINT mode)
  tft.setFreeFont(&UbuntuMono_Regular11pt7b);
  tft.setTextDatum(MC_DATUM);
  tft.setTextColor(TFT_WHITE);
  uint16_t osintHeaderColor = hex24to565(0x4A148C); // Deep purple
  tft.fillRect(0, 0, 480, 30, osintHeaderColor);
  tft.drawString("PROBE REQUEST TRACKER", 240, 15);

  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);

  // 2. Calculate Pagination Boundaries
  int start_idx = probe_current_page * PROBES_PER_PAGE;
  int end_idx = start_idx + PROBES_PER_PAGE;

  int row = 0;
  for (int i = start_idx; i < end_idx; i++) {
    // Check if the slot has a valid, recorded MAC (not empty/all zeros)
    bool is_slot_empty = true;
    for (int b = 0; b < 6; b++) {
      if (probeList[i].mac[b] != 0) {
        is_slot_empty = false;
        break;
      }
    }

    int y = 35 + (row * 50); // Each entry block gets 50px of vertical height

    if (!is_slot_empty) {
      // --- LINE 1: Metadata (Vendor, MAC, & Hit Count) ---
      tft.setTextColor(TFT_GREEN);
      char metaStr[60];
      snprintf(metaStr, sizeof(metaStr), "[%02d] %-8s %02X:%02X:%02X:%02X:%02X:%02X",
               i + 1,
               probeList[i].vendor,
               probeList[i].mac[0], probeList[i].mac[1], probeList[i].mac[2],
               probeList[i].mac[3], probeList[i].mac[4], probeList[i].mac[5]);
      tft.drawString(metaStr, 10, y + 5);

      // Right-aligned Hit Counter
      tft.setTextColor(TFT_YELLOW);
      char hitStr[16];
      snprintf(hitStr, sizeof(hitStr), "Pkt: %u", probeList[i].hits);
      tft.setTextDatum(TR_DATUM);
      tft.drawString(hitStr, 470, y + 5);
      tft.setTextDatum(TL_DATUM); // Reset to Top-Left datum

      // --- LINE 2: SSID Chain Traversal ---
      tft.setTextColor(TFT_WHITE);
      char ssidListStr[256] = ""; // Temporary assembly buffer
      int current_node = probeList[i].first_ssid_idx;
      bool first = true;

      // Follow the pointer index chain through the shared pool
      while (current_node != -1) {
        if (!first) {
          strlcat(ssidListStr, ", ", sizeof(ssidListStr));
        }
        strlcat(ssidListStr, ssidPool[current_node].text, sizeof(ssidListStr));
        first = false;
        current_node = ssidPool[current_node].next_node_idx;
      }

      if (strlen(ssidListStr) == 0) {
        strncpy(ssidListStr, "<no SSIDs captured>", sizeof(ssidListStr));
      }

      // Truncate cleanly with an ellipsis if string exceeds screen width capability
      if (strlen(ssidListStr) > 52) {
        ssidListStr[49] = '.';
        ssidListStr[50] = '.';
        ssidListStr[51] = '.';
        ssidListStr[52] = '\0';
      }
      
      tft.drawString(ssidListStr, 30, y + 25);

    } else {
      // Clear visual placeholder for empty tracking slots
      tft.setTextColor(hex24to565(0x333333));
      char emptyStr[24];
      snprintf(emptyStr, sizeof(emptyStr), "[%02d] -- EMPTY SLOT --", i + 1);
      tft.drawString(emptyStr, 10, y + 15);
    }

    // Draw row separator line
    tft.drawLine(0, y + 49, 480, y + 49, hex24to565(0x222222));
    row++;
  }

  // --- FOOTER AND NAVIGATION NAVIGATION ---
  tft.drawLine(0, 285, 480, 285, TFT_WHITE);
  
  tft.setTextColor(TFT_RED);
  tft.drawString("BACK", 215, 295);

  tft.setTextColor(TFT_WHITE);
  if (probe_current_page > 0) {
    tft.drawString("<- PREV", 20, 295);
  }
  if (end_idx < MAX_PROBE_SLOTS) {
    tft.drawString("NEXT ->", 360, 295);
  }
}

void setup() {
  Serial.begin(115200);
  pinMode(15, OUTPUT); digitalWrite(15, HIGH);
  pinMode(21, OUTPUT); digitalWrite(21, HIGH);
  pinMode(5, OUTPUT);  digitalWrite(5, HIGH);

  delay(1000);
  tft.init();
  tft.setTouch(calData);
  tft.setRotation(1);
  tft.fillScreen(TFT_BLACK);
  drawChartHeader();

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
  bool pressed = tft.getTouch(&t_x, &t_y);

  if (pressed) {

    // 1. CHART SCREEN TOUCH LOGIC
    if (currentState == SCREEN_CHART) {
      if (t_x > 400 && t_y < 40) {
        currentState = SCREEN_MENU;
        pause_sniffing = true;
        esp_wifi_set_promiscuous(false);
        drawMenu();
        delay(300);
      }
    }

    // 2. MENU SCREEN TOUCH LOGIC
    else if (currentState == SCREEN_MENU) {
      if (t_x > 50 && t_x < 250 && t_y > 90 && t_y < 130) {
        useLogScale = !useLogScale;
        drawMenu();
        delay(300);
      }
      else if (t_x > 50 && t_x < 250 && t_y > 140 && t_y < 180) {
        sort_descending = !sort_descending;
        drawMenu();
        delay(300);
      }
      // Probe Request Tracker Button Touch Zone
      else if (t_x > 300 && t_x < 450 && t_y > 140 && t_y < 180) {
        currentState = SCREEN_PROBE_TRACKER;
        probe_current_page = 0; 
        drawProbeTracker();
        delay(300); 
      }
      // 3. AP Scanner Button (X: 50-250, Y: 190-230)
      else if (t_x > 50 && t_x < 250 && t_y > 190 && t_y < 230) {
        // NEW SAFETY CHECK: Only respond if Wi-Fi is the active radio!
        if (currentRadioMode == RADIO_WIFI) {
          currentState = SCREEN_AP_SCAN;
          drawApScanner();
          delay(300);
        }
      }
      else if (t_x > 50 && t_x < 250 && t_y > 240 && t_y < 280) {
        currentState = SCREEN_DEVICE_LIST;
        device_current_page = 0;
        drawDeviceList();
        delay(300);
      }
      else if (t_x > 300 && t_x < 450 && t_y > 190 && t_y < 230) {
        if (currentRadioMode == RADIO_WIFI) switchRadioMode(RADIO_BLE);
        else switchRadioMode(RADIO_WIFI);
        drawMenu();
        delay(300);
      }
      else if (t_x > 300 && t_x < 450 && t_y > 240 && t_y < 280) {
        currentState = SCREEN_CHART;
        tft.fillScreen(TFT_BLACK);
        drawChartHeader();
        if (currentRadioMode == RADIO_WIFI) {
          if (target_locked) esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);
          esp_wifi_set_promiscuous(true);
        }
        current_x = 0;
        pause_sniffing = false;
        delay(300);
      }
    }

    // 4. OSINT PROBE TRACKER TOUCH LOGIC
    else if (currentState == SCREEN_PROBE_TRACKER) {
      // Check for navigation footer clicks (Y: 260 to bottom)
      if (t_y > 260) {
        // PREV PAGE (Left Third)
        if (t_x < 160 && probe_current_page > 0) {
          probe_current_page--;
          drawProbeTracker();
          delay(250);
        }
        // NEXT PAGE (Right Third)
        else if (t_x > 320 && (probe_current_page + 1) * PROBES_PER_PAGE < MAX_PROBE_SLOTS) {
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
        delay(300);
      }
      
      // 2. PAGINATION & BACK FOOTER (y: 260 to bottom of screen)
      else if (t_y > 260) {
        int total_aps = WiFi.scanComplete();
        
        // PREV PAGE (Left Third)
        if (t_x < 160 && ap_current_page > 0) {
          ap_current_page--;
          drawApScanner();
          delay(250);
        }
        // NEXT PAGE (Right Third)
        else if (t_x > 320 && ((ap_current_page + 1) * APS_PER_PAGE) < total_aps) {
          ap_current_page++;
          drawApScanner();
          delay(250);
        }
        // BACK TO MENU (Center Third)
        else if (t_x >= 160 && t_x <= 320) {
          currentState = SCREEN_MENU;
          ap_current_page = 0; // Reset pagination for next time
          drawMenu(); 
          delay(300);
        }
      }
      
      // 3. AP SELECTION LIST ROWS (y: 70 to 260)
      else if (t_y >= 70 && t_y <= 260) {
        int clicked_row = (t_y - 70) / 25;
        int actual_index = (ap_current_page * APS_PER_PAGE) + clicked_row;

        if (actual_index < WiFi.scanComplete()) {
          memcpy(target_bssid, WiFi.BSSID(actual_index), 6);
          target_channel = WiFi.channel(actual_index);
          strncpy(target_ssid, WiFi.SSID(actual_index).c_str(), 32);
          target_ssid[32] = '\0';
          target_locked = true;
          target_rssi = WiFi.RSSI(actual_index);

          WiFi.scanDelete();
          esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);
          esp_wifi_set_promiscuous(true);

          resetMonitorState();
          currentState = SCREEN_CHART;
          tft.fillScreen(TFT_BLACK);
          drawChartHeader();
          delay(300);
        }
      }
    }

// 4. SEEN DEVICES TOUCH LOGIC
    else if (currentState == SCREEN_DEVICE_LIST) {
      if (t_y > 260) { // Changed to 260 to perfectly match the new Y-coordinate layout
        int total_devices = (currentRadioMode == RADIO_WIFI) ? sessionMacCount : sessionBleCount;
        
        // CRITICAL: Synchronize the math with the UI!
        // int items_per_page = (currentRadioMode == RADIO_WIFI) ? 6 : DEVICES_PER_PAGE;
        int items_per_page = 6;

        // 1. PREV PAGE
        if (t_x < 160 && device_current_page > 0) {
          device_current_page--;
          drawDeviceList();
          delay(250);
        }
        // 2. NEXT PAGE (Bug Squashed here!)
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
    }
  } // <-- End of main if (pressed)

  if (currentState == SCREEN_CHART) {
    static unsigned long lastTimer = 0;
    bool should_render = false; // Local render trigger

    tft.setTextWrap(false);

    // ==========================================
    // RADIO-AWARE TIMERS
    // ==========================================
    if (currentRadioMode == RADIO_WIFI) {
      if (!target_locked) {
        if (millis() - lastTimer > HOP_INTERVAL) {
          lastTimer = millis();
          current_ch_idx++;

          if (current_ch_idx >= NUM_CHANNELS) {
            current_ch_idx = 0;
            should_render = true;
          }

          esp_wifi_set_channel(CHANNELS[current_ch_idx], WIFI_SECOND_CHAN_NONE);

          tft.fillRect(5, 4, 80, 15, TFT_BLACK);
          tft.setFreeFont(&UbuntuMono_Regular9pt7b);
          tft.setTextDatum(TL_DATUM);
          tft.setTextColor(TFT_WHITE);

          char chStr[16];
          sprintf(chStr, "CH: %02d", CHANNELS[current_ch_idx]);
          tft.drawString(chStr, 5, 4);
        }
      }
      else {
        if (millis() - lastTimer > LOCKED_UPDATE_INTERVAL) {
          lastTimer = millis();
          should_render = true;
        }
      }
    } 
    else {
      // BLE MODE WATERFALL
      if (millis() - lastTimer > BLE_UPDATE_INTERVAL) { 
        lastTimer = millis();
        should_render = true; 
        
        tft.fillRect(5, 4, 200, 15, TFT_BLACK); 
        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.setTextDatum(TL_DATUM);
        tft.setTextColor(TFT_WHITE);
        tft.drawString("BLE MODE | SNIFFING...", 5, 4);
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
              sessionData[j].rate = liveData[i].rate;
              sessionData[j].last_seen = liveData[i].last_seen;
              //sessionData[j].last_seen = millis(); // Keep the timestamp fresh!
              // EMA Distance Filter
              if (rawDistance > 0) {
                  sessionData[j].smoothedDistance = 
                      (0.2 * rawDistance) + (0.8 * sessionData[j].smoothedDistance);
              }
              
              found = true;
              break;
            }
          }
          
          // B. If it's a completely new MAC, claim a new slot
          if (!found) {
            if (sessionMacCount < MAX_MACS) {
              // Copy the MAC address safely
              memcpy(sessionData[sessionMacCount].mac, (void*)(uint8_t*)liveData[i].mac, 6);
              
              // Transfer metrics line-by-line to bypass volatile errors
              sessionData[sessionMacCount].packets = liveData[i].packets;
              sessionData[sessionMacCount].tx_bytes = liveData[i].tx_bytes;
              sessionData[sessionMacCount].rx_bytes = liveData[i].rx_bytes;
              sessionData[sessionMacCount].sum_bytes = liveData[i].sum_bytes;
              sessionData[sessionMacCount].sum_sq_bytes = liveData[i].sum_sq_bytes;
              sessionData[sessionMacCount].rssi = liveData[i].rssi;
              sessionData[sessionMacCount].rate = liveData[i].rate;
              
              // Critical flags and Initial Timestamp
              sessionData[sessionMacCount].vendorFound = liveData[i].vendorFound;
              sessionData[sessionMacCount].vendor[0] = '\0'; // Guarantee a clean string
              sessionData[sessionMacCount].first_seen = liveData[i].first_seen;
              sessionData[sessionMacCount].last_seen = liveData[i].last_seen;
              sessionData[sessionMacCount].smoothedDistance = rawDistance > 0 ? rawDistance : 0.0;
              sessionMacCount++;
            } else {
              // Master array is full, dump it to the overflow bucket dynamically
              sessionOtherBytes += (liveData[i].tx_bytes + liveData[i].rx_bytes);
            }
          }
        }

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
          uint32_t key_total = key.tx_bytes + key.rx_bytes;
          int j = i - 1;

          if (sort_descending) {
            while (j >= 0 && (sortData[j].tx_bytes + sortData[j].rx_bytes) < key_total) {
              sortData[j + 1] = sortData[j];
              j = j - 1;
            }
          } else {
            while (j >= 0 && (sortData[j].tx_bytes + sortData[j].rx_bytes) > key_total && key_total > 0) {
              sortData[j + 1] = sortData[j];
              j = j - 1;
            }
          }
          sortData[j + 1] = key;
        }

        // --- FAST INSERTION SORT: WI-FI SESSION ---
        for (int i = 1; i < sessionMacCount; i++) {
          MacRecord key = sessionData[i];
          uint32_t key_total = key.tx_bytes + key.rx_bytes;
          int j = i - 1;

          if (sort_descending) {
            while (j >= 0 && (sessionData[j].tx_bytes + sessionData[j].rx_bytes) < key_total) {
              sessionData[j + 1] = sessionData[j];
              j = j - 1;
            }
          } else {
            while (j >= 0 && (sessionData[j].tx_bytes + sessionData[j].rx_bytes) > key_total && key_total > 0) {
              sessionData[j + 1] = sessionData[j];
              j = j - 1;
            }
          }
          sessionData[j + 1] = key;
        }

        // Calculate "Other" for the live view 
        sortOtherBytes = 0; 
        for(int i = 8; i < sortMacCount; i++) {
          sortOtherBytes += (sortData[i].tx_bytes + sortData[i].rx_bytes);
        }

        // Attempt Vendor Resolution for the top 8 visible devices
        for(int i = 0; i < 8 && i < sortMacCount; i++) {
          resolveMacVendor(&sortData[i]);
        }
      }
      else {
        // ==========================================
        // 2. BLE DATA PROCESSING PIPELINE
        // ==========================================
        // Snapshot the live data for the waterfall
        memcpy(sortBleData, (void*)liveBleData, sizeof(liveBleData));
        sortBleCount = liveBleCount;

        for (int i = 0; i < liveBleCount; i++) {
          bool found = false;
          float rawDistance = calculateRfDistance(liveBleData[i].rssi, liveBleData[i].txPower, RADIO_BLE_24GHZ);
          for (int j = 0; j < sessionBleCount; j++) {
            
            // CRITICAL FIX 1: Use memcmp for raw byte arrays, NOT strcmp!
            if (memcmp(sessionBleData[j].mac, (void*)(uint8_t*)liveBleData[i].mac, 6) == 0) {
                
                sessionBleData[j].hits += liveBleData[i].hits;
                sessionBleData[j].rssi = liveBleData[i].rssi;

                // CRITICAL FIX 2: Propagate the fresh timestamp from the live buffer!
                sessionBleData[j].lastSeen = liveBleData[i].lastSeen;

                // EMA smooth the distance into the session record
                if (rawDistance > 0) {
                    sessionBleData[j].smoothedDistance =
                        (0.2 * rawDistance) + (0.8 * sessionBleData[j].smoothedDistance);
                }

                // Propagate OSINT fields if the live buffer captured new data
                if (liveBleData[i].name[0] != '\0')
                    strncpy((char*)sessionBleData[j].name, (char*)liveBleData[i].name, 24);
                if (liveBleData[i].trackerData[0] != '\0')
                    strncpy((char*)sessionBleData[j].trackerData, (char*)liveBleData[i].trackerData, 19);
                if (liveBleData[i].appearance[0] != '\0')
                    strncpy((char*)sessionBleData[j].appearance, (char*)liveBleData[i].appearance, 19);
                if (liveBleData[i].service[0] != '\0')
                    strncpy((char*)sessionBleData[j].service, (char*)liveBleData[i].service, 19);

                found = true;
                break;
            }
          }

          if (!found) {
            if (sessionBleCount < MAX_BLE_DEVICES) {
              
              // 1. Bulk copy the entire raw packet struct (MAC, hits, OSINT strings, etc.)
              memcpy((void*)&sessionBleData[sessionBleCount], (void*)&liveBleData[i], sizeof(BLERecord));
              
              // 2. Inject the math we calculated at the top of the pipeline
              sessionBleData[sessionBleCount].smoothedDistance = rawDistance > 0 ? rawDistance : 0.0;
              
              sessionBleCount++;
            }
          }
        }

        memset((void*)liveBleData, 0, sizeof(liveBleData));
        liveBleCount = 0;

        // --- FAST INSERTION SORT: BLE SNAPSHOT (WATERFALL) ---
        for (int i = 1; i < sortBleCount; i++) {
          BLERecord key = sortBleData[i];
          uint32_t key_hits = key.hits;
          int j = i - 1;

          if (sort_descending) {
            while (j >= 0 && sortBleData[j].hits < key_hits) {
              sortBleData[j + 1] = sortBleData[j];
              j = j - 1;
            }
          } else {
            while (j >= 0 && sortBleData[j].hits > key_hits && key_hits > 0) {
              sortBleData[j + 1] = sortBleData[j];
              j = j - 1;
            }
          }
          sortBleData[j + 1] = key;
        }

        // --- FAST INSERTION SORT: BLE SESSION (SEEN DEVICES) ---
        for (int i = 1; i < sessionBleCount; i++) {
          BLERecord key = sessionBleData[i];
          uint32_t key_hits = key.hits;
          int j = i - 1;

          if (sort_descending) {
            while (j >= 0 && sessionBleData[j].hits < key_hits) {
              sessionBleData[j + 1] = sessionBleData[j];
              j = j - 1;
            }
          } else {
            while (j >= 0 && sessionBleData[j].hits > key_hits && key_hits > 0) {
              sessionBleData[j + 1] = sessionBleData[j];
              j = j - 1;
            }
          }
          sessionBleData[j + 1] = key;
        }
      }

      pause_sniffing = false; 

      int displayCount = (currentRadioMode == RADIO_WIFI) ? sortMacCount : sortBleCount;
      
      if (displayCount > 0 || (currentRadioMode == RADIO_WIFI && sortOtherBytes > 0)) {

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

        for(int i = 0; i < 8 && i < displayCount; i++) {
          char short_text[20];

          if (currentRadioMode == RADIO_WIFI) {
            strncpy(short_text, sortData[i].vendor, 19);
            short_text[19] = '\0';
          } else {
            // BLE: Use the snapshot broadcast Name. If empty, fallback to MAC address.
            if (strlen(sortBleData[i].name) > 0) {
              strncpy(short_text, sortBleData[i].name, 19);
              short_text[19] = '\0';
            } else {
              // THE FIX: Format the 6 raw bytes directly into the short_text buffer.
              // I'm using %02X (capital X) here so the MAC letters are uppercase, 
              // which usually looks crisper on a TFT display.
              snprintf(short_text, sizeof(short_text), "%02X:%02X:%02X:%02X:%02X:%02X", 
                       sortBleData[i].mac[0], sortBleData[i].mac[1], sortBleData[i].mac[2], 
                       sortBleData[i].mac[3], sortBleData[i].mac[4], sortBleData[i].mac[5]);
            }
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
      else {
        // ==========================================
        // BLE PLOTTING (Hits / Traffic volume)
        // ==========================================
        uint32_t total_hits = 0;
        int ble_count = (sortBleCount > 8) ? 8 : sortBleCount;

        for(int i = 0; i < ble_count; i++) {
          total_hits += sortBleData[i].hits;
        }

        if (total_hits > 0) {
          double log_total = 0;

          if (useLogScale) {
            for(int j = 0; j < ble_count; j++) {
              log_total += log10((double)sortBleData[j].hits + 1.0);
            }
          }

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
          
          // Fill any remaining pixel gap at the top due to integer rounding
          if (current_y > HEADER_HEIGHT && ble_count > 0) {
            tft.drawLine(current_x, current_y, current_x, HEADER_HEIGHT + 1, colors[ble_count - 1]);
            tft.drawLine(current_x + 1, current_y, current_x + 1, HEADER_HEIGHT + 1, colors[ble_count - 1]);
          }
        }
      }

      current_x += 2;
      if (current_x >= 478) current_x = 0;
    }
  }
}