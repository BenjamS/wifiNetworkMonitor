#include <Arduino.h>
#include <WiFi.h>
#include "esp_wifi.h"
#include <TFT_eSPI.h>
#include <SPI.h>
#include "SdFat.h"
#include <NimBLEDevice.h>
#include "ble_oui.h"
#include "UbuntuMono_Regular11pt7b.h"
#include "UbuntuMono_Regular9pt7b.h"

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
const int TOTAL_SSID_POOL = 30;     // Total unique SSID strings shared among all devices
const int EMERGENCY_CUTOFF = 15;    // Max SSIDs a single device can claim

struct SSIDNode {
  char text[33];
  int next_node_idx = -1;                // Index of the next SSID for this device (-1 if end)
};

struct ProbeRecordShared {
  uint8_t mac[6];
  uint16_t hits;
  int first_ssid_idx;               // Head of this device's SSID chain (-1 if none)
  uint8_t ssid_count;
  unsigned long last_seen;
  char vendor[25];
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
struct BLERecord {
  char mac[18];       // BLE MACs are often randomized, but still formatted xx:xx:xx:xx:xx:xx
  int rssi;           // Signal strength is the primary metric for BLE tracking
  uint32_t hits;      // How many advertisement packets we've seen
  char name[30];      // Broadcasted name or Company ID
};

// BLE Variables
const int BLE_UPDATE_INTERVAL = 2000;         // Refresh rate for BLE waterfall (ms)
const int MAX_BLE_DEVICES = 150;              // Max BLE devices stored in live RAM

// 1. VOLATILE LIVE BLE DATA (Filled by NimBLE Callback)
volatile BLERecord liveBleData[MAX_BLE_DEVICES];
volatile uint16_t liveBleCount = 0;

// 2. SNAPSHOT BLE DATA (For Waterfall Display & Legend)
BLERecord sortBleData[MAX_BLE_DEVICES];
uint16_t sortBleCount = 0;

// 3. MASTER SESSION BLE DATA (For UI Lists & Foxhunting)
BLERecord sessionBleData[MAX_BLE_DEVICES];
uint16_t sessionBleCount = 0;

// NimBLE Global Scanner Pointer
BLEScan* pBLEScan;

int device_current_page = 0;
const int DEVICES_PER_PAGE = 13; // 9pt font with 18px line spacing fits 13 devices perfectly

volatile bool pause_sniffing = false;
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
  uint8_t mac[6];
  uint32_t bytes;
  char vendor[25];
  bool vendorFound;
};

// This is filled by the background radio interrupt. MUST be volatile!
volatile MacRecord liveData[MAX_MACS];
volatile uint16_t liveMacCount = 0;
volatile uint32_t liveOtherBytes = 0;

// A snapshot safely copied from liveData so the UI can draw it.
MacRecord sortData[MAX_MACS];
uint16_t sortMacCount = 0;
uint32_t sortOtherBytes = 0;

// The permanent historical memory bank
MacRecord sessionData[MAX_MACS];
uint16_t sessionMacCount = 0;
uint32_t sessionOtherBytes = 0;

// ==========================================
// OUI RAM CACHE (Ring Buffer)
// ==========================================
#define OUI_CACHE_SIZE 300

struct OUICache {
  uint8_t oui[3];
  char vendor[25];
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
  hex24to565(0x889FD7), // [0] Periwinkle Blue
  hex24to565(0xD1C9CA), // [1] Light Gray
  hex24to565(0xD9D680), // [2] Pale Yellow
  hex24to565(0xB75BE2), // [3] Purple
  hex24to565(0xE07EB6), // [4] Pink
  hex24to565(0xDA815E), // [5] Rust/Orange
  hex24to565(0x7CD9CA), // [6] Mint Green
  hex24to565(0x87E370), // [7] Bright Green
  TFT_DARKGREY          // [8] "Other" category (unchanged)
};

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
          // Ignore "Null Probes" (length 0) and corrupted massive strings
          if (tag_len > 0 && tag_len <= 32) {
            char extracted_ssid[33];
            memcpy(extracted_ssid, &payload[offset + 2], tag_len);
            extracted_ssid[tag_len] = '\0'; // Ensure it's null-terminated

            // Pass the clean data to the Shared Pool Ingestion Engine!
            processProbeRequestShared(sa, extracted_ssid);
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
  for(int i = 0; i < liveMacCount; i++) {
    if(memcmp((void*)liveData[i].mac, client_mac, 6) == 0) {
      liveData[i].bytes += len;
      return;
    }
  }

  if(liveMacCount < MAX_MACS) {
    memcpy((void*)liveData[liveMacCount].mac, client_mac, 6);
    liveData[liveMacCount].bytes = len;
    liveData[liveMacCount].vendorFound = false;
    liveMacCount++;
  } else {
    liveOtherBytes += len;
  }
}

void resetMonitorState() {
  // 1. Lock the radio interrupt to prevent memory collisions
  pause_sniffing = true;
  
  // 2. Reset the waterfall chart cursor back to the left edge
  current_x = 0;

  // ==========================================
  // FLUSH WI-FI ARRAYS
  // ==========================================
  memset((void*)liveData, 0, sizeof(liveData));
  liveMacCount = 0;
  liveOtherBytes = 0;

  memset(sortData, 0, sizeof(sortData));
  sortMacCount = 0;
  sortOtherBytes = 0;

  memset(sessionData, 0, sizeof(sessionData));
  sessionMacCount = 0;
  sessionOtherBytes = 0;

  // ==========================================
  // FLUSH BLE ARRAYS
  // ==========================================
  memset((void*)liveBleData, 0, sizeof(liveBleData));
  liveBleCount = 0;

  memset(sortBleData, 0, sizeof(sortBleData));
  sortBleCount = 0;

  memset(sessionBleData, 0, sizeof(sessionBleData));
  sessionBleCount = 0;

  // 3. Unlock the radio interrupt
  pause_sniffing = false;
}

void resolveMacVendor(MacRecord* record) {
  if (record->vendorFound) return;

  for (int i = 0; i < cacheCount; i++) {
    if (vendorCache[i].oui[0] == record->mac[0] &&
        vendorCache[i].oui[1] == record->mac[1] &&
        vendorCache[i].oui[2] == record->mac[2]) {
      
      strncpy(record->vendor, vendorCache[i].vendor, 25);
      record->vendorFound = true;
      return; 
    }
  }

  sprintf(record->vendor, "%02X:%02X:%02X:%02X:%02X:%02X",
          record->mac[0], record->mac[1], record->mac[2],
          record->mac[3], record->mac[4], record->mac[5]);

  char target[7];
  sprintf(target, "%02X%02X%02X", record->mac[0], record->mac[1], record->mac[2]);

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
        strncpy(record->vendor, &line[7], 24);
        record->vendor[24] = '\0';
        
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

  vendorCache[cacheHead].oui[0] = record->mac[0];
  vendorCache[cacheHead].oui[1] = record->mac[1];
  vendorCache[cacheHead].oui[2] = record->mac[2];
  
  strncpy(vendorCache[cacheHead].vendor, record->vendor, 25);
  
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
  tft.drawString("OSINT PROBES", 375, 160);

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
  tft.setFreeFont(NULL); 
  tft.drawRoundRect(420, 2, 55, 14, 2, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.setTextSize(1);
  tft.setCursor(433, 5);
  tft.print("MENU");

  // BANNER
  tft.setTextWrap(false); 
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);

  char bannerStr[64];

  if (currentRadioMode == RADIO_BLE) {
    tft.setTextColor(TFT_PURPLE); 
    snprintf(bannerStr, sizeof(bannerStr), "BLE MODE | SCANNING...");
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

void drawDeviceList() {
  tft.fillScreen(TFT_BLACK);
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);
  tft.setTextSize(1);

  int total_devices = (currentRadioMode == RADIO_WIFI) ? sessionMacCount : sessionBleCount;

  tft.fillRect(0, 0, 480, 30, (currentRadioMode == RADIO_WIFI) ? TFT_BLUE : TFT_PURPLE);
  tft.setTextColor(TFT_WHITE);

  char headerStr[64];
  snprintf(headerStr, sizeof(headerStr), " SEEN %s DEVICES (Total: %d) ", 
          (currentRadioMode == RADIO_WIFI) ? "WI-FI" : "BLE", total_devices);
  tft.drawString(headerStr, 5, 7);

  if (total_devices == 0) {
    tft.drawString("No devices captured yet.", 5, 50);
  } else {
    int start_idx = device_current_page * DEVICES_PER_PAGE;
    if (start_idx >= total_devices) {
      device_current_page = 0;
      start_idx = 0;
    }

    int end_idx = start_idx + DEVICES_PER_PAGE;
    if (end_idx > total_devices) end_idx = total_devices;

    int row = 0;
    for (int i = start_idx; i < end_idx; i++) {
      char rowStr[64];

      if (currentRadioMode == RADIO_WIFI) {
        resolveMacVendor(&sessionData[i]);

        char macStr[18];
        sprintf(macStr, "%02X:%02X:%02X:%02X:%02X:%02X",
                sessionData[i].mac[0], sessionData[i].mac[1], sessionData[i].mac[2],
                sessionData[i].mac[3], sessionData[i].mac[4], sessionData[i].mac[5]);

        char short_vendor[20];
        if (sessionData[i].vendor[2] == ':') {
          strcpy(short_vendor, "                   ");
        } else {
          snprintf(short_vendor, sizeof(short_vendor), "%-19.19s", sessionData[i].vendor);
        }

        snprintf(rowStr, sizeof(rowStr), "%2d. %s %-12s %6luB", (i + 1), macStr, short_vendor, sessionData[i].bytes);
      
      } else {
        char short_name[20];
        if (strlen(sessionBleData[i].name) == 0) {
          strcpy(short_name, "                   ");
        } else {
          snprintf(short_name, sizeof(short_name), "%-19.19s", sessionBleData[i].name);
        }

        snprintf(rowStr, sizeof(rowStr), "%2d. %s %-12s %ddBm (%d)", 
                 (i + 1), sessionBleData[i].mac, short_name, sessionBleData[i].rssi, sessionBleData[i].hits);
      }

      int y = 42 + (row * 18);
      tft.drawString(rowStr, 5, y);
      row++;
    }
  }

  tft.drawLine(0, 285, 480, 285, TFT_WHITE);

  if (device_current_page > 0 && total_devices > 0) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("<- PREV", 20, 295);
  }
  
  tft.setTextColor(TFT_RED);
  tft.drawString("BACK", 215, 295); 

  if (((device_current_page + 1) * DEVICES_PER_PAGE) < total_devices) {
    tft.setTextColor(TFT_WHITE);
    tft.drawString("NEXT ->", 360, 295);
  }
}

class BLEPassiveCallbacks: public BLEAdvertisedDeviceCallbacks {
  void onResult(BLEAdvertisedDevice* advertisedDevice) {
    if (pause_sniffing) return; 

    std::string macStr = advertisedDevice->getAddress().toString();
    int rssi = advertisedDevice->getRSSI();

    std::string deviceName = "";

    if (advertisedDevice->haveName()) {
      deviceName = advertisedDevice->getName();
    } 
    else if (advertisedDevice->haveManufacturerData()) {
      deviceName = resolveBleCompanyId(advertisedDevice->getManufacturerData());
    }

    bool found = false;
    for (int i = 0; i < liveBleCount; i++) {
      if (strcmp((char*)liveBleData[i].mac, macStr.c_str()) == 0) {
        liveBleData[i].hits++;
        liveBleData[i].rssi = rssi; 
        found = true;
        break;
      }
    }

    if (!found && liveBleCount < MAX_BLE_DEVICES) {
      strncpy((char*)liveBleData[liveBleCount].mac, macStr.c_str(), 17);
      liveBleData[liveBleCount].mac[17] = '\0';
      
      liveBleData[liveBleCount].rssi = rssi;
      liveBleData[liveBleCount].hits = 1;
      
      strncpy((char*)liveBleData[liveBleCount].name, deviceName.c_str(), 29);
      liveBleData[liveBleCount].name[29] = '\0';
      
      liveBleCount++;
    }
  }
};

// ADD THIS FLAG RIGHT ABOVE THE switchRadioMode FUNCTION
bool ble_initialized = false; 

void switchRadioMode(RadioMode targetMode) {
  pause_sniffing = true; 

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
  for (int i = 0; i < MAX_PROBE_SLOTS; i++) {
    // If the slot has an active flag, process it safely
    if (probeList[i].needs_lookup) {
      MacRecord dummy;
      memcpy(dummy.mac, probeList[i].mac, 6);
      dummy.vendorFound = false;
      
      resolveMacVendor(&dummy); 
      
      strncpy(probeList[i].vendor, dummy.vendor, 25);
      probeList[i].needs_lookup = false; // Clear the flag
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
  tft.drawString("OSINT: PASSIVE PROBE TRACKER", 240, 15);

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
      if (t_y > 250) {
        int total_devices = (currentRadioMode == RADIO_WIFI) ? sessionMacCount : sessionBleCount;

        // 1. PREV PAGE
        if (t_x < 160 && device_current_page > 0) {
          device_current_page--;
          drawDeviceList();
          delay(250);
        }
        // 2. NEXT PAGE
        else if (t_x > 320 && ((device_current_page + 1) * DEVICES_PER_PAGE) < total_devices) {
          device_current_page++;
          drawDeviceList();
          delay(250);
        }
        // 3. BACK TO MENU
        else if (t_x >= 160 && t_x <= 320) {
          currentState = SCREEN_MENU;
          device_current_page = 0; // Reset pagination for next time
          drawMenu(); // Draw the menu UI
          
          // Note: We intentionally leave pause_sniffing = true 
          // because the Menu screen expects the radios to remain paused!
          
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
        tft.drawString("BLE MODE | SCANNING...", 5, 4);
      }
    }

    if (should_render) {
      pause_sniffing = true; 
      
      if (currentRadioMode == RADIO_WIFI) {
        // ==========================================
        // 1. WI-FI DATA PROCESSING PIPELINE
        // ==========================================
        memcpy(sortData, (void*)liveData, sizeof(liveData));
        sortMacCount = liveMacCount;
        sortOtherBytes = liveOtherBytes;

        sessionOtherBytes += liveOtherBytes;
        for (int i = 0; i < liveMacCount; i++) {
          bool found = false;
          for (int j = 0; j < sessionMacCount; j++) {
            if (memcmp(sessionData[j].mac, (void*)liveData[i].mac, 6) == 0) {
              sessionData[j].bytes += liveData[i].bytes;
              found = true;
              break;
            }
          }
          if (!found) {
            if (sessionMacCount < MAX_MACS) {
              memcpy(&sessionData[sessionMacCount], (void*)&liveData[i], sizeof(MacRecord));
              sessionMacCount++;
            } else {
              sessionOtherBytes += liveData[i].bytes;
            }
          }
        }

        memset((void*)liveData, 0, sizeof(liveData));
        liveMacCount = 0;
        liveOtherBytes = 0;

        for (int i = 0; i < sortMacCount - 1; i++) {
          for (int j = 0; j < sortMacCount - i - 1; j++) {
            bool shouldSwap = false;
            if (sort_descending) {
              if (sortData[j].bytes < sortData[j+1].bytes) shouldSwap = true;
            } else {
              if (sortData[j].bytes == 0 && sortData[j+1].bytes > 0) shouldSwap = true;
              else if (sortData[j].bytes > sortData[j+1].bytes && sortData[j+1].bytes > 0) shouldSwap = true;
            }
            if (shouldSwap) {
              MacRecord temp = sortData[j];
              sortData[j] = sortData[j+1];
              sortData[j+1] = temp;
            }
          }
        }

        for (int i = 0; i < sessionMacCount - 1; i++) {
          for (int j = 0; j < sessionMacCount - i - 1; j++) {
            bool shouldSwap = false;
            if (sort_descending) {
              if (sessionData[j].bytes < sessionData[j+1].bytes) shouldSwap = true;
            } else {
              if (sessionData[j].bytes == 0 && sessionData[j+1].bytes > 0) shouldSwap = true;
              else if (sessionData[j].bytes > sessionData[j+1].bytes && sessionData[j+1].bytes > 0) shouldSwap = true;
            }
            if (shouldSwap) {
              MacRecord temp = sessionData[j];
              sessionData[j] = sessionData[j+1];
              sessionData[j+1] = temp;
            }
          }
        }

        sortOtherBytes = 0; 
        for(int i = 8; i < sortMacCount; i++) {
          sortOtherBytes += sortData[i].bytes;
        }

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
          for (int j = 0; j < sessionBleCount; j++) {
            if (strcmp((char*)sessionBleData[j].mac, (char*)liveBleData[i].mac) == 0) {
              sessionBleData[j].hits += liveBleData[i].hits;
              sessionBleData[j].rssi = liveBleData[i].rssi; 
              found = true;
              break;
            }
          }

          if (!found && sessionBleCount < MAX_BLE_DEVICES) {
            memcpy((void*)&sessionBleData[sessionBleCount], (void*)&liveBleData[i], sizeof(BLERecord));
            sessionBleCount++;
          }
        }

        memset((void*)liveBleData, 0, sizeof(liveBleData));
        liveBleCount = 0;

        // --- SORT BLE SNAPSHOT (WATERFALL) ---
        for (int i = 0; i < sortBleCount - 1; i++) {
          for (int j = 0; j < sortBleCount - i - 1; j++) {
            bool shouldSwap = false;
            if (sort_descending) {
              if (sortBleData[j].hits < sortBleData[j + 1].hits) shouldSwap = true;
            } else {
              if (sortBleData[j].hits == 0 && sortBleData[j + 1].hits > 0) shouldSwap = true;
              else if (sortBleData[j].hits > sortBleData[j + 1].hits && sortBleData[j + 1].hits > 0) shouldSwap = true;
            }
            if (shouldSwap) {
              BLERecord temp = sortBleData[j];
              sortBleData[j] = sortBleData[j + 1];
              sortBleData[j + 1] = temp;
            }
          }
        }

        // --- SORT BLE SESSION (SEEN DEVICES LIST) ---
        for (int i = 0; i < sessionBleCount - 1; i++) {
          for (int j = 0; j < sessionBleCount - i - 1; j++) {
            bool shouldSwap = false;
            if (sort_descending) {
              if (sessionBleData[j].hits < sessionBleData[j + 1].hits) shouldSwap = true;
            } else {
              if (sessionBleData[j].hits == 0 && sessionBleData[j + 1].hits > 0) shouldSwap = true;
              else if (sessionBleData[j].hits > sessionBleData[j + 1].hits && sessionBleData[j + 1].hits > 0) shouldSwap = true;
            }
            if (shouldSwap) {
              BLERecord temp = sessionBleData[j];
              sessionBleData[j] = sessionBleData[j + 1];
              sessionBleData[j + 1] = temp;
            }
          }
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
          } else {
            // BLE: Use the snapshot broadcast Name. If empty, fallback to MAC address.
            if (strlen(sortBleData[i].name) > 0) {
              strncpy(short_text, sortBleData[i].name, 19);
            } else {
              strncpy(short_text, sortBleData[i].mac, 19);
            }
          }
          short_text[19] = '\0';

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
        for(int i = 0; i < 8 && i < sortMacCount; i++) total_bytes += sortData[i].bytes;

        if (total_bytes > 0) {
          double log_total = 0;

          if (useLogScale) {
            for(int j = 0; j < 8 && j < sortMacCount; j++) {
              log_total += log10((double)sortData[j].bytes + 1.0);
            }
            log_total += log10((double)sortOtherBytes + 1.0);
          }

          for(int i = 0; i < 8 && i < sortMacCount; i++) {
            double fraction;
            if (useLogScale) {
              fraction = log10((double)sortData[i].bytes + 1.0) / log_total;
            } else {
              fraction = (double)sortData[i].bytes / (double)total_bytes;
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