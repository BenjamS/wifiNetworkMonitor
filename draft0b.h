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

enum UIState { SCREEN_CHART, SCREEN_MENU, SCREEN_AP_SCAN, SCREEN_DEVICE_LIST };
UIState currentState = SCREEN_CHART;

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
const int MAX_BLE_DEVICES = 250;              // Max BLE devices stored in live RAM

// 1. VOLATILE LIVE BLE DATA (Filled by NimBLE Callback)
volatile BLERecord liveBleData[MAX_BLE_DEVICES];
volatile uint16_t liveBleCount = 0;
volatile int current_ble_traffic = 0;

// 2. MASTER SESSION BLE DATA (For UI Lists & Foxhunting)
BLERecord sessionBleData[MAX_BLE_DEVICES];
uint16_t sessionBleCount = 0;

// NimBLE Global Scanner Pointer
BLEScan* pBLEScan;

// We will eventually need live/sort arrays for BLE just like Wi-Fi,
// but let's keep the footprint clean for now while we build the UI switch.

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
char target_ssid[33] = {0}; // NEW: Store the name of the targeted network

const int HEADER_HEIGHT = 110; //125; //80;
const int CHART_BOTTOM = 320;
int current_x = 0;

struct MacRecord {
  uint8_t mac[6];
  uint32_t bytes;
  char vendor[25];
  bool vendorFound;
};

void resolveMacVendor(MacRecord* record);

// This is filled by the background radio interrupt. MUST be volatile!
volatile MacRecord liveData[MAX_MACS];
volatile uint16_t liveMacCount = 0;
volatile uint32_t liveOtherBytes = 0;

// A 1.5-second snapshot safely copied from liveData so the UI can draw it.
MacRecord sortData[MAX_MACS];
uint16_t sortMacCount = 0;
uint32_t sortOtherBytes = 0;

// The permanent historical memory bank that fixes the Amnesia Bug!
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
// Feed this a standard 24-bit hex value (e.g., 0xDA815E) and it returns the 16-bit version
// Compile-time converter: Standard 24-bit web hex (0xRRGGBB) to 16-bit RGB565
constexpr uint16_t hex24to565(uint32_t hex24) {
  return ((((hex24 >> 16) & 0xFF) & 0xF8) << 8) |
  ((((hex24 >> 8) & 0xFF) & 0xFC) << 3) |
  (((hex24) & 0xFF) >> 3);
}

// Your new 8-color array using standard web hex codes!
uint16_t colors[9] = {
  hex24to565(0x889FD7), // [0] Periwinkle Blue
  hex24to565(0xD1C9CA), // [1] Light Gray
  hex24to565(0xD9D680), // [2] Pale Yellow
  hex24to565(0xB75BE2), // [3] Purple
  hex24to565(0xE07EB6), // [4] Pink
  hex24to565(0xDA815E), // [5] Rust/Orange
  hex24to565(0x7CD9CA), // [6] Mint Green
  hex24to565(0x87E370),  // [7] Bright Green
  TFT_DARKGREY             // [8] "Other" category (unchanged)
};

// --- The Smart Endpoint Wi-Fi Sniffer Callback ---
void sniffer_callback(void* buf, wifi_promiscuous_pkt_type_t type) {
  if (pause_sniffing) return;
  wifi_promiscuous_pkt_t *pkt = (wifi_promiscuous_pkt_t *)buf;
  uint16_t len = pkt->rx_ctrl.sig_len;
  uint8_t* payload = pkt->payload;

  if (len < 24) return;

  // 1. Filter out everything except Data Frames (Type 0x08)
  if ((payload[0] & 0x0C) != 0x08) return;

  uint8_t* mac1 = payload + 4;  // Receiver
  uint8_t* mac2 = payload + 10; // Transmitter
  uint8_t* mac3 = payload + 16; // Source / Destination

  // 2. The Target AP Lock Gate (Still necessary to ignore other networks when locked)
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

  // 4. Smart Endpoint Identification (Replaces the old target_locked string comparison)
  uint8_t* client_mac = mac2; // Default to Transmitter

  if (from_ds && !to_ds) {
    // AP is transmitting to a client (Download). Track the Receiver.
    client_mac = mac1;
  }
  else if (to_ds && !from_ds) {
    // Client is transmitting to an AP (Upload). Track the Transmitter.
    client_mac = mac2;
  }

  // 5. Handle Broadcasts and Multicasts (Bypass to see the actual generator)
  bool is_broadcast = (client_mac[0] == 0xFF);
  bool is_ipv4_multicast = (client_mac[0] == 0x01 && client_mac[1] == 0x00 && client_mac[2] == 0x5E);
  bool is_ipv6_multicast = (client_mac[0] == 0x33 && client_mac[1] == 0x33);
  bool is_stp_multicast = (client_mac[0] == 0x01 && client_mac[1] == 0x80 && client_mac[2] == 0xC2);

  if (is_broadcast || is_ipv4_multicast || is_ipv6_multicast || is_stp_multicast) {
    client_mac = mac3; // Bypass the group address and track the true sender!
  }

  // 6. Target Exclusion Gate
  // If we are locked onto a target, we still want to keep the router's own MAC
  // out of the client legend so it doesn't skew the chart.
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
  // 1. Lock the radio interrupt to prevent race conditions during memory wipe
  pause_sniffing = true;

  // 2. Reset the waterfall chart cursor back to the left edge
  current_x = 0;

  // 3. Flush the background packet sniffing array (Volatile RAM)
  memset((void*)liveData, 0, sizeof(liveData));
  liveMacCount = 0;
  liveOtherBytes = 0;

  // 4. Flush the UI sorting and display array
  memset(sortData, 0, sizeof(sortData));
  sortMacCount = 0;
  sortOtherBytes = 0;

  // 5. Unlock the radio interrupt to resume capturing fresh packets
  pause_sniffing = false;
}

// --- UI Drawing Functions ---
void drawMenu() {
  tft.fillScreen(TFT_BLACK);

  // CRITICAL: Must be 1 when using custom GFX fonts to prevent pixelation
  tft.setTextSize(1);

  // ==========================================
  // HEADER
  // ==========================================
  tft.setFreeFont(&UbuntuMono_Regular11pt7b); // Using your 11pt font for the title
  tft.setTextDatum(MC_DATUM); // Middle-Center alignment
  tft.setTextColor(TFT_WHITE);
  tft.drawString("DASHBOARD SETTINGS", 240, 40); // Centered on the 480px screen

  // Switch to the smaller font for the buttons
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);

  // ==========================================
  // 1. LOG SCALE TOGGLE (Y: 90 - 130)
  // ==========================================
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

  // ==========================================
  // 2. SORT TOGGLE (Y: 140 - 180)
  // ==========================================
  if (sort_descending) {
    tft.fillRect(50, 140, 200, 40, TFT_DARKGREY);
    tft.setTextColor(TFT_WHITE);
    tft.drawRect(50, 140, 200, 40, TFT_WHITE);
    tft.drawString("SORT: HIGHEST", 150, 160);
  } else {
    // Optional: Make it a different color (like cyan) when ascending so it's visually distinct
    tft.fillRect(50, 140, 200, 40, TFT_DARKCYAN);
    tft.setTextColor(TFT_WHITE);
    tft.drawRect(50, 140, 200, 40, TFT_WHITE);
    tft.drawString("SORT: LOWEST", 150, 160);
  }

  // ==========================================
  // 3. AP SCANNER BUTTON (Y: 190 - 230)
  // ==========================================
  tft.fillRect(50, 190, 200, 40, TFT_BLACK);
  tft.drawRect(50, 190, 200, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("SELECT AP", 150, 210);

  // ==========================================
  // 4. SEEN DEVICES BUTTON (Y: 240 - 280)
  // ==========================================
  tft.fillRect(50, 240, 200, 40, TFT_BLACK);
  tft.drawRect(50, 240, 200, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("SEEN DEVICES", 150, 260);

  // ==========================================
  // NEW: RADIO MODE TOGGLE (X: 300, Y: 190 - 230)
  // ==========================================
  if (currentRadioMode == RADIO_WIFI) {
  tft.fillRect(300, 190, 150, 40, TFT_BLUE);
  tft.setTextColor(TFT_WHITE);
  } else {
    tft.fillRect(300, 190, 150, 40, TFT_PURPLE);
    tft.setTextColor(TFT_WHITE);
  }
  tft.drawRect(300, 190, 150, 40, TFT_WHITE);
  tft.drawString(currentRadioMode == RADIO_WIFI ? "MODE: WI-FI" : "MODE: BLE", 375, 210);

  // ==========================================
  // 5. EXIT BUTTON (Y: 240 - 280, X: 300)
  // ==========================================
  tft.fillRect(300, 240, 150, 40, TFT_RED);
  tft.drawRect(300, 240, 150, 40, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.drawString("EXIT", 375, 260);
}

void drawChartHeader() {
  tft.drawLine(0, HEADER_HEIGHT, 480, HEADER_HEIGHT, TFT_WHITE);

  // --- PRESERVED: MENU BUTTON (Standard GLCD Font Size 1) ---
  tft.setFreeFont(NULL); // Force standard font for menu button bounds
  tft.drawRoundRect(420, 2, 55, 14, 2, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.setTextSize(1);
  tft.setCursor(433, 5);
  tft.print("MENU");

  // --- MONOSPACE OVERHAUL: LEFT BANNER ---
  tft.setTextWrap(false);
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);

  char bannerStr[64];

  // ==========================================
  // RADIO-AWARE BANNER LOGIC
  // ==========================================
  if (currentRadioMode == RADIO_BLE) {
    // BLE MODE: Purple text, static scanner message
    tft.setTextColor(TFT_PURPLE);
    snprintf(bannerStr, sizeof(bannerStr), "BLE MODE | SCANNING...");
  }
  else {
    // WI-FI MODE: White text, dynamic channel/AP data
    tft.setTextColor(TFT_WHITE);

    if (!target_locked) {
      // Formatted exactly like your printf statement
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | FREE AIRSPACE", CHANNELS[current_ch_idx]);
    } else {
      // Preserved your exact safe truncation logic
      char safe_ssid[15];
      strncpy(safe_ssid, target_ssid, 14);
      safe_ssid[14] = '\0';
      snprintf(bannerStr, sizeof(bannerStr), "CH: %02d | %s (%ddBm)", target_channel, safe_ssid, target_rssi);
    }
  }

  // Draw the final calculated string at X: 5, Y: 4
  tft.drawString(bannerStr, 5, 4);
}

void drawApScanner() {
  tft.fillScreen(TFT_BLACK);
  tft.setTextSize(1); // Safety lock to prevent custom font pixelation

  int n = WiFi.scanComplete();
  if (n < 0) {
    // --- FIX 1: THE STATE RESET ---
    ap_current_page = 0;

    // SCANNING HEADER
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

  // --- STANDARD HEADERS ---
  tft.setFreeFont(&UbuntuMono_Regular11pt7b);
  tft.setTextDatum(MC_DATUM);
  tft.setTextColor(TFT_WHITE);
  tft.fillRect(0, 0, 480, 30, TFT_BLUE);
  tft.drawString("SELECT TARGET AP", 240, 15);

  // --- FREE AIRSPACE ROW ---
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM); // Switch back to Top-Left for list items
  tft.setTextColor(TFT_GREEN);
  tft.drawRect(0, 40, 480, 25, TFT_DARKGREY);
  // Drop the text down 5px to center it vertically within the 25px tall box
  tft.drawString("[*] SNIFF ALL (Free Airspace)", 5, 45);

  tft.setTextColor(TFT_WHITE);
  if (n == 0) {
    tft.drawString("No networks found in airspace.", 5, 75);
  } else {
    int start_idx = ap_current_page * APS_PER_PAGE;

    // --- FIX 2: THE SAFETY CLAMP ---
    if (start_idx >= n) {
      ap_current_page = 0;
      start_idx = 0;
    }

    int end_idx = start_idx + APS_PER_PAGE;
    if (end_idx > n) end_idx = n;

    int row = 0;
    for (int i = start_idx; i < end_idx; ++i) {
      int y = 70 + (row * 25);

      // We format the string exactly as you had it
      char apRowStr[80];
      snprintf(apRowStr, sizeof(apRowStr), "CH:%02d  %-16s  %4ddBm  %s",
               WiFi.channel(i),
               WiFi.SSID(i).substring(0, 16).c_str(),
               WiFi.RSSI(i),
               WiFi.BSSIDstr(i).c_str());

      // Draw string pushed down 5px to avoid hitting the top grey bounding box line
      tft.drawString(apRowStr, 5, y + 5);

      tft.drawRect(0, y, 480, 25, TFT_DARKGREY);
      row++;
    }

    // --- TURN OFF CUSTOM FONT FOR THE FOOTER ---
    tft.setFreeFont(NULL);
    tft.setTextSize(2);
    tft.setTextDatum(TL_DATUM);

    if (n > APS_PER_PAGE) {
      tft.drawLine(0, 285, 480, 285, TFT_WHITE);
      // Standard fonts allow background colors in setTextColor
      tft.setTextColor(TFT_WHITE, TFT_BLACK);

      if (ap_current_page > 0) {
        tft.setCursor(20, 295);
        tft.print("<- PREV");
      }
      if (end_idx < n) {
        tft.setCursor(360, 295);
        tft.print("NEXT ->");
      }
    }
  }
}

void drawDeviceList() {
  tft.fillScreen(TFT_BLACK);

  // --- GLOBALLY SET THE MONOSPACE FONT FOR THIS SCREEN ---
  tft.setFreeFont(&UbuntuMono_Regular9pt7b);
  tft.setTextDatum(TL_DATUM);
  tft.setTextSize(1); // Safety lock to prevent multiplier bleeding

  // --- DETERMINE THE ACTIVE DATA SOURCE ---
  int total_devices = (currentRadioMode == RADIO_WIFI) ? sessionMacCount : sessionBleCount;

  // --- 1. DRAW DYNAMIC HEADER ---
  tft.fillRect(0, 0, 480, 30, (currentRadioMode == RADIO_WIFI) ? TFT_BLUE : TFT_PURPLE);
  tft.setTextColor(TFT_WHITE);

  char headerStr[64];
  snprintf(headerStr, sizeof(headerStr), " SEEN %s DEVICES (Total: %d) ",
          (currentRadioMode == RADIO_WIFI) ? "WI-FI" : "BLE", total_devices);
  tft.drawString(headerStr, 5, 7);

  if (total_devices == 0) {
    tft.drawString("No devices captured yet.", 5, 50);
  } else {
    // --- 2. THE SAFETY CLAMP ---
    int start_idx = device_current_page * DEVICES_PER_PAGE;
    if (start_idx >= total_devices) {
      device_current_page = 0;
      start_idx = 0;
    }

    int end_idx = start_idx + DEVICES_PER_PAGE;
    if (end_idx > total_devices) end_idx = total_devices;

    // --- 3. DRAW DATA ROWS ---
    int row = 0;
    for (int i = start_idx; i < end_idx; i++) {
      char rowStr[64];

      if (currentRadioMode == RADIO_WIFI) {
        // WI-FI FORMATTING (Vendor + Bytes)
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
        // BLE FORMATTING (Name + RSSI + Hits)
        char short_name[20];

        // If the device broadcasts no name, blank it out to keep the columns aligned
        if (strlen(sessionBleData[i].name) == 0) {
          strcpy(short_name, "                   ");
        } else {
          snprintf(short_name, sizeof(short_name), "%-19.19s", sessionBleData[i].name);
        }

        // Display MAC, Name, RSSI, and total advertisement hits
        snprintf(rowStr, sizeof(rowStr), "%2d. %s %-12s %ddBm (%d)",
                 (i + 1), sessionBleData[i].mac, short_name, sessionBleData[i].rssi, sessionBleData[i].hits);
      }

      int y = 42 + (row * 18);
      tft.drawString(rowStr, 5, y);
      row++;
    }
  }

  // --- 4. DRAW FOOTER BUTTONS ---
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

// --- SD Card Binary Search ---
void resolveMacVendor(MacRecord* record) {
  // 1. SAFETY CHECK
  if (record->vendorFound) return;

  // 2. RAM CACHE CHECK: Search the high-speed ring buffer for this OUI
  for (int i = 0; i < cacheCount; i++) {
    if (vendorCache[i].oui[0] == record->mac[0] &&
        vendorCache[i].oui[1] == record->mac[1] &&
        vendorCache[i].oui[2] == record->mac[2]) {

      // CACHE HIT! Instantly copy it and exit without touching the SD card
      strncpy(record->vendor, vendorCache[i].vendor, 25);
      record->vendorFound = true;
      return;
    }
  }

  // 3. CACHE MISS: Prepare the default fallback (Raw MAC address)
  sprintf(record->vendor, "%02X:%02X:%02X:%02X:%02X:%02X",
          record->mac[0], record->mac[1], record->mac[2],
          record->mac[3], record->mac[4], record->mac[5]);

  char target[7];
  sprintf(target, "%02X%02X%02X", record->mac[0], record->mac[1], record->mac[2]);

  // 4. SD CARD LOOKUP
  FsFile file = sd.open("/oui_db.txt", O_READ);
  if (file) { // Only search if the file actually opened
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
        // MATCH FOUND! Overwrite the raw MAC fallback with the real vendor name
        strncpy(record->vendor, &line[7], 24);
        record->vendor[24] = '\0';

        // Trim trailing spaces
        for(int i = 23; i >= 0; i--) {
          if(record->vendor[i] == ' ') record->vendor[i] = '\0';
          else break;
        }
        break; // Exit the while loop early!
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

  // 5. Mark as resolved
  record->vendorFound = true;

  // 6. UPDATE THE RAM CACHE
  // Save the final result (whether it was the real name or the raw MAC fallback)
  // so we never have to hit the SD card for this OUI again.
  vendorCache[cacheHead].oui[0] = record->mac[0];
  vendorCache[cacheHead].oui[1] = record->mac[1];
  vendorCache[cacheHead].oui[2] = record->mac[2];

  strncpy(vendorCache[cacheHead].vendor, record->vendor, 25);

  // Advance the ring buffer head (looping back to 0 if it hits OUI_CACHE_SIZE)
  if (cacheCount < OUI_CACHE_SIZE) cacheCount++;
  cacheHead = (cacheHead + 1) % OUI_CACHE_SIZE;
}

std::string resolveBleCompanyId(std::string mfgData) {
  if (mfgData.length() < 2) return "";

  // Extract the 16-bit Company ID (Little Endian format)
  uint16_t companyId = (uint8_t)mfgData[1] << 8 | (uint8_t)mfgData[0];

  // High-Speed Binary Search through your PROGMEM array
  int left = 0;
  int right = numBleVendors - 1;

  while (left <= right) {
    int mid = left + (right - left) / 2;

    if (bleVendors[mid].id == companyId) {
      return bleVendors[mid].name; // Match found!
    }

    if (bleVendors[mid].id < companyId) {
      left = mid + 1; // Search right half
    } else {
      right = mid - 1; // Search left half
    }
  }

  return ""; // No match found
}

class BLEPassiveCallbacks: public BLEAdvertisedDeviceCallbacks {
  void onResult(BLEAdvertisedDevice* advertisedDevice) {
    if (pause_sniffing) return; // Respect the UI pause state

    current_ble_traffic++;

    std::string macStr = advertisedDevice->getAddress().toString();
    int rssi = advertisedDevice->getRSSI();

    // ==========================================
    // SMART VENDOR RESOLUTION PIPELINE
    // ==========================================
    std::string deviceName = "";

    // 1. Try to get the broadcasted human-readable name first
    if (advertisedDevice->haveName()) {
      deviceName = advertisedDevice->getName();
    }
    // 2. If no name, rip open the payload and search our new PROGMEM dictionary
    else if (advertisedDevice->haveManufacturerData()) {
      deviceName = resolveBleCompanyId(advertisedDevice->getManufacturerData());
    }

    // Check if we already saw this device in the current LIVE window
    bool found = false;
    for (int i = 0; i < liveBleCount; i++) {

      // FIX 1: Cast away 'volatile' so strcmp accepts the MAC array
      if (strcmp((char*)liveBleData[i].mac, macStr.c_str()) == 0) {

        liveBleData[i].hits++;
        liveBleData[i].rssi = rssi; // Always keep the freshest signal strength
        found = true;
        break;
      }
    }

    // If it's a new device, add it to the live array
    if (!found && liveBleCount < MAX_BLE_DEVICES) {

      // FIX 2: Cast away 'volatile' so strncpy accepts the MAC array
      strncpy((char*)liveBleData[liveBleCount].mac, macStr.c_str(), 17);
      liveBleData[liveBleCount].mac[17] = '\0';

      liveBleData[liveBleCount].rssi = rssi;
      liveBleData[liveBleCount].hits = 1;

      // FIX 3: Cast away 'volatile' so strncpy accepts the Name array
      // NOTE: Now pulling from our smartly resolved 'deviceName' string!
      strncpy((char*)liveBleData[liveBleCount].name, deviceName.c_str(), 29);
      liveBleData[liveBleCount].name[29] = '\0';

      liveBleCount++;
    }
  }
};

void switchRadioMode(RadioMode targetMode) {
  pause_sniffing = true; // Lock the data arrays

  if (targetMode == RADIO_WIFI) {
    // 1. TEARDOWN BLE
    if (pBLEScan != nullptr) {
      pBLEScan->stop();
      BLEDevice::deinit(true); // 'true' frees the Bluetooth memory back to the heap!
    }

    // 2. BOOT UP WI-FI
    esp_wifi_start();
    esp_wifi_set_promiscuous(true);

  } else if (targetMode == RADIO_BLE) {
    // 1. TEARDOWN WI-FI
    esp_wifi_set_promiscuous(false);
    esp_wifi_stop(); // Puts the Wi-Fi modem to sleep

    // 2. BOOT UP BLE
    BLEDevice::init("");
    pBLEScan = BLEDevice::getScan();
    pBLEScan->setAdvertisedDeviceCallbacks(new BLEPassiveCallbacks(), true);
    pBLEScan->setActiveScan(false); // CRITICAL: Passive scanning only to act as a true ghost
    pBLEScan->setInterval(100);     // How often to scan (ms)
    pBLEScan->setWindow(99);        // How long to listen per interval (ms)

    // Start scanning in the background (0 = scan continuously)
    pBLEScan->start(0, nullptr, false);
  }

  currentRadioMode = targetMode;
  pause_sniffing = false; // Unlock the arrays
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

  // --- RESTORED SD CARD SANITY CHECK ---
  Serial.println("\n--- Initializing SD Card ---");

  // Note: Replace SD_CS and SHARED_SPI with 5 and SPI if your compiler complains!
  if (!sd.begin(SdSpiConfig(5, SHARED_SPI, SD_SCK_MHZ(4)))) {
    Serial.println("[!] SD Card Mount Failed! Dumping exact hardware error:");
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
  uint16_t t_x = 0, t_y = 0;
  bool pressed = tft.getTouch(&t_x, &t_y);

  if (pressed) {

    // ==========================================
    // 1. CHART SCREEN TOUCH LOGIC
    // ==========================================
    if (currentState == SCREEN_CHART) {
      if (t_x > 400 && t_y < 40) {
        currentState = SCREEN_MENU;
        pause_sniffing = true;
        esp_wifi_set_promiscuous(false);
        drawMenu();
        delay(300);
      }
    }

    // ==========================================
    // 2. MENU SCREEN TOUCH LOGIC
    // ==========================================
    else if (currentState == SCREEN_MENU) {

      // 1. Log Scale Toggle (X: 50-250, Y: 90-130)
      if (t_x > 50 && t_x < 250 && t_y > 90 && t_y < 130) {
        useLogScale = !useLogScale;
        drawMenu();
        delay(300);
      }
      // 2. Sort Order Toggle (X: 50-250, Y: 140-180)
      else if (t_x > 50 && t_x < 250 && t_y > 140 && t_y < 180) {
        sort_descending = !sort_descending;
        drawMenu();
        delay(300);
      }
      // 3. AP Scanner Button (X: 50-250, Y: 190-230)
      else if (t_x > 50 && t_x < 250 && t_y > 190 && t_y < 230) {
        currentState = SCREEN_AP_SCAN;
        drawApScanner();
        delay(300);
      }
      // 4. Seen Devices Button (X: 50-250, Y: 240-280)
      else if (t_x > 50 && t_x < 250 && t_y > 240 && t_y < 280) {
        currentState = SCREEN_DEVICE_LIST;
        device_current_page = 0;
        drawDeviceList();
        delay(300);
      }
      // 5. Radio Mode Toggle Button (X: 300-450, Y: 190-230)
      else if (t_x > 300 && t_x < 450 && t_y > 190 && t_y < 230) {
        if (currentRadioMode == RADIO_WIFI) {
          switchRadioMode(RADIO_BLE);
        } else {
          switchRadioMode(RADIO_WIFI);
        }
        drawMenu();
        delay(300);
      }
      // 6. Exit Button (Moved Right to match bottom row: X: 300-450, Y: 240-280)
      else if (t_x > 300 && t_x < 450 && t_y > 240 && t_y < 280) {
        currentState = SCREEN_CHART;
        tft.fillScreen(TFT_BLACK);
        drawChartHeader();
        if (currentRadioMode == RADIO_WIFI) {
          if (target_locked) esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);
          esp_wifi_set_promiscuous(true);
        }
        pause_sniffing = false;
        delay(300);
      }
    }

    // ==========================================
    // 3. AP SCANNER TOUCH LOGIC
    // ==========================================
    else if (currentState == SCREEN_AP_SCAN) {
      // 1. SNIFF ALL BUTTON (y: 40 to 65)
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
      // 2. PAGINATION FOOTER (y: 270 to bottom of screen)
      else if (t_y >= 270) {
        int total_aps = WiFi.scanComplete();
        // Left half of screen handles PREV page
        if (t_x < 240 && ap_current_page > 0) {
          ap_current_page--;
          drawApScanner();
          delay(250);
        }
        // Right half of screen handles NEXT page
        else if (t_x >= 240 && ((ap_current_page + 1) * APS_PER_PAGE) < total_aps) {
          ap_current_page++;
          drawApScanner();
          delay(250);
        }
      }
      // 3. AP SELECTION LIST ROWS (y: 70 to 269)
      else if (t_y >= 70 && t_y < 270) {
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

    // ==========================================
    // 4. SEEN DEVICES TOUCH LOGIC
    // ==========================================
    else if (currentState == SCREEN_DEVICE_LIST) {
      if (t_y > 250) {
        // 1. PREV PAGE (Left Third)
        if (t_x < 160 && device_current_page > 0) {
          device_current_page--;
          drawDeviceList();
          delay(250);
        }
        // 2. NEXT PAGE BUTTON (Right Third)
        else if (t_x > 320) {
          if (currentRadioMode == RADIO_BLE) {
            // Check if there are enough BLE devices to justify a next page
            // (Assuming you display 10 items per page)
            if ((ble_list_page + 1) * 10 < liveBleCount) {
              ble_list_page++;
              should_render = true;
            }
          }
          else {
            // WI-FI MODE Pagination
            if ((wifi_list_page + 1) * 10 < liveWifiCount) {
              wifi_list_page++;
              should_render = true;
            }
          }
          delay(250); // Touch debounce
        }
        // 2. NEXT PAGE (Right Third)
        // FIX: Now uses sessionMacCount to page through historical data!
        //else if (t_x > 320 && ((device_current_page + 1) * DEVICES_PER_PAGE) < sessionMacCount) {
        //  device_current_page++;
        //  drawDeviceList();
        //  delay(250);
        //}
        // 3. BACK TO CHART (Center Third - Catch All)
        else if (t_x >= 160 && t_x <= 320) {
          currentState = SCREEN_CHART;
          tft.fillScreen(TFT_BLACK);
          drawChartHeader();
          if (currentRadioMode == RADIO_WIFI) {
            if (target_locked) esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);
            esp_wifi_set_promiscuous(true);
          }
          pause_sniffing = false;
          delay(300);
        }
      }
    }

  } // <-- End of main if (pressed)

if (currentState == SCREEN_CHART) {
    static unsigned long lastTimer = 0;
    bool should_render = false;

    // --- PREVENT INVISIBLE TEXT WRAPPING SLICE ---
    tft.setTextWrap(false);

    // ==========================================
    // RADIO-AWARE TIMERS & CHANNEL HOPPING
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

          // --- Header Text for Free Airspace ---
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

        // CRITICAL: Tells the UI to shift the waterfall down one pixel!
        should_render = true;

        // 1. Safely grab and reset the traffic counter
        int adverts = current_ble_traffic;
        current_ble_traffic = 0;

        // 2. Draw the Header (Width 200 to clear any old Wi-Fi AP names)
        tft.fillRect(5, 4, 200, 15, TFT_BLACK);
        tft.setFreeFont(&UbuntuMono_Regular9pt7b);
        tft.setTextDatum(TL_DATUM);
        tft.setTextColor(TFT_PURPLE);
        tft.drawString("BLE MODE | SCANNING...", 5, 4);

        // 3. Map traffic to screen width (0 to 480 pixels)
        // Tune the '50' down if the bars are too short, or up if maxing out too easily
        int barWidth = map(adverts, 0, 50, 0, 480);
        if (barWidth > 480) barWidth = 480;

        // 4. Dynamic Color Logic based on traffic density
        uint16_t barColor = TFT_PURPLE;
        if (adverts > 25) barColor = TFT_ORANGE;
        if (adverts > 40) barColor = TFT_RED;

        // 5. Draw the new traffic bar
        // Note: The waterfall shift logic happens elsewhere when should_render == true,
        // leaving the top row (e.g., Y=20) blank for this new line!
        tft.drawFastHLine(0, 20, barWidth, barColor);
      }
    }

if (should_render) {
      pause_sniffing = true; // Lock memory for both radios

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

        sortOtherBytes = 0; // Reset before recalculating
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

        // Sort BLE by strongest RSSI
        for (int i = 0; i < sessionBleCount - 1; i++) {
          for (int j = 0; j < sessionBleCount - i - 1; j++) {
            if (sessionBleData[j].rssi < sessionBleData[j + 1].rssi) {
              BLERecord temp = sessionBleData[j];
              sessionBleData[j] = sessionBleData[j + 1];
              sessionBleData[j + 1] = temp;
            }
          }
        }
      }

      pause_sniffing = false; // Unlock memory

      // Determine how many devices to show based on the active mode...
      int displayCount = (currentRadioMode == RADIO_WIFI) ? sortMacCount : sessionBleCount;

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
            // WI-FI: Use the OUI Vendor string
            strncpy(short_text, sortData[i].vendor, 19);
          } else {
            // BLE: Use the broadcast Name. If empty, fallback to MAC address.
            if (strlen(sessionBleData[i].name) > 0) {
              strncpy(short_text, sessionBleData[i].name, 19);
            } else {
              strncpy(short_text, sessionBleData[i].mac, 19);
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

      // Narrow eraser head to 4 pixels wide to save SPI bandwidth
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
        // BLE PLOTTING (Mapped RSSI / Proximity)
        // ==========================================
        double total_weight = 0;
        double weights[8] = {0};

        int ble_count = (sessionBleCount > 8) ? 8 : sessionBleCount;

        for(int i = 0; i < ble_count; i++) {
          // Clamp RSSI between -100 (weak) and -30 (strong)
          int rssi = sessionBleData[i].rssi;
          if (rssi < -100) rssi = -100;
          if (rssi > -30) rssi = -30;

          // Translate negative dBm to a positive visual weight
          weights[i] = rssi + 100;
          total_weight += weights[i];
        }

        if (total_weight > 0) {
          for(int i = 0; i < ble_count; i++) {
            double fraction = weights[i] / total_weight;

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
