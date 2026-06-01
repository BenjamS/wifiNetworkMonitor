#include <Arduino.h>
#include <WiFi.h>
#include "esp_wifi.h"
#include <TFT_eSPI.h>
#include <SPI.h>
#include "SdFat.h"

int ap_current_page = 0;
const int APS_PER_PAGE = 8; // Number of APs that fit safely between the header and footer

int target_rssi = 0;

SdFs sd;

enum UIState { SCREEN_CHART, SCREEN_MENU, SCREEN_AP_SCAN };
UIState currentState = SCREEN_CHART;

volatile bool pause_sniffing = false;
bool useLogScale = false;  

uint16_t calData[5] = { 288, 3501, 301, 3244, 7 };
TFT_eSPI tft = TFT_eSPI();

const int CHANNELS[] = {1, 6, 11};            
const int NUM_CHANNELS = 3;
int current_ch_idx = 0;

const int HOP_INTERVAL = 1500;                // Time spent on each channel (ms)
const int LOCKED_UPDATE_INTERVAL = 2000;      // Refresh rate when locked to an AP (ms)
const int MAX_MACS = 100;                     

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

volatile MacRecord liveData[MAX_MACS];
volatile uint16_t liveMacCount = 0;
volatile uint32_t liveOtherBytes = 0;

MacRecord sortData[MAX_MACS];
uint16_t sortMacCount = 0;
uint32_t sortOtherBytes = 0;

uint16_t colors[9] = {TFT_RED, TFT_CYAN, TFT_GREEN, TFT_YELLOW, TFT_MAGENTA, TFT_ORANGE, TFT_PURPLE, TFT_BLUE, TFT_DARKGREY};

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
  // 1. Reset the waterfall chart cursor back to the left edge
  current_x = 0;

  // 2. Lock the radio and flush all data buffers so old MACs don't bleed over
  pause_sniffing = true;
  
  memset((void*)liveData, 0, sizeof(liveData));
  liveMacCount = 0;
  liveOtherBytes = 0;
  
  memset((void*)sortData, 0, sizeof(sortData));
  sortMacCount = 0;
  sortOtherBytes = 0;
  
  pause_sniffing = false;
}

// --- UI Drawing Functions ---
void drawMenu() {
  tft.fillScreen(TFT_BLACK);
  tft.setTextSize(3);
  tft.setTextColor(TFT_WHITE);
  tft.setCursor(50, 30);
  tft.print("DASHBOARD SETTINGS");

  if (useLogScale) {
    tft.fillRect(50, 100, 200, 50, TFT_GREEN);
    tft.setTextColor(TFT_BLACK);
  } else {
    tft.fillRect(50, 100, 200, 50, TFT_DARKGREY);
    tft.setTextColor(TFT_WHITE);
  }
  tft.drawRect(50, 100, 200, 50, TFT_WHITE);
  tft.setTextSize(2);
  tft.setCursor(65, 115);
  if (useLogScale) tft.print("MODE: LOG");
  else tft.print("MODE: LINEAR");

  tft.drawRect(50, 175, 200, 50, TFT_WHITE); 
  tft.setCursor(65, 190);
  tft.setTextColor(TFT_WHITE);
  tft.print("Select AP");

  tft.fillRect(300, 250, 150, 50, TFT_RED);
  tft.drawRect(300, 250, 150, 50, TFT_WHITE);
  tft.setTextColor(TFT_WHITE);
  tft.setCursor(340, 265);
  tft.print("EXIT");
}

void drawChartHeader() {
  tft.drawLine(0, HEADER_HEIGHT, 480, HEADER_HEIGHT, TFT_WHITE); 
  tft.drawRoundRect(420, 2, 55, 14, 2, TFT_WHITE); 
  tft.setTextColor(TFT_WHITE);
  tft.setTextSize(1);
  tft.setCursor(433, 5);
  tft.print("MENU");

  // --- NEW: DRAW THE STATIC LEFT BANNER ONCE ---
  tft.setTextWrap(false);
  tft.setTextColor(TFT_WHITE, TFT_BLACK); 
  tft.setCursor(5, 5);
  
  if (!target_locked) {
    // Draw the full Free Airspace banner
    tft.printf("CH: %02d | FREE AIRSPACE", CHANNELS[current_ch_idx]);
  } else {
    // Draw the full Target AP banner with truncated SSID and RSSI
    char safe_ssid[15];
    strncpy(safe_ssid, target_ssid, 14);
    safe_ssid[14] = '\0';
    tft.printf("CH: %02d | %s (%ddBm)", target_channel, safe_ssid, target_rssi);
  }
}

void drawApScanner() {
  tft.fillScreen(TFT_BLACK);
  
  int n = WiFi.scanComplete();
  if (n < 0) {
    // --- FIX 1: THE STATE RESET ---
    // Instantly snap back to Page 1 on any fresh hardware scan
    ap_current_page = 0; 
    
    tft.setTextSize(2);
    tft.setTextColor(TFT_WHITE, TFT_BLUE);
    tft.fillRect(0, 0, 480, 30, TFT_BLUE);
    tft.setCursor(5, 7);
    tft.print(" SCANNING ACCESS POINTS... ");

    esp_wifi_set_promiscuous(false); 
    WiFi.mode(WIFI_STA);
    WiFi.disconnect();
    delay(100);
    
    n = WiFi.scanNetworks(); 
  }

  tft.setTextSize(2);
  tft.setTextColor(TFT_WHITE, TFT_BLUE);
  tft.fillRect(0, 0, 480, 30, TFT_BLUE);
  tft.setCursor(5, 7);
  tft.print(" SELECT TARGET AP (nmcli style) ");

  tft.setTextSize(1);
  tft.setCursor(5, 48);
  tft.setTextColor(TFT_GREEN, TFT_BLACK); 
  tft.print("[*] SNIFF ALL (Unfiltered Airspace)");
  tft.drawRect(0, 40, 480, 25, TFT_DARKGREY); 

  tft.setTextColor(TFT_WHITE, TFT_BLACK);
  if (n == 0) {
    tft.setCursor(5, 70);
    tft.print("No networks found in airspace.");
  } else {
    int start_idx = ap_current_page * APS_PER_PAGE;
    
    // --- FIX 2: THE SAFETY CLAMP ---
    // If the cache shrank and our page index is now pointing to empty 
    // space, force the math back to Page 1 before attempting to draw.
    if (start_idx >= n) {
      ap_current_page = 0;
      start_idx = 0;
    }
    
    int end_idx = start_idx + APS_PER_PAGE;
    if (end_idx > n) end_idx = n;

    int row = 0;
    for (int i = start_idx; i < end_idx; ++i) { 
      int y = 70 + (row * 25); 
      tft.setCursor(5, y + 8); 
      
      tft.printf("CH:%02d  %-16s  %4ddBm  %s", 
        WiFi.channel(i), 
        WiFi.SSID(i).substring(0, 16).c_str(), 
        WiFi.RSSI(i), 
        WiFi.BSSIDstr(i).c_str());
        
      tft.drawRect(0, y, 480, 25, TFT_DARKGREY);
      row++;
    }

    if (n > APS_PER_PAGE) {
      tft.drawLine(0, 285, 480, 285, TFT_WHITE);
      tft.setTextSize(2); 
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

// --- SD Card Binary Search ---
void resolveMacVendor(MacRecord* record) {
  if (record->vendorFound) return; 
  
  // --- NEW: Print the raw MAC address instead of "Unknown Device" ---
  sprintf(record->vendor, "%02X:%02X:%02X:%02X:%02X:%02X", 
          record->mac[0], record->mac[1], record->mac[2], 
          record->mac[3], record->mac[4], record->mac[5]);
  record->vendorFound = true; 

  char target[7];
  sprintf(target, "%02X%02X%02X", record->mac[0], record->mac[1], record->mac[2]);
  
  FsFile file = sd.open("/oui_db.txt", O_READ);
  if (!file) return;

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
    if (currentState == SCREEN_CHART) {
      if (t_x > 400 && t_y < 40) {
        currentState = SCREEN_MENU;
        pause_sniffing = true;           
        esp_wifi_set_promiscuous(false); 
        drawMenu(); 
        delay(300); 
      }
    } 
    else if (currentState == SCREEN_MENU) {
      if (t_x > 50 && t_x < 250 && t_y > 100 && t_y < 150) {
        useLogScale = !useLogScale;
        drawMenu(); 
        delay(300);
      }
      if (t_x > 50 && t_x < 250 && t_y > 175 && t_y < 225) {
        currentState = SCREEN_AP_SCAN;
        drawApScanner(); 
        delay(300); 
      }
      if (t_x > 300 && t_x < 450 && t_y > 250 && t_y < 300) {
        currentState = SCREEN_CHART;
        tft.fillScreen(TFT_BLACK); 
        drawChartHeader();               
        if (target_locked) esp_wifi_set_channel(target_channel, WIFI_SECOND_CHAN_NONE);
        esp_wifi_set_promiscuous(true);
        pause_sniffing = false;          
        delay(300);
      }
    }
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
      // Placed before the list selection to ensure it strictly intercepts footer clicks
      else if (t_y >= 270) {
        int total_aps = WiFi.scanComplete();
        
        // Left half of screen handles PREV page
        if (t_x < 240 && ap_current_page > 0) {
          ap_current_page--;
          drawApScanner(); // Forcibly redraw the menu with the new page
          delay(250);      // Debounce the touch so it doesn't double-skip pages
        } 
        // Right half of screen handles NEXT page
        else if (t_x >= 240 && ((ap_current_page + 1) * APS_PER_PAGE) < total_aps) {
          ap_current_page++;
          drawApScanner(); 
          delay(250);      
        }
      }
      
      // 3. AP SELECTION LIST ROWS (y: 70 to 269)
      // The starting Y is shifted to 70, and clamped at 269 so it never overlaps the footer
      else if (t_y >= 70 && t_y < 270) {
        int clicked_row = (t_y - 70) / 25; 
        
        // NEW MATH: Translate the screen row into the actual sliding window array index
        int actual_index = (ap_current_page * APS_PER_PAGE) + clicked_row;
        
        if (actual_index < WiFi.scanComplete()) {
          memcpy(target_bssid, WiFi.BSSID(actual_index), 6);
          target_channel = WiFi.channel(actual_index);
          
          // PRESERVED: Save the actual SSID text into memory with safety cap
          strncpy(target_ssid, WiFi.SSID(actual_index).c_str(), 32);
          target_ssid[32] = '\0'; 
          
          target_locked = true; 
          target_rssi = WiFi.RSSI(actual_index); // PRESERVED: Save static RSSI
          
          // PRESERVED: Your exact state transition and radio setup
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
  }
  
  if (currentState == SCREEN_CHART) {
    static unsigned long lastTimer = 0;
    bool should_render = false;

// --- PREVENT INVISIBLE TEXT WRAPPING SLICE ---
    tft.setTextWrap(false); 

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
        tft.setTextWrap(false);
        tft.setTextSize(1);
        tft.setTextColor(TFT_WHITE, TFT_BLACK); 
        tft.setCursor(5, 5);
        tft.printf("CH: %02d", CHANNELS[current_ch_idx]);
      }
    } 
    else {
      if (millis() - lastTimer > LOCKED_UPDATE_INTERVAL) {
        lastTimer = millis();
        should_render = true; 
      }
    }

    if (should_render) {
      pause_sniffing = true;
      memcpy(sortData, (void*)liveData, sizeof(liveData));
      sortMacCount = liveMacCount;
      sortOtherBytes = liveOtherBytes;
      memset((void*)liveData, 0, sizeof(liveData));
      liveMacCount = 0;
      liveOtherBytes = 0;
      pause_sniffing = false;
      
      for (int i = 0; i < sortMacCount - 1; i++) {
        for (int j = 0; j < sortMacCount - i - 1; j++) {
          if (sortData[j].bytes < sortData[j+1].bytes) {
            MacRecord temp = sortData[j];
            sortData[j] = sortData[j+1];
            sortData[j+1] = temp;
          }
        }
      }
      
      for(int i = 8; i < sortMacCount; i++) {
        sortOtherBytes += sortData[i].bytes;
      }

if (sortMacCount > 0 || sortOtherBytes > 0) {
        
        // 1. CALCULATE AND DRAW "OTHER" IN THE TOP MENU BANNER
        int otherCount = 0;
        if (sortMacCount > 8) {
          otherCount = sortMacCount - 8;
        }
        
        tft.setTextSize(1);          // Small font to match the top banner
        tft.setTextColor(colors[8], TFT_BLACK); // Keep your "Other" color mapping
        tft.setCursor(350, 5);
        tft.printf("OTHER: %-4d", otherCount);

        // 2. DRAW THE MAIN 8-DEVICE LEGEND
        // Start clearing at y=25 so we don't erase the top banner we just drew!
        tft.fillRect(0, 18, 480, HEADER_HEIGHT - 18, TFT_BLACK); 
        tft.setTextSize(2); // The big, readable font!
        
        for(int i = 0; i < 8 && i < sortMacCount; i++) {
          resolveMacVendor(&sortData[i]);
          
          char short_vendor[20];
          strncpy(short_vendor, sortData[i].vendor, 19);
          short_vendor[19] = '\0';
          
          tft.setTextColor(colors[i]);
          int x_pos = 5 + (i % 2) * 240; // 2 Columns (0px and 240px)
          int y_pos = 20 + (i / 2) * 22; // Start at 20px down, 22px spacing
          
          tft.setCursor(x_pos, y_pos);
          tft.print(short_vendor);
        }
      }

      // --- WATERFALL CHART PLOTTING MATH ---
      tft.fillRect(current_x + 1, HEADER_HEIGHT + 1, 10, CHART_BOTTOM - HEADER_HEIGHT, TFT_BLACK);
      
      int current_y = CHART_BOTTOM;
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
      
      current_x += 2;
      if (current_x >= 478) current_x = 0;
    }
  }
}