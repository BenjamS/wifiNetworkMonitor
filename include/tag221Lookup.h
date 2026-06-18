#ifndef TAG221_DICTIONARY_H
#define TAG221_DICTIONARY_H

#include <Arduino.h> // Required so the compiler knows what uint8_t is

// ==========================================
// TAG 221: WEIGHTED OUI DICTIONARY
// ==========================================
struct Tag221_Vendor {
  uint8_t oui[3];
  uint8_t weight; // 3 = Device Brand, 2 = Silicon, 1 = Protocol
  const char* name;
};

// Update count to 48 to include the 3 new Amazon tags
const int TAG_221_COUNT = 48; 

// In C++, 'const' at the global scope has internal linkage, 
// making it perfectly safe to define this array directly in the header.
const Tag221_Vendor TAG_221_DATABASE[TAG_221_COUNT] = {
  
  // ==========================================
  // THE BIG FOUR (90% of Global Traffic)
  // ==========================================
  {{0x00, 0x50, 0xF2}, 1, "Microsoft (WPS)"},     
  {{0x50, 0x6F, 0x9A}, 1, "Wi-Fi Alliance"},      
  {{0x00, 0x10, 0x18}, 2, "Broadcom"},            
  {{0x00, 0x17, 0xF2}, 3, "Apple Inc."},          
  
  // ==========================================
  // TIER 3: DEVICE BRANDS & ECOSYSTEMS
  // ==========================================
  // Amazon Ecosystem (Echo, Ring, Eero)
  {{0xF0, 0xD2, 0xF1}, 3, "Amazon (Echo/Alexa)"},
  {{0xFC, 0xA1, 0x83}, 3, "Amazon Technologies"},
  {{0x44, 0x65, 0x0D}, 3, "Amazon Technologies"},

  // Mobile / Smart Home
  {{0x00, 0x1A, 0x11}, 3, "Google / Nest"},
  {{0x00, 0x12, 0x36}, 3, "Samsung Electronics"},
  {{0x00, 0x09, 0xAF}, 3, "Samsung Electronics"},
  {{0x00, 0x24, 0xE4}, 3, "Withings (Smart Health)"},
  
  // Gaming Consoles
  {{0x00, 0x50, 0x14}, 3, "Sony (PlayStation)"},
  {{0x00, 0x01, 0x4A}, 3, "Sony Corporation"},
  {{0x00, 0x14, 0x4F}, 3, "Nintendo"},
  {{0x00, 0x04, 0x4B}, 3, "NVIDIA (Shield/Tegra)"},
  
  // Enterprise / Infrastructure Networking
  {{0x00, 0x22, 0x5B}, 3, "Cisco Systems"},
  {{0x00, 0x40, 0x96}, 3, "Cisco Aironet"},
  {{0x00, 0x18, 0x0A}, 3, "Cisco Meraki"},
  {{0x00, 0x25, 0x9C}, 3, "Cisco Meraki"},
  {{0x00, 0x1A, 0xE1}, 3, "Ubiquiti Networks"},
  {{0x00, 0x27, 0x22}, 3, "Ubiquiti Networks"},
  {{0x00, 0x0B, 0x86}, 3, "Aruba Networks"},
  {{0x00, 0x1D, 0xC3}, 3, "Ruckus Wireless"},
  {{0x00, 0x14, 0x6C}, 3, "Netgear"},
  {{0x00, 0x10, 0x5A}, 3, "ZyXEL"},

  // Alternate Apple OUIs
  {{0x00, 0x03, 0x93}, 3, "Apple Inc."},
  {{0x00, 0x0A, 0x95}, 3, "Apple Inc."},
  
  // ==========================================
  // TIER 2: SILICON & CHIPSETS
  // ==========================================
  {{0x00, 0x15, 0x00}, 2, "Intel Corp"},
  {{0x00, 0x13, 0x74}, 2, "Atheros / Qualcomm"},
  {{0x00, 0x03, 0x7F}, 2, "Atheros / Qualcomm"},
  {{0x00, 0x0C, 0x43}, 2, "Ralink / MediaTek"},
  {{0x00, 0xE0, 0x4C}, 2, "Realtek Semiconductor"},
  {{0x08, 0x00, 0x28}, 2, "Texas Instruments"},
  {{0x00, 0x08, 0x22}, 2, "Intersil"},
  {{0x00, 0x01, 0x37}, 2, "Marvell Semiconductor"},
  {{0x00, 0x0A, 0xF5}, 2, "Airgo Networks"},
  {{0x00, 0x90, 0x4C}, 2, "Epigram (Broadcom)"},
  
  // ==========================================
  // TIER 1: PROTOCOLS & NICHE STANDARDS
  // ==========================================
  {{0x00, 0x03, 0x2A}, 1, "Cisco CCX"},           
  {{0x00, 0x0B, 0x86}, 1, "Aruba AirWave"},
  {{0x00, 0x50, 0x43}, 1, "Marvell WPS (Legacy)"},
  {{0x00, 0x0A, 0x43}, 1, "Cisco / Airespace"},
  {{0x00, 0x1B, 0x4F}, 1, "Avaya"},
  {{0x00, 0x05, 0xB5}, 1, "Broadcom (Legacy)"},
  {{0x00, 0x0F, 0xAC}, 1, "Sony (WPS/Legacy)"},
  {{0x00, 0x0E, 0x8E}, 1, "Intel (Legacy)"},
  {{0x00, 0x17, 0xDF}, 1, "Brocade"},
  {{0x00, 0x1C, 0x58}, 1, "Arris Group"}
};

#endif // TAG221_DICTIONARY_H