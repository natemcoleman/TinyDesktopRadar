#include <WiFi.h>
#include <WiFiClientSecure.h>
#include <WebServer.h>
#include <DNSServer.h>
#include <HTTPClient.h>
#include <ESPmDNS.h>
#include <ArduinoJson.h>
#include <LovyanGFX.hpp>
#include <Preferences.h>
#include <vector>
#include <cmath>
#include <freertos/FreeRTOS.h>
#include <freertos/task.h>
#include <LittleFS.h>

#define SERIAL_SAFE if (Serial)

// --- Custom PSRAM Allocator for Massive JSON Payloads ---
struct SpiRamAllocator {
  void* allocate(size_t size) { return heap_caps_malloc(size, MALLOC_CAP_SPIRAM); }
  void deallocate(void* pointer) { heap_caps_free(pointer); }
  void* reallocate(void* ptr, size_t new_size) { return heap_caps_realloc(ptr, new_size, MALLOC_CAP_SPIRAM); }
};
using PsramJsonDocument = BasicJsonDocument<SpiRamAllocator>;

WebServer server(80);
DNSServer dnsServer;
Preferences preferences;

// --- State Tracking ---
bool isAPMode = false;
unsigned long touchStartTime = 0;
bool isTouching = false;
bool showSettingsQR = false;

// --- Stored Credentials ---
String savedSSID = "";
String savedPASS = "";
String osUser = "";
String osPass = "";

// --- Configurable Radar Settings ---
int radarMode = 0;              
float radarRangeMiles = 25.0;
float homeLat = 0.0;        
float homeLon = 0.0;
int altFloor = 0;
int altCeiling = 50000;
String filterCallsign = "";
int screenBrightness = 200;
float latOffset = 0.0;
float lonOffset = 0.0;
float lastFetchedLat = 0.0;
float lastFetchedLon = 0.0;

bool runwaysLoaded = false;
unsigned long lastRunwayAttempt = 0;
bool forceApiUpdate = false;

// --- API Status & Synchronization ---
String apiStatusMsg = "Waiting for first API connection...";
String apiStatusColor = "#aaaaaa"; 
String bearerToken = "";
unsigned long tokenExpiresAt = 0;
unsigned long currentPollIntervalMs = 22000; 
// unsigned long currentPollIntervalMs = 10000; 
int currentBaseInterval = 22;

// --- Authentic Radar Data Structures ---
struct Aircraft {
  String callsign;
  float lat, lon;
  float altitude_ft, heading, speed_knots, vert_rate;
  int px, py;
  float angle;
  unsigned long lastSeen;
};

struct GeoLine {
  float lat1, lon1;
  float lat2, lon2;
};

struct BoundingBox {
  int x, y, w, h;
};

SemaphoreHandle_t planesMutex;
std::vector<Aircraft> targetPlanes; 
std::vector<Aircraft> activePlanes; 
std::vector<GeoLine> localRunways;
std::vector<GeoLine> localCoastlines;
std::vector<GeoLine> localStates;

float sweepAngle = 0;

// --- Helper Functions ---
bool isOverlapping(BoundingBox newBox, const std::vector<BoundingBox>& drawnBoxes) {
  for (const auto& box : drawnBoxes) {
    if (newBox.x < box.x + box.w && newBox.x + newBox.w > box.x &&
        newBox.y < box.y + box.h && newBox.y + newBox.h > box.y) {
      return true; 
    }
  }
  return false; 
}
// Checks a single box against another single box
bool isOverlapping(BoundingBox box1, BoundingBox box2) {
  return (box1.x < box2.x + box2.w && box1.x + box1.w > box2.x &&
          box1.y < box2.y + box2.h && box1.y + box1.h > box2.y);
}

String urlEncode(String str) {
  String encodedString = "";
  for (int i = 0; i < str.length(); i++) {
    char c = str.charAt(i);
    if (isalnum(c)) { encodedString += c; }
    else {
      char code0 = (c & 0xf) + '0';
      if ((c & 0xf) > 9) code0 = (c & 0xf) - 10 + 'A';
      char code1 = ((c >> 4) & 0xf) + '0';
      if (((c >> 4) & 0xf) > 9) code1 = ((c >> 4) & 0xf) - 10 + 'A';
      encodedString += '%'; encodedString += code1; encodedString += code0;
    }
  }
  return encodedString;
}

// --- Custom Waveshare ESP32-S3 I80 Hardware Definition ---
class LGFX : public lgfx::LGFX_Device {
  lgfx::Panel_GC9A01      _panel_instance;
  lgfx::Bus_SPI           _bus_instance;
  lgfx::Light_PWM         _light_instance;
  lgfx::Touch_CST816S     _touch_instance;

public:
  LGFX(void) {
    { // SPI Bus Configuration
      auto cfg = _bus_instance.config();
      cfg.spi_host = SPI2_HOST;
      cfg.spi_mode = 0;
      cfg.freq_write = 40000000; // 40MHz SPI clock
      cfg.pin_sclk = 3;          // SPI Clock (SCL)
      cfg.pin_mosi = 10;         // SPI MOSI (SDA)
      cfg.pin_miso = -1;         // Not used by screen
      cfg.pin_dc   = 18;         // Data/Command (DC)
      _bus_instance.config(cfg); 
      _panel_instance.setBus(&_bus_instance);
    }
    { // Panel Configuration
      auto cfg = _panel_instance.config();
      cfg.pin_cs = 2;            // Chip Select (CS)
      cfg.pin_rst = 21;          // Reset (RST)
      cfg.pin_busy = -1;
      cfg.memory_width = 240; cfg.memory_height = 240;
      cfg.panel_width = 240; cfg.panel_height = 240;
      cfg.offset_x = 0; cfg.offset_y = 0; 
      cfg.invert = true;         
      _panel_instance.config(cfg);
    }
    { // Backlight Configuration
      auto cfg = _light_instance.config();
      cfg.pin_bl = 42;           // Backlight Pin (BLK)
      cfg.invert = false; 
      cfg.freq = 44100; 
      cfg.pwm_channel = 7;
      _light_instance.config(cfg); 
      _panel_instance.setLight(&_light_instance);
    }
    { // Touch Configuration
      auto cfg = _touch_instance.config();
      cfg.x_min = 239; cfg.x_max = 0;
      cfg.y_min = 0; cfg.y_max = 239;
      cfg.bus_shared = false; 
      cfg.offset_rotation = 0;
      cfg.i2c_port = 1; cfg.i2c_addr = 0x15;
      cfg.pin_sda = 8;           // Touch I2C SDA
      cfg.pin_scl = 9;           // Touch I2C SCL
      cfg.pin_int = 11;          // Touch Interrupt (updated to IO11)
      cfg.pin_rst = 0;           // Touch Reset (IO0)
      cfg.freq = 400000;
      _touch_instance.config(cfg); 
      _panel_instance.setTouch(&_touch_instance);
    }
    setPanel(&_panel_instance);
  }
};

LGFX lcd;
LGFX_Sprite sprite(&lcd); 

const char index_html[] PROGMEM = R"rawliteral(
<!DOCTYPE html>
<html>
<head>
  <meta charset="UTF-8"> <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Radar Configuration</title>
  <style>
    body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; background: #121212; color: #fff; padding: 20px; }
    
    /* --- Collapsible Accordion Styling --- */
    details { background: #1a1a1a; border-radius: 8px; margin-top: 15px; border: 1px solid #333; overflow: hidden; transition: box-shadow 0.3s, border-color 0.3s; }
    summary { font-size: 18px; font-weight: bold; padding: 15px; cursor: pointer; background: #222; display: flex; align-items: center; border-bottom: 1px solid transparent; user-select: none; }
    details[open] summary { border-bottom: 1px solid #333; color: #fff; }
    summary:hover { background: #2a2a2a; }
    .section-content { padding: 15px; }
    
    /* The Glow Effect for missing setup steps */
    details.needs-attention { border-color: #0A84FF; box-shadow: 0 0 12px rgba(10, 132, 255, 0.4); }
    details.needs-attention summary { color: #0A84FF; }
    
    label { display: block; margin-top: 15px; font-size: 14px; color: #aaa; }
    input, select { width: 100%; padding: 10px; margin-top: 5px; border-radius: 6px; border: 1px solid #444; background: #222; color: #fff; box-sizing: border-box; }
    input[type="file"] { background: transparent; border: 1px dashed #444; padding: 15px; text-align: center; color: #0A84FF; cursor: pointer; }
    
    .checkbox-container { display: flex; align-items: center; margin-top: 8px; }
    .checkbox-container input { width: auto; margin: 0 8px 0 0; }
    .checkbox-container label { margin: 0; font-size: 13px; color: #ddd; }

    button { background: #0A84FF; color: white; padding: 15px; border: none; border-radius: 8px; width: 100%; margin-top: 30px; font-size: 16px; font-weight: bold; cursor: pointer; transition: background 0.3s;}
    button.secondary { background: transparent; border: 2px solid #0A84FF; color: #0A84FF; margin-top: 15px; }
    
    .status { font-size: 13px; margin-top: 8px; font-weight: bold; }
    .help-link { color: #0A84FF; text-decoration: none; font-size: 12px; font-weight: normal; margin-bottom: 10px; display: inline-block; }
    .location-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 10px; align-items: end;}
    .save-box { margin-top: 25px; padding: 15px; background: #151515; border-radius: 8px; border: 1px solid #333; }
  </style>
  <script>
    function submitForm(event) {
      event.preventDefault();
      var btn = document.getElementById('saveBtn');
      btn.innerHTML = "Saved! Updating...";
      btn.style.background = "#28a745";
      
      fetch('/save', { method: 'POST', body: new FormData(event.target) })
        .then(response => response.text())
        .then(text => {
          if(text.includes("Rebooting")) {
             btn.innerHTML = "Rebooting Radar...";
             setTimeout(() => { location.reload(); }, 6000); // Auto-refresh page after reboot
          } else {
             setTimeout(() => { btn.innerHTML = "Save & Update"; btn.style.background = "#0A84FF"; }, 2000);
          }
        });
    }

    function togglePasswords() {
      var type = document.getElementById('showPass').checked ? 'text' : 'password';
      document.getElementsByName('pass')[0].type = type;
      document.getElementsByName('osPass')[0].type = type;
    }

    const defaultAirports = {
      "Baltimore/Washington (BWI)": {lat: 39.1774, lon: -76.6684},
      "Reagan National (DCA)": {lat: 38.8512, lon: -77.0402},
      "Washington Dulles (IAD)": {lat: 38.9531, lon: -77.4565},
      "Stockholm Arlanda (ARN)": {lat: 59.6498, lon: 17.9238},
      "New York (JFK)": {lat: 40.6413, lon: -73.7781},
      "Los Angeles (LAX)": {lat: 33.9416, lon: -118.4085},
      "Chicago O'Hare (ORD)": {lat: 41.9742, lon: -87.9073},
      "London Heathrow (LHR)": {lat: 51.4700, lon: -0.4543}
    };

    let customAirports = JSON.parse(localStorage.getItem('customAirports')) || {};

    // --- Smart Setup Wizard ---
    function initSetupWizard() {
      // 1. Initialize the dropdowns
      var sel = document.getElementById('airportSelect');
      sel.innerHTML = '<option value="">-- Select Hub or Saved Location --</option>';
      let grpDef = document.createElement('optgroup');
      grpDef.label = "Major Hubs";
      for (let key in defaultAirports) { grpDef.innerHTML += `<option value="${key}">${key}</option>`; }
      sel.appendChild(grpDef);
      if (Object.keys(customAirports).length > 0) {
        let grpCust = document.createElement('optgroup');
        grpCust.label = "My Saved Locations";
        for (let key in customAirports) { grpCust.innerHTML += `<option value="${key}">${key}</option>`; }
        sel.appendChild(grpCust);
      }

      // 2. Execute Collapse Logic
      const ssid = document.getElementsByName('ssid')[0].value;
      const osUser = document.getElementsByName('osUser')[0].value;

      const secNetwork = document.getElementById('sec-network');
      const secOpenSky = document.getElementById('sec-opensky');
      const secFocus = document.getElementById('sec-focus');
      const secFilters = document.getElementById('sec-filters');
      const secOverlays = document.getElementById('sec-overlays');

      // Close everything by default
      [secNetwork, secOpenSky, secFocus, secFilters, secOverlays].forEach(sec => sec.removeAttribute('open'));

      if (!ssid) {
          // Step 1: Needs WiFi
          secNetwork.setAttribute('open', '');
          secNetwork.classList.add('needs-attention');
      } else if (!osUser) {
          // Step 2: Needs API Keys
          secOpenSky.setAttribute('open', '');
          secOpenSky.classList.add('needs-attention');
      } else {
          // Setup Complete: Open normal daily usage sections
          secFocus.setAttribute('open', '');
          secFilters.setAttribute('open', '');
      }
    }

    window.onload = initSetupWizard;

    function setAirport() {
      var sel = document.getElementById('airportSelect').value;
      let target = defaultAirports[sel] || customAirports[sel];
      if(target) {
        document.getElementsByName('lat')[0].value = target.lat;
        document.getElementsByName('lon')[0].value = target.lon;
      }
    }

    async function recenterGPS() {
      var btn = document.getElementById('gpsBtn');
      btn.innerHTML = "⏳ Locating Network...";
      try {
        let response = await fetch('http://ip-api.com/json/');
        let data = await response.json();
        if (data && data.status === "success") {
          document.getElementsByName('lat')[0].value = parseFloat(data.lat).toFixed(4);
          document.getElementsByName('lon')[0].value = parseFloat(data.lon).toFixed(4);
          document.getElementById('airportSelect').value = ""; 
          alert("✅ Location locked via WiFi IP Address!");
        } else {
          alert("❌ IP lookup failed.");
        }
      } catch (err) { alert("⚠️ Network error."); }
      btn.innerHTML = "📍 Auto-Locate (IP)";
    }

    async function lookupAirportCode() {
      let query = document.getElementById('airportSearch').value.trim();
      if (!query) return;
      let btn = document.getElementById('lookupBtn');
      btn.innerHTML = "⏳ Searching...";
      try {
        let response = await fetch(`https://nominatim.openstreetmap.org/search?q=${encodeURIComponent(query)}+airport&format=json&limit=1`);
        let data = await response.json();
        if (data && data.length > 0) {
          let foundName = data[0].name || (query.toUpperCase() + " Airport");
          document.getElementsByName('lat')[0].value = parseFloat(data[0].lat).toFixed(4);
          document.getElementsByName('lon')[0].value = parseFloat(data[0].lon).toFixed(4);
          document.getElementById('customName').value = foundName;
          alert("✅ Found: " + foundName + "!\nCoordinates loaded.");
        } else {
          alert("❌ Could not find an airport matching '" + query + "'.");
        }
      } catch (err) { alert("⚠️ Network error."); }
      btn.innerHTML = "🔍 Lookup";
    }

    function saveCustomLocation() {
      let name = document.getElementById('customName').value.trim();
      let lat = document.getElementsByName('lat')[0].value;
      let lon = document.getElementsByName('lon')[0].value;
      if(!name || !lat || !lon) return;
      customAirports[name] = {lat: parseFloat(lat), lon: parseFloat(lon)};
      localStorage.setItem('customAirports', JSON.stringify(customAirports));
      initSetupWizard();
      document.getElementById('airportSelect').value = name;
      document.getElementById('customName').value = '';
      alert("Added to your saved dropdown!");
    }

    function handleFileUpload(event) {
      var file = event.target.files[0];
      if (!file) return;
      var reader = new FileReader();
      reader.onload = function(e) {
        try {
          var json = JSON.parse(e.target.result);
          var id = json.clientId || json.client_id || "";
          var secret = json.secret || json.clientSecret || json.client_secret || "";
          if (id) document.getElementsByName('osUser')[0].value = id;
          if (secret) document.getElementsByName('osPass')[0].value = secret;
        } catch (err) { alert("❌ Error reading file."); }
      };
      reader.readAsText(file);
    }
  </script>
</head>
<body>
  <h1>Desktop Radar</h1>
  <form onsubmit="submitForm(event)">
    
    <details id="sec-network">
      <summary>📡 Network Setup</summary>
      <div class="section-content">
        <label>WiFi SSID</label><input type="text" name="ssid" value="%SSID%">
        <label>WiFi Password</label><input type="password" name="pass" value="%PASS%">
      </div>
    </details>

    <details id="sec-opensky">
      <summary>☁️ OpenSky API</summary>
      <div class="section-content">
        <a class="help-link" href="https://opensky-network.org/my-opensky/account" target="_blank">Generate Keys Here &rarr;</a>
        
        <label style="color: #0A84FF; margin-top: 0;">Auto-Fill from downloaded file:</label>
        <input type="file" accept=".json" onchange="handleFileUpload(event)">
        
        <label>API Client ID</label><input type="text" name="osUser" value="%OSUSER%">
        <label>API Client Secret</label><input type="password" name="osPass" value="%OSPASS%">
        
        <div class="checkbox-container">
          <input type="checkbox" id="showPass" onchange="togglePasswords()">
          <label for="showPass">Show Passwords & Keys</label>
        </div>
        
        <div class="status">%AUTH_STATUS%</div>
      </div>
    </details>
    
    <details id="sec-focus">
      <summary>🎯 Radar Focus</summary>
      <div class="section-content">
        <label>Quick Center on Location</label>
        <select id="airportSelect" onchange="setAirport()"></select>

        <button type="button" id="gpsBtn" class="secondary" onclick="recenterGPS()">📍 Auto-Locate (IP)</button>

        <div class="location-grid">
          <div><label>Latitude</label><input type="text" name="lat" value="%LAT%"></div>
          <div><label>Longitude</label><input type="text" name="lon" value="%LON%"></div>
        </div>

        <div class="save-box">
          <label style="color: #0A84FF; margin-top: 0; font-weight: bold;">Find & Save New Location</label>
          <div class="location-grid" style="margin-bottom: 10px;">
            <div><input type="text" id="airportSearch" placeholder="Code (e.g. DIJ)"></div>
            <div><button type="button" id="lookupBtn" class="secondary" style="margin-top: 5px; padding: 11px;" onclick="lookupAirportCode()">🔍 Lookup</button></div>
          </div>
          <div class="location-grid">
            <div><input type="text" id="customName" placeholder="Display Name"></div>
            <div><button type="button" class="secondary" style="margin-top: 5px; padding: 11px; border-color: #28a745; color: #28a745;" onclick="saveCustomLocation()">➕ Save</button></div>
          </div>
        </div>
      </div>
    </details>

    <details id="sec-overlays">
      <summary>⚙️ Overlays</summary>
      <div class="section-content">
        <div class="checkbox-container">
          <input type="checkbox" id="showCoast" name="showCoast" %CHECKED_COAST%>
          <label for="showCoast">Show Coastlines</label>
        </div>
        <div class="checkbox-container" style="margin-bottom: 25px;">
          <input type="checkbox" id="showStates" name="showStates" %CHECKED_STATES%>
          <label for="showStates">Show State Borders</label>
        </div>
      </div>
    </details>

    <details id="sec-filters">
      <summary>✈️ Airspace Filters</summary>
      <div class="section-content">
        <label>Radius (Miles)</label><input type="number" name="range" value="%RANGE%">
        <label>Filter Callsign (Leave blank for all)</label><input type="text" name="filter" value="%FILTER%">
        <div class="location-grid">
          <div><label>Min Altitude (ft)</label><input type="number" name="floor" value="%FLOOR%"></div>
          <div><label>Max Altitude (ft)</label><input type="number" name="ceil" value="%CEIL%"></div>
        </div>
      </div>
    </details>
    
    <button id="saveBtn" type="submit">Save & Update</button>
  </form>
</body>
</html>
)rawliteral";

void drawQRCode(String url, String title) {
  sprite.fillScreen(TFT_WHITE);
  sprite.setTextColor(TFT_BLACK, TFT_WHITE);
  sprite.qrcode(url.c_str(), 40, 40, 160, 3);
  sprite.setTextColor(TFT_BLUE, TFT_WHITE);
  sprite.setTextDatum(top_center);
  sprite.drawString(title, 120, 15);
  sprite.drawString("Scan to Configure", 120, 215);
}

void handleRoot() {
  String html = String(index_html);
  html.replace("%SSID%", savedSSID); html.replace("%PASS%", savedPASS);
  html.replace("%OSUSER%", osUser); html.replace("%OSPASS%", osPass);
  html.replace("%LAT%", String(homeLat, 4)); html.replace("%LON%", String(homeLon, 4));
  html.replace("%RANGE%", String((int)radarRangeMiles)); html.replace("%FILTER%", filterCallsign);
  html.replace("%FLOOR%", String(altFloor)); html.replace("%CEIL%", String(altCeiling));
  
  String statusHtml = "<span style='color: " + apiStatusColor + ";'>Status: " + apiStatusMsg + "</span>";
  html.replace("%AUTH_STATUS%", statusHtml);
  
  html.replace("%CHECKED_COAST%", preferences.getBool("showCoast", true) ? "checked" : "");
  html.replace("%CHECKED_STATES%", preferences.getBool("showStates", true) ? "checked" : "");
  
  server.send(200, "text/html", html);
}

void handleSave() {
  if (server.hasArg("ssid")) {
    
    // --- NEW: REBOOT DETECTION ---
    bool needsReboot = false;
    if (server.arg("ssid") != savedSSID || 
        server.arg("pass") != savedPASS || 
        server.arg("osUser") != osUser || 
        server.arg("osPass") != osPass) {
        
        needsReboot = true;
        SERIAL_SAFE Serial.println("[SYSTEM] Critical Network/API changes detected. Reboot scheduled.");
    }

    // 1. Save to non-volatile flash memory (for the next time you actually unplug it)
    preferences.putString("ssid", server.arg("ssid"));
    preferences.putString("pass", server.arg("pass"));
    preferences.putString("os_user", server.arg("osUser")); 
    preferences.putString("os_pass", server.arg("osPass"));
    preferences.putFloat("lat", server.arg("lat").toFloat());
    preferences.putFloat("lon", server.arg("lon").toFloat());
    preferences.putFloat("range", server.arg("range").toFloat()); 
    preferences.putString("filter", server.arg("filter"));
    preferences.putInt("floor", server.arg("floor").toInt()); 
    preferences.putInt("ceil", server.arg("ceil").toInt());

    preferences.putBool("showCoast", server.hasArg("showCoast"));
    preferences.putBool("showStates", server.hasArg("showStates"));
    
    // 2. LIVE UPDATE: Immediately overwrite the active variables in RAM
    savedSSID = server.arg("ssid"); // Added so the RAM matches flash!
    savedPASS = server.arg("pass"); // Added so the RAM matches flash!
    osUser = server.arg("osUser");
    osPass = server.arg("osPass");
    homeLat = server.arg("lat").toFloat();
    homeLon = server.arg("lon").toFloat();
    radarRangeMiles = server.arg("range").toFloat();
    filterCallsign = server.arg("filter");
    altFloor = server.arg("floor").toInt();
    altCeiling = server.arg("ceil").toInt();

    // --- LOCATION SENTINEL ---
    float newLat = server.arg("lat").toFloat();
    float newLon = server.arg("lon").toFloat();
    
    // Only trigger heavy updates if the user actually moved the pin significantly (> 0.05 degrees)
    if (abs(newLat - lastFetchedLat) > 0.05 || abs(newLon - lastFetchedLon) > 0.05) {
        SERIAL_SAFE Serial.println("[SYSTEM] Significant location change detected. Refreshing maps...");
        lastFetchedLat = newLat;
        lastFetchedLon = newLon;
        runwaysLoaded = false;
        lastRunwayAttempt = 0; 
        forceApiUpdate = true;
        
        xSemaphoreTake(planesMutex, portMAX_DELAY);
        activePlanes.clear();
        targetPlanes.clear();
        xSemaphoreGive(planesMutex);
        sprite.fillScreen(TFT_BLACK);
    } else {
        SERIAL_SAFE Serial.println("[SYSTEM] Location unchanged. Maps preserved.");
    }
    
    // --- EXECUTE REBOOT IF NEEDED ---
    if (needsReboot) {
        server.send(200, "text/plain", "Network/API updated. Rebooting..."); 
        delay(1000); // CRITICAL: Wait 1 second so the web browser actually receives the HTTP 200 Success message!
        ESP.restart();
    } else {
        server.send(200, "text/plain", "Settings saved and updated live!"); 
    }
  }
}

void fetchLocationFromIP() {
  HTTPClient http;
  http.begin("http://ip-api.com/json/"); 
  if (http.GET() == HTTP_CODE_OK) {
    JsonDocument doc;
    deserializeJson(doc, http.getString());
    if (doc["status"] == "success") {
      homeLat = doc["lat"]; homeLon = doc["lon"];
      preferences.putFloat("lat", homeLat); preferences.putFloat("lon", homeLon);
    }
  }
  http.end();
}

// --- REUSABLE MAP LOADER ---
void loadGeoFile(const char* filename, std::vector<GeoLine>& targetVector, const char* label) {
  // SERIAL_SAFE Serial.printf("\n[%s] Sweeping Flash for %s...\n", label, filename);
  targetVector.clear();

  File file = LittleFS.open(filename, "r");
  if (!file) {
    SERIAL_SAFE Serial.printf("[ERROR] Failed to open %s.\n", filename);
    return;
  }

  latOffset = radarRangeMiles / 69.0;
  lonOffset = radarRangeMiles / (69.0 * cos(homeLat * PI / 180.0));
  
  float boundsLatMin = homeLat - latOffset;
  float boundsLatMax = homeLat + latOffset;
  float boundsLonMin = homeLon - lonOffset;
  float boundsLonMax = homeLon + lonOffset;

  float buffer[4]; 
  
  while (file.available() >= 16) {
    file.read((uint8_t*)buffer, 16);
    
    bool p1_in = (buffer[0] >= boundsLatMin && buffer[0] <= boundsLatMax && buffer[1] >= boundsLonMin && buffer[1] <= boundsLonMax);
    bool p2_in = (buffer[2] >= boundsLatMin && buffer[2] <= boundsLatMax && buffer[3] >= boundsLonMin && buffer[3] <= boundsLonMax);

    if (p1_in || p2_in) {
      GeoLine line;
      line.lat1 = buffer[0]; line.lon1 = buffer[1];
      line.lat2 = buffer[2]; line.lon2 = buffer[3];
      targetVector.push_back(line);
    }
  }
  file.close();
}

void fetchLocalRunways() {
  lastRunwayAttempt = millis();
  SERIAL_SAFE Serial.println("\n[MAP] Fetching local runways from OpenStreetMap...");
  
  // Create a 50-mile bounding box around the user's home location
  latOffset = radarRangeMiles / 69.0;
  lonOffset = radarRangeMiles / (69.0 * cos(homeLat * PI / 180.0));
  
  String query = "[out:json];way[\"aeroway\"=\"runway\"][\"ref\"][\"area\"!=\"yes\"](" + 
                 String(homeLat - latOffset, 4) + "," + String(homeLon - lonOffset, 4) + "," + 
                 String(homeLat + latOffset, 4) + "," + String(homeLon + lonOffset, 4) + ");out geom;";

  HTTPClient http;
  http.begin("http://overpass-api.de/api/interpreter?data=" + urlEncode(query));
  
  if (http.GET() == HTTP_CODE_OK) {
    PsramJsonDocument mapDoc(256000); 
    deserializeJson(mapDoc, http.getString());
    
    localRunways.clear();
    
    for (JsonObject element : mapDoc["elements"].as<JsonArray>()) {
      JsonArray geom = element["geometry"];
      
      // FIX: Ensure geometry exists and has at least 2 points to prevent math underflow!
      if (!geom.isNull() && geom.size() >= 2) {
        for (size_t i = 0; i < geom.size() - 1; i++) {
          GeoLine line;
          line.lat1 = geom[i]["lat"]; line.lon1 = geom[i]["lon"];
          line.lat2 = geom[i+1]["lat"]; line.lon2 = geom[i+1]["lon"];
          localRunways.push_back(line);
        }
      }
    }
    SERIAL_SAFE Serial.printf("[MAP] Success! Loaded %d runway segments.\n", localRunways.size());
    runwaysLoaded = true;
  } else {
    SERIAL_SAFE Serial.println("[MAP] Failed to fetch runways. Ensure internet connection.");
  }
  http.end();

  // loadGeoFile("/map.dat", localCoastlines, "COAST");
  // loadGeoFile("/states.dat", localStates, "STATE");
}

void loadMapFromFS() {
  SERIAL_SAFE Serial.println("[MAP] Sweeping Internal Flash for local coastlines...");
  localCoastlines.clear();

  File file = LittleFS.open("/map.dat", "r");
  if (!file) {
    SERIAL_SAFE Serial.println("[MAP] Failed to open map.dat in internal memory.");
    return;
  }

  float boundsLatMin = homeLat - latOffset;
  float boundsLatMax = homeLat + latOffset;
  float boundsLonMin = homeLon - lonOffset;
  float boundsLonMax = homeLon + lonOffset;

  float buffer[4]; // Array to hold: lat1, lon1, lat2, lon2
  
  while (file.available() >= 16) {
    file.read((uint8_t*)buffer, 16);
    
    bool p1_in = (buffer[0] >= boundsLatMin && buffer[0] <= boundsLatMax && buffer[1] >= boundsLonMin && buffer[1] <= boundsLonMax);
    bool p2_in = (buffer[2] >= boundsLatMin && buffer[2] <= boundsLatMax && buffer[3] >= boundsLonMin && buffer[3] <= boundsLonMax);

    if (p1_in || p2_in) {
      GeoLine line;
      line.lat1 = buffer[0]; line.lon1 = buffer[1];
      line.lat2 = buffer[2]; line.lon2 = buffer[3];
      localCoastlines.push_back(line);
    }
  }
  
  file.close();
  SERIAL_SAFE Serial.printf("[MAP] Flash sweep complete. Loaded %d background segments.\n", localCoastlines.size());
}

void apiTask(void * parameter) {
  for(;;) {
    if (!isAPMode && WiFi.status() == WL_CONNECTED && homeLat != 0.0) {

      if (!runwaysLoaded && (millis() - lastRunwayAttempt > 60000)) {
          SERIAL_SAFE Serial.println("\n[MAP] Attempting background runway fetch...");
          fetchLocalRunways();
          loadMapFromFS();
      }
      
      if (osUser != "" && osPass != "") {
        if (bearerToken == "" || millis() > tokenExpiresAt) {
          SERIAL_SAFE Serial.println("\n[AUTH] Requesting new OAuth2 Token from OpenSky...");
          
          HTTPClient tokenHttp;
          WiFiClientSecure tokenClient; tokenClient.setInsecure();
          tokenHttp.begin(tokenClient, "https://auth.opensky-network.org/auth/realms/opensky-network/protocol/openid-connect/token");
          tokenHttp.addHeader("Content-Type", "application/x-www-form-urlencoded");
          
          String tokenPayload = "grant_type=client_credentials&client_id=" + osUser + "&client_secret=" + osPass;
          int tokenHttpCode = tokenHttp.POST(tokenPayload);
          
          if (tokenHttpCode == HTTP_CODE_OK) {
             JsonDocument tDoc;
             deserializeJson(tDoc, tokenHttp.getString());
             bearerToken = tDoc["access_token"].as<String>();
             tokenExpiresAt = millis() + (tDoc["expires_in"].as<int>() * 1000) - 5000;
             apiStatusMsg = "Authenticated (OAuth2 Active)"; apiStatusColor = "#28a745"; 
             SERIAL_SAFE Serial.println("[AUTH] Success! Token acquired.");
          } else {
             bearerToken = "";
             apiStatusMsg = "OAuth2 Auth Failed (Check ID/Secret)"; apiStatusColor = "#dc3545"; 
             SERIAL_SAFE Serial.println("[AUTH] Failed to get token. Check your API Keys.");
          }
          tokenHttp.end();
        }
      }

      latOffset = radarRangeMiles / 69.0;
      lonOffset = radarRangeMiles / (69.0 * cos(homeLat * PI / 180.0));
      float lamin = homeLat - latOffset; float lamax = homeLat + latOffset;
      float lomin = homeLon - lonOffset; float lomax = homeLon + lonOffset;
      
      float boxWidthDegrees = lonOffset * 2.0;
      float boxHeightDegrees = latOffset * 2.0;
      float sqDegrees = boxWidthDegrees * boxHeightDegrees;
      
      int creditCost = 1;
      if (sqDegrees > 400.0) creditCost = 4;
      else if (sqDegrees > 100.0) creditCost = 3;
      else if (sqDegrees > 25.0) creditCost = 2;
      
      // currentPollIntervalMs = (creditCost * 22) * 1000UL;
      // currentPollIntervalMs = (creditCost * 10) * 1000UL;
      currentPollIntervalMs = (creditCost * currentBaseInterval) * 1000UL;

      String url = "https://opensky-network.org/api/states/all?lamin=" + String(lamin, 4) + "&lamax=" + String(lamax, 4) + "&lomin=" + String(lomin, 4) + "&lomax=" + String(lomax, 4);

      SERIAL_SAFE Serial.println("\n--- [API] Polling OpenSky ---");
      Serial.print("Target URL: "); SERIAL_SAFE Serial.println(url);
      SERIAL_SAFE Serial.printf("Geographic Area: %.2f sq degrees | Cost: %d credits\n", sqDegrees, creditCost);
      SERIAL_SAFE Serial.printf("Dynamic Sleep Timer: %lu seconds\n", currentPollIntervalMs / 1000);
      SERIAL_SAFE Serial.println("-----------------------------");

      WiFiClientSecure client; client.setInsecure(); 
      HTTPClient http; http.begin(client, url);
      http.addHeader("User-Agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) Chrome/120.0.0.0 Safari/537.36");
      if (bearerToken != "") { http.addHeader("Authorization", "Bearer " + bearerToken); }

      const char* headerKeys[] = {"X-Rate-Limit-Remaining"};
      http.collectHeaders(headerKeys, 1);

      int httpCode = http.GET();
      
      if (httpCode == HTTP_CODE_OK) {
        if (http.hasHeader("X-Rate-Limit-Remaining")) {
          int creditsLeft = http.header("X-Rate-Limit-Remaining").toInt();
          SERIAL_SAFE Serial.printf("\n[API] OpenSky Credits Remaining Today: %d\n", creditsLeft);

         if (creditsLeft > 3000) {
            currentBaseInterval = 8;  // Hyper-fast (Plenty of credits)
          } else if (creditsLeft > 1500) {
            currentBaseInterval = 12; // Fast
          } else if (creditsLeft > 500) {
            currentBaseInterval = 22; // Standard
          } else {
            currentBaseInterval = 60; // Survival mode (Avoid the 429 ban!)
          }
          
          // Apply it immediately so this specific loop's sleep timer is accurate
          currentPollIntervalMs = (creditCost * currentBaseInterval) * 1000UL;
          SERIAL_SAFE Serial.printf("[API] Next sleep interval dynamically adjusted to: %lu seconds\n", currentPollIntervalMs / 1000);
        }

        String payload = http.getString();
        PsramJsonDocument doc(512000); 
        DeserializationError error = deserializeJson(doc, payload);

        if (!error) {
          std::vector<Aircraft> tempPlanes;
          for (JsonArray state : doc["states"].as<JsonArray>()) {
            float alt_ft = (state[7].isNull() ? 0 : state[7].as<float>()) * 3.28084;
            if (alt_ft < altFloor || alt_ft > altCeiling) continue;
            
            Aircraft p;
            p.callsign = state[1].as<String>(); p.callsign.trim();
            p.lon = state[5].as<float>(); p.lat = state[6].as<float>();
            p.altitude_ft = alt_ft;
            p.heading = state[10].isNull() ? 0 : state[10].as<float>();
            p.speed_knots = (state[9].isNull() ? 0 : state[9].as<float>()) * 1.94384; 
            p.vert_rate = state[11].isNull() ? 0.0 : state[11].as<float>();

            float dx = (p.lon - homeLon) * 69.0 * cos(homeLat * PI / 180.0);
            float dy = (p.lat - homeLat) * 69.0;
            p.px = 120 + (dx / radarRangeMiles) * 120;
            p.py = 120 - (dy / radarRangeMiles) * 120;
            
            p.angle = atan2(p.py - 120, p.px - 120);
            if (p.angle < 0) p.angle += TWO_PI;
            
            float distFromCenter = sqrt(pow(p.px - 120, 2) + pow(p.py - 120, 2));
            if (distFromCenter <= 114) {
              tempPlanes.push_back(p);
            }
          }
          
          xSemaphoreTake(planesMutex, portMAX_DELAY);
          targetPlanes = tempPlanes;
          xSemaphoreGive(planesMutex);
        }
      } else if (httpCode == 401) {
        apiStatusMsg = "401 Unauthorized (Check API Keys)"; apiStatusColor = "#dc3545"; 
      } else if (httpCode == 429) {
        apiStatusMsg = "429 Rate Limited (Too Many Requests)"; apiStatusColor = "#dc3545"; 
      } else {
        apiStatusMsg = "API Error (HTTP " + String(httpCode) + ")"; apiStatusColor = "#dc3545"; 
      }
      http.end();
    }
    // vTaskDelay(pdMS_TO_TICKS(currentPollIntervalMs)); 
    unsigned long startWait = millis();
    while (millis() - startWait < currentPollIntervalMs) {
      if (forceApiUpdate) {
        forceApiUpdate = false; // Reset the flag
        break;                  // Break the loop and immediately fetch new data!
      }
      vTaskDelay(pdMS_TO_TICKS(100)); 
    }
  }
}

void setup() {
  Serial.begin(115200);
  Serial.setTxTimeoutMs(0);

  lcd.init();
  lcd.setBrightness(screenBrightness);
  sprite.createSprite(240, 240);

  // --- Initialize Internal Flash Memory ---
  if (!LittleFS.begin(true)) {
    SERIAL_SAFE Serial.println("[FS] ERROR: LittleFS Mount Failed!");
  } else {
    SERIAL_SAFE Serial.println("[FS] Internal Flash Memory Mounted Successfully!");
  }

  planesMutex = xSemaphoreCreateMutex();

  preferences.begin("radar-config", false);
  savedSSID = preferences.getString("ssid", ""); savedPASS = preferences.getString("pass", "");
  osUser = preferences.getString("os_user", ""); osPass = preferences.getString("os_pass", "");
  homeLat = preferences.getFloat("lat", 0.0); homeLon = preferences.getFloat("lon", 0.0);
  radarRangeMiles = preferences.getFloat("range", 25.0); filterCallsign = preferences.getString("filter", "");
  altFloor = preferences.getInt("floor", 0); altCeiling = preferences.getInt("ceil", 40000);

  if (savedSSID == "") {
    isAPMode = true;
    WiFi.softAP("FlightRadar-Setup");
    dnsServer.start(53, "*", WiFi.softAPIP());
    if (MDNS.begin("radar")) { MDNS.addService("http", "tcp", 80); }
    server.on("/", handleRoot); server.on("/save", handleSave);
    server.onNotFound([]() { server.sendHeader("Location", "http://192.168.4.1/", true); server.send(302, "text/plain", ""); });
    server.begin();
  } else {
    WiFi.begin(savedSSID.c_str(), savedPASS.c_str());
    int attempts = 0;
    while (WiFi.status() != WL_CONNECTED && attempts < 20) { delay(500); attempts++; }

    if (WiFi.status() == WL_CONNECTED) {
      SERIAL_SAFE Serial.println("\n[NETWORK] WiFi Connected Successfully!");
      Serial.print("[NETWORK] IP Address: "); SERIAL_SAFE Serial.println(WiFi.localIP());
      
      if (MDNS.begin("radar")) { 
        MDNS.addService("http", "tcp", 80); 
        SERIAL_SAFE Serial.println("[NETWORK] Web Portal Active: http://radar.local\n");
      }
      
      server.on("/", handleRoot); server.on("/save", handleSave);
      server.begin();
      
      // fetchLocationFromIP();
      // if (homeLat != 0.0) {
      //   fetchLocalRunways(); // Fetch the dynamic runway maps on boot!
      // }
      if (homeLat == 0.0 && homeLon == 0.0) {
        SERIAL_SAFE Serial.println("[NETWORK] No saved location found. Fetching from IP...");
        fetchLocationFromIP();
      } else {
        SERIAL_SAFE Serial.printf("[NETWORK] Booting with saved location: %.4f, %.4f\n", homeLat, homeLon);
      }
      
      // Always fetch the runways for whatever location we are currently using
      // if (homeLat != 0.0) {
      //   fetchLocalRunways(); 
      // }
      if (homeLat != 0.0) {
        lastFetchedLat = homeLat;
        lastFetchedLon = homeLon;
        loadGeoFile("/map.dat", localCoastlines, "COAST");
        loadGeoFile("/states.dat", localStates, "STATE");
        fetchLocalRunways();
      }
      
      xTaskCreatePinnedToCore(apiTask, "apiTask", 20000, NULL, 1, NULL, 0); 
    } else {
      isAPMode = true;
      WiFi.softAP("FlightRadar-Setup");
      dnsServer.start(53, "*", WiFi.softAPIP());
      if (MDNS.begin("radar")) { MDNS.addService("http", "tcp", 80); }
      server.on("/", handleRoot); server.on("/save", handleSave);
      server.onNotFound([]() { server.sendHeader("Location", "http://192.168.4.1/", true); server.send(302, "text/plain", ""); });
      server.begin();
    }
  }
}

void loop() {
  if (isAPMode) dnsServer.processNextRequest();
  server.handleClient();

  // --- UNIFIED SWIPE & TAP GESTURE ENGINE (WITH DEBUGGING) ---
  static bool isDragging = false;
  static int16_t startX = 0, startY = 0;
  static int16_t lastX = 0, lastY = 0;
  static unsigned long touchStartTime = 0; 
  
  uint16_t touchX, touchY;
  bool currentTouch = lcd.getTouch(&touchX, &touchY);

  if (currentTouch && !isDragging) {
    // 1. FINGER DOWN: Record the start
    startX = touchX;
    startY = touchY;
    lastX = touchX;
    lastY = touchY;
    touchStartTime = millis(); 
    isDragging = true;
    
    // SERIAL_SAFE Serial.printf("\n[TOUCH DOWN] Started at X:%d Y:%d\n", startX, startY);
  } 
  else if (currentTouch && isDragging) {
    // 2. FINGER MOVING: Update last known position
    // (Only update if the values are realistic, ignoring sudden 0,0 drops upon lift)
    if (touchX > 0 && touchY > 0) {
      lastX = touchX;
      lastY = touchY;
    }
  } 
  else if (!currentTouch && isDragging) {
    // 3. FINGER LIFTED: Evaluate the path
    isDragging = false;
    unsigned long touchDuration = millis() - touchStartTime;

    // Calculate the distance from the center (120, 120)
    float startDist = sqrt(pow(startX - 120, 2) + pow(startY - 120, 2));
    float endDist = sqrt(pow(lastX - 120, 2) + pow(lastY - 120, 2));
    float distChange = endDist - startDist;

    // Print the raw diagnostic math!
    // SERIAL_SAFE Serial.printf("[TOUCH UP] Lifted at X:%d Y:%d. Duration: %lu ms\n", lastX, lastY, touchDuration);
    // SERIAL_SAFE Serial.printf("[MATH] startDist: %.1f | endDist: %.1f | distChange: %.1f\n", startDist, endDist, distChange);

    // --- GESTURE 1: RADIAL SWIPE (Threshold 15 pixels) ---
    if (abs(distChange) > 15) { 
      // SERIAL_SAFE Serial.println("[GESTURE] ➡️ Valid Swipe Detected!");
      
      if (distChange > 0) {
        // SERIAL_SAFE Serial.println("[ACTION] Swiped OUTWARD -> ZOOMING IN");
        // Decrease by 5, with a hard floor of 5 miles
        if (radarRangeMiles > 5.0) {
          radarRangeMiles -= 5.0;
        }
      } 
      else {
        // SERIAL_SAFE Serial.println("[ACTION] Swiped INWARD -> ZOOMING OUT");
        // Increase by 5, with a hard ceiling of 50 miles
        if (radarRangeMiles < 100.0) {
          radarRangeMiles += 5.0;
        }
      }
      
      // CRITICAL: Instantly update the geographic bounding box. 
      // 1. Existing planes will immediately snap to the correct screen scale.
      // 2. The next OpenSky API fetch will automatically use these new bounds!
      latOffset = radarRangeMiles / 69.0; // 1 deg Lat is ~69 miles
      lonOffset = radarRangeMiles / (69.0 * cos(homeLat * PI / 180.0)); // Adjust for Earth's curvature

      SERIAL_SAFE Serial.printf("[UPDATE] New Radar Range is now: %.1f Miles\n", radarRangeMiles);
      
      loadGeoFile("/map.dat", localCoastlines, "COAST");
      loadGeoFile("/states.dat", localStates, "STATE");

      // --- NEW: INSTANT PLANE RESCALE (DUAL ARRAY) ---
      float pixelsPerMile = 120.0 / radarRangeMiles; 
      
      // CRITICAL: Lock the memory so we can safely overwrite the background holding tank!
      xSemaphoreTake(planesMutex, portMAX_DELAY);
      
      // 1. Update the VISIBLE planes (Fixes Classic Mode)
      for (size_t i = 0; i < activePlanes.size(); i++) {
         float deltaLat = activePlanes[i].lat - homeLat;
         float deltaLon = activePlanes[i].lon - homeLon;
         
         activePlanes[i].px = 120 + ((deltaLon * (69.0 * cos(homeLat * PI / 180.0))) * pixelsPerMile);
         activePlanes[i].py = 120 - ((deltaLat * 69.0) * pixelsPerMile); 
         
         activePlanes[i].angle = atan2(activePlanes[i].py - 120, activePlanes[i].px - 120);
         if (activePlanes[i].angle < 0) activePlanes[i].angle += TWO_PI;
      }
      
      // 2. Update the HIDDEN planes (Fixes Modern Mode overwrites!)
      for (size_t i = 0; i < targetPlanes.size(); i++) {
         float deltaLat = targetPlanes[i].lat - homeLat;
         float deltaLon = targetPlanes[i].lon - homeLon;
         
         targetPlanes[i].px = 120 + ((deltaLon * (69.0 * cos(homeLat * PI / 180.0))) * pixelsPerMile);
         targetPlanes[i].py = 120 - ((deltaLat * 69.0) * pixelsPerMile); 
         
         targetPlanes[i].angle = atan2(targetPlanes[i].py - 120, targetPlanes[i].px - 120);
         if (targetPlanes[i].angle < 0) targetPlanes[i].angle += TWO_PI;
      }
      
      xSemaphoreGive(planesMutex); // Unlock the memory

      // Force a screen clear so the next loop draws the new scale instantly
      if (radarMode == 0) sprite.fillScreen(TFT_BLACK);
    }
    // --- GESTURE 2 & 3: STATIONARY TAP ---
    else {
      // SERIAL_SAFE Serial.println("[GESTURE] 🛑 Swipe too short. Treating as Tap.");
      
      if (touchDuration < 500 && !isAPMode) {
        // SERIAL_SAFE Serial.println("[ACTION] SHORT TAP: Swapping View");
        if (showSettingsQR) {
           showSettingsQR = false; 
        } else {
           radarMode = (radarMode == 0) ? 1 : 0; 
        }
        sprite.fillScreen(TFT_BLACK); 
      } 
      else if (touchDuration > 1000 && !isAPMode) {
        // SERIAL_SAFE Serial.println("[ACTION] LONG PRESS: Showing QR Code");
        showSettingsQR = true; 
        sprite.fillScreen(TFT_BLACK);
      }
    }
  }

  // --- Responsive Rendering Block ---
  if (isAPMode) { 
    drawQRCode("WIFI:S:FlightRadar-Setup;T:nopass;;", "Join Setup Network"); 
  } else if (showSettingsQR) { 
    drawQRCode("http://radar.local", "Local Settings"); 
  } else {
    // float prevSweepAngle = sweepAngle;
    // sweepAngle = (millis() % currentPollIntervalMs) / (float)currentPollIntervalMs * TWO_PI;
    static unsigned long lastFrameTime = millis();
    unsigned long currentMillis = millis();
    unsigned long deltaTime = currentMillis - lastFrameTime;
    lastFrameTime = currentMillis;

    float prevSweepAngle = sweepAngle;
    
    // Calculate how much the arm should advance this exact frame
    float deltaAngle = ((float)deltaTime / (float)currentPollIntervalMs) * TWO_PI;
    sweepAngle += deltaAngle;
    if (sweepAngle >= TWO_PI) {
        sweepAngle -= TWO_PI;
    }

    // --- Sweep vs. Instant Rendering Logic ---
    xSemaphoreTake(planesMutex, portMAX_DELAY);
    
    if (radarMode == 0) {
      // SWEEP MODE: Only reveal planes when the arm passes over them
      for (const auto& target : targetPlanes) {
        bool justSwept = false;
        if (sweepAngle > prevSweepAngle) {
          if (target.angle >= prevSweepAngle && target.angle <= sweepAngle) justSwept = true;
        } else { 
          if (target.angle >= prevSweepAngle || target.angle <= sweepAngle) justSwept = true;
        }

        if (justSwept) {
          bool found = false;
          for (auto& active : activePlanes) {
            if (active.callsign == target.callsign) {
              active = target; active.lastSeen = millis(); found = true; break;
            }
          }
          if (!found) {
            Aircraft newPlane = target; newPlane.lastSeen = millis();
            activePlanes.push_back(newPlane);
          }
        }
      }
    } else {
      // MODERN MODE: Instantly show all planes grabbed from the API
      activePlanes = targetPlanes;
      for (auto& p : activePlanes) {
        p.lastSeen = millis(); // Keep them fresh so they don't fade out
      }
    }
    
    xSemaphoreGive(planesMutex);

    // activePlanes.erase(std::remove_if(activePlanes.begin(), activePlanes.end(),
    //   [](const Aircraft& a) { return millis() - a.lastSeen > 30000; }), activePlanes.end());
    activePlanes.erase(std::remove_if(activePlanes.begin(), activePlanes.end(),
      [](const Aircraft& a) { return millis() - a.lastSeen > (currentPollIntervalMs + 5000); }), activePlanes.end());

      // --- PRINT VISIBLE PLANE COUNT (Every 5 seconds) ---
  static unsigned long lastCountPrint = 0;
  if (millis() - lastCountPrint > 5000) { 
    lastCountPrint = millis();
    Serial.print("[RADAR] Mode: ");
    Serial.print(radarMode == 0 ? "Sweep | Fading planes on screen: " : "Modern | Showing all planes: ");
    SERIAL_SAFE Serial.println(activePlanes.size());
  }
    sprite.fillScreen(TFT_BLACK);

    if (radarMode == 0) {
      // --- THE SWEEP ARM ---
      int endX = 120 + 120 * cos(sweepAngle); 
      int endY = 120 + 120 * sin(sweepAngle);
      sprite.drawLine(120, 120, endX, endY, TFT_GREEN);
      
      // for (const auto& p : activePlanes) {
      //   float angleDiff = sweepAngle - p.angle;
      //   if (angleDiff < 0) angleDiff += TWO_PI;
        
      //   uint8_t brightness = 255 - (angleDiff / TWO_PI) * 200; 
      //   // uint8_t brightness = 255 - (angleDiff / TWO_PI) * 240; 
      //   uint16_t color = (filterCallsign != "" && p.callsign.equalsIgnoreCase(filterCallsign)) 
      //                    ? sprite.color565(brightness, 0, 0) 
      //                    : sprite.color565(0, brightness, 0);
      //   sprite.fillCircle(p.px, p.py, 3, color);
      // }
      for (const auto& p : activePlanes) {
        float angleDiff = sweepAngle - p.angle;
        if (angleDiff < 0) angleDiff += TWO_PI;
        
        // FADE FIX: Multiply by 255.0 to force the tail to fade completely to 0 (pure black)
        // Note: If you want the tail to be shorter, increase 255.0 to something like 350.0.
        float fadeAmount = (angleDiff / TWO_PI) * 255.0;
        uint8_t brightness = (fadeAmount >= 255.0) ? 0 : (255 - (uint8_t)fadeAmount);
        
        uint16_t color = (filterCallsign != "" && p.callsign.equalsIgnoreCase(filterCallsign)) 
                         ? sprite.color565(brightness, 0, 0) 
                         : sprite.color565(0, brightness, 0);
                         
        sprite.fillCircle(p.px, p.py, 3, color);
      }

      // --- FIXED 10-MILE DISTANCE RINGS & LABELS ---
    int rangeInt = (int)radarRangeMiles;
    int ringStep = 10; 

    // Determine the color based on the current view mode
    uint16_t ringColor = (radarMode == 0) ? TFT_DARKGREEN : TFT_DARKGREY;
    
    // Set text alignment so the text draws to the right of the given coordinate
    sprite.setTextDatum(middle_left);

    // Draw the rings and the text labels running West (left of center)
    for (int r = ringStep; r <= rangeInt; r += ringStep) {
      int pixelRadius = (r / radarRangeMiles) * 120;
      if (pixelRadius > 119) pixelRadius = 119; // Keep on screen
      
      sprite.drawCircle(120, 120, pixelRadius, ringColor);
      
      // Position text just inside the left edge of the ring
      int textX = 120 - pixelRadius + 2; 
      sprite.setTextColor(ringColor);
      sprite.drawString(String(r), textX, 120);
    }
    } else {
      // --- FIXED 10-MILE DISTANCE RINGS & LABELS ---
    int rangeInt = (int)radarRangeMiles;
    int ringStep = 10; 

    // Determine the color based on the current view mode
    uint16_t ringColor = (radarMode == 0) ? TFT_DARKGREEN : TFT_DARKGREY;
    
    // Set text alignment so the text draws to the right of the given coordinate
    sprite.setTextDatum(middle_left);

    // Draw the rings and the text labels running West (left of center)
    for (int r = ringStep; r <= rangeInt; r += ringStep) {
      int pixelRadius = (r / radarRangeMiles) * 120;
      if (pixelRadius > 119) pixelRadius = 119; // Keep on screen
      
      sprite.drawCircle(120, 120, pixelRadius, ringColor);
      
      // Position text just inside the left edge of the ring
      int textX = 120 - pixelRadius + 2; 
      sprite.setTextColor(ringColor);
      sprite.drawString(String(r), textX, 120);
    }
      // sprite.drawCircle(120, 120, 40, TFT_DARKGREY);
      // sprite.drawCircle(120, 120, 80, TFT_DARKGREY);
      // sprite.drawCircle(120, 120, 119, TFT_DARKGREY);
      // sprite.setTextDatum(top_left); 
      sprite.setTextDatum(top_left); // Reset text datum for the plane labels

      // --- DRAW BACKGROUND MAPS (Internal Flash) ---
      // 1. States (Muted Slate Blue)
      if (preferences.getBool("showStates", true)) {
        for (const auto& line : localStates) {
          float dx1 = (line.lon1 - homeLon) * 69.0 * cos(homeLat * PI / 180.0);
          float dy1 = (line.lat1 - homeLat) * 69.0;
          int px1 = 120 + (dx1 / radarRangeMiles) * 120;
          int py1 = 120 - (dy1 / radarRangeMiles) * 120;

          float dx2 = (line.lon2 - homeLon) * 69.0 * cos(homeLat * PI / 180.0);
          float dy2 = (line.lat2 - homeLat) * 69.0;
          int px2 = 120 + (dx2 / radarRangeMiles) * 120;
          int py2 = 120 - (dy2 / radarRangeMiles) * 120;

          float dist1 = sqrt(pow(px1 - 120, 2) + pow(py1 - 120, 2));
          float dist2 = sqrt(pow(px2 - 120, 2) + pow(py2 - 120, 2));

          if (dist1 <= 119 || dist2 <= 119) {
            // uint16_t stateColor = sprite.color565(30, 55, 90); 
            uint16_t stateColor = sprite.color565(60, 90, 130);
            // uint16_t stateColor = sprite.color565(70, 110, 150);
            sprite.drawLine(px1, py1, px2, py2, stateColor);
          }
        }
      }

      // 2. Coastlines (Dark Radar Green)
      if (preferences.getBool("showCoast", true)) {
        for (const auto& line : localCoastlines) {
          float dx1 = (line.lon1 - homeLon) * 69.0 * cos(homeLat * PI / 180.0);
          float dy1 = (line.lat1 - homeLat) * 69.0;
          int px1 = 120 + (dx1 / radarRangeMiles) * 120;
          int py1 = 120 - (dy1 / radarRangeMiles) * 120;

          float dx2 = (line.lon2 - homeLon) * 69.0 * cos(homeLat * PI / 180.0);
          float dy2 = (line.lat2 - homeLat) * 69.0;
          int px2 = 120 + (dx2 / radarRangeMiles) * 120;
          int py2 = 120 - (dy2 / radarRangeMiles) * 120;

          float dist1 = sqrt(pow(px1 - 120, 2) + pow(py1 - 120, 2));
          float dist2 = sqrt(pow(px2 - 120, 2) + pow(py2 - 120, 2));

          if (dist1 <= 119 || dist2 <= 119) {
            // uint16_t coastColor = sprite.color565(0, 80, 0); 
            // uint16_t coastColor = sprite.color565(40, 140, 40);
            uint16_t coastColor = sprite.color565(0, 150, 0);
            sprite.drawLine(px1, py1, px2, py2, coastColor);
          }
        }
      }

      // --- DRAW VIDEO MAP (Dynamic OpenStreetMap Runways) ---
      for (const auto& line : localRunways) {
        float dx1 = (line.lon1 - homeLon) * 69.0 * cos(homeLat * PI / 180.0);
        float dy1 = (line.lat1 - homeLat) * 69.0;
        int px1 = 120 + (dx1 / radarRangeMiles) * 120;
        int py1 = 120 - (dy1 / radarRangeMiles) * 120;

        float dx2 = (line.lon2 - homeLon) * 69.0 * cos(homeLat * PI / 180.0);
        float dy2 = (line.lat2 - homeLat) * 69.0;
        int px2 = 120 + (dx2 / radarRangeMiles) * 120;
        int py2 = 120 - (dy2 / radarRangeMiles) * 120;

        float dist1 = sqrt(pow(px1 - 120, 2) + pow(py1 - 120, 2));
        float dist2 = sqrt(pow(px2 - 120, 2) + pow(py2 - 120, 2));
        
        if (dist1 <= 119 || dist2 <= 119) {
          // uint16_t mapColor = sprite.color565(40, 40, 60); 
          uint16_t mapColor = sprite.color565(255, 180, 50);
          sprite.drawLine(px1, py1, px2, py2, mapColor);
        }
      }

      // --- SPATIAL DECONFLICTION ENGINE (Greedy Optimization) ---
      
      // 1. Define a temporary struct to hold our "Render Plan"
      struct RenderJob {
        Aircraft p;
        uint16_t color;
        BoundingBox box;
        int lx1, ly1, barTopY, textStartX;
        bool showText;
      };
      
      std::vector<RenderJob> jobs;
      std::vector<BoundingBox> occupiedSpace;

      // 2. PHASE 1: Draft the Plan (Try to place everything in its best quadrant)
      for (const auto& p : activePlanes) {
        uint16_t color = (filterCallsign != "" && p.callsign.equalsIgnoreCase(filterCallsign)) ? TFT_RED : TFT_GREENYELLOW;
        int anchors[4][4] = { {6, -6, 1, -1}, {6, 6, 1, 1}, {-6, 6, -1, 1}, {-6, -6, -1, -1} };

        int lx1, ly1, barTopY, textStartX;
        BoundingBox bestBox;

        for (int i = 0; i < 4; i++) {
          lx1 = p.px + anchors[i][0];
          ly1 = p.py + anchors[i][1];
          barTopY = (anchors[i][3] == -1) ? (ly1 - 24) : (ly1 + 2);
          textStartX = (anchors[i][2] == 1) ? (lx1 + 3) : (lx1 - 40);
          bestBox = { textStartX, barTopY, 40, 25 };

          if (!isOverlapping(bestBox, occupiedSpace)) {
            break; // We found a clean quadrant!
          }
        }

        // Even if it overlaps, save it to the plan. We will optimize it next.
        occupiedSpace.push_back(bestBox);
        jobs.push_back({p, color, bestBox, lx1, ly1, barTopY, textStartX, true});
      }

      // 3. PHASE 2: The Greedy Optimization Loop
      bool overlapsExist = true;
      while (overlapsExist) {
        int maxOverlaps = 0;
        int worstIndex = -1;

        // Count how many times each visible box touches another visible box
        for (size_t i = 0; i < jobs.size(); i++) {
          if (!jobs[i].showText) continue; 
          
          int currentOverlaps = 0;
          for (size_t j = 0; j < jobs.size(); j++) {
            if (i == j || !jobs[j].showText) continue; 
            if (isOverlapping(jobs[i].box, jobs[j].box)) {
              currentOverlaps++;
            }
          }
          
          // Keep track of the absolute worst offender
          if (currentOverlaps > maxOverlaps) {
            maxOverlaps = currentOverlaps;
            worstIndex = i;
          }
        }

        // If the worst offender has 0 overlaps, the screen is perfectly clean!
        if (maxOverlaps == 0) {
          overlapsExist = false; 
        } else {
          // Otherwise, hide the worst offender and run the loop again
          jobs[worstIndex].showText = false; 
        }
      }

      // 4. PHASE 3: Execute the Rendering Plan
      // --- EASY TWEAK SETTING ---
      // If the total number of planes on screen hits this number, hide ALL text to prevent clutter.
      const int CLUTTER_THRESHOLD = 25; 
      
      // Evaluate this once before the loop starts
      bool renderText = (activePlanes.size() < CLUTTER_THRESHOLD);

      for (const auto& job : jobs) {
        // ALWAYS draw the physical radar blip and heading vector (Extremely fast geometry)
        sprite.fillCircle(job.p.px, job.p.py, 3, job.color);
        float headingRad = (job.p.heading - 90) * PI / 180.0;
        int headX = job.p.px + 10 * cos(headingRad);
        int headY = job.p.py + 10 * sin(headingRad);
        sprite.drawLine(job.p.px, job.p.py, headX, headY, job.color);

        // ONLY draw the leader line and text if we are under the threshold AND it survived optimization
        if (renderText && job.showText) {
          
          // Draw the routing leader line
          sprite.drawLine(job.p.px, job.p.py, job.lx1, job.ly1, job.color);
          if (job.barTopY < job.ly1) {
            sprite.drawLine(job.lx1, job.ly1, job.lx1, job.barTopY, job.color);
          } else {
            sprite.drawLine(job.lx1, job.ly1, job.lx1, job.barTopY + 22, job.color);
          }
          
          // Set text color
          sprite.setTextColor(job.color, TFT_BLACK);

          // 1. Draw Callsign
          sprite.drawString(job.p.callsign, job.textStartX, job.barTopY - 2);
          
          // 2. Draw ATC Altitude
          char altBuf[8];
          sprintf(altBuf, "%03d", (int)(job.p.altitude_ft / 100));
          String altStr = String(altBuf); 
          sprite.drawString(altStr, job.textStartX, job.barTopY + 7);
          
          // 3. Draw Custom Trend Arrows
          int arrowX = job.textStartX + sprite.textWidth(altStr) + 3;
          int arrowY = job.barTopY + 7 + 4; 
          if (job.p.vert_rate > 2.0) {
              sprite.drawLine(arrowX, arrowY + 3, arrowX, arrowY - 3, job.color);     
              sprite.drawLine(arrowX, arrowY - 3, arrowX - 2, arrowY - 1, job.color); 
              sprite.drawLine(arrowX, arrowY - 3, arrowX + 2, arrowY - 1, job.color); 
          } else if (job.p.vert_rate < -2.0) {
              sprite.drawLine(arrowX, arrowY - 3, arrowX, arrowY + 3, job.color);     
              sprite.drawLine(arrowX, arrowY + 3, arrowX - 2, arrowY + 1, job.color); 
              sprite.drawLine(arrowX, arrowY + 3, arrowX + 2, arrowY + 1, job.color); 
          }

          // 4. Draw Speed
          char spdStr[10];
          sprintf(spdStr, "%d", (int)job.p.speed_knots);
          sprite.drawString(spdStr, job.textStartX, job.barTopY + 16);
        }
      }
    }
  }
  
  sprite.pushSprite(0, 0);
  delay(15); 
}
// --- END OF FILE ---