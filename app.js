/**
 * AirBridge - Client Logic
 * Handles P2P WebRTC audio, MQTT-based signaling & auto-discovery,
 * audio analysis, and reactive UI view states.
 */

// --- CONFIGURATION & CONSTANTS ---
const MQTT_BROKER = "wss://broker.hivemq.com:8884/mqtt";
const APP_NAMESPACE = "airbridge_app_v1";
const DISCOVERY_INTERVAL = 5000; // Publish presence every 5 seconds
const PRESENCE_TIMEOUT = 15000;  // Remove devices older than 15 seconds

const RTC_CONFIG = {
  iceServers: [
    { urls: "stun:stun.l.google.com:19302" },
    { urls: "stun:stun1.l.google.com:19302" },
    { urls: "stun:stun2.l.google.com:19302" }
  ],
  iceCandidatePoolSize: 10
};

// --- APP STATE ---
let myClientId = "ab_" + Math.random().toString(36).substring(2, 11);
let myDeviceName = "";
let myDeviceType = "desktop";
let myPublicIP = "";
let myLanToken = ""; // SHA-256 of public IP for local network isolation

let mqttClient = null;
let peerConnection = null;
let localStream = null;
let remoteStream = null;
let audioElements = []; // Store dynamically created audio elements for cleanup

// Session State
let activeSessionPartnerId = null;
let activeSessionPartnerName = null;
let sessionRole = null;          // "sender" (streaming out) or "receiver" (playing back)
let sessionRoleDetail = null;    // "mic" or "speaker" (from local perspective)
let isInitiator = false;
let roomCode = null;             // Active WAN Room Code
let connectionTimeoutId = null;
let sessionStartTime = null;
let sessionTimerInterval = null;

// Recording & WebRTC stability states
let iceCandidatesQueue = [];
let mediaRecorder = null;
let recordedChunks = [];
let recordingStartTime = null;
let recordingTimerInterval = null;

// Audio Visualization
let audioCtx = null;
let analyser = null;
let dataArray = null;
let animationFrameId = null;

// Peer Discovery
let discoveredDevices = new Map();
let currentTargetDevice = null;  // Device we are currently trying to connect to

// Settings
let settings = {
  displayName: "",
  echoCancel: true,
  noiseSuppress: true,
  gainControl: true,
  micDeviceId: "default"
};

// --- DOM ELEMENTS ---
const elements = {
  statusDot: document.getElementById("status-dot"),
  statusText: document.getElementById("status-text"),
  
  // Views
  viewDiscovery: document.getElementById("view-discovery"),
  viewRoleSelection: document.getElementById("view-role-selection"),
  viewSession: document.getElementById("view-session"),
  viewSettings: document.getElementById("view-settings"),
  
  // Buttons
  btnOpenSettings: document.getElementById("btn-open-settings"),
  btnCreateRoom: document.getElementById("btn-create-room"),
  btnJoinRoom: document.getElementById("btn-join-room"),
  btnCopyCode: document.getElementById("btn-copy-code"),
  btnCancelRole: document.getElementById("btn-cancel-role"),
  btnSessionMute: document.getElementById("btn-session-mute"),
  btnSessionDisconnect: document.getElementById("btn-session-disconnect"),
  btnSaveSettings: document.getElementById("btn-save-settings"),
  
  // Inputs & Displays
  currentDeviceNameDisplay: document.getElementById("current-device-name-display"),
  deviceList: document.getElementById("device-list"),
  roomCodeDisplayWrapper: document.getElementById("room-code-display-wrapper"),
  roomCodeText: document.getElementById("room-code-text"),
  inputRoomCode: document.getElementById("input-room-code"),
  targetDeviceNameDisplay: document.getElementById("target-device-name-display"),
  sessionPartnerName: document.getElementById("session-partner-name"),
  sessionTimer: document.getElementById("session-timer"),
  sessionModeBadge: document.getElementById("session-mode-badge"),
  
  // Settings Panel
  inputDisplayName: document.getElementById("input-display-name"),
  selectAudioInput: document.getElementById("select-audio-input"),
  checkboxNoiseSuppress: document.getElementById("checkbox-noise-suppress"),
  checkboxEchoCancel: document.getElementById("checkbox-echo-cancel"),
  checkboxGainControl: document.getElementById("checkbox-gain-control"),
  
  // Role cards
  roleMic: document.getElementById("role-mic"),
  roleSpeaker: document.getElementById("role-speaker"),
  iosUnsupportedTag: document.getElementById("ios-unsupported-tag"),
  
  // VU Meter & Volume
  vuCanvas: document.getElementById("vu-canvas"),
  vuMeterDirectionLabel: document.getElementById("vu-meter-direction-label"),
  vuDbText: document.getElementById("vu-db-text"),
  volumePanel: document.getElementById("volume-panel"),
  sessionVolume: document.getElementById("session-volume"),
  
  toastContainer: document.getElementById("toast-container"),
  iconMuteUnmuted: document.getElementById("icon-mute-unmuted"),
  iconMuteMuted: document.getElementById("icon-mute-muted"),
  
  // Modal Overlay
  connectionModal: document.getElementById("connection-modal"),
  modalTitle: document.getElementById("modal-title"),
  modalMessage: document.getElementById("modal-message"),
  btnModalAccept: document.getElementById("btn-modal-accept"),
  btnModalReject: document.getElementById("btn-modal-reject"),
  
  // Recording controls
  btnRecord: document.getElementById("btn-session-record"),
  iconRecordActive: document.getElementById("icon-record-active"),
  iconRecordInactive: document.getElementById("icon-record-inactive"),
  recordingBadge: document.getElementById("recording-badge"),
  recordingTimer: document.getElementById("recording-timer")
};

// --- INITIALIZATION ---
window.addEventListener("DOMContentLoaded", async () => {
  detectDeviceType();
  loadSettings();
  initUIEvents();
  initCompatibility();
  
  updateStatus("idle", "Connecting signaling...");
  await initDiscoveryToken();
  initMQTT();
  
  // Start cleanup interval for stale discovered devices
  setInterval(cleanupDevices, 3000);
});

// Detect if mobile browser
function detectDeviceType() {
  const ua = navigator.userAgent;
  if (/tablet|ipad|playbook|silk/i.test(ua)) {
    myDeviceType = "tablet";
  } else if (/Mobile|Android|iP(hone|od)|IEMobile|BlackBerry|Kindle|Opera Mini/i.test(ua)) {
    myDeviceType = "mobile";
  } else {
    myDeviceType = "desktop";
  }
}

// Generate fallback or check device details
function initCompatibility() {
  const isIOS = /iPad|iPhone|iPod/.test(navigator.userAgent) && !window.MSStream;
  // If iOS Safari, warn that system audio sharing isn't supported, only mic
  if (isIOS) {
    elements.iosUnsupportedTag.classList.remove("hidden");
  }
  
  // Request mic permissions early to populate settings dropdown
  navigator.mediaDevices.enumerateDevices()
    .then(devices => {
      populateMicrophoneList(devices);
    })
    .catch(() => {
      showToast("Allow mic permission in settings to see available devices.", "error");
    });
}

function populateMicrophoneList(devices) {
  elements.selectAudioInput.innerHTML = "";
  const audioInputs = devices.filter(device => device.kind === 'audioinput');
  
  if (audioInputs.length === 0) {
    const opt = document.createElement("option");
    opt.value = "default";
    opt.text = "Default System Mic";
    elements.selectAudioInput.appendChild(opt);
    return;
  }

  audioInputs.forEach((device, index) => {
    const opt = document.createElement("option");
    opt.value = device.deviceId;
    opt.text = device.label || `Microphone ${index + 1}`;
    if (settings.micDeviceId === device.deviceId) {
      opt.selected = true;
    }
    elements.selectAudioInput.appendChild(opt);
  });
}

// Compute hash of IP address for local subnet auto-discovery
async function initDiscoveryToken() {
  try {
    const res = await fetch("https://api.ipify.org?format=json");
    const data = await res.json();
    myPublicIP = data.ip;
    
    // Hash IP address
    const msgBuffer = new TextEncoder().encode(myPublicIP);
    const hashBuffer = await crypto.subtle.digest("SHA-256", msgBuffer);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    myLanToken = hashArray.map(b => b.toString(16).padStart(2, "0")).join("");
  } catch (err) {
    console.warn("Public IP fetch failed, local auto-discovery fallback active.", err);
    myLanToken = "local_subnet_fallback";
  }
}

// Load and populate settings
function loadSettings() {
  const saved = localStorage.getItem("airbridge_settings");
  if (saved) {
    try {
      settings = JSON.parse(saved);
    } catch (e) {
      console.error("Failed to parse saved settings", e);
    }
  }
  
  // Generate random default name if none exists
  if (!settings.displayName) {
    const randomSuffix = Math.floor(100 + Math.random() * 900);
    const brand = getBrowserBrand();
    settings.displayName = `${capitalize(myDeviceType)} ${brand} #${randomSuffix}`;
  }
  
  myDeviceName = settings.displayName;
  elements.currentDeviceNameDisplay.textContent = myDeviceName;
  
  // Update form values
  elements.inputDisplayName.value = settings.displayName;
  elements.checkboxEchoCancel.checked = settings.echoCancel;
  elements.checkboxNoiseSuppress.checked = settings.noiseSuppress;
  elements.checkboxGainControl.checked = settings.gainControl;
}

function saveSettings() {
  settings.displayName = elements.inputDisplayName.value.trim() || myDeviceName;
  settings.micDeviceId = elements.selectAudioInput.value;
  settings.echoCancel = elements.checkboxEchoCancel.checked;
  settings.noiseSuppress = elements.checkboxNoiseSuppress.checked;
  settings.gainControl = elements.checkboxGainControl.checked;
  
  localStorage.setItem("airbridge_settings", JSON.stringify(settings));
  myDeviceName = settings.displayName;
  elements.currentDeviceNameDisplay.textContent = myDeviceName;
  
  // If connected to MQTT, re-announce immediately
  announcePresence();
  showToast("Settings saved and applied!", "success");
  switchView("view-discovery");
}

// Helper utilities
function getBrowserBrand() {
  const ua = navigator.userAgent;
  if (ua.indexOf("Chrome") > -1 && ua.indexOf("Edg") === -1) return "Chrome";
  if (ua.indexOf("Safari") > -1 && ua.indexOf("Chrome") === -1) return "Safari";
  if (ua.indexOf("Firefox") > -1) return "Firefox";
  if (ua.indexOf("Edg") > -1) return "Edge";
  return "Browser";
}

function capitalize(s) {
  return s.charAt(0).toUpperCase() + s.slice(1);
}

// --- VIEW NAVIGATION ---
function switchView(viewId) {
  const panels = [elements.viewDiscovery, elements.viewRoleSelection, elements.viewSession, elements.viewSettings];
  panels.forEach(panel => {
    if (panel.id === viewId) {
      panel.classList.add("active");
    } else {
      panel.classList.remove("active");
    }
  });
}

// --- SIGNALING & MQTT SERVICE ---
function initMQTT() {
  console.log("Connecting to MQTT broker at " + MQTT_BROKER);
  
  const options = {
    clientId: myClientId,
    keepalive: 60,
    clean: true,
    reconnectPeriod: 2000,
    connectTimeout: 30000
  };
  
  try {
    mqttClient = mqtt.connect(MQTT_BROKER, options);
  } catch (err) {
    updateStatus("error", "Signaling server connection failed");
    showToast("Connection to signaling server failed. Offline mode.", "error");
    return;
  }
  
  mqttClient.on("connect", () => {
    console.log("Connected to MQTT signaling broker");
    updateStatus("idle", "Ready");
    
    // Subscribe to local LAN subnet discovery topic
    if (myLanToken) {
      mqttClient.subscribe(`${APP_NAMESPACE}/lan/${myLanToken}`, (err) => {
        if (err) console.error("LAN subscribe error", err);
      });
    }
    
    // Subscribe to my private messaging channel
    mqttClient.subscribe(`${APP_NAMESPACE}/private/${myClientId}`, (err) => {
      if (err) console.error("Private channel subscribe error", err);
    });
    
    // Broadcast initial presence
    announcePresence();
    
    // Set up presence heartbeat loop
    setInterval(announcePresence, DISCOVERY_INTERVAL);
  });
  
  mqttClient.on("message", (topic, message) => {
    let payload;
    try {
      payload = JSON.parse(message.toString());
    } catch (e) {
      console.warn("Received invalid non-JSON payload:", message.toString());
      return;
    }
    
    handleMQTTMessage(topic, payload);
  });
  
  mqttClient.on("error", (err) => {
    console.error("MQTT Client error", err);
    updateStatus("error", "Signaling server error");
  });
  
  mqttClient.on("close", () => {
    console.warn("MQTT signaling connection closed");
    updateStatus("reconnecting", "Reconnecting signaling...");
  });
}

// Publish presence announcement to the LAN subnet topic
function announcePresence() {
  if (!mqttClient || !mqttClient.connected || !myLanToken) return;
  
  const payload = {
    clientId: myClientId,
    name: myDeviceName,
    type: myDeviceType,
    timestamp: Date.now()
  };
  
  mqttClient.publish(
    `${APP_NAMESPACE}/lan/${myLanToken}`,
    JSON.stringify(payload),
    { qos: 0, retain: false }
  );
}

// Parse and distribute signaling commands
function handleMQTTMessage(topic, payload) {
  // Ignore self-published messages on LAN broadcast
  if (payload.clientId === myClientId) return;
  
  // 1. LAN Discovery Message
  if (topic === `${APP_NAMESPACE}/lan/${myLanToken}`) {
    discoveredDevices.set(payload.clientId, {
      clientId: payload.clientId,
      name: payload.name,
      type: payload.type,
      lastSeen: Date.now()
    });
    renderDeviceList();
    return;
  }
  
  // 2. WAN Room code messages
  if (roomCode && topic === `${APP_NAMESPACE}/room/${roomCode}`) {
    if (payload.type === "join_request") {
      // Someone is trying to join our room
      console.log("Received WAN room join request from", payload.name);
      
      // Stop the pairing code timeout
      if (connectionTimeoutId) clearTimeout(connectionTimeoutId);
      
      // Accept their join, sharing our identity
      mqttClient.publish(
        `${APP_NAMESPACE}/room/${roomCode}`,
        JSON.stringify({
          type: "join_accept",
          clientId: myClientId,
          name: myDeviceName
        })
      );
      
      // Setup connection parameters
      currentTargetDevice = {
        clientId: payload.clientId,
        name: payload.name
      };
      
      showToast(`${payload.name} joined room. Initiating session...`, "success");
      isInitiator = true;
      
      // Open role selection
      elements.targetDeviceNameDisplay.textContent = payload.name;
      switchView("view-role-selection");
    } 
    else if (payload.type === "join_accept" && !isInitiator) {
      // We entered the code, and the host accepted our connection
      console.log("Room host accepted connection:", payload.name);
      
      if (connectionTimeoutId) clearTimeout(connectionTimeoutId);
      
      currentTargetDevice = {
        clientId: payload.clientId,
        name: payload.name
      };
      
      showToast(`Connected to host room! Waiting for role selection...`, "success");
      updateStatus("connecting", "Waiting for host choice...");
    }
    return;
  }
  
  // 3. Private Session signaling messages
  if (topic === `${APP_NAMESPACE}/private/${myClientId}`) {
    console.log("Private message received:", payload.type, payload);
    
    switch (payload.type) {
      case "connect_request":
        handleConnectRequest(payload);
        break;
      case "connect_accept":
        handleConnectAccept(payload);
        break;
      case "connect_reject":
        handleConnectReject(payload);
        break;
      case "sdp_offer":
        handleSdpOffer(payload);
        break;
      case "sdp_answer":
        handleSdpAnswer(payload);
        break;
      case "ice_candidate":
        handleIceCandidate(payload);
        break;
      case "disconnect":
        handleDisconnectMessage();
        break;
    }
  }
}

// --- DEVICE MANAGEMENT & UI DRAWING ---
function renderDeviceList() {
  // If list is empty, show default empty state
  if (discoveredDevices.size === 0) {
    elements.deviceList.innerHTML = `
      <div class="empty-state">
        <svg viewBox="0 0 24 24"><path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm1 15h-2v-6h2v6zm0-8h-2V7h2v2z"/></svg>
        <span>Searching for devices...</span>
        <span style="font-size: 0.75rem; color: var(--text-muted);">Ensure other devices have AirBridge open</span>
      </div>
    `;
    return;
  }
  
  elements.deviceList.innerHTML = "";
  discoveredDevices.forEach(device => {
    const deviceEl = document.createElement("div");
    deviceEl.className = "device-item";
    
    let iconSvg = "";
    if (device.type === "mobile") {
      iconSvg = `<svg viewBox="0 0 24 24"><path d="M17 1.01L7 1c-1.1 0-2 .9-2 2v18c0 1.1.9 2 2 2h10c1.1 0 2-.9 2-2V3c0-1.1-.9-1.99-2-1.99zM17 19H7V5h10v14z"/></svg>`;
    } else if (device.type === "tablet") {
      iconSvg = `<svg viewBox="0 0 24 24"><path d="M18.5 0h-13C3.57 0 2 1.57 2 3.5v17C2 22.43 3.57 24 5.5 24h13c1.93 0 3.5-1.57 3.5-3.5v-17C22 1.57 20.43 0 18.5 0zM12 22c-.55 0-1-.45-1-1s.45-1 1-1 1 .45 1 1-.45 1-1 1zm8-4H4V3h16v15z"/></svg>`;
    } else {
      // Laptop/Desktop
      iconSvg = `<svg viewBox="0 0 24 24"><path d="M20 18c1.1 0 1.99-.9 1.99-2L22 5c0-1.1-.9-2-2-2H4c-1.1 0-2 .9-2 2v11c0 1.1.9 2 2 2H0v2h24v-2h-4zM4 5h16v11H4V5z"/></svg>`;
    }
    
    deviceEl.innerHTML = `
      <div class="device-info">
        <div class="device-icon-wrapper">${iconSvg}</div>
        <div class="device-details">
          <h4>${escapeHTML(device.name)}</h4>
          <span>Ready to pair</span>
        </div>
      </div>
      <button class="btn btn-connect-device" data-id="${device.clientId}">Connect</button>
    `;
    
    // Bind connect handler
    deviceEl.querySelector(".btn-connect-device").addEventListener("click", () => {
      initiateConnection(device);
    });
    
    elements.deviceList.appendChild(deviceEl);
  });
}

// Periodically remove devices that stopped broadcasting
function cleanupDevices() {
  const now = Date.now();
  let changed = false;
  
  discoveredDevices.forEach((device, id) => {
    if (now - device.lastSeen > PRESENCE_TIMEOUT) {
      discoveredDevices.delete(id);
      changed = true;
    }
  });
  
  if (changed) renderDeviceList();
}

function escapeHTML(str) {
  return str.replace(/[&<>'"]/g, 
    tag => ({
      '&': '&amp;',
      '<': '&lt;',
      '>': '&gt;',
      "'": '&#39;',
      '"': '&quot;'
    }[tag] || tag)
  );
}

// --- UI STATE MANAGEMENT & EVENTS ---
function updateStatus(state, message) {
  elements.statusDot.className = "status-dot " + state;
  elements.statusText.textContent = message;
}

function initUIEvents() {
  // Settings view toggle
  elements.btnOpenSettings.addEventListener("click", () => {
    switchView("view-settings");
  });
  
  elements.btnSaveSettings.addEventListener("click", saveSettings);
  
  // WAN Room Creation
  elements.btnCreateRoom.addEventListener("click", createWANRoom);
  
  elements.btnCopyCode.addEventListener("click", () => {
    if (roomCode) {
      navigator.clipboard.writeText(roomCode);
      showToast("Room code copied to clipboard!", "success");
    }
  });
  
  // WAN Room Join
  elements.btnJoinRoom.addEventListener("click", joinWANRoom);
  
  // Cancel Connection/Role Selection
  elements.btnCancelRole.addEventListener("click", () => {
    sendPrivateMessage(currentTargetDevice.clientId, { type: "connect_reject" });
    resetToDiscovery();
  });
  
  // Role card triggers
  elements.roleMic.addEventListener("click", () => {
    selectRole("mic");
  });
  
  elements.roleSpeaker.addEventListener("click", () => {
    if (elements.roleSpeaker.classList.contains("unsupported")) return;
    selectRole("speaker");
  });
  
  // Active session volume handler
  elements.sessionVolume.addEventListener("input", (e) => {
    const vol = e.target.value;
    audioElements.forEach(audio => {
      audio.volume = vol;
    });
  });
  
  // Active session controls
  elements.btnSessionMute.addEventListener("click", toggleMute);
  elements.btnRecord.addEventListener("click", toggleRecording);
  elements.btnSessionDisconnect.addEventListener("click", () => {
    closeSession(true);
  });
}

function showToast(message, type = "info") {
  const toast = document.createElement("div");
  toast.className = `toast ${type === "error" ? "toast-error" : type === "success" ? "toast-success" : ""}`;
  
  let iconSvg = "";
  if (type === "success") {
    iconSvg = `<svg viewBox="0 0 24 24"><path d="M9 16.17L4.83 12l-1.42 1.41L9 19 21 7l-1.41-1.41L9 16.17z"/></svg>`;
  } else if (type === "error") {
    iconSvg = `<svg viewBox="0 0 24 24"><path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm1 15h-2v-2h2v2zm0-4h-2V7h2v6z"/></svg>`;
  } else {
    iconSvg = `<svg viewBox="0 0 24 24"><path d="M12 2C6.48 2 2 6.48 2 12s4.48 10 10 10 10-4.48 10-10S17.52 2 12 2zm1 15h-2v-6h2v6zm0-8h-2V7h2v2z"/></svg>`;
  }
  
  toast.innerHTML = `
    <div class="toast-icon">${iconSvg}</div>
    <span>${message}</span>
  `;
  
  elements.toastContainer.appendChild(toast);
  
  // Auto-remove toast
  setTimeout(() => {
    toast.style.animation = "slideInRight 0.3s cubic-bezier(0.4, 0, 0.2, 1) reverse forwards";
    setTimeout(() => toast.remove(), 300);
  }, 4000);
}

// --- PAIRING FLOW ---

// Local connection trigger
function initiateConnection(device) {
  currentTargetDevice = device;
  isInitiator = true;
  elements.targetDeviceNameDisplay.textContent = device.name;
  
  showToast(`Initiating connection to ${device.name}...`, "info");
  updateStatus("connecting", "Negotiating roles...");
  switchView("view-role-selection");
}

// WAN Code Pairing - Host
function createWANRoom() {
  // Generate random 6-character room code
  const chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"; // No easily confused characters (O, I, 1, 0)
  let code = "";
  for (let i = 0; i < 6; i++) {
    code += chars.charAt(Math.floor(Math.random() * chars.length));
  }
  
  roomCode = code;
  elements.roomCodeText.textContent = roomCode;
  elements.roomCodeDisplayWrapper.classList.remove("hidden");
  elements.btnCreateRoom.classList.add("hidden");
  
  // Subscribe to room signaling
  mqttClient.subscribe(`${APP_NAMESPACE}/room/${roomCode}`);
  
  showToast("WAN Room created. Share the code!", "success");
  updateStatus("connecting", "Waiting for remote peer...");
  
  // Set code expiry timeout (10 mins)
  connectionTimeoutId = setTimeout(() => {
    showToast("Room code has expired. Generate a new code.", "error");
    resetWANRoomUI();
  }, 600000);
}

// WAN Code Pairing - Guest
function joinWANRoom() {
  const code = elements.inputRoomCode.value.trim().toUpperCase();
  if (code.length !== 6) {
    showToast("Please enter a valid 6-character room code.", "error");
    return;
  }
  
  roomCode = code;
  showToast(`Connecting to room ${roomCode}...`, "info");
  updateStatus("connecting", `Joining room ${roomCode}...`);
  
  // Subscribe to room signaling
  mqttClient.subscribe(`${APP_NAMESPACE}/room/${roomCode}`);
  
  // Publish join announcement
  mqttClient.publish(
    `${APP_NAMESPACE}/room/${roomCode}`,
    JSON.stringify({
      type: "join_request",
      clientId: myClientId,
      name: myDeviceName
    })
  );
  
  isInitiator = false;
  
  // Fallback timeout for failed room join
  connectionTimeoutId = setTimeout(() => {
    showToast("No response from room. The code may be invalid or expired.", "error");
    resetToDiscovery();
  }, 10000);
}

function resetWANRoomUI() {
  if (roomCode) {
    mqttClient.unsubscribe(`${APP_NAMESPACE}/room/${roomCode}`);
    roomCode = null;
  }
  elements.roomCodeDisplayWrapper.classList.add("hidden");
  elements.btnCreateRoom.classList.remove("hidden");
  elements.inputRoomCode.value = "";
  updateStatus("idle", "Ready");
}

function resetToDiscovery() {
  if (connectionTimeoutId) clearTimeout(connectionTimeoutId);
  resetWANRoomUI();
  currentTargetDevice = null;
  isInitiator = false;
  switchView("view-discovery");
}

// Send private envelope to target client
function sendPrivateMessage(targetId, data) {
  if (!mqttClient || !mqttClient.connected) return;
  mqttClient.publish(
    `${APP_NAMESPACE}/private/${targetId}`,
    JSON.stringify(data)
  );
}

// --- CONNECTION REQUEST & ROLE SELECTION HANDLERS ---

// A device chosen role, notify partner and start media negotiation
function selectRole(role) {
  sessionRoleDetail = role;
  
  // Determine session mapping:
  // If I am 'mic', I send audio (role: sender).
  // If I am 'speaker', I receive audio (role: receiver).
  if (role === "mic") {
    sessionRole = "sender";
  } else {
    sessionRole = "receiver";
  }
  
  const targetRole = role === "mic" ? "speaker" : "mic";
  
  showToast(`Offering role: ${capitalize(role)}...`, "info");
  
  sendPrivateMessage(currentTargetDevice.clientId, {
    type: "connect_request",
    clientId: myClientId,
    name: myDeviceName,
    suggestedRole: targetRole // Suggest the opposite matching role to target
  });
  
  updateStatus("connecting", "Awaiting acceptance...");
}

// Helper for connection request modal
function showConnectionModal(deviceName, roleName) {
  return new Promise((resolve) => {
    elements.modalTitle.textContent = "Incoming Connection Request";
    elements.modalMessage.textContent = `${deviceName} wants to connect with you.\nSuggested role for this device is ${roleName}.`;
    elements.connectionModal.classList.remove("hidden");
    
    const handleAccept = () => {
      cleanup();
      resolve(true);
    };
    
    const handleReject = () => {
      cleanup();
      resolve(false);
    };
    
    const cleanup = () => {
      elements.btnModalAccept.removeEventListener("click", handleAccept);
      elements.btnModalReject.removeEventListener("click", handleReject);
      elements.connectionModal.classList.add("hidden");
    };
    
    elements.btnModalAccept.addEventListener("click", handleAccept);
    elements.btnModalReject.addEventListener("click", handleReject);
  });
}

// Receive connect request from remote device
async function handleConnectRequest(payload) {
  currentTargetDevice = {
    clientId: payload.clientId,
    name: payload.name
  };
  
  const roleName = payload.suggestedRole === "mic" ? "Microphone Source" : "Speaker Output";
  
  // Show connection dialog/role modal automatically on receiving side
  const accept = await showConnectionModal(payload.name, roleName);
  
  if (accept) {
    // If we accepted, lock our role to the matching opposite
    sessionRoleDetail = payload.suggestedRole;
    sessionRole = sessionRoleDetail === "mic" ? "sender" : "receiver";
    isInitiator = false;
    
    sendPrivateMessage(currentTargetDevice.clientId, {
      type: "connect_accept",
      clientId: myClientId,
      name: myDeviceName
    });
    
    showToast("Connection accepted. Initializing P2P audio...", "success");
    initializeP2PSession();
  } else {
    sendPrivateMessage(payload.clientId, {
      type: "connect_reject",
      clientId: myClientId
    });
    resetToDiscovery();
  }
}

// Receiver accepted our request
function handleConnectAccept(payload) {
  showToast(`${payload.name} accepted connection! Establishing audio bridge...`, "success");
  
  // Stop safety timeout
  if (connectionTimeoutId) clearTimeout(connectionTimeoutId);
  
  // Now we initialize the P2P connection.
  initializeP2PSession();
}

function handleConnectReject(payload) {
  showToast("The connection request was declined.", "error");
  resetToDiscovery();
}

// --- WEBRTC CORE IMPLEMENTATION ---

async function initializeP2PSession() {
  activeSessionPartnerId = currentTargetDevice.clientId;
  activeSessionPartnerName = currentTargetDevice.name;
  
  // Clean up any old WebRTC connections or tracks (caching role variables first)
  const savedRole = sessionRole;
  const savedRoleDetail = sessionRoleDetail;
  closeSession(false);
  sessionRole = savedRole;
  sessionRoleDetail = savedRoleDetail;
  iceCandidatesQueue = [];
  
  updateStatus("connecting", "Initializing Peer Connection...");
  
  // Switch to Session View UI
  elements.sessionPartnerName.textContent = activeSessionPartnerName;
  elements.sessionModeBadge.textContent = sessionRoleDetail === "mic" ? "Mic Streaming" : "Speaker Output";
  
  // Show volume controller only on receiving speaker side
  if (sessionRole === "receiver") {
    elements.volumePanel.classList.remove("hidden");
    elements.vuMeterDirectionLabel.textContent = "Incoming Audio Level";
  } else {
    elements.volumePanel.classList.add("hidden");
    elements.vuMeterDirectionLabel.textContent = "Outgoing Audio Level";
  }
  
  switchView("view-session");
  startSessionTimer();

  try {
    peerConnection = new RTCPeerConnection(RTC_CONFIG);
    
    // Exchange ICE candidates
    peerConnection.onicecandidate = (event) => {
      if (event.candidate) {
        sendPrivateMessage(activeSessionPartnerId, {
          type: "ice_candidate",
          candidate: event.candidate
        });
      }
    };
    
    peerConnection.onconnectionstatechange = () => {
      console.log("WebRTC Connection State changed:", peerConnection.connectionState);
      
      switch (peerConnection.connectionState) {
        case "connected":
          updateStatus("connected", "Connected");
          showToast("Audio bridge established successfully!", "success");
          break;
        case "disconnected":
        case "failed":
          updateStatus("reconnecting", "Connection lost. Reconnecting...");
          showToast("Connection dropped. Attempting to restore...", "error");
          break;
        case "closed":
          updateStatus("idle", "Ready");
          break;
      }
    };

    if (sessionRole === "sender") {
      // Sender: Capture media and add tracks to negotiate connection
      updateStatus("connecting", "Requesting audio stream permissions...");
      
      try {
        if (sessionRoleDetail === "mic") {
          // Standard mic capture
          localStream = await getAudioStream();
        } else {
          // Sharing system/tab audio capture (getDisplayMedia)
          localStream = await getSystemAudioStream();
        }
      } catch (err) {
        console.error("Audio capture failed:", err);
        showToast("Could not access audio hardware. Ensure permissions are granted.", "error");
        closeSession(true);
        return;
      }

      // Add local audio tracks to the peer connection
      localStream.getAudioTracks().forEach(track => {
        peerConnection.addTrack(track, localStream);
      });
      
      // Start outbound VU meter
      setupVUMeter(localStream);
      
      // Create and send SDP Offer (since sender has the tracks)
      updateStatus("connecting", "Negotiating network path...");
      const offer = await peerConnection.createOffer();
      await peerConnection.setLocalDescription(offer);
      
      sendPrivateMessage(activeSessionPartnerId, {
        type: "sdp_offer",
        sdp: offer.sdp
      });
      
    } else {
      // Receiver: Prepare to receive audio track
      peerConnection.ontrack = (event) => {
        console.log("Received remote audio track");
        if (event.streams && event.streams[0]) {
          remoteStream = event.streams[0];
        } else {
          remoteStream = new MediaStream([event.track]);
        }
        
        playStream(remoteStream);
        setupVUMeter(remoteStream);
      };
      
      updateStatus("connecting", "Waiting for audio streams...");
    }
    
  } catch (err) {
    console.error("Failed to initialize WebRTC:", err);
    showToast("WebRTC error. Reconnecting signaling...", "error");
    closeSession(true);
  }
}

// Request local mic stream
async function getAudioStream() {
  const constraints = {
    audio: {
      echoCancellation: settings.echoCancel,
      noiseSuppression: settings.noiseSuppress,
      autoGainControl: settings.gainControl,
      deviceId: settings.micDeviceId !== "default" ? { exact: settings.micDeviceId } : undefined
    },
    video: false
  };
  
  return await navigator.mediaDevices.getUserMedia(constraints);
}

// Request system/tab share stream
async function getSystemAudioStream() {
  if (!navigator.mediaDevices.getDisplayMedia) {
    throw new Error("getDisplayMedia not supported on this browser.");
  }
  
  // DisplayMedia prompts screen selection. User must check "Share system audio"
  const captureStream = await navigator.mediaDevices.getDisplayMedia({
    video: {
      width: 1, // Minimum video capture to satisfy browser requirements
      height: 1,
      frameRate: 1
    },
    audio: {
      echoCancellation: false, // Turn off filters for cleaner system music stream
      noiseSuppression: false
    }
  });
  
  // Verify that an audio track actually exists (user might forget to check "Share Audio" checkbox)
  if (captureStream.getAudioTracks().length === 0) {
    // Stop the video tracks immediately to clean up sharing banner
    captureStream.getTracks().forEach(t => t.stop());
    throw new Error("System audio checkbox was not checked during screen sharing.");
  }
  
  return captureStream;
}

// Drain queued ICE candidates once remote SDP description is set
async function drainIceCandidatesQueue() {
  console.log(`Draining ${iceCandidatesQueue.length} queued ICE candidates`);
  while (iceCandidatesQueue.length > 0) {
    const candidate = iceCandidatesQueue.shift();
    try {
      await peerConnection.addIceCandidate(new RTCIceCandidate(candidate));
    } catch (e) {
      console.warn("Failed to add queued ICE candidate:", e);
    }
  }
}

// Handle inbound SDP Offer (called on Receiver)
async function handleSdpOffer(payload) {
  if (!peerConnection) return;
  
  try {
    await peerConnection.setRemoteDescription(new RTCSessionDescription({
      type: "offer",
      sdp: payload.sdp
    }));
    
    await drainIceCandidatesQueue();
    
    const answer = await peerConnection.createAnswer();
    await peerConnection.setLocalDescription(answer);
    
    sendPrivateMessage(activeSessionPartnerId, {
      type: "sdp_answer",
      sdp: answer.sdp
    });
  } catch (err) {
    console.error("Error handling SDP offer", err);
    showToast("Signaling negotiation failed.", "error");
  }
}

// Handle inbound SDP Answer (called on Sender)
async function handleSdpAnswer(payload) {
  if (!peerConnection) return;
  
  try {
    await peerConnection.setRemoteDescription(new RTCSessionDescription({
      type: "answer",
      sdp: payload.sdp
    }));
    
    await drainIceCandidatesQueue();
  } catch (err) {
    console.error("Error setting remote SDP answer", err);
    showToast("Signaling handshake failed.", "error");
  }
}

// Handle ICE Candidate exchange
async function handleIceCandidate(payload) {
  if (!peerConnection) return;
  
  if (peerConnection.remoteDescription && peerConnection.remoteDescription.type) {
    try {
      await peerConnection.addIceCandidate(new RTCIceCandidate(payload.candidate));
    } catch (e) {
      console.warn("Failed to add ICE candidate:", e);
    }
  } else {
    iceCandidatesQueue.push(payload.candidate);
  }
}

// Play remote WebRTC audio stream
function playStream(stream) {
  // Clean up previous elements first
  cleanupAudioElements();
  
  const audio = document.createElement("audio");
  audio.srcObject = stream;
  audio.autoplay = true;
  audio.playsInline = true;
  audio.volume = parseFloat(elements.sessionVolume.value);
  
  // Append to document to trigger playback on various mobile browsers
  document.body.appendChild(audio);
  audioElements.push(audio);
  
  audio.play().catch(err => {
    console.warn("Audio autoplay blocked by browser policy. Interaction required.", err);
    showToast("Autoplay blocked. Tap screen to enable audio.", "info");
    
    // Unlock on body click gesture
    const unlock = () => {
      audio.play();
      if (audioCtx && audioCtx.state === "suspended") {
        audioCtx.resume();
      }
      document.removeEventListener("click", unlock);
    };
    document.addEventListener("click", unlock);
  });
}

function cleanupAudioElements() {
  audioElements.forEach(audio => {
    try {
      audio.pause();
      audio.srcObject = null;
      audio.remove();
    } catch (e) {}
  });
  audioElements = [];
}

// Toggle session microphone/outbound track state
function toggleMute() {
  if (sessionRole === "sender" && localStream) {
    const audioTrack = localStream.getAudioTracks()[0];
    if (audioTrack) {
      audioTrack.enabled = !audioTrack.enabled;
      updateMuteButtonUI(!audioTrack.enabled);
    }
  } else if (sessionRole === "receiver") {
    // Receiver muting (local playback)
    audioElements.forEach(audio => {
      audio.muted = !audio.muted;
      updateMuteButtonUI(audio.muted);
    });
  }
}

function updateMuteButtonUI(isMuted) {
  if (isMuted) {
    elements.btnSessionMute.classList.add("muted");
    elements.iconMuteUnmuted.classList.add("hidden");
    elements.iconMuteMuted.classList.remove("hidden");
    elements.vuDbText.textContent = "Muted";
  } else {
    elements.btnSessionMute.classList.remove("muted");
    elements.iconMuteUnmuted.classList.remove("hidden");
    elements.iconMuteMuted.classList.add("hidden");
  }
}

// End local active session
function closeSession(notifyRemote = true) {
  console.log("Closing active audio session");
  
  // Stop recording if active
  stopRecording();
  
  // Stop session timers
  stopSessionTimer();
  
  // Disconnect WebRTC connection
  if (peerConnection) {
    peerConnection.close();
    peerConnection = null;
  }
  
  // Stop all local audio capture tracks
  if (localStream) {
    localStream.getTracks().forEach(track => track.stop());
    localStream = null;
  }
  
  remoteStream = null;
  cleanupAudioElements();
  stopVUMeter();
  updateMuteButtonUI(false);
  
  if (notifyRemote && activeSessionPartnerId) {
    sendPrivateMessage(activeSessionPartnerId, { type: "disconnect" });
  }
  
  activeSessionPartnerId = null;
  activeSessionPartnerName = null;
  sessionRole = null;
  sessionRoleDetail = null;
  
  resetToDiscovery();
}

// Handle remote peer disconnect notification
function handleDisconnectMessage() {
  showToast("The remote device ended the session.", "info");
  closeSession(false);
}

// --- AUDIO RECORDING ENGINE ---

function toggleRecording() {
  if (mediaRecorder && mediaRecorder.state === "recording") {
    stopRecording();
  } else {
    startRecording();
  }
}

function startRecording() {
  const streamToRecord = sessionRole === "sender" ? localStream : remoteStream;
  if (!streamToRecord) {
    showToast("No active audio stream found to record.", "error");
    return;
  }
  
  recordedChunks = [];
  
  // Choose standard mime type supported by browser
  let options = { mimeType: "audio/webm;codecs=opus" };
  if (!MediaRecorder.isTypeSupported(options.mimeType)) {
    options = { mimeType: "audio/webm" };
  }
  if (!MediaRecorder.isTypeSupported(options.mimeType)) {
    options = { mimeType: "audio/ogg;codecs=opus" };
  }
  if (!MediaRecorder.isTypeSupported(options.mimeType)) {
    options = { mimeType: "" }; // default fallback
  }

  try {
    mediaRecorder = new MediaRecorder(streamToRecord, options);
    
    mediaRecorder.ondataavailable = (event) => {
      if (event.data && event.data.size > 0) {
        recordedChunks.push(event.data);
      }
    };
    
    mediaRecorder.onstop = () => {
      stopRecordingTimer();
      saveRecordingFile();
    };
    
    mediaRecorder.start(1000); // chunk every 1 second
    
    // UI updates
    elements.btnRecord.classList.add("recording-active");
    elements.iconRecordActive.classList.remove("hidden");
    elements.iconRecordInactive.classList.add("hidden");
    elements.recordingBadge.classList.remove("hidden");
    
    // Start recording timer
    startRecordingTimer();
    showToast("Session recording started", "success");
  } catch (err) {
    console.error("Failed to start MediaRecorder:", err);
    showToast("Audio recording not supported or failed to start.", "error");
  }
}

function stopRecording() {
  if (mediaRecorder && mediaRecorder.state !== "inactive") {
    mediaRecorder.stop();
  }
  
  // UI updates
  elements.btnRecord.classList.remove("recording-active");
  elements.iconRecordActive.classList.add("hidden");
  elements.iconRecordInactive.classList.remove("hidden");
  elements.recordingBadge.classList.add("hidden");
  mediaRecorder = null;
}

function saveRecordingFile() {
  if (recordedChunks.length === 0) return;
  
  const blob = new Blob(recordedChunks, { type: "audio/webm" });
  const url = URL.createObjectURL(blob);
  
  const a = document.createElement("a");
  a.style.display = "none";
  a.href = url;
  
  const dateStr = new Date().toISOString().slice(0, 19).replace(/:/g, "-");
  const prefix = sessionRole === "sender" ? "outgoing" : "incoming";
  a.download = `airbridge_record_${prefix}_${dateStr}.webm`;
  
  document.body.appendChild(a);
  a.click();
  
  setTimeout(() => {
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  }, 100);
  
  showToast("Audio recording downloaded!", "success");
}

function startRecordingTimer() {
  recordingStartTime = Date.now();
  elements.recordingTimer.textContent = "00:00";
  
  if (recordingTimerInterval) clearInterval(recordingTimerInterval);
  recordingTimerInterval = setInterval(() => {
    const elapsed = Date.now() - recordingStartTime;
    const minutes = Math.floor(elapsed / 60000).toString().padStart(2, "0");
    const seconds = Math.floor((elapsed % 60000) / 1000).toString().padStart(2, "0");
    elements.recordingTimer.textContent = `${minutes}:${seconds}`;
  }, 1000);
}

function stopRecordingTimer() {
  if (recordingTimerInterval) {
    clearInterval(recordingTimerInterval);
    recordingTimerInterval = null;
  }
}

// --- VU METER AUDIO ANALYSER ---

function setupVUMeter(stream) {
  try {
    stopVUMeter();
    
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    
    // Explicitly handle suspended state (autoplay security policy on modern browsers)
    if (audioCtx.state === "suspended") {
      audioCtx.resume();
      
      const resumeContext = () => {
        if (audioCtx && audioCtx.state === "suspended") {
          audioCtx.resume();
        }
        document.removeEventListener("click", resumeContext);
      };
      document.addEventListener("click", resumeContext);
    }
    
    analyser = audioCtx.createAnalyser();
    
    const source = audioCtx.createMediaStreamSource(stream);
    source.connect(analyser);
    
    analyser.fftSize = 256;
    const bufferLength = analyser.frequencyBinCount;
    dataArray = new Uint8Array(bufferLength);
    
    drawVUMeter();
  } catch (err) {
    console.error("Failed to setup VU Meter analyzer:", err);
  }
}

function drawVUMeter() {
  if (!analyser || !elements.vuCanvas) return;
  
  animationFrameId = requestAnimationFrame(drawVUMeter);
  analyser.getByteFrequencyData(dataArray);
  
  const canvas = elements.vuCanvas;
  const ctx = canvas.getContext("2d");
  const width = canvas.width;
  const height = canvas.height;
  
  ctx.clearRect(0, 0, width, height);
  
  // Compute average amplitude
  let sum = 0;
  for (let i = 0; i < dataArray.length; i++) {
    sum += dataArray[i];
  }
  const average = sum / dataArray.length;
  
  // Render animated VU meter bars (gradient style)
  const barWidth = 3;
  const barGap = 2;
  const barCount = Math.floor(width / (barWidth + barGap));
  
  const gradient = ctx.createLinearGradient(0, 0, width, 0);
  gradient.addColorStop(0, "#00f0ff");  // Cyan
  gradient.addColorStop(0.6, "#3b82f6"); // Blue
  gradient.addColorStop(1, "#ef4444");   // Red warning
  
  ctx.fillStyle = gradient;
  
  // Handle mute feedback state
  const isMuted = (sessionRole === "sender" && localStream && !localStream.getAudioTracks()[0].enabled) || 
                  (sessionRole === "receiver" && audioElements.length > 0 && audioElements[0].muted);
  
  if (isMuted) {
    elements.vuDbText.textContent = "MUTED";
    ctx.fillStyle = "rgba(100, 116, 139, 0.2)"; // Grayed out
    for (let i = 0; i < barCount; i++) {
      ctx.fillRect(i * (barWidth + barGap), height - 4, barWidth, 4);
    }
    return;
  }
  
  // Active decibels rendering
  const db = Math.round((average / 255) * 100);
  elements.vuDbText.textContent = db > 5 ? `${db}% Volume` : "SILENT";
  
  for (let i = 0; i < barCount; i++) {
    // Map frequency bands to bar heights with frequency scaling
    const value = dataArray[i % dataArray.length];
    const percent = value / 255;
    const barHeight = Math.max(4, percent * height);
    
    // Float bar styling
    const x = i * (barWidth + barGap);
    const y = height - barHeight;
    ctx.fillRect(x, y, barWidth, barHeight);
  }
}

function stopVUMeter() {
  if (animationFrameId) {
    cancelAnimationFrame(animationFrameId);
    animationFrameId = null;
  }
  
  if (audioCtx) {
    try {
      audioCtx.close();
    } catch (e) {}
    audioCtx = null;
  }
  
  analyser = null;
  dataArray = null;
  
  // Clear canvas
  const canvas = elements.vuCanvas;
  if (canvas) {
    const ctx = canvas.getContext("2d");
    ctx.clearRect(0, 0, canvas.width, canvas.height);
  }
}

// --- SESSION DURATION TIMER ---
function startSessionTimer() {
  sessionStartTime = Date.now();
  elements.sessionTimer.textContent = "00:00";
  
  sessionTimerInterval = setInterval(() => {
    const elapsed = Math.floor((Date.now() - sessionStartTime) / 1000);
    const mins = Math.floor(elapsed / 60).toString().padStart(2, "0");
    const secs = (elapsed % 60).toString().padStart(2, "0");
    elements.sessionTimer.textContent = `${mins}:${secs}`;
  }, 1000);
}

function stopSessionTimer() {
  if (sessionTimerInterval) {
    clearInterval(sessionTimerInterval);
    sessionTimerInterval = null;
  }
  elements.sessionTimer.textContent = "00:00";
}
