// ==UserScript==
// @name         Twitch GIF Gallery + Kappa.lol
// @namespace    https://github.com/BigFluffyCatOnWatermelon/twitch-media-gallery
// @version      5.2.0
// @description  Twitch media gallery with Rendi animated WebP video conversion, FreeConvert rules, original 7TV links, persistent previews, pagination and Gist settings sync.
// @updateURL    https://raw.githubusercontent.com/BigFluffyCatOnWatermelon/twitch-media-gallery/main/twitch-helper.user.js
// @downloadURL  https://raw.githubusercontent.com/BigFluffyCatOnWatermelon/twitch-media-gallery/main/twitch-helper.user.js
// @match        https://www.twitch.tv/*
// @match        https://twitch.tv/*
// @run-at       document-idle
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_xmlhttpRequest
// @connect      kappa.lol
// @connect      api.github.com
// @connect      gist.githubusercontent.com
// @connect      api.freeconvert.com
// @connect      freeconvert.com
// @connect      *.freeconvert.com
// @connect      api.rendi.dev
// @connect      *.rendi.dev
// @connect      7tv.io
// @connect      7tv.app
// @connect      cdn.7tv.app
// ==/UserScript==

(() => {
  'use strict';

  const VERSION = 5;
  const DEFAULT_MAX_WIDTH = 1500;
  const MAX_FILE_BYTES = 100 * 1024 * 1024;
  const DATA_KEY = 'twgif_gallery_data_v1';
  const CONFIG_KEY = 'twgif_gallery_config_v2';
  const LEGACY_SYNC_KEY = 'twgif_gallery_sync_v1';
  const SYNC_FILENAME = 'twitch-gif-gallery.json';
  const KAPPA_UPLOAD_URL = 'https://kappa.lol/api/upload';
  const GITHUB_API = 'https://api.github.com';
  const FREECONVERT_API = 'https://api.freeconvert.com/v1';
  const RENDI_API = 'https://api.rendi.dev/v1';
  const SETTINGS_FILENAME = 'twitch-gif-gallery-settings.json';
  const SETTINGS_SCHEMA_VERSION = 3;

  let panelView = 'gallery';
  let settingsTab = 'general';
  let galleryPage = 0;
  let mediaLoadRun = 0;
  let chatMediaObserver = null;
  let chatMediaScanQueued = false;
  let holdPreviewTimer = 0;
  let holdPreviewItem = null;
  const mediaCardCache = new Map();
  const loadedMediaUrls = new Set();
  let activeTrigger = null;
  let activeComposer = null;
  let savedComposerRange = null;
  let savedComposerOffset = null;
  let lastStatus = '';
  let lastStatusType = 'info';
  let statusTimer = 0;
  let syncTimer = 0;
  let syncRunning = false;
  let syncAgain = false;
  let observer = null;
  let ensureQueued = false;
  let lastObservedInput = null;
  const debugLogs = [];
  const processingFiles = new Map();
  const recentFileFingerprints = new Map();

  const EMPTY_DATA = () => ({ version: VERSION, items: [], deleted: {} });
  const DEFAULT_CONFIG = () => ({
    maxWidth: DEFAULT_MAX_WIDTH,
    mediaScale: 1,
    tileView: 'masonry',
    pageSize: 100,
    previewScale: 1.6,
    conversionRules: { image: 'webp', gif: 'webp', video: 'gif' },
    settingsSchemaVersion: SETTINGS_SCHEMA_VERSION,
    freeConvertToken: '',
    // This key deliberately never enters a Gist snapshot.
    rendiApiKey: '',
    gistToken: '',
    gistId: '',
    debug: false,
    settingsUpdatedAt: 0
  });

  const SVG_GALLERY = '<svg viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="6" width="13" height="14" rx="2"></rect><path d="M8 6V4.8A1.8 1.8 0 0 1 9.8 3h9.4A1.8 1.8 0 0 1 21 4.8v10.4a1.8 1.8 0 0 1-1.8 1.8H16"></path><circle cx="7.5" cy="10.5" r="1.3"></circle><path d="m4 17 4.2-4 2.5 2 1.8-1.5 1.5 1.4"></path></svg>';
  const SVG_SETTINGS = '<svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="3"></circle><path d="m19.4 15 .1.1a1.7 1.7 0 0 1-2.4 2.4l-.1-.1a1.7 1.7 0 0 0-2.9 1.2v.2a1.7 1.7 0 0 1-3.4 0v-.2a1.7 1.7 0 0 0-2.9-1.2l-.1.1a1.7 1.7 0 1 1-2.4-2.4l.1-.1a1.7 1.7 0 0 0-1.2-2.9H4a1.7 1.7 0 0 1 0-3.4h.2a1.7 1.7 0 0 0 1.2-2.9l-.1-.1a1.7 1.7 0 1 1 2.4-2.4l.1.1a1.7 1.7 0 0 0 2.9-1.2V2a1.7 1.7 0 0 1 3.4 0v.2a1.7 1.7 0 0 0 2.9 1.2l.1-.1a1.7 1.7 0 1 1 2.4 2.4l-.1.1a1.7 1.7 0 0 0 1.2 2.9h.2a1.7 1.7 0 0 1 0 3.4h-.2a1.7 1.7 0 0 0-1.2 2.9Z"></path></svg>';
  const SVG_CLOSE = '<svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><path d="m6 6 12 12M18 6 6 18"></path></svg>';
  const SVG_SEARCH = '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" aria-hidden="true"><circle cx="10.5" cy="10.5" r="6.5"></circle><path d="m16 16 4.2 4.2"></path></svg>';

  function parseJson(value, fallback) {
    if (typeof value !== 'string') return value == null ? fallback : value;
    try { return JSON.parse(value); } catch (_) { return fallback; }
  }

  function loadData() {
    const raw = parseJson(GM_getValue(DATA_KEY, EMPTY_DATA()), EMPTY_DATA());
    const data = EMPTY_DATA();
    if (!raw || typeof raw !== 'object') return data;

    const rawItems = Array.isArray(raw.items) ? raw.items : [];
    const cleaned = rawItems
      .filter(item => item && typeof item.id === 'string' && typeof item.url === 'string')
      .map(item => ({
        id: String(item.id),
        url: String(item.url),
        previewUrl: String(item.previewUrl || item.url),
        name: String(item.name || 'Медиафайл').slice(0, 120),
        type: String(item.type || 'image'),
        sourceKey: String(item.sourceKey || ''),
        addedAt: Number(item.addedAt) || Date.now(),
        updatedAt: Number(item.updatedAt) || Number(item.addedAt) || Date.now()
      }));

    // Clean duplicates already created by older builds. A local file fingerprint is
    // more reliable than the Kappa URL because uploading the same file creates a new URL.
    const bySource = new Map();
    for (const item of cleaned) {
      const key = item.sourceKey ? `source:${item.sourceKey}` : `url:${item.url}`;
      const previous = bySource.get(key);
      if (!previous || item.updatedAt > previous.updatedAt) bySource.set(key, item);
    }
    data.items = [...bySource.values()];
    data.deleted = raw.deleted && typeof raw.deleted === 'object' && !Array.isArray(raw.deleted)
      ? Object.fromEntries(Object.entries(raw.deleted)
        .filter(([id, time]) => typeof id === 'string' && Number.isFinite(Number(time)))
        .map(([id, time]) => [id, Number(time)]))
      : {};

    if (data.items.length !== rawItems.length) {
      GM_setValue(DATA_KEY, sortData(data));
      logDebug('Removed duplicate local gallery items', { before: rawItems.length, after: data.items.length });
    }
    return data;
  }

  function loadConfig() {
    const raw = parseJson(GM_getValue(CONFIG_KEY, {}), {}) || {};
    const legacy = parseJson(GM_getValue(LEGACY_SYNC_KEY, {}), {}) || {};
    const defaults = DEFAULT_CONFIG();
    const previousSchemaVersion = Number(raw.settingsSchemaVersion) || 0;
    const rules = raw.conversionRules && typeof raw.conversionRules === 'object'
      ? { ...raw.conversionRules }
      : {};
    const allowedTargets = ['keep', 'webp', 'gif', 'webm', 'mp4', 'png', 'jpg'];
    const cleanTarget = (value, fallback) => allowedTargets.includes(String(value)) ? String(value) : fallback;
    const config = {
      maxWidth: clampInt(raw.maxWidth ?? defaults.maxWidth, 100, 4000, defaults.maxWidth),
      mediaScale: clampFloat(raw.mediaScale ?? defaults.mediaScale, 0.5, 2, defaults.mediaScale),
      tileView: raw.tileView === 'grid' ? 'grid' : 'masonry',
      pageSize: clampInt(raw.pageSize ?? 100, 10, 500, 100),
      previewScale: clampFloat(raw.previewScale ?? defaults.previewScale, 1.1, 3, defaults.previewScale),
      conversionRules: {
        image: cleanTarget(rules.image, 'webp'),
        gif: cleanTarget(rules.gif, 'webp'),
        video: cleanTarget(rules.video, 'gif')
      },
      freeConvertToken: String(raw.freeConvertToken || raw.cloudConvertToken || '').trim(),
      rendiApiKey: String(raw.rendiApiKey || '').trim(),
      gistToken: String(raw.gistToken || legacy.token || '').trim(),
      gistId: String(raw.gistId || legacy.gistId || '').trim(),
      debug: Boolean(raw.debug),
      settingsUpdatedAt: Number(raw.settingsUpdatedAt) || 0,
      settingsSchemaVersion: SETTINGS_SCHEMA_VERSION
    };

    // One-time migration: old versions defaulted video conversion to WebP.
    // Move that old default to GIF so existing installs actually use the new behavior.
    if (previousSchemaVersion < SETTINGS_SCHEMA_VERSION) {
      if (config.conversionRules.video === 'webp') {
        config.conversionRules.video = 'gif';
        config.settingsUpdatedAt = Date.now();
      }
      GM_setValue(CONFIG_KEY, config);
    }
    return config;
  }


  function saveConfig(next) {
    const current = loadConfig();
    const defaults = DEFAULT_CONFIG();
    const rules = { ...current.conversionRules, ...(next.conversionRules && typeof next.conversionRules === 'object' ? next.conversionRules : {}) };
    const allowedTargets = ['keep', 'webp', 'gif', 'webm', 'mp4', 'png', 'jpg'];
    for (const key of ['image', 'gif', 'video']) if (!allowedTargets.includes(String(rules[key]))) rules[key] = defaults.conversionRules[key];
    const config = {
      maxWidth: clampInt(next.maxWidth ?? current.maxWidth, 100, 4000, defaults.maxWidth),
      mediaScale: clampFloat(next.mediaScale ?? current.mediaScale, 0.5, 2, defaults.mediaScale),
      tileView: (next.tileView ?? current.tileView) === 'grid' ? 'grid' : 'masonry',
      pageSize: clampInt(next.pageSize ?? current.pageSize, 10, 500, defaults.pageSize),
      previewScale: clampFloat(next.previewScale ?? current.previewScale, 1.1, 3, defaults.previewScale),
      conversionRules: rules,
      freeConvertToken: String(next.freeConvertToken ?? current.freeConvertToken).trim(),
      rendiApiKey: String(next.rendiApiKey ?? current.rendiApiKey).trim(),
      gistToken: String(next.gistToken ?? current.gistToken).trim(),
      gistId: String(next.gistId ?? current.gistId).trim(),
      debug: Boolean(next.debug ?? current.debug),
      settingsUpdatedAt: Number.isFinite(Number(next.settingsUpdatedAt)) ? Number(next.settingsUpdatedAt) : Date.now(),
      settingsSchemaVersion: SETTINGS_SCHEMA_VERSION
    };
    GM_setValue(CONFIG_KEY, config);
    return config;
  }

  function clampInt(value, min, max, fallback) {
    const number = Number.parseInt(value, 10);
    return Number.isFinite(number) ? Math.max(min, Math.min(max, number)) : fallback;
  }

  function clampFloat(value, min, max, fallback) {
    const number = Number.parseFloat(value);
    return Number.isFinite(number) ? Math.max(min, Math.min(max, number)) : fallback;
  }

  function sortData(value) {
    const data = value && typeof value === 'object' ? value : EMPTY_DATA();
    const normalized = {
      version: VERSION,
      items: Array.isArray(data.items) ? data.items.slice() : [],
      deleted: data.deleted && typeof data.deleted === 'object' ? { ...data.deleted } : {}
    };
    normalized.items.sort((a, b) => b.addedAt - a.addedAt || a.name.localeCompare(b.name));
    normalized.deleted = Object.fromEntries(Object.entries(normalized.deleted).sort(([a], [b]) => a.localeCompare(b)));
    return normalized;
  }

  function dataSignature(data) {
    return JSON.stringify(sortData(data));
  }

  function mergeData(leftValue, rightValue) {
    const left = leftValue || EMPTY_DATA();
    const right = rightValue || EMPTY_DATA();
    const deleted = { ...(left.deleted || {}) };
    for (const [id, time] of Object.entries(right.deleted || {})) {
      deleted[id] = Math.max(Number(deleted[id]) || 0, Number(time) || 0);
    }
    const byId = new Map();
    for (const item of [...(left.items || []), ...(right.items || [])]) {
      const old = byId.get(item.id);
      if (!old || (Number(item.updatedAt) || 0) > (Number(old.updatedAt) || 0)) byId.set(item.id, item);
    }
    const alive = [...byId.values()].filter(item => (deleted[item.id] || 0) < (Number(item.updatedAt) || 0));
    const deduped = new Map();
    for (const item of alive) {
      const key = item.sourceKey ? `source:${item.sourceKey}` : `url:${item.url}`;
      const previous = deduped.get(key);
      if (!previous || (Number(item.updatedAt) || 0) > (Number(previous.updatedAt) || 0)) deduped.set(key, item);
    }
    const items = [...deduped.values()];
    return sortData({ version: VERSION, items, deleted });
  }

  function logDebug(...parts) {
    const text = parts.map(part => {
      if (part instanceof Error) return `${part.name}: ${part.message}`;
      if (typeof part === 'string') return part;
      try { return JSON.stringify(part); } catch (_) { return String(part); }
    }).join(' ');
    debugLogs.push(`${new Date().toLocaleTimeString()}  ${text}`);
    if (debugLogs.length > 80) debugLogs.shift();
    if (loadConfig().debug) console.debug('[Twitch GIF Gallery]', ...parts);
    const logView = document.getElementById('twgif-debug-log');
    if (logView) logView.value = debugLogs.join('\n');
  }

  function setStatus(message, type = 'info', sticky = false) {
    lastStatus = String(message || '');
    lastStatusType = type;
    const element = document.getElementById('twgif-status');
    if (element) {
      element.textContent = lastStatus;
      element.dataset.type = lastStatusType;
    }
    if (statusTimer) clearTimeout(statusTimer);
    if (!sticky && lastStatus) {
      const messageAtSet = lastStatus;
      statusTimer = setTimeout(() => {
        if (lastStatus === messageAtSet) {
          lastStatus = '';
          const current = document.getElementById('twgif-status');
          if (current) current.textContent = '';
        }
      }, 7000);
    }
    if (message) logDebug(`status:${type}`, message);
  }

  function request(options) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        ...options,
        timeout: options.timeout || 35000,
        onload: response => {
          if (response.status >= 200 && response.status < 300) resolve(response);
          else {
            const detail = String(response.responseText || '').slice(0, 500);
            reject(new Error(`HTTP ${response.status}${detail ? ` — ${detail}` : ''}`));
          }
        },
        onerror: () => reject(new Error('Сетевая ошибка. Проверь соединение и доступ к сервису.')),
        ontimeout: () => reject(new Error('Истекло время ожидания ответа сервера.'))
      });
    });
  }

  function requestBlob(url, timeout = 120000) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'GET', url, responseType: 'blob', timeout,
        onload: response => {
          if (response.status < 200 || response.status >= 300) {
            reject(new Error(`Не удалось скачать результат конвертации (HTTP ${response.status}).`));
            return;
          }
          const blob = response.response instanceof Blob
            ? response.response
            : new Blob([response.response], { type: response.responseHeaders?.match(/content-type:\s*([^;\r\n]+)/i)?.[1] || 'application/octet-stream' });
          resolve(blob);
        },
        onerror: () => reject(new Error('Не удалось скачать файл после конвертации.')),
        ontimeout: () => reject(new Error('Истекло время скачивания результата конвертации.'))
      });
    });
  }

  function parseResponse(response, label) {
    try { return JSON.parse(response.responseText || '{}'); }
    catch (_) { throw new Error(`${label}: сервис вернул некорректный JSON.`); }
  }

  function formatGitHubSyncError(error) {
    const message = String(error?.message || error || 'Неизвестная ошибка');
    if (/HTTP 401\b/i.test(message) || /Bad credentials/i.test(message)) {
      return 'GitHub отклонил токен (401 Bad credentials). Создай новый токен и замени старый: Fine-grained token — разрешение Gists: Read and write; Classic token — scope gist. Затем нажми «Сохранить доступ» и повтори действие.';
    }
    if (/HTTP 403\b/i.test(message)) {
      return 'GitHub запретил операцию (403). Проверь срок действия токена и разрешение Gists: Read and write (для Classic token — gist).';
    }
    return message;
  }

  function makeId() {
    if (globalThis.crypto && typeof crypto.randomUUID === 'function') return crypto.randomUUID();
    return `${Date.now().toString(36)}-${Math.random().toString(36).slice(2)}-${Math.random().toString(36).slice(2)}`;
  }

  function getExtension(mime, fallbackName = '') {
    const map = {
      'image/jpeg': '.jpg', 'image/png': '.png', 'image/gif': '.gif', 'image/webp': '.webp',
      'image/avif': '.avif', 'image/bmp': '.bmp', 'image/svg+xml': '.svg',
      'video/webm': '.webm', 'video/mp4': '.mp4', 'video/quicktime': '.mov', 'video/x-matroska': '.mkv'
    };
    if (map[mime]) return map[mime];
    const match = String(fallbackName).match(/\.([a-z0-9]{2,5})$/i);
    return match ? `.${match[1].toLowerCase()}` : '.bin';
  }

  function mimeFromFile(file) {
    if (file.type && /^(image|video)\//i.test(file.type)) return file.type.toLowerCase();
    const ext = (String(file.name || '').match(/\.([a-z0-9]+)$/i) || ['', ''])[1].toLowerCase();
    const map = {
      jpg: 'image/jpeg', jpeg: 'image/jpeg', png: 'image/png', gif: 'image/gif', webp: 'image/webp',
      avif: 'image/avif', bmp: 'image/bmp', svg: 'image/svg+xml',
      mp4: 'video/mp4', m4v: 'video/mp4', mov: 'video/quicktime', webm: 'video/webm',
      mkv: 'video/x-matroska', avi: 'video/x-msvideo', ogv: 'video/ogg', mpg: 'video/mpeg', mpeg: 'video/mpeg'
    };
    return map[ext] || '';
  }

  function mediaTypeFromUrl(rawUrl, responseType = '') {
    let pathname = '';
    try { pathname = new URL(rawUrl).pathname.toLowerCase(); } catch (_) {}
    if (String(responseType).startsWith('video/')) return 'video';
    if (/\.(webm|mp4|mov|m4v|mkv|avi|ogv|mpg|mpeg)(?:$)/i.test(pathname)) return 'video';
    if (/\.gif$/i.test(pathname)) return 'gif';
    return 'image';
  }

  function normalizeKappaLink(data, fallbackMime, fallbackName) {
    const raw = String(data.link || data.url || '').trim();
    if (!raw) throw new Error('kappa.lol не вернул ссылку на файл.');
    let url;
    try { url = new URL(raw, KAPPA_UPLOAD_URL); }
    catch (_) { throw new Error('kappa.lol вернул некорректную ссылку.'); }
    let ext = String(data.ext || getExtension(data.type || fallbackMime, fallbackName)).trim();
    if (ext && !ext.startsWith('.')) ext = `.${ext}`;
    if (ext && !url.pathname.toLowerCase().endsWith(ext.toLowerCase())) url.pathname += ext;
    url.protocol = 'https:';
    // kappa.lol and its sibling domains serve the same uploaded objects.
    url.hostname = 'kappa.lol';
    url.port = '';
    return url.toString();
  }

  async function uploadToKappa(file) {
    const form = new FormData();
    form.append('file', file, file.name || 'media');
    logDebug('Kappa upload start', { name: file.name, size: file.size, type: file.type });
    const response = await request({
      method: 'POST', url: KAPPA_UPLOAD_URL, data: form, timeout: 120000,
      headers: { 'Accept': 'application/json' }
    });
    const result = parseResponse(response, 'kappa.lol');
    return {
      url: normalizeKappaLink(result, file.type || mimeFromFile(file), file.name),
      type: String(result.type || file.type || mimeFromFile(file) || 'application/octet-stream'),
      name: file.name || 'Медиафайл'
    };
  }

  function getGifDimensions(file) {
    return file.slice(0, 10).arrayBuffer().then(buffer => {
      const bytes = new Uint8Array(buffer);
      if (bytes.length < 10 || bytes[0] !== 0x47 || bytes[1] !== 0x49 || bytes[2] !== 0x46) {
        throw new Error('Файл с расширением GIF повреждён или не является GIF.');
      }
      return { width: bytes[6] | (bytes[7] << 8), height: bytes[8] | (bytes[9] << 8) };
    });
  }

  async function getStaticImageDimensions(file) {
    let bitmap;
    try {
      bitmap = await createImageBitmap(file);
      const result = { width: bitmap.width, height: bitmap.height };
      if (typeof bitmap.close === 'function') bitmap.close();
      return result;
    } catch (_) {
      return new Promise((resolve, reject) => {
        const image = new Image();
        const objectUrl = URL.createObjectURL(file);
        const timer = setTimeout(() => {
          URL.revokeObjectURL(objectUrl);
          reject(new Error('Изображение слишком долго обрабатывается.'));
        }, 15000);
        image.onload = () => {
          clearTimeout(timer);
          const result = { width: image.naturalWidth, height: image.naturalHeight };
          URL.revokeObjectURL(objectUrl);
          resolve(result);
        };
        image.onerror = () => {
          clearTimeout(timer);
          URL.revokeObjectURL(objectUrl);
          reject(new Error('Не удалось прочитать изображение.'));
        };
        image.src = objectUrl;
      });
    }
  }

  function canvasToBlob(canvas, mime, quality) {
    return new Promise((resolve, reject) => {
      canvas.toBlob(blob => blob ? resolve(blob) : reject(new Error('Не удалось сохранить уменьшенное изображение.')), mime, quality);
    });
  }

  async function resizeStaticImage(file, maxWidth, outputFormat = 'webp') {
    const dims = await getStaticImageDimensions(file);
    if (!dims.width || !dims.height) throw new Error('Не удалось определить размеры изображения.');

    const sourceMime = mimeFromFile(file);
    const needsResize = dims.width > maxWidth;
    if (outputFormat === 'keep' && !needsResize) return file;

    // Canvas can reliably export these formats. If the user selected "keep" for
    // an oversized AVIF/SVG/BMP, resize to WebP instead of failing silently.
    let targetMime = outputFormat === 'keep'
      ? (['image/webp', 'image/png', 'image/jpeg'].includes(sourceMime) ? sourceMime : 'image/webp')
      : ({ webp: 'image/webp', png: 'image/png', jpg: 'image/jpeg' }[outputFormat] || '');

    if (!targetMime || !['image/webp', 'image/png', 'image/jpeg'].includes(targetMime)) {
      throw new Error(`Для формата ${outputFormat} нужна внешняя конвертация FreeConvert.`);
    }

    const needsConvert = sourceMime !== targetMime;
    if (!needsResize && !needsConvert) return file;

    if (dims.width * dims.height > 20_000_000) {
      throw new Error('Изображение слишком большое для локального Canvas. Уменьши его заранее или выбери совместимый формат/сервис.');
    }

    const scale = Math.min(1, maxWidth / dims.width);
    const width = Math.max(1, Math.round(dims.width * scale));
    const height = Math.max(1, Math.round(dims.height * scale));
    const canvas = document.createElement('canvas');
    canvas.width = width;
    canvas.height = height;
    const context = canvas.getContext('2d');
    if (!context) throw new Error('Браузер не смог создать холст для изменения размера изображения.');

    const bitmap = await createImageBitmap(file);
    if (targetMime === 'image/jpeg') {
      context.fillStyle = '#fff';
      context.fillRect(0, 0, width, height);
    }
    context.drawImage(bitmap, 0, 0, width, height);
    if (typeof bitmap.close === 'function') bitmap.close();

    const blob = await canvasToBlob(canvas, targetMime, targetMime === 'image/png' ? undefined : 0.86);
    const finalMime = blob.type || targetMime;
    const baseName = String(file.name || 'image').replace(/\.[^.]+$/, '') || 'image';
    const name = `${baseName}${getExtension(finalMime, file.name)}`;
    logDebug('Static image converted locally', { from: dims, to: { width, height }, mime: finalMime, bytes: blob.size });
    return new File([blob], name, { type: finalMime, lastModified: Date.now() });
  }

  function delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  function fileExtension(file) {
    const match = String(file.name || '').toLowerCase().match(/\.([a-z0-9]{2,8})$/);
    if (match) return match[1];
    const mime = mimeFromFile(file);
    return getExtension(mime, file.name).replace(/^\./, '') || 'bin';
  }

  function findTaskList(payload) {
    const root = payload && (payload.data || payload);
    const lists = [root?.tasks, payload?.tasks, root?.data?.tasks, root?.docs, payload?.docs, root?.data?.docs, root?.results, payload?.results];
    for (const list of lists) {
      if (Array.isArray(list)) return list.map(entry => entry && entry.data ? { ...entry.data, name: entry.name || entry.data.name } : entry);
      if (list && typeof list === 'object') return Object.entries(list).map(([name, task]) => ({ name, ...task }));
    }
    return [];
  }

  async function getFreeConvertOptions(inputFormat, outputFormat, maxWidth, isVideo) {
    let available = [];
    try {
      const response = await request({
        method: 'GET',
        url: `${FREECONVERT_API}/query/options/convert?input_format=${encodeURIComponent(inputFormat)}&output_format=${encodeURIComponent(outputFormat)}`,
        timeout: 20000,
        headers: { 'Accept': 'application/json' }
      });
      const json = parseResponse(response, 'FreeConvert options');
      available = (json.data || json).options || [];
    } catch (error) {
      logDebug('FreeConvert advanced options lookup skipped', error.message || error);
    }

    const output = {};
    const findOption = name => available.find(option => option && option.name === name);

    if (!isVideo) {
      const resizeType = findOption('resize_type_image');
      if (resizeType && Array.isArray(resizeType.enum_values)) {
        const widthOption = resizeType.enum_values.find(option => option.value === 'by_width_keep_ar');
        if (widthOption) output.resize_type_image = widthOption.value;
      }
      if (findOption('image_custom_width')) output.image_custom_width = maxWidth;
    } else {
      for (const option of available) {
        const name = String(option.name || '').toLowerCase();
        if (name.includes('video') && name.includes('width') && option.data_type === 'number') {
          output[option.name] = maxWidth;
        } else if (name.includes('video') && (name.includes('resize') || name.includes('resolution')) && Array.isArray(option.enum_values)) {
          const desired = option.enum_values.find(v => /width|custom|resolution/i.test(`${v.value} ${v.label || ''}`));
          if (desired) output[option.name] = desired.value;
        }
      }

      // FreeConvert may expose the WebP animation loop setting under a
      // format-specific option name. Prefer the exact option advertised by its API.
      if (['webp', 'gif'].includes(outputFormat)) {
        const loopOption = available.find(option => {
          const name = String(option?.name || '').toLowerCase();
          const dataType = String(option?.data_type || '').toLowerCase();
          const isNumeric = !dataType || ['number', 'integer', 'float'].includes(dataType);
          const isLoopCount = /(?:^|_)loop_count$/.test(name);
          const isLoop = name === 'loop' || /(?:^|_)loop$/.test(name);
          return isNumeric && (isLoopCount || isLoop) && !/(?:^|_)(?:ignore|disable)_?loop/.test(name);
        });
        if (loopOption) output[loopOption.name] = 0;
      }
    }

    return output;
  }

  async function freeConvertFile(file, outputFormat, maxWidth = loadConfig().maxWidth) {
    const config = loadConfig();
    if (!config.freeConvertToken) {
      throw new Error('Для выбранной конвертации нужен FreeConvert API-токен. Открой настройки → Конвертация.');
    }

    const inputFormat = fileExtension(file);
    const isVideo = mimeFromFile(file).startsWith('video/');
    const options = await getFreeConvertOptions(inputFormat, outputFormat, maxWidth, isVideo);
    const outName = `${String(file.name || 'media').replace(/\.[^.]+$/, '')}.${outputFormat}`;
    const stamp = `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 8)}`;
    const convertOptions = { loop_count: 0 };
    if (isVideo && outputFormat === 'gif') {
      // FreeConvert names the GIF option gif_loop_count; 0 means loop forever.
      delete convertOptions.loop_count;
      const loopOptionNames = Object.keys(options).filter(optionName => /loop_count$/i.test(optionName));
      if (loopOptionNames.length) {
        for (const optionName of loopOptionNames) convertOptions[optionName] = 0;
      } else {
        convertOptions.gif_loop_count = 0;
      }
    } else if (isVideo && outputFormat === 'webp') {
      // Keep existing WebP behavior unchanged; use the option name advertised by FreeConvert.
      for (const optionName of Object.keys(options)) {
        if (/loop/i.test(optionName)) convertOptions[optionName] = 0;
      }
    }
    const tasksDefinition = {
      'import-source': {
        operation: 'import/upload'
      },
      'convert-media': {
        operation: 'convert',
        input: 'import-source',
        input_format: inputFormat,
        output_format: outputFormat,
        options: convertOptions
      },
      'export-media': {
        operation: 'export/url',
        input: 'convert-media',
        filename: outName
      }
    };

    logDebug('FreeConvert job create', { inputFormat, outputFormat, width: maxWidth, isVideo, availableOptions: options, convertOptions, size: file.size });
    setStatus(`Передаю «${file.name || 'медиа'}» в FreeConvert…`, 'info', true);

    const createResponse = await request({
      method: 'POST',
      url: `${FREECONVERT_API}/process/jobs`,
      timeout: 35000,
      headers: {
        'Authorization': `Bearer ${config.freeConvertToken}`,
        'Accept': 'application/json',
        'Content-Type': 'application/json'
      },
      data: JSON.stringify({ tag: `twitch-gallery-${stamp}`, tasks: tasksDefinition })
    });
    const created = parseResponse(createResponse, 'FreeConvert');
    const jobRoot = created.data || created;
    const taskList = findTaskList(created);
    const importTask = taskList.find(task => task.name === 'import-source' || task.operation === 'import/upload');
    let uploadForm = importTask?.result?.form || importTask?.form || null;

    const jobId = jobRoot.id || jobRoot.job || created.job || created.id || importTask?.job;
    if (!jobId) throw new Error('FreeConvert не вернул ID задачи. Проверь API-токен и формат ответа.');

    // If the import form is not included in the initial job response, wait briefly for the task detail.
    if (!uploadForm) {
      for (let i = 0; i < 8 && !uploadForm; i++) {
        await delay(900);
        try {
          const taskResponse = await request({
            method: 'GET',
            url: `${FREECONVERT_API}/process/tasks?job=${encodeURIComponent(jobId)}&per_page=200`,
            timeout: 20000,
            headers: { 'Authorization': `Bearer ${config.freeConvertToken}`, 'Accept': 'application/json' }
          });
          const taskData = parseResponse(taskResponse, 'FreeConvert');
          const list = findTaskList(taskData);
          const task = list.find(entry => entry.name === 'import-source' || entry.operation === 'import/upload');
          uploadForm = task?.result?.form || task?.form || null;
        } catch (error) {
          logDebug('FreeConvert waiting for upload form', error.message || error);
        }
      }
    }

    if (!uploadForm?.url || !uploadForm?.parameters) {
      throw new Error('FreeConvert не выдал форму загрузки. Проверь токен и доступ к API.');
    }

    const uploadData = new FormData();
    for (const [key, value] of Object.entries(uploadForm.parameters)) uploadData.append(key, String(value));
    uploadData.append('file', file, file.name || `source.${inputFormat}`);

    setStatus(`Загружаю файл в FreeConvert (${formatBytes(file.size)})…`, 'info', true);
    await request({
      method: 'POST',
      url: uploadForm.url,
      data: uploadData,
      timeout: 180000,
      headers: { 'Accept': '*/*' }
    });
    logDebug('FreeConvert upload complete', jobId);

    let exportUrl = '';
    let taskError = '';
    let done = false;

    for (let attempt = 0; attempt < 180; attempt++) {
      await delay(2000);
      const statusResponse = await request({
        method: 'GET',
        url: `${FREECONVERT_API}/process/tasks?job=${encodeURIComponent(jobId)}&per_page=200`,
        timeout: 25000,
        headers: { 'Authorization': `Bearer ${config.freeConvertToken}`, 'Accept': 'application/json' }
      });
      const statusPayload = parseResponse(statusResponse, 'FreeConvert');
      const tasks = findTaskList(statusPayload);
      const convertTask = tasks.find(task => task.name === 'convert-media' || task.operation === 'convert');
      const exportTask = tasks.find(task => task.name === 'export-media' || task.operation === 'export/url');
      const allFailed = tasks.find(task => ['failed', 'error', 'canceled'].includes(String(task.status || '').toLowerCase()));

      if (allFailed) {
        taskError = allFailed.message || allFailed.msg || allFailed.result?.msg || allFailed.result?.errorCode || allFailed.error || allFailed.code || `${allFailed.name || allFailed.operation} завершился со статусом ${allFailed.status}`;
        break;
      }

      if (exportTask && ['completed', 'finished', 'success'].includes(String(exportTask.status || '').toLowerCase())) {
        exportUrl = exportTask.result?.url || exportTask.result?.files?.[0]?.url || exportTask.result?.file?.url || exportTask.url || '';
        if (exportUrl) { done = true; break; }
      }

      // Some API builds expose export result at the job root or in the completed convert task.
      const root = statusPayload.data || statusPayload;
      exportUrl = exportUrl || root.result?.url || convertTask?.result?.url || '';
      if (exportUrl && ['completed', 'finished', 'success'].includes(String(root.status || convertTask?.status || '').toLowerCase())) {
        done = true;
        break;
      }

      if (attempt % 5 === 0) {
        setStatus(`Обработка FreeConvert… ${Math.min(99, Math.round((attempt / 180) * 100))}%`, 'info', true);
      }
    }

    if (taskError) throw new Error(`FreeConvert: ${taskError}`);
    if (!done || !exportUrl) {
      throw new Error('FreeConvert не завершил задачу за 6 минут. Проверь API-лимит или выбери другой формат в настройках.');
    }

    setStatus('Скачиваю обработанный файл…', 'info', true);
    const blob = await requestBlob(exportUrl, 180000);
    if (!blob.size) throw new Error('FreeConvert вернул пустой файл.');

    const typeMap = {
      webp: 'image/webp', gif: 'image/gif', png: 'image/png', jpg: 'image/jpeg', jpeg: 'image/jpeg',
      webm: 'video/webm', mp4: 'video/mp4'
    };
    const type = typeMap[outputFormat] || 'application/octet-stream';
    logDebug('FreeConvert job finished', { jobId, outputFormat, bytes: blob.size, type });
    return new File([blob], outName, { type, lastModified: Date.now() });
  }

  function rendiHeaders(apiKey, json = false) {
    return json
      ? { 'X-API-KEY': apiKey, 'Accept': 'application/json', 'Content-Type': 'application/json' }
      : { 'X-API-KEY': apiKey, 'Accept': 'application/json' };
  }

  async function waitForRendiStoredFile(fileId, apiKey) {
    for (let attempt = 0; attempt < 90; attempt++) {
      const response = await request({
        method: 'GET', url: `${RENDI_API}/files/${encodeURIComponent(fileId)}`,
        timeout: 25000, headers: rendiHeaders(apiKey)
      });
      const file = parseResponse(response, 'Rendi file');
      if (String(file.status || '').toUpperCase() === 'STORED' && file.storage_url) return file;
      if (['FAILED', 'ERROR', 'CANCELED', 'CANCELLED'].includes(String(file.status || '').toUpperCase())) {
        throw new Error(`Rendi не сохранил исходный файл: ${file.error || file.detail || file.status}.`);
      }
      await delay(1000);
    }
    throw new Error('Rendi не подготовил загруженный файл за отведённое время.');
  }

  async function rendiVideoToWebp(file, maxWidth = loadConfig().maxWidth) {
    const config = loadConfig();
    if (!config.rendiApiKey) {
      throw new Error('Для конвертации видео в WebP через Rendi укажи Rendi API key в настройках → Конвертация.');
    }

    const inputName = file.name || `source.${fileExtension(file) || 'mp4'}`;
    setStatus(`Подготавливаю «${inputName}» для Rendi…`, 'info', true);
    const initResponse = await request({
      method: 'POST', url: `${RENDI_API}/files/init-upload`, timeout: 35000,
      headers: rendiHeaders(config.rendiApiKey, true),
      data: JSON.stringify({ filename: inputName, size_bytes: file.size })
    });
    const init = parseResponse(initResponse, 'Rendi upload');
    if (!init.file_id || !Number(init.part_size) || !Array.isArray(init.upload_urls) || !init.upload_urls.length) {
      throw new Error('Rendi не вернул параметры multipart-загрузки.');
    }

    const uploadedParts = [];
    for (let index = 0; index < init.upload_urls.length; index++) {
      const start = index * init.part_size;
      const chunk = file.slice(start, Math.min(start + init.part_size, file.size));
      setStatus(`Загружаю в Rendi: часть ${index + 1}/${init.upload_urls.length}…`, 'info', true);
      // The presigned upload URL is used directly by the browser. Rendi exposes
      // the ETag header for this documented multipart completion flow, so this
      // does not require an all-sites userscript network permission.
      const partResponse = await fetch(init.upload_urls[index], { method: 'PUT', body: chunk });
      if (!partResponse.ok) throw new Error(`Rendi отклонил часть ${index + 1} (HTTP ${partResponse.status}).`);
      const etag = String(partResponse.headers.get('etag') || '').replace(/^"|"$/g, '');
      if (!etag) throw new Error(`Rendi не вернул ETag для части ${index + 1}.`);
      uploadedParts.push({ part_number: index + 1, etag });
    }

    const completeResponse = await request({
      method: 'POST', url: `${RENDI_API}/files/${encodeURIComponent(init.file_id)}/complete-upload`, timeout: 35000,
      headers: rendiHeaders(config.rendiApiKey, true), data: JSON.stringify({ parts: uploadedParts })
    });
    const completed = parseResponse(completeResponse, 'Rendi upload completion');
    const stored = completed.storage_url ? completed : await waitForRendiStoredFile(init.file_id, config.rendiApiKey);
    if (!stored.storage_url) throw new Error('Rendi не вернул URL загруженного видео.');

    const baseName = String(inputName).replace(/\.[^.]+$/, '') || 'video';
    const outputName = `${baseName}.webp`;
    const width = clampInt(maxWidth, 100, 4000, 480);
    // -loop 0 is FFmpeg's infinite-loop value for animated WebP.
    const ffmpegCommand = `-i {{in_1}} -vf "fps=12,scale='min(iw,${width})':-2:flags=lanczos" -an -c:v libwebp -q:v 70 -loop 0 {{out_1}}`;
    setStatus('Запускаю конвертацию видео в анимированный WebP через Rendi…', 'info', true);
    const commandResponse = await request({
      method: 'POST', url: `${RENDI_API}/run-ffmpeg-command`, timeout: 35000,
      headers: rendiHeaders(config.rendiApiKey, true),
      data: JSON.stringify({
        input_files: { in_1: stored.storage_url },
        output_files: { out_1: outputName },
        ffmpeg_command: ffmpegCommand
      })
    });
    const command = parseResponse(commandResponse, 'Rendi command');
    if (!command.command_id) throw new Error('Rendi не вернул ID команды.');

    let outputUrl = '';
    for (let attempt = 0; attempt < 180; attempt++) {
      await delay(2000);
      const statusResponse = await request({
        method: 'GET', url: `${RENDI_API}/commands/${encodeURIComponent(command.command_id)}`,
        timeout: 25000, headers: rendiHeaders(config.rendiApiKey)
      });
      const status = parseResponse(statusResponse, 'Rendi command status');
      const state = String(status.status || '').toUpperCase();
      if (['FAILED', 'ERROR', 'CANCELED', 'CANCELLED'].includes(state)) {
        throw new Error(`Rendi: ${status.error || status.detail || status.message || state}.`);
      }
      if (state === 'SUCCESS') {
        outputUrl = status.output_files?.out_1?.storage_url || '';
        if (!outputUrl) throw new Error('Rendi завершил конвертацию без URL результата.');
        break;
      }
      if (attempt % 5 === 0) setStatus('Rendi обрабатывает видео…', 'info', true);
    }
    if (!outputUrl) throw new Error('Rendi не завершил конвертацию за 6 минут.');

    setStatus('Скачиваю WebP из Rendi…', 'info', true);
    const blob = await requestBlob(outputUrl, 180000);
    if (!blob.size) throw new Error('Rendi вернул пустой WebP-файл.');
    logDebug('Rendi WebP conversion finished', { commandId: command.command_id, bytes: blob.size, width });
    return new File([blob], outputName, { type: 'image/webp', lastModified: Date.now() });
  }

  function formatBytes(bytes) {
    if (!Number.isFinite(bytes)) return '';
    if (bytes < 1024) return `${bytes} Б`;
    if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} КБ`;
    return `${(bytes / (1024 * 1024)).toFixed(1)} МБ`;
  }

  async function prepareUpload(file) {
    if (!file || !file.size) throw new Error('Файл пустой.');
    if (file.size > MAX_FILE_BYTES) throw new Error(`Файл больше ${formatBytes(MAX_FILE_BYTES)}. Уменьши его перед загрузкой.`);

    const mime = mimeFromFile(file);
    if (!mime || (!mime.startsWith('image/') && !mime.startsWith('video/'))) {
      throw new Error('Поддерживаются изображения, GIF и видео.');
    }

    const config = loadConfig();
    const category = mime.startsWith('video/') ? 'video'
      : (mime === 'image/gif' || /\.gif$/i.test(file.name || '') ? 'gif' : 'image');
    const target = config.conversionRules[category] || 'webp';
    const sourceExt = fileExtension(file);
    const sourceCategoryFormat = sourceExt === 'jpeg' ? 'jpg' : sourceExt;

    if (target === 'keep') {
      if (category === 'image') {
        return resizeStaticImage(file, config.maxWidth, 'keep');
      }
      if (category === 'gif') {
        const dimensions = await getGifDimensions(file);
        if (dimensions.width > config.maxWidth) {
          if (!config.freeConvertToken) throw new Error(`GIF шире ${config.maxWidth}px. Для изменения размера укажи FreeConvert API-токен или выбери конвертацию в настройках.`);
          return freeConvertFile(file, 'gif', config.maxWidth);
        }
      }
      return file;
    }

    // Small static images can be processed locally; no API credits and no main-thread animation decoding.
    if (category === 'image' && ['webp', 'png', 'jpg'].includes(target)) {
      return resizeStaticImage(file, config.maxWidth, target);
    }

    if (category === 'gif' && target === 'gif') {
      const dimensions = await getGifDimensions(file);
      if (dimensions.width <= config.maxWidth) return file;
    }

    const extForTarget = target === 'jpg' ? 'jpg' : target;
    if (sourceCategoryFormat === extForTarget && category !== 'video') {
      if (category === 'gif') {
        const dimensions = await getGifDimensions(file);
        if (dimensions.width <= config.maxWidth) return file;
      } else {
        return resizeStaticImage(file, config.maxWidth, target);
      }
    }

    // Rendi is purpose-built here for video → animated WebP. Other conversion
    // rules retain the existing FreeConvert behavior.
    if (category === 'video' && target === 'webp' && config.rendiApiKey) {
      return rendiVideoToWebp(file, config.maxWidth);
    }
    return freeConvertFile(file, target, config.maxWidth);
  }

  function addItem(url, name, type, sourceKey = '', previewUrl = '') {
    const data = loadData();
    const normalizedUrl = String(url || '').trim();
    const normalizedPreview = String(previewUrl || normalizedUrl).trim();
    const existing = data.items.find(item =>
      item.url === normalizedUrl ||
      (sourceKey && item.sourceKey === sourceKey) ||
      (normalizedPreview && item.previewUrl === normalizedPreview)
    );
    if (existing) {
      setStatus('Это медиа уже есть в галерее.', 'info');
      return false;
    }

    const now = Date.now();
    data.items.push({
      id: makeId(),
      url: normalizedUrl,
      previewUrl: normalizedPreview,
      name: String(name || 'Медиафайл').slice(0, 120),
      type: type || 'image',
      sourceKey: String(sourceKey || ''),
      addedAt: now,
      updatedAt: now
    });
    galleryPage = 0;
    persistData(data);
    setStatus('Добавлено в коллекцию.', 'success');
    return true;
  }

  function persistData(data, doSync = true) {
    const normalized = sortData(data);
    const previous = loadData();
    const changed = dataSignature(previous) !== dataSignature(normalized);

    // Do not rebuild the gallery when a background Gist read returns the same data.
    // Keeping the existing image/video nodes alive avoids needless reloads after tab inactivity.
    if (changed) {
      GM_setValue(DATA_KEY, normalized);
      if (isPanelOpen() && panelView === 'gallery') renderGalleryItems();
    }

    if (doSync && changed) {
      const cfg = loadConfig();
      if (cfg.gistToken && cfg.gistId) queueSync();
    }
  }

  function isPanelOpen() {
    const panel = document.getElementById('twgif-panel');
    return Boolean(panel && !panel.hidden);
  }

  function waitForImage(url, timeoutMs = 12000) {
    return new Promise((resolve, reject) => {
      const image = new Image();
      let settled = false;
      const timer = setTimeout(() => finish(new Error('Ссылка не загрузилась за 12 секунд. Нужна прямая ссылка на файл.')), timeoutMs);
      function finish(error, value) {
        if (settled) return;
        settled = true;
        clearTimeout(timer);
        image.onload = null;
        image.onerror = null;
        error ? reject(error) : resolve(value);
      }
      image.onload = () => image.naturalWidth && image.naturalHeight
        ? finish(null, { width: image.naturalWidth, height: image.naturalHeight })
        : finish(new Error('По ссылке нет изображения.'));
      image.onerror = () => finish(new Error('Не удалось открыть изображение по этой ссылке. Используй прямую ссылку на файл.'));
      image.src = url;
    });
  }

  function parse7TVEmoteId(url) {
    if (!url || !/(^|\.)7tv\.app$/i.test(url.hostname)) return '';
    const match = url.pathname.match(/^\/emotes?\/([a-z0-9]{20,32})\/?$/i);
    return match ? match[1] : '';
  }

  async function resolve7TVEmote(url) {
    const id = parse7TVEmoteId(url);
    if (!id) return null;

    setStatus('Получаю прямую ссылку на эмоут 7TV…', 'info', true);
    logDebug('7TV emote link detected', { id });

    let emote = null;
    try {
      const response = await request({
        method: 'GET',
        url: `https://7tv.io/v3/emotes/${encodeURIComponent(id)}`,
        timeout: 18000,
        headers: { 'Accept': 'application/json' }
      });
      const payload = parseResponse(response, '7TV API');
      emote = payload.data || payload;
    } catch (error) {
      logDebug('7TV API request failed; trying CDN fallback', error);
    }

    if (emote && emote.host && emote.host.url) {
      const rawBase = String(emote.host.url);
      const base = rawBase.startsWith('//')
        ? `https:${rawBase}`
        : (/^https?:\/\//i.test(rawBase) ? rawBase : `https://${rawBase.replace(/^\/+/, '')}`);
      const files = Array.isArray(emote.host.files) ? emote.host.files : [];
      const supported = files.filter(file => file && typeof file.name === 'string' && /\.(webp|gif|png|avif|jpeg|jpg)$/i.test(file.name));
      const rank = file => {
        const name = String(file.name || '').toLowerCase();
        const width = Number(file.width) || Number((name.match(/(\d+)x/) || [])[1]) || 0;
        const format = String(file.format || '').toLowerCase();
        const preference = format === 'webp' || name.endsWith('.webp') ? 30
          : format === 'gif' || name.endsWith('.gif') ? 20
          : format === 'png' || name.endsWith('.png') ? 10 : 0;
        return width * 100 + preference;
      };
      supported.sort((a, b) => rank(b) - rank(a));
      if (supported[0]) {
        const direct = `${base.replace(/\/+$/, '')}/${String(supported[0].name).replace(/^\/+/, '')}`;
        return {
          url: direct,
          name: String(emote.name || `7TV ${id}`),
          type: emote.animated ? 'gif' : 'image',
          emoteId: id
        };
      }
    }

    // Standard public CDN fallback for temporary API failures.
    const fallbackUrl = `https://cdn.7tv.app/emote/${encodeURIComponent(id)}/3x.webp`;
    try {
      await waitForImage(fallbackUrl, 10000);
      return { url: fallbackUrl, name: `7TV ${id}`, type: 'image', emoteId: id };
    } catch (_) {
      throw new Error('Не удалось получить файл эмоута из 7TV. Проверь ссылку или доступ к 7tv.io.');
    }
  }

  async function addUrl(rawUrl, customName = '') {
    const text = String(rawUrl || '').trim().replace(/^<|>$/g, '');
    let parsed;
    try { parsed = new URL(text); }
    catch (_) { throw new Error('Вставь прямую ссылку на медиа или ссылку 7TV вида https://7tv.app/emotes/ID.'); }
    if (!['https:', 'http:'].includes(parsed.protocol)) throw new Error('Разрешены только HTTP- и HTTPS-ссылки.');

    // Keep the user's original 7TV page URL as the item/link inserted into chat.
    // Resolve a CDN URL only for the gallery preview.
    const originalUrl = parsed.toString();
    const sevenTv = parse7TVEmoteId(parsed) ? await resolve7TVEmote(parsed) : null;
    const previewUrl = sevenTv ? sevenTv.url : originalUrl;
    const type = sevenTv ? sevenTv.type : mediaTypeFromUrl(originalUrl);
    if (type !== 'video') await waitForImage(previewUrl);

    let name = String(customName || '').trim();
    if (!name && sevenTv) name = sevenTv.name;
    if (!name) {
      try { name = decodeURIComponent(new URL(originalUrl).pathname.split('/').filter(Boolean).pop() || new URL(originalUrl).hostname).slice(0, 120); }
      catch (_) { name = 'Медиафайл'; }
    }

    addItem(originalUrl, name, type, '', previewUrl);
  }

  function fileFingerprint(file) {
    return [String(file.name || ''), String(file.size || 0), String(file.lastModified || 0), String(file.type || '')].join('|');
  }

  async function processSingleFile(file, sourceKey) {
    try {
      setStatus(`Подготавливаю «${file.name || 'медиа'}»…`, 'info', true);
      const prepared = await prepareUpload(file);
      setStatus(`Загружаю «${prepared.name || file.name}» на kappa.lol…`, 'info', true);
      const uploaded = await uploadToKappa(prepared);
      const ext = fileExtension(prepared);
      const type = ext === 'gif' ? 'gif'
        : ['webm', 'mp4', 'mov', 'mkv', 'avi'].includes(ext) ? 'video' : 'image';
      addItem(uploaded.url, prepared.name || file.name || 'Медиафайл', type, sourceKey, uploaded.url);
      setStatus(`Готово: ${prepared.name || file.name} загружен на kappa.lol.`, 'success');
      return true;
    } catch (error) {
      logDebug('File processing failed', file.name, error);
      setStatus(`${file.name || 'Файл'}: ${error.message || error}`, 'error', true);
      return false;
    }
  }

  async function processFiles(fileList) {
    const files = Array.from(fileList || []).filter(file => {
      const mime = mimeFromFile(file);
      return mime.startsWith('image/') || mime.startsWith('video/');
    });
    if (!files.length) {
      setStatus('Буфер или перетаскивание не содержат изображение или видео.', 'error');
      return;
    }

    for (const file of files) {
      const key = fileFingerprint(file);
      const now = Date.now();
      for (const [fingerprint, expiresAt] of recentFileFingerprints) {
        if (expiresAt <= now) recentFileFingerprints.delete(fingerprint);
      }
      if (loadData().items.some(item => item.sourceKey && item.sourceKey === key)) {
        logDebug('File fingerprint already exists in collection; upload skipped', { name: file.name, size: file.size });
        setStatus(`«${file.name || 'Файл'}» уже есть в галерее — повторная загрузка пропущена.`, 'info');
        recentFileFingerprints.set(key, Date.now() + 20000);
        continue;
      }
      if (processingFiles.has(key)) {
        logDebug('Duplicate file event ignored while processing', { name: file.name, size: file.size });
        continue;
      }
      if ((recentFileFingerprints.get(key) || 0) > now) {
        logDebug('Repeated file event ignored after success', { name: file.name, size: file.size });
        continue;
      }

      // Register before the first await so a bubbling/duplicate event cannot
      // create a second converter job and a second Kappa upload.
      const task = processSingleFile(file, key);
      processingFiles.set(key, task);
      let succeeded = false;
      try {
        succeeded = await task;
      } finally {
        processingFiles.delete(key);
        if (succeeded) recentFileFingerprints.set(key, Date.now() + 20000);
      }
    }
  }

  function deleteItem(id) {
    const data = loadData();
    const item = data.items.find(entry => entry.id === id);
    if (!item) return;
    data.items = data.items.filter(entry => entry.id !== id);
    data.deleted[id] = Date.now();
    const cachedCard = mediaCardCache.get(id);
    if (cachedCard) cachedCard.remove();
    mediaCardCache.delete(id);
    persistData(data);
    setStatus('Удалено из галереи.', 'success');
  }

  // ----- Twitch composer integration -----

  function getChatInput() {
    const selectors = [
      '[data-a-target="chat-input"][contenteditable="true"]',
      '[data-a-target="chat-input"][role="textbox"]',
      '[data-a-target="chat-input"] textarea',
      'textarea[data-a-target="chat-input"]',
      '[contenteditable="true"][data-slate-editor="true"]',
      '[contenteditable="true"][role="textbox"][aria-label*="Send a message"]'
    ];
    for (const selector of selectors) {
      const element = document.querySelector(selector);
      if (element && element.isConnected && element.getClientRects().length && !element.closest('#twgif-panel')) return element;
    }
    return null;
  }

  function isEditor(element) {
    return Boolean(element && (
      element instanceof HTMLTextAreaElement || element instanceof HTMLInputElement ||
      element.isContentEditable || element.getAttribute('contenteditable') === 'true' ||
      element.getAttribute('role') === 'textbox'
    ));
  }

  function getEditorText(editor) {
    if (!editor) return '';
    if (editor instanceof HTMLInputElement || editor instanceof HTMLTextAreaElement) return editor.value;
    return editor.innerText ?? editor.textContent ?? '';
  }

  function selectionOffset(editor, range) {
    try {
      const before = range.cloneRange();
      before.selectNodeContents(editor);
      before.setEnd(range.startContainer, range.startOffset);
      return before.toString().length;
    } catch (_) {
      return null;
    }
  }

  function captureComposerSelection() {
    const editor = getChatInput();
    if (!editor || !isEditor(editor)) return;
    activeComposer = editor;
    const selection = window.getSelection && window.getSelection();
    if (selection && selection.rangeCount) {
      const range = selection.getRangeAt(0);
      if (editor.contains(range.startContainer) || range.startContainer === editor) {
        savedComposerRange = range.cloneRange();
        savedComposerOffset = selectionOffset(editor, range);
      }
    }
  }

  function makeRangeAtOffset(editor, offset) {
    if (!Number.isFinite(offset)) return null;
    const walker = document.createTreeWalker(editor, NodeFilter.SHOW_TEXT);
    let node;
    let left = Math.max(0, offset);
    let lastText = null;
    while ((node = walker.nextNode())) {
      lastText = node;
      const length = node.nodeValue.length;
      if (left <= length) {
        const range = document.createRange();
        range.setStart(node, left);
        range.collapse(true);
        return range;
      }
      left -= length;
    }
    const range = document.createRange();
    if (lastText) range.setStart(lastText, lastText.nodeValue.length);
    else {
      range.selectNodeContents(editor);
      range.collapse(false);
    }
    range.collapse(true);
    return range;
  }

  function restoreComposerSelection(editor) {
    if (!editor || !editor.isConnected) return false;
    try {
      const selection = window.getSelection();
      let range = null;
      if (savedComposerRange &&
          (editor.contains(savedComposerRange.startContainer) || savedComposerRange.startContainer === editor) &&
          (editor.contains(savedComposerRange.endContainer) || savedComposerRange.endContainer === editor)) {
        range = savedComposerRange.cloneRange();
      }
      if (!range && Number.isFinite(savedComposerOffset)) range = makeRangeAtOffset(editor, savedComposerOffset);
      if (!range && selection && selection.rangeCount && editor.contains(selection.getRangeAt(0).commonAncestorContainer)) {
        range = selection.getRangeAt(0).cloneRange();
      }
      if (!range) {
        range = document.createRange();
        range.selectNodeContents(editor);
        range.collapse(false);
      }
      editor.focus({ preventScroll: true });
      if (selection) {
        selection.removeAllRanges();
        selection.addRange(range);
      }
      savedComposerRange = range.cloneRange();
      savedComposerOffset = selectionOffset(editor, range);
      return true;
    } catch (error) {
      logDebug('Could not restore composer caret', error);
      return false;
    }
  }

  function prefixSuffixForEditor(editor, range, insertedText) {
    const currentText = getEditorText(editor).replace(/\u00a0/g, ' ');
    let offset = null;
    let selectedLength = 0;
    if (range && editor.isContentEditable) {
      offset = selectionOffset(editor, range);
      try { selectedLength = range.toString().length; } catch (_) {}
    } else if (editor instanceof HTMLTextAreaElement || editor instanceof HTMLInputElement) {
      offset = Number.isInteger(editor.selectionStart) ? editor.selectionStart : currentText.length;
      selectedLength = Number.isInteger(editor.selectionEnd) ? editor.selectionEnd - offset : 0;
    }
    if (!Number.isFinite(offset)) offset = currentText.length;
    const before = currentText.slice(0, offset);
    const after = currentText.slice(offset + Math.max(0, selectedLength));
    const prefix = before && !/\s$/.test(before) ? ' ' : '';
    const suffix = after && !/^\s/.test(after) ? ' ' : '';
    return prefix + insertedText + suffix;
  }

  function dispatchPaste(editor, text) {
    try {
      const data = new DataTransfer();
      data.setData('text/plain', text);
      const event = new ClipboardEvent('paste', {
        clipboardData: data,
        bubbles: true,
        cancelable: true
      });
      return editor.dispatchEvent(event);
    } catch (error) {
      logDebug('Synthetic paste unavailable', error);
      return false;
    }
  }

  function insertIntoPlainInput(editor, url) {
    const current = editor.value;
    const start = Number.isInteger(editor.selectionStart) ? editor.selectionStart : current.length;
    const end = Number.isInteger(editor.selectionEnd) ? editor.selectionEnd : start;
    const before = current.slice(0, start);
    const after = current.slice(end);
    const prefix = before && !/\s$/.test(before) ? ' ' : '';
    const suffix = after && !/^\s/.test(after) ? ' ' : '';
    const text = prefix + url + suffix;
    editor.focus({ preventScroll: true });
    try {
      editor.setRangeText(text, start, end, 'end');
    } catch (_) {
      const nativeSetter = Object.getOwnPropertyDescriptor(Object.getPrototypeOf(editor), 'value')?.set;
      if (nativeSetter) nativeSetter.call(editor, before + text + after);
      else editor.value = before + text + after;
    }
    editor.dispatchEvent(new InputEvent('input', { bubbles: true, inputType: 'insertText', data: text }));
    editor.dispatchEvent(new Event('change', { bubbles: true }));
    savedComposerOffset = start + text.length;
    return editor.value.includes(url);
  }

  async function insertLinkIntoChat(url) {
    const editor = getChatInput() || (activeComposer && activeComposer.isConnected ? activeComposer : null);
    if (!editor || !isEditor(editor)) {
      setStatus('Не нашёл поле ввода чата Twitch. Открой чат и повтори.', 'error', true);
      return false;
    }
    activeComposer = editor;
    logDebug('Insert link requested', { url, editor: editor.tagName, editable: editor.isContentEditable });

    if (editor instanceof HTMLTextAreaElement || editor instanceof HTMLInputElement) {
      captureComposerSelection();
      return insertIntoPlainInput(editor, url);
    }

    const initialText = getEditorText(editor);
    restoreComposerSelection(editor);
    const selection = window.getSelection();
    let range = selection && selection.rangeCount ? selection.getRangeAt(0) : null;
    const textToInsert = prefixSuffixForEditor(editor, range, url);

    // Twitch's Slate editor listens to paste/insertText events; editing innerHTML directly
    // produces the familiar ghost text where the placeholder/send button state is wrong.
    dispatchPaste(editor, textToInsert);
    await new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve)));
    let after = getEditorText(editor);
    if (after !== initialText && after.includes(url)) {
      captureComposerSelection();
      setStatus('Ссылка вставлена в чат. Нажми Enter для отправки.', 'success');
      return true;
    }

    // A native editing command is the next-best fallback for Slate/ProseMirror-like editors.
    restoreComposerSelection(editor);
    let commandWorked = false;
    try { commandWorked = document.execCommand('insertText', false, textToInsert); }
    catch (_) { commandWorked = false; }
    editor.dispatchEvent(new InputEvent('input', { bubbles: true, inputType: 'insertText', data: textToInsert }));
    await new Promise(resolve => requestAnimationFrame(resolve));
    after = getEditorText(editor);
    if (after !== initialText && after.includes(url)) {
      captureComposerSelection();
      setStatus('Ссылка вставлена в чат. Нажми Enter для отправки.', 'success');
      return true;
    }

    // Final non-mutating fallback: ask React/Slate to process beforeinput; never write DOM text directly.
    restoreComposerSelection(editor);
    try {
      editor.dispatchEvent(new InputEvent('beforeinput', {
        bubbles: true, cancelable: true, inputType: 'insertText', data: textToInsert
      }));
      editor.dispatchEvent(new InputEvent('input', {
        bubbles: true, inputType: 'insertText', data: textToInsert
      }));
    } catch (_) {}
    await new Promise(resolve => requestAnimationFrame(resolve));
    after = getEditorText(editor);
    if (after !== initialText && after.includes(url)) {
      captureComposerSelection();
      setStatus('Ссылка вставлена в чат. Нажми Enter для отправки.', 'success');
      return true;
    }

    setStatus('Twitch не принял вставку через редактор. Ничего не было отправлено; попробуй ещё раз.', 'error', true);
    logDebug('Insert failed; editor text unchanged', { before: initialText.slice(-120), after: after.slice(-120) });
    return false;
  }

  // ----- GitHub Gist sync -----

  async function createGist(config, data) {
    const response = await request({
      method: 'POST', url: `${GITHUB_API}/gists`, timeout: 35000,
      headers: {
        'Accept': 'application/vnd.github+json',
        'Authorization': `Bearer ${config.gistToken}`,
        'X-GitHub-Api-Version': '2022-11-28',
        'Content-Type': 'application/json'
      },
      data: JSON.stringify({
        description: 'Twitch GIF Gallery sync',
        public: false,
        files: { [SYNC_FILENAME]: { content: JSON.stringify(sortData(data), null, 2) } }
      })
    });
    const payload = parseResponse(response, 'GitHub Gist');
    if (!payload.id) throw new Error('GitHub не вернул ID Gist.');
    return payload.id;
  }

  async function getRemoteData(config) {
    const response = await request({
      method: 'GET', url: `${GITHUB_API}/gists/${encodeURIComponent(config.gistId)}`, timeout: 35000,
      headers: {
        'Accept': 'application/vnd.github+json',
        'Authorization': `Bearer ${config.gistToken}`,
        'X-GitHub-Api-Version': '2022-11-28'
      }
    });
    const payload = parseResponse(response, 'GitHub Gist');
    const file = payload.files && payload.files[SYNC_FILENAME];
    if (!file) return EMPTY_DATA();
    let content = file.content;
    if (file.truncated && file.raw_url) {
      const rawResponse = await request({ method: 'GET', url: file.raw_url, timeout: 35000,
        headers: { 'Authorization': `Bearer ${config.gistToken}` } });
      content = rawResponse.responseText;
    }
    const parsed = parseJson(content, null);
    if (!parsed || !Array.isArray(parsed.items)) throw new Error('В Gist не найден файл коллекции в ожидаемом формате.');
    return parseDataForMerge(parsed);
  }

  function parseDataForMerge(raw) {
    const clean = EMPTY_DATA();
    clean.items = Array.isArray(raw.items) ? raw.items.filter(x => x && typeof x.id === 'string' && typeof x.url === 'string') : [];
    clean.deleted = raw.deleted && typeof raw.deleted === 'object' ? raw.deleted : {};
    return clean;
  }

  async function writeRemoteData(config, data) {
    const response = await request({
      method: 'PATCH', url: `${GITHUB_API}/gists/${encodeURIComponent(config.gistId)}`, timeout: 35000,
      headers: {
        'Accept': 'application/vnd.github+json',
        'Authorization': `Bearer ${config.gistToken}`,
        'X-GitHub-Api-Version': '2022-11-28',
        'Content-Type': 'application/json'
      },
      data: JSON.stringify({ files: { [SYNC_FILENAME]: { content: JSON.stringify(sortData(data), null, 2) } } })
    });
    return parseResponse(response, 'GitHub Gist');
  }


  function syncableSettings(config = loadConfig()) {
    return {
      maxWidth: config.maxWidth,
      mediaScale: config.mediaScale,
      tileView: config.tileView,
      pageSize: config.pageSize,
      previewScale: config.previewScale,
      conversionRules: { ...config.conversionRules },
      freeConvertToken: config.freeConvertToken,
      // Rendi credentials are intentionally local-only and must never be copied to a Gist.
      debug: config.debug,
      settingsUpdatedAt: config.settingsUpdatedAt || 0,
      settingsSchemaVersion: SETTINGS_SCHEMA_VERSION
    };
  }


  async function readGistFile(config, filename) {
    const response = await request({
      method: 'GET', url: `${GITHUB_API}/gists/${encodeURIComponent(config.gistId)}`, timeout: 35000,
      headers: {
        'Accept': 'application/vnd.github+json',
        'Authorization': `Bearer ${config.gistToken}`,
        'X-GitHub-Api-Version': '2022-11-28'
      }
    });
    const payload = parseResponse(response, 'GitHub Gist');
    const file = payload.files && payload.files[filename];
    if (!file) return null;
    if (!file.truncated) return parseJson(file.content, null);
    if (!file.raw_url) return null;
    const rawResponse = await request({
      method: 'GET', url: file.raw_url, timeout: 35000,
      headers: { 'Authorization': `Bearer ${config.gistToken}` }
    });
    return parseJson(rawResponse.responseText, null);
  }

  async function writeGistFile(config, filename, content) {
    const response = await request({
      method: 'PATCH', url: `${GITHUB_API}/gists/${encodeURIComponent(config.gistId)}`, timeout: 35000,
      headers: {
        'Accept': 'application/vnd.github+json',
        'Authorization': `Bearer ${config.gistToken}`,
        'X-GitHub-Api-Version': '2022-11-28',
        'Content-Type': 'application/json'
      },
      data: JSON.stringify({ files: { [filename]: { content: JSON.stringify(content, null, 2) } } })
    });
    return parseResponse(response, 'GitHub Gist');
  }

  async function syncSettingsNow() {
    const config = loadConfig();
    if (!config.gistToken || !config.gistId) {
      throw new Error('Сначала сохрани GitHub token и ID Gist во вкладке синхронизации.');
    }

    const remote = await readGistFile(config, SETTINGS_FILENAME);
    const localSnapshot = syncableSettings(config);

    if (!remote || !Number(remote.settingsUpdatedAt)) {
      await writeGistFile(config, SETTINGS_FILENAME, localSnapshot);
      setStatus('Настройки и FreeConvert API-токен отправлены в Gist.', 'success', true);
      return;
    }

    const remoteSchemaVersion = Number(remote.settingsSchemaVersion) || 0;
    if (remoteSchemaVersion < SETTINGS_SCHEMA_VERSION) {
      const remoteUpdatedAt = Number(remote.settingsUpdatedAt) || 0;
      const localUpdatedAt = Number(config.settingsUpdatedAt) || 0;

      // Prefer the newer local settings. If the remote snapshot is newer, migrate
      // it and publish the new schema so another device won't restore the old WebP default.
      if (localUpdatedAt > 0 && localUpdatedAt >= remoteUpdatedAt) {
        await writeGistFile(config, SETTINGS_FILENAME, localSnapshot);
        setStatus('Настройки синхронизированы. Старый формат Gist обновлён; видео теперь по умолчанию конвертируется в GIF.', 'success', true);
        return;
      }

      const migratedRules = {
        ...(remote.conversionRules && typeof remote.conversionRules === 'object' ? remote.conversionRules : {})
      };
      if (migratedRules.video === 'webp') migratedRules.video = 'gif';

      const migratedSettingsUpdatedAt = Date.now();
      saveConfig({
        ...remote,
        conversionRules: migratedRules,
        gistToken: config.gistToken,
        gistId: config.gistId,
        settingsUpdatedAt: migratedSettingsUpdatedAt,
        settingsSchemaVersion: SETTINGS_SCHEMA_VERSION
      });
      const migratedSnapshot = syncableSettings(loadConfig());
      await writeGistFile(config, SETTINGS_FILENAME, migratedSnapshot);
      setStatus('Настройки загружены из старого Gist и обновлены. Видео конвертируется в GIF.', 'success', true);
      logDebug('Settings schema migrated in Gist', { from: remoteSchemaVersion, to: SETTINGS_SCHEMA_VERSION });
      if (panelView === 'settings') renderSettings();
      return;
    }

    if (Number(remote.settingsUpdatedAt) > Number(config.settingsUpdatedAt || 0)) {
      // Pull the newest cloud settings, but never replace the local GitHub credential/Gist ID.
      saveConfig({
        ...remote,
        gistToken: config.gistToken,
        gistId: config.gistId,
        settingsUpdatedAt: Number(remote.settingsUpdatedAt)
      });
      const snapshot = loadConfig();
      GM_setValue(CONFIG_KEY, { ...snapshot, settingsUpdatedAt: Number(remote.settingsUpdatedAt) });
      setStatus('Настройки загружены из Gist, включая FreeConvert API-токен.', 'success', true);
      logDebug('Settings synced from Gist', { settingsUpdatedAt: remote.settingsUpdatedAt });
      if (panelView === 'settings') renderSettings();
    } else {
      await writeGistFile(config, SETTINGS_FILENAME, localSnapshot);
      setStatus('Текущие настройки, включая FreeConvert API-токен, синхронизированы.', 'success', true);
      logDebug('Settings synced to Gist', { settingsUpdatedAt: config.settingsUpdatedAt });
    }
  }


  async function performSyncOnce() {
    const config = loadConfig();
    if (!config.gistToken || !config.gistId) throw new Error('Сначала настрой GitHub token и ID Gist.');
    const remote = await getRemoteData(config);
    const local = loadData();
    const merged = mergeData(local, remote);
    persistData(merged, false);
    if (dataSignature(merged) !== dataSignature(remote)) await writeRemoteData(config, merged);
    setStatus(`Синхронизировано · ${merged.items.length} элементов.`, 'success');
    logDebug('Gist sync complete', { count: merged.items.length, gistId: config.gistId });
  }

  async function syncNow() {
    if (syncRunning) { syncAgain = true; return; }
    syncRunning = true;
    try {
      do { syncAgain = false; await performSyncOnce(); } while (syncAgain);
    } finally { syncRunning = false; }
  }

  function queueSync() {
    const config = loadConfig();
    if (!config.gistToken || !config.gistId) return;
    if (syncTimer) clearTimeout(syncTimer);
    syncTimer = setTimeout(() => syncNow().catch(error => {
      logDebug('Automatic Gist sync failed', error);
      setStatus(`Автосинхронизация: ${formatGitHubSyncError(error)}`, 'error', true);
    }), 1400);
  }

  // ----- UI -----

  function buildStyles() {
    if (document.getElementById('twgif-style')) return;
    const style = document.createElement('style');
    style.id = 'twgif-style';
    style.textContent = `
      #twgif-trigger{appearance:none!important;border:0!important;background:transparent!important;color:var(--color-text-base,#efeff1)!important;display:inline-flex!important;align-items:center!important;justify-content:center!important;flex:0 0 32px!important;width:32px!important;min-width:32px!important;height:32px!important;margin:0 2px!important;padding:0!important;border-radius:var(--border-radius-medium,4px)!important;cursor:pointer!important;line-height:1!important}
      #twgif-trigger:hover,#twgif-trigger[aria-expanded=true]{background:var(--color-background-button-text-hover,#2b2b2f)!important;color:var(--color-text-link,#bf94ff)!important}
      #twgif-trigger svg{display:block;pointer-events:none}
      #twgif-panel{position:fixed;z-index:2147483000;width:400px;max-width:calc(100vw - 16px);max-height:68vh;display:flex;flex-direction:column;overflow:hidden;color:#efeff1;background:#18181b;border:1px solid #34343b;border-radius:10px;box-shadow:0 10px 34px #0009;font:13px/1.4 Inter,system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;box-sizing:border-box;pointer-events:auto}
      #twgif-panel[hidden]{display:none!important}#twgif-panel *{box-sizing:border-box}
      .twgif-head{display:flex;align-items:center;gap:5px;padding:6px 8px;min-height:42px;border-bottom:1px solid #34343b;flex-shrink:0}
      .twgif-heading{font-size:13px;font-weight:700;flex:1;min-width:0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
      .twgif-head-btn{appearance:none;border:0;background:transparent;color:#c4c4cc;width:29px;height:29px;display:inline-flex;align-items:center;justify-content:center;padding:0;border-radius:6px;cursor:pointer;flex-shrink:0}
      .twgif-head-btn:hover{background:#303036;color:#fff}.twgif-head-btn[hidden]{display:none!important}
      .twgif-settings-tabs{display:flex;align-items:center;gap:1px}.twgif-settings-tabs[hidden]{display:none!important}
      .twgif-tab{appearance:none;border:0;background:transparent;color:#a8a8b3;width:28px;height:28px;border-radius:6px;display:inline-flex;align-items:center;justify-content:center;cursor:pointer;padding:0}
      .twgif-tab:hover{background:#303036;color:#fff}.twgif-tab[aria-selected=true]{background:#392653;color:#d6b4ff}
      .twgif-panel-body{padding:9px 10px 10px;overflow:auto;min-height:90px;overscroll-behavior:contain}
      .twgif-toolbar{display:flex;align-items:center;gap:5px;margin-bottom:8px}
      .twgif-input{display:block;width:100%;min-width:0;background:#0e0e10;color:#efeff1;border:1px solid #3f3f46;border-radius:6px;padding:8px 9px;outline:none;font-family:inherit;font-size:12px;line-height:1.35}
      .twgif-input:focus{border-color:#a970ff;box-shadow:0 0 0 1px #9147ff40}.twgif-url-input{flex:1 1 120px;width:100%}
      .twgif-count{color:#adadb8;white-space:nowrap;font-size:11px}
      .twgif-small-btn{appearance:none;border:1px solid #42424a;background:#252529;color:#efeff1;padding:7px 9px;border-radius:6px;cursor:pointer;font-family:inherit;font-size:11px;font-weight:500;line-height:1.2;white-space:nowrap}
      .twgif-small-btn:hover{background:#34343b;border-color:#65656e}.twgif-small-btn:disabled{opacity:.55;cursor:wait}
      .twgif-primary{background:#9147ff;border-color:#9147ff;color:#fff}.twgif-primary:hover{background:#772ce8;border-color:#772ce8}
      .twgif-toolbar-icon{width:30px;min-width:30px;height:30px;padding:0;display:inline-flex;align-items:center;justify-content:center;font-size:19px}
      .twgif-drop{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:6px 7px;margin-bottom:8px;border:1px dashed #41414b;border-radius:7px;color:#a8a8b3;font-size:10px}
      .twgif-drop strong{display:block;color:#d9d9df;font-size:10px;font-weight:600}.twgif-drop span{font-size:9px}.twgif-drop.twgif-drag{border-color:#a970ff;background:#9147ff1a}
      .twgif-masonry{columns:4 78px;column-gap:7px}.twgif-masonry.twgif-grid-mode{display:grid;grid-template-columns:repeat(auto-fill,minmax(var(--twgif-tile-min,76px),1fr));align-items:start;gap:7px}.twgif-masonry[hidden]{display:none!important}
      .twgif-card{display:inline-block;position:relative;width:100%;margin:0 0 7px;break-inside:avoid;vertical-align:top;border:1px solid #34343b;border-radius:6px;overflow:visible;background:#202024;cursor:pointer;outline:none;transition:border-color .12s,box-shadow .12s}
      .twgif-card[hidden]{display:none!important}.twgif-masonry.twgif-grid-mode .twgif-card{display:block;width:100%;margin:0;overflow:visible}
      .twgif-media-frame{position:relative;overflow:hidden;border-radius:5px;background:#101012;isolation:isolate}
      .twgif-media{display:block;width:100%;height:auto;max-width:100%;background:#101012;object-fit:contain}.twgif-masonry.twgif-grid-mode .twgif-media{width:100%;height:var(--twgif-thumb-height,90px);object-fit:contain}
      .twgif-media-error{min-height:44px;padding:10px;text-align:center;color:#9c9ca6;font-size:10px}
      .twgif-delete{position:absolute;z-index:3;top:-1px;right:-1px;display:flex;align-items:center;justify-content:center;width:17px;height:17px;padding:0;border:1px solid #ffffff26;border-radius:0 5px 0 6px;background:#18181beF;color:#f2f2f2;opacity:0;pointer-events:none;transition:opacity .13s,background .13s,transform .13s;cursor:pointer}
      .twgif-delete svg{width:10px;height:10px;display:block;pointer-events:none}.twgif-card:hover .twgif-delete,.twgif-card:focus-within .twgif-delete{opacity:1;pointer-events:auto}.twgif-delete:hover{background:#b42335;border-color:#ef4444;transform:scale(1.08)}
      .twgif-pagination{display:flex;align-items:center;justify-content:center;gap:10px;padding:9px 0 0}.twgif-pagination[hidden]{display:none!important}.twgif-page-label{font-size:10px;color:#b7b7c1;min-width:54px;text-align:center}
      .twgif-empty{padding:22px 8px;text-align:center;color:#a8a8b3;font-size:12px}.twgif-empty[hidden]{display:none}
      #twgif-status{padding:6px 10px 7px;border-top:1px solid #34343b;font-size:10px;color:#aaaab5;overflow-wrap:anywhere;flex-shrink:0}#twgif-status:empty{display:none}#twgif-status[data-type=success]{color:#55d995}#twgif-status[data-type=error]{color:#ff8585}
      .twgif-settings{display:flex;flex-direction:column;gap:7px}.twgif-section{border:1px solid #33333a;border-radius:7px;padding:8px}.twgif-section-title{margin:0 0 7px;font-size:11px;font-weight:700;color:#dddde5}.twgif-help{color:#a8a8b3;font-size:10px;line-height:1.45;margin:5px 0 0}.twgif-help a{color:#bf94ff;text-decoration:none}.twgif-help a:hover{text-decoration:underline}.twgif-field-label{display:block;margin:6px 0 4px;font-size:10px;color:#c8c8d0}.twgif-row{display:flex;align-items:center;gap:6px;flex-wrap:wrap}.twgif-row>.twgif-input{flex:1 1 145px}.twgif-check-row{display:flex;align-items:center;gap:7px;font-size:11px;color:#dbdbe2;margin:3px 0}.twgif-check-row input{accent-color:#9147ff}
      .twgif-debug-log{display:block;width:100%;min-height:78px;max-height:125px;resize:vertical;background:#0c0c0e;color:#bfc0cb;border:1px solid #36363d;border-radius:5px;padding:6px;font:10px/1.35 ui-monospace,Consolas,monospace}
      .twgif-chat-add{appearance:none!important;display:inline-flex!important;align-items:center!important;justify-content:center!important;vertical-align:middle!important;width:16px!important;height:16px!important;margin:0 0 0 4px!important;padding:0!important;border:1px solid #9147ff70!important;border-radius:4px!important;color:#d7b8ff!important;background:#18181bcc!important;font:700 12px/1 system-ui!important;cursor:pointer!important;opacity:.35;transition:opacity .12s,background .12s!important}.twgif-chat-add:hover{opacity:1!important;background:#9147ff!important;color:#fff!important}
      #twgif-hold-preview{position:fixed;z-index:2147483100;pointer-events:none;display:flex;align-items:center;justify-content:center;opacity:0;transform:scale(.88);transition:transform .18s ease,opacity .18s ease;filter:drop-shadow(0 12px 30px #000b);max-width:90vw;max-height:75vh}
      #twgif-hold-preview.twgif-preview-visible{opacity:1;transform:scale(1)}#twgif-hold-preview img,#twgif-hold-preview video{display:block;max-width:90vw;max-height:75vh;object-fit:contain;border:1px solid #ffffff33;border-radius:8px;background:#111}
      @media(max-width:500px){#twgif-panel{max-height:68vh}.twgif-masonry{columns:3 66px}.twgif-drop{align-items:flex-start;flex-direction:column}.twgif-head{gap:2px;padding-left:6px}.twgif-heading{font-size:12px}}
    `;
    document.head.appendChild(style);

    if (!document.getElementById('twgif-hold-preview')) {
      const preview = document.createElement('div');
      preview.id = 'twgif-hold-preview';
      document.body.appendChild(preview);
    }
  }

  function buildPanel() {
    if (document.getElementById('twgif-panel')) return;
    const panel = document.createElement('div');
    panel.id = 'twgif-panel';
    panel.hidden = true;
    panel.setAttribute('role', 'dialog');
    panel.setAttribute('aria-label', 'Коллекция GIF и изображений');
    panel.innerHTML = `
      <div class="twgif-head">
        <button id="twgif-settings-back-top" class="twgif-head-btn" type="button" title="Назад к галерее" aria-label="Назад" hidden>←</button>
        <div id="twgif-heading" class="twgif-heading">GIF и картинки</div>
        <div id="twgif-settings-tabs" class="twgif-settings-tabs" hidden>
          <button class="twgif-tab" type="button" data-tab="general" title="Вид и общие" aria-label="Общие настройки" aria-selected="false">◫</button>
          <button class="twgif-tab" type="button" data-tab="convert" title="Конвертация" aria-label="Настройки конвертации" aria-selected="false">⇄</button>
          <button class="twgif-tab" type="button" data-tab="sync" title="Синхронизация" aria-label="Синхронизация" aria-selected="false">☁</button>
          <button class="twgif-tab" type="button" data-tab="debug" title="Отладка" aria-label="Отладка" aria-selected="false">⌘</button>
        </div>
        <button id="twgif-settings-open" class="twgif-head-btn" type="button" title="Настройки" aria-label="Настройки">${SVG_SETTINGS}</button>
        <button id="twgif-close" class="twgif-head-btn" type="button" title="Закрыть" aria-label="Закрыть">${SVG_CLOSE}</button>
      </div>
      <div id="twgif-panel-body" class="twgif-panel-body"></div>
      <div id="twgif-status" role="status" aria-live="polite"></div>
    `;
    document.body.appendChild(panel);

    panel.querySelector('#twgif-close').addEventListener('click', closePanel);
    panel.querySelector('#twgif-settings-open').addEventListener('click', () => {
      settingsTab = 'general';
      panelView = 'settings';
      renderPanelView();
    });
    panel.querySelector('#twgif-settings-back-top').addEventListener('click', () => {
      panelView = 'gallery';
      renderPanelView();
    });
    panel.querySelectorAll('.twgif-tab').forEach(button => button.addEventListener('click', () => {
      settingsTab = button.dataset.tab || 'general';
      renderPanelView();
    }));

    panel.addEventListener('dragenter', event => {
      if (!panel.hidden && event.dataTransfer && Array.from(event.dataTransfer.types || []).includes('Files')) {
        event.preventDefault(); panel.classList.add('twgif-drag');
      }
    });
    panel.addEventListener('dragover', event => {
      if (!panel.hidden && event.dataTransfer && Array.from(event.dataTransfer.types || []).includes('Files')) {
        event.preventDefault(); panel.classList.add('twgif-drag');
      }
    });
    panel.addEventListener('dragleave', event => {
      if (!panel.contains(event.relatedTarget)) panel.classList.remove('twgif-drag');
    });
    panel.addEventListener('drop', async event => {
      if (panel.hidden || !event.dataTransfer) return;
      if (event.target?.closest?.('#twgif-drop')) return;
      const files = event.dataTransfer.files;
      if (!files?.length) return;
      event.preventDefault();
      event.stopPropagation();
      if (event.stopImmediatePropagation) event.stopImmediatePropagation();
      panel.classList.remove('twgif-drag');
      await processFiles(files);
    });
  }

  function getChatRegion(input) {
    return document.querySelector('[data-a-target="chat-room-component-layout"]') ||
      input?.closest('.chat-room') || input?.closest('[class*="chat-room"]') ||
      input?.closest('[data-a-target="chat-input-container"]')?.parentElement?.parentElement ||
      input?.parentElement?.parentElement?.parentElement || document.body;
  }

  function getToolbar(input) {
    return document.querySelector('.chat-input__buttons-container') ||
      input?.closest('[data-a-target="chat-input-container"]')?.parentElement?.querySelector('[class*="buttons-container"]') ||
      input?.closest('form')?.querySelector('[class*="buttons-container"]') || null;
  }

  function createTrigger() {
    const button = document.createElement('button');
    button.id = 'twgif-trigger';
    button.type = 'button';
    button.title = 'GIF и изображения';
    button.setAttribute('aria-label', 'Открыть коллекцию GIF и изображений');
    button.setAttribute('aria-haspopup', 'dialog');
    button.setAttribute('aria-expanded', 'false');
    button.innerHTML = SVG_GALLERY;
    button.addEventListener('pointerdown', captureComposerSelection, true);
    button.addEventListener('mousedown', captureComposerSelection, true);
    button.addEventListener('click', event => {
      event.preventDefault();
      event.stopPropagation();
      captureComposerSelection();
      if (isPanelOpen()) closePanel(); else openPanel(button);
    });
    return button;
  }

  function ensureTrigger() {
    const input = getChatInput();
    if (!input) return false;
    activeComposer = input;
    const toolbar = getToolbar(input);
    if (!toolbar) return false;

    let button = document.getElementById('twgif-trigger');
    if (!button) button = createTrigger();
    activeTrigger = button;

    const settingsButton = toolbar.querySelector('[data-a-target="chat-settings-button"], [aria-label*="Chat settings" i], [aria-label*="Настройки чата" i]');
    const rightGroup = settingsButton?.parentElement || toolbar.querySelector('[class*="buttons-right"]') || toolbar;

    // Put our icon immediately before chat settings (and next to channel points/emote buttons).
    if (settingsButton && settingsButton.parentElement === rightGroup) {
      if (button.parentElement !== rightGroup || button.nextElementSibling !== settingsButton) {
        rightGroup.insertBefore(button, settingsButton);
        logDebug('Picker button mounted left of chat settings', { toolbar: toolbar.className, group: rightGroup.className });
      }
    } else if (button.parentElement !== rightGroup) {
      rightGroup.insertBefore(button, rightGroup.firstChild);
      logDebug('Picker button mounted in chat toolbar', { toolbar: toolbar.className, group: rightGroup.className });
    }
    return true;
  }

  function scheduleEnsure() {
    if (ensureQueued) return;
    ensureQueued = true;
    requestAnimationFrame(() => {
      ensureQueued = false;
      if (!document.getElementById('twgif-trigger')?.isConnected) ensureTrigger();
      else if (activeTrigger && activeTrigger.parentElement) {
        const input = getChatInput();
        const toolbar = input && getToolbar(input);
        if (toolbar && !toolbar.contains(activeTrigger)) ensureTrigger();
      }
    });
  }

  function panelMetrics() {
    const panel = document.getElementById('twgif-panel');
    if (!panel || panel.hidden) return;
    const input = getChatInput() || activeComposer;
    if (!input || !input.isConnected) return;

    const inputRect = input.getBoundingClientRect();
    const region = getChatRegion(input);
    const regionRect = region.getBoundingClientRect
      ? region.getBoundingClientRect()
      : { left: 0, right: innerWidth, top: 0, bottom: innerHeight, width: innerWidth, height: innerHeight };

    const availableWidth = Math.max(250, Math.min(420, regionRect.width - 16, innerWidth - 16));
    panel.style.width = `${availableWidth}px`;
    const roomAbove = Math.max(120, inputRect.top - 12);
    panel.style.maxHeight = `${Math.max(120, Math.min(520, innerHeight * 0.68, roomAbove))}px`;

    const panelHeight = panel.getBoundingClientRect().height || Math.min(380, innerHeight * 0.55);
    const minLeft = Math.max(8, Math.min(innerWidth - availableWidth - 8, regionRect.left + 8));
    const maxLeft = Math.max(minLeft, Math.min(innerWidth - availableWidth - 8, regionRect.right - availableWidth - 8));
    // Align the panel's right edge with the input field's right edge.
    const left = Math.round(Math.min(maxLeft, Math.max(minLeft, inputRect.right - availableWidth)));

    // Keep the popup docked above the input. If the viewport is exceptionally short,
    // it stays above the input and becomes scrollable instead of jumping to the bottom.
    const top = Math.round(Math.max(8, Math.min(inputRect.top - panelHeight - 7, innerHeight - panelHeight - 8)));
    panel.style.left = `${left}px`;
    panel.style.top = `${top}px`;
  }

  function repositionPanel() {
    if (!isPanelOpen()) return;
    requestAnimationFrame(() => {
      panelMetrics();
      requestAnimationFrame(panelMetrics);
    });
  }

  function isMediaLink(rawUrl) {
    try {
      const url = new URL(rawUrl);
      if (!['http:', 'https:'].includes(url.protocol)) return false;
      if (parse7TVEmoteId(url)) return true;
      return /\.(png|jpe?g|gif|webp|avif|bmp|svg|webm|mp4|mov|mkv|avi|ogv)(?:$|[?#])/i.test(url.href);
    } catch (_) { return false; }
  }

  function addChatMediaButton(anchor) {
    if (!anchor || anchor.dataset.twgifDecorated === '1' || !isMediaLink(anchor.href)) return;
    if (!anchor.closest('[data-a-target="chat-line-message"], [data-a-target^="chat-line"], [class*="chat-line__message"]')) return;
    anchor.dataset.twgifDecorated = '1';
    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'twgif-chat-add';
    button.textContent = '+';
    button.title = 'Добавить медиа в GIF-галерею';
    button.setAttribute('aria-label', 'Добавить медиа в галерею');
    button.addEventListener('pointerdown', event => { event.preventDefault(); event.stopPropagation(); }, true);
    button.addEventListener('click', async event => {
      event.preventDefault(); event.stopPropagation();
      try {
        await addUrl(anchor.href);
        button.textContent = '✓';
        setTimeout(() => { if (button.isConnected) button.textContent = '+'; }, 1200);
      } catch (error) {
        setStatus(`Не удалось добавить ссылку из чата: ${error.message || error}`, 'error', true);
      }
    });
    anchor.insertAdjacentElement('afterend', button);
  }

  function decorateChatMedia(root) {
    if (!root || root.nodeType !== 1) return;
    const anchorList = [];
    if (root.matches?.('a[href]')) anchorList.push(root);
    anchorList.push(...(root.querySelectorAll?.('a[href]') || []));
    for (const anchor of anchorList) addChatMediaButton(anchor);
  }

  function queueChatMediaScan() {
    if (chatMediaScanQueued) return;
    chatMediaScanQueued = true;
    requestAnimationFrame(() => {
      chatMediaScanQueued = false;
      const root = document.querySelector('[data-a-target="chat-scrollable-area__message-container"]') || document.querySelector('[data-a-target="chat-room-component-layout"]');
      if (root) decorateChatMedia(root);
    });
  }

  function installChatMediaObserver() {
    if (chatMediaObserver) chatMediaObserver.disconnect();
    const root = document.querySelector('[data-a-target="chat-scrollable-area__message-container"]') || document.querySelector('[data-a-target="chat-room-component-layout"]');
    if (!root) return;
    decorateChatMedia(root);
    chatMediaObserver = new MutationObserver(records => {
      let shouldScan = false;
      for (const record of records) {
        for (const node of record.addedNodes || []) {
          if (node.nodeType === 1) {
            decorateChatMedia(node);
            shouldScan = true;
          }
        }
      }
      if (shouldScan) queueChatMediaScan();
    });
    chatMediaObserver.observe(root, { childList: true, subtree: true });
  }

  function openPanel(trigger) {
    buildPanel();
    activeTrigger = trigger || document.getElementById('twgif-trigger');
    panelView = 'gallery';
    const panel = document.getElementById('twgif-panel');
    panel.hidden = false;
    activeTrigger?.setAttribute('aria-expanded', 'true');
    renderPanelView();
    repositionPanel();
    if (loadConfig().gistToken && loadConfig().gistId) {
      syncNow().catch(error => setStatus(`Синхронизация: ${formatGitHubSyncError(error)}`, 'error', true));
    }
    logDebug('Panel opened');
  }

  function closePanel() {
    const panel = document.getElementById('twgif-panel');
    if (panel) panel.hidden = true;
    activeTrigger?.setAttribute('aria-expanded', 'false');
    logDebug('Panel closed');
  }

  function renderPanelView() {
    const panel = document.getElementById('twgif-panel');
    if (!panel) return;
    const heading = panel.querySelector('#twgif-heading');
    const settingsBack = panel.querySelector('#twgif-settings-back-top');
    const settingsTabs = panel.querySelector('#twgif-settings-tabs');
    const settingsOpen = panel.querySelector('#twgif-settings-open');

    const inSettings = panelView === 'settings';
    heading.textContent = inSettings ? 'Настройки' : 'GIF и картинки';
    settingsBack.hidden = !inSettings;
    settingsTabs.hidden = !inSettings;
    settingsOpen.hidden = inSettings;
    settingsTabs.querySelectorAll('.twgif-tab').forEach(button => {
      button.setAttribute('aria-selected', String(button.dataset.tab === settingsTab));
    });

    if (inSettings) {
      renderSettings();
    } else {
      const existingGallery = document.querySelector('#twgif-panel-body #twgif-masonry');
      if (existingGallery) {
        // Only update positions/pagination; do not rebuild the element tree.
        renderGalleryItems();
      } else {
        renderGallery();
      }
    }

    const status = document.getElementById('twgif-status');
    if (status) { status.textContent = lastStatus; status.dataset.type = lastStatusType; }
    repositionPanel();
  }

  function renderGallery() {
    const body = document.getElementById('twgif-panel-body');
    if (!body) return;
    body.innerHTML = `
      <div class="twgif-toolbar">
        <input id="twgif-url-input" class="twgif-input twgif-url-input" type="url" placeholder="Ссылка на медиа или эмоут 7TV…" autocomplete="url" aria-label="Ссылка для добавления">
        <button id="twgif-add-url" class="twgif-small-btn twgif-primary twgif-toolbar-icon" type="button" title="Добавить ссылку" aria-label="Добавить ссылку">+</button>
        <span id="twgif-count" class="twgif-count"></span>
      </div>
      <div id="twgif-drop" class="twgif-drop"><div><strong>Перетащи файлы или нажми Ctrl+V</strong><span>Медиа обрабатывается по правилам во вкладке конвертации</span></div><button id="twgif-file-pick" class="twgif-small-btn" type="button">Выбрать</button><input id="twgif-file-input" type="file" accept="image/*,video/*,.gif,.webm,.mp4,.mov,.mkv,.avi" multiple hidden></div>
      <div id="twgif-masonry" class="twgif-masonry"></div>
      <div id="twgif-empty" class="twgif-empty" hidden></div>
      <div id="twgif-pagination" class="twgif-pagination" hidden><button id="twgif-page-prev" class="twgif-small-btn" type="button">‹</button><span id="twgif-page-label" class="twgif-page-label"></span><button id="twgif-page-next" class="twgif-small-btn" type="button">›</button></div>
    `;

    const urlInput = body.querySelector('#twgif-url-input');
    const addButton = body.querySelector('#twgif-add-url');
    const addLink = async () => {
      const value = urlInput.value.trim();
      if (!value) { urlInput.focus(); return; }
      addButton.disabled = true;
      setStatus('Проверяю ссылку…', 'info', true);
      try {
        await addUrl(value);
        urlInput.value = '';
        urlInput.focus();
      } catch (error) {
        setStatus(error.message || String(error), 'error', true);
      } finally {
        addButton.disabled = false;
      }
    };
    addButton.addEventListener('click', addLink);
    urlInput.addEventListener('keydown', event => {
      if (event.key === 'Enter') { event.preventDefault(); addLink(); }
    });

    body.querySelector('#twgif-file-pick').addEventListener('click', () => body.querySelector('#twgif-file-input').click());
    body.querySelector('#twgif-file-input').addEventListener('change', async event => {
      await processFiles(event.target.files);
      event.target.value = '';
    });
    body.querySelector('#twgif-drop').addEventListener('dragover', event => {
      event.preventDefault(); event.stopPropagation(); event.currentTarget.classList.add('twgif-drag');
    });
    body.querySelector('#twgif-drop').addEventListener('dragleave', event => {
      if (!event.currentTarget.contains(event.relatedTarget)) event.currentTarget.classList.remove('twgif-drag');
    });
    body.querySelector('#twgif-drop').addEventListener('drop', async event => {
      event.preventDefault(); event.stopPropagation();
      if (event.stopImmediatePropagation) event.stopImmediatePropagation();
      event.currentTarget.classList.remove('twgif-drag');
      if (event.dataTransfer?.files?.length) {
        await processFiles(event.dataTransfer.files);
      } else {
        const uri = (event.dataTransfer?.getData('text/uri-list') || event.dataTransfer?.getData('text/plain') || '').trim();
        if (/^https?:\/\//i.test(uri)) {
          try { await addUrl(uri); }
          catch (error) { setStatus(error.message || String(error), 'error', true); }
        }
      }
    });

    renderGalleryItems();
  }

  function makeMediaCard(item) {
    const card = document.createElement('div');
    card.className = 'twgif-card';
    card.tabIndex = 0;
    card.setAttribute('role', 'button');
    card.setAttribute('aria-label', 'Вставить ссылку на медиа в чат');
    card.__twgifItem = item;

    const frame = document.createElement('div');
    frame.className = 'twgif-media-frame';
    const previewUrl = item.previewUrl || item.url;
    const isVideo = item.type === 'video' || /\.(webm|mp4|mov|mkv|avi)(?:$|\?)/i.test(previewUrl);
    let media;

    if (isVideo) {
      media = document.createElement('video');
      media.muted = true;
      media.loop = true;
      media.autoplay = true;
      media.playsInline = true;
      media.preload = 'none';
    } else {
      media = document.createElement('img');
      media.loading = 'eager';
      media.decoding = 'async';
      media.alt = '';
    }
    media.className = 'twgif-media';
    media.dataset.src = previewUrl;
    media.dataset.loadState = loadedMediaUrls.has(previewUrl) ? 'loaded' : 'pending';
    if (loadedMediaUrls.has(previewUrl)) {
      media.src = previewUrl;
      media.dataset.loadState = 'loaded';
    }
    media.addEventListener('load', () => {
      media.dataset.loadState = 'loaded';
      loadedMediaUrls.add(media.dataset.src || media.src);
    }, { once: true });
    media.addEventListener('loadedmetadata', () => {
      media.dataset.loadState = 'loaded';
      loadedMediaUrls.add(media.dataset.src || media.src);
    }, { once: true });
    media.addEventListener('error', () => {
      media.dataset.loadState = 'error';
      const note = document.createElement('div');
      note.className = 'twgif-media-error';
      note.textContent = 'Превью недоступно';
      media.replaceWith(note);
    }, { once: true });
    frame.appendChild(media);
    card.appendChild(frame);

    const del = document.createElement('button');
    del.type = 'button';
    del.className = 'twgif-delete';
    del.title = 'Удалить из галереи';
    del.setAttribute('aria-label', 'Удалить медиа');
    del.innerHTML = '<svg viewBox="0 0 12 12" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"><path d="m3 3 6 6M9 3 3 9"/></svg>';
    del.addEventListener('click', event => { event.stopPropagation(); deleteItem(card.__twgifItem.id); });
    card.appendChild(del);

    let holdStarted = false;
    const beginHold = event => {
      if (event.button !== undefined && event.button !== 0) return;
      if (event.target === del || event.target.closest('.twgif-delete')) return;
      holdStarted = false;
      hideHoldPreview();
      holdPreviewTimer = setTimeout(() => {
        holdStarted = true;
        showHoldPreview(card.__twgifItem, card);
      }, 260);
    };
    const endHold = () => {
      if (holdPreviewTimer) clearTimeout(holdPreviewTimer);
      holdPreviewTimer = 0;
      if (holdStarted) {
        card.dataset.previewSuppressClick = '1';
        setTimeout(() => { card.dataset.previewSuppressClick = ''; }, 0);
      }
      hideHoldPreview();
    };
    card.addEventListener('pointerdown', beginHold);
    card.addEventListener('pointerup', endHold);
    card.addEventListener('pointercancel', endHold);
    card.addEventListener('pointerleave', endHold);

    const insert = event => {
      if (card.dataset.previewSuppressClick === '1') {
        event.preventDefault();
        event.stopPropagation();
        card.dataset.previewSuppressClick = '';
        return;
      }
      if (event.target === del || event.target.closest('.twgif-delete')) return;
      insertLinkIntoChat(card.__twgifItem.url);
    };
    card.addEventListener('click', insert);
    card.addEventListener('keydown', event => {
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        insertLinkIntoChat(card.__twgifItem.url);
      }
    });
    return card;
  }

  function showHoldPreview(item, card) {
    if (!item || !card) return;
    const holder = document.getElementById('twgif-hold-preview');
    if (!holder) return;
    holdPreviewItem = item;
    const url = item.previewUrl || item.url;
    const isVideo = item.type === 'video' || /\.(webm|mp4|mov|mkv|avi)(?:$|[?#])/i.test(url);
    const current = holder.firstElementChild;
    const currentType = current?.tagName === 'VIDEO' ? 'video' : 'image';
    const wantedType = isVideo ? 'video' : 'image';

    // Reuse the same preview element when holding the same tile again. This avoids
    // unnecessary new requests/decode work after the tab has been in the background.
    let el = current;
    if (!el || holder.dataset.currentUrl !== url || currentType !== wantedType) {
      holder.replaceChildren();
      el = document.createElement(isVideo ? 'video' : 'img');
      if (isVideo) {
        el.muted = true; el.loop = true; el.autoplay = true; el.playsInline = true; el.preload = 'metadata';
      } else {
        el.alt = '';
        el.decoding = 'async';
      }
      el.src = url;
      holder.appendChild(el);
      holder.dataset.currentUrl = url;
    }

    const config = loadConfig();
    const rect = card.getBoundingClientRect();
    const scale = config.previewScale;
    const width = Math.min(innerWidth * 0.88, Math.max(140, rect.width * scale));
    holder.style.width = `${width}px`;
    holder.style.left = `${Math.max(8, Math.min(innerWidth - width - 8, rect.left + rect.width / 2 - width / 2))}px`;
    holder.style.top = `${Math.max(8, Math.min(innerHeight * 0.75 - 80, rect.top + rect.height / 2 - 100))}px`;
    el.style.width = '100%';
    if (isVideo && typeof el.play === 'function') el.play().catch(() => {});
    requestAnimationFrame(() => holder.classList.add('twgif-preview-visible'));
  }

  function hideHoldPreview() {
    const holder = document.getElementById('twgif-hold-preview');
    if (!holder) return;
    holder.classList.remove('twgif-preview-visible');
    holdPreviewItem = null;
    const media = holder.firstElementChild;
    if (media && media.tagName === 'VIDEO') { try { media.pause(); } catch (_) {} }
    // Keep the last single preview element and URL attached; do not clear its src.
  }

  async function loadCardMedia(card, token) {
    const media = card.querySelector('.twgif-media');
    if (!media || media.dataset.loadState === 'loaded' || media.dataset.loadState === 'error' || media.src) return;
    if (token !== mediaLoadRun) return;
    const url = media.dataset.src;
    if (!url) return;
    media.dataset.loadState = 'loading';
    const video = media.tagName === 'VIDEO';
    const promise = new Promise(resolve => {
      let settled = false;
      const done = () => { if (!settled) { settled = true; resolve(); } };
      media.addEventListener(video ? 'loadedmetadata' : 'load', done, { once: true });
      media.addEventListener('error', done, { once: true });
      setTimeout(done, video ? 1800 : 12000);
    });
    media.src = url;
    if (video) media.load();
    await promise;
    if (token !== mediaLoadRun) return;
    if (media.naturalWidth > 0 || media.videoWidth > 0) {
      media.dataset.loadState = 'loaded';
      loadedMediaUrls.add(url);
    }
  }

  async function loadVisibleMediaSequentially(cards) {
    const token = ++mediaLoadRun;
    for (const card of cards) {
      if (token !== mediaLoadRun) return;
      await loadCardMedia(card, token);
    }
  }

  function renderGalleryItems() {
    const body = document.getElementById('twgif-panel-body');
    if (!body || panelView !== 'gallery') return;
    const masonry = body.querySelector('#twgif-masonry');
    const empty = body.querySelector('#twgif-empty');
    const count = body.querySelector('#twgif-count');
    const pagination = body.querySelector('#twgif-pagination');
    const pageLabel = body.querySelector('#twgif-page-label');
    const prev = body.querySelector('#twgif-page-prev');
    const next = body.querySelector('#twgif-page-next');
    if (!masonry || !empty || !count || !pagination) return;

    const config = loadConfig();
    const scale = config.mediaScale;
    masonry.classList.toggle('twgif-grid-mode', config.tileView === 'grid');
    masonry.style.setProperty('--twgif-scale', String(scale));
    masonry.style.setProperty('--twgif-tile-min', `${Math.round(76 * scale)}px`);
    masonry.style.setProperty('--twgif-thumb-height', `${Math.round(90 * scale)}px`);
    masonry.style.columnWidth = `${Math.round(78 * scale)}px`;
    masonry.style.columnCount = 'auto';
    masonry.style.columnGap = `${Math.max(3, Math.round(7 * scale))}px`;
    masonry.style.gap = `${Math.max(3, Math.round(7 * scale))}px`;

    const data = loadData();
    const items = data.items.slice().sort((a, b) => b.addedAt - a.addedAt || b.updatedAt - a.updatedAt);
    const pageSize = config.pageSize;
    const pages = Math.max(1, Math.ceil(items.length / pageSize));
    galleryPage = Math.max(0, Math.min(galleryPage, pages - 1));
    const start = galleryPage * pageSize;
    const visible = items.slice(start, start + pageSize);
    const visibleIds = new Set(visible.map(item => item.id));

    // Preserve card/image DOM nodes across sync refreshes and page switches.
    // Reorder only when the visible page actually changes; repeatedly appending
    // already-mounted <img> nodes can force browsers to drop decoded image data.
    const itemIds = new Set(items.map(item => item.id));
    const orderedVisibleCards = [];
    for (const item of visible) {
      let card = mediaCardCache.get(item.id);
      if (!card) {
        card = makeMediaCard(item);
        mediaCardCache.set(item.id, card);
      } else {
        const oldItem = card.__twgifItem || {};
        card.__twgifItem = item;
        const media = card.querySelector('.twgif-media');
        const newPreview = item.previewUrl || item.url;
        if (media && media.dataset.src !== newPreview) {
          media.dataset.src = newPreview;
          media.dataset.loadState = loadedMediaUrls.has(newPreview) ? 'loaded' : 'pending';
          if (loadedMediaUrls.has(newPreview)) media.src = newPreview;
          else { media.removeAttribute('src'); }
        }
        if (oldItem.url !== item.url) card.setAttribute('aria-label', 'Вставить ссылку на медиа в чат');
      }
      card.hidden = false;
      orderedVisibleCards.push(card);
    }

    for (let i = 0; i < orderedVisibleCards.length; i++) {
      const card = orderedVisibleCards[i];
      const currentAtPosition = masonry.children[i];
      if (currentAtPosition !== card) masonry.insertBefore(card, currentAtPosition || null);
    }

    for (const [id, card] of mediaCardCache) {
      if (!itemIds.has(id)) {
        card.remove();
        mediaCardCache.delete(id);
      } else if (!visibleIds.has(id)) {
        card.hidden = true;
      }
    }

    masonry.hidden = visible.length === 0;
    count.textContent = String(items.length);
    empty.hidden = visible.length > 0;
    empty.textContent = 'Коллекция пуста. Добавь ссылку или перетащи файл.';

    pagination.hidden = items.length <= pageSize;
    pageLabel.textContent = `Стр. ${galleryPage + 1} / ${pages}`;
    prev.disabled = galleryPage === 0;
    next.disabled = galleryPage >= pages - 1;
    prev.onclick = () => { if (galleryPage > 0) { galleryPage--; renderGalleryItems(); } };
    next.onclick = () => { if (galleryPage < pages - 1) { galleryPage++; renderGalleryItems(); } };

    loadVisibleMediaSequentially(visible.map(item => mediaCardCache.get(item.id)));
    repositionPanel();
  }

  function renderSettings() {
    const body = document.getElementById('twgif-panel-body');
    if (!body) return;
    const config = loadConfig();
    const targetOptions = (selected, values) => values.map(([value, label]) =>
      `<option value="${value}" ${selected === value ? 'selected' : ''}>${label}</option>`
    ).join('');

    let content = '';
    if (settingsTab === 'general') {
      content = `
        <div class="twgif-settings">
          <div class="twgif-section">
            <div class="twgif-section-title">Галерея</div>
            <label class="twgif-field-label" for="twgif-media-scale">Масштаб плиток</label>
            <select id="twgif-media-scale" class="twgif-input">
              ${targetOptions(String(config.mediaScale), [['0.5','50%'],['0.7','70%'],['0.85','85%'],['1','100%'],['1.2','120%'],['1.4','140%'],['1.6','160%'],['2','200%']])}
            </select>
            <label class="twgif-field-label" for="twgif-tile-view">Вид плиток</label>
            <select id="twgif-tile-view" class="twgif-input">
              <option value="masonry" ${config.tileView === 'masonry' ? 'selected' : ''}>Плотная мозаика</option>
              <option value="grid" ${config.tileView === 'grid' ? 'selected' : ''}>Ровная сетка</option>
            </select>
            <label class="twgif-field-label" for="twgif-page-size">Медиа на странице (10–500)</label>
            <input id="twgif-page-size" class="twgif-input" type="number" min="10" max="500" step="10" value="${config.pageSize}">
            <label class="twgif-field-label" for="twgif-preview-scale">Увеличение при удержании</label>
            <select id="twgif-preview-scale" class="twgif-input">
              ${targetOptions(String(config.previewScale), [['1.1','110%'],['1.3','130%'],['1.6','160%'],['2','200%'],['2.5','250%'],['3','300%']])}
            </select>
            <div class="twgif-row" style="margin-top:8px">
              <button id="twgif-save-gallery-settings" class="twgif-small-btn twgif-primary" type="button">Применить</button>
              <button id="twgif-reset-defaults" class="twgif-small-btn" type="button">Настройки по умолчанию</button>
            </div>
          </div>
        </div>`;
    } else if (settingsTab === 'convert') {
      content = `
        <div class="twgif-settings">
          <div class="twgif-section">
            <div class="twgif-section-title">Правила конвертации</div>
            <label class="twgif-field-label" for="twgif-max-width">Максимальная ширина (px)</label>
            <input id="twgif-max-width" class="twgif-input" type="number" min="100" max="4000" step="50" value="${config.maxWidth}">
            <label class="twgif-field-label" for="twgif-rule-image">Обычные изображения →</label>
            <select id="twgif-rule-image" class="twgif-input">${targetOptions(config.conversionRules.image, [['keep','Не конвертировать'],['webp','WebP'],['jpg','JPG'],['png','PNG']])}</select>
            <label class="twgif-field-label" for="twgif-rule-gif">GIF →</label>
            <select id="twgif-rule-gif" class="twgif-input">${targetOptions(config.conversionRules.gif, [['keep','Оставить GIF'],['webp','WebP'],['gif','GIF'],['mp4','MP4']])}</select>
            <label class="twgif-field-label" for="twgif-rule-video">Видео →</label>
            <select id="twgif-rule-video" class="twgif-input">${targetOptions(config.conversionRules.video, [['keep','Оставить оригинал'],['gif','GIF'],['webp','WebP'],['webm','WebM'],['mp4','MP4']])}</select>
            <div class="twgif-help">Видео по умолчанию конвертируется в GIF с бесконечным повторением. Для GIF используется параметр loop_count = 0 (или gif_loop_count = 0, если его требует FreeConvert). При выборе «Видео → WebP» и заполненном ключе Rendi видео превращается в зацикленный анимированный WebP через Rendi; остальные форматы продолжают обрабатываться FreeConvert.</div>
            <label class="twgif-field-label" for="twgif-rendi-api-key">Rendi API key (только на этом устройстве)</label>
            <input id="twgif-rendi-api-key" name="twgif-rendi-api-key" class="twgif-input" type="text" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" data-1p-ignore="true" data-lpignore="true" data-bwignore="true" data-form-type="other" style="-webkit-text-security:disc" placeholder="Rendi API key" value="${escapeAttr(config.rendiApiKey)}">
            <div class="twgif-help"><a href="https://www.rendi.dev/docs/direct-upload" target="_blank" rel="noopener noreferrer">Rendi Direct Upload</a> + FFmpeg API. Ключ хранится только локально и никогда не добавляется в Gist. Исходное видео загружается в Rendi для конвертации.</div>
            <label class="twgif-field-label" for="twgif-freeconvert-token">FreeConvert API-токен</label>
            <input id="twgif-freeconvert-token" name="twgif-freeconvert-api-token" class="twgif-input" type="text" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" data-1p-ignore="true" data-lpignore="true" data-bwignore="true" data-form-type="other" style="-webkit-text-security:disc" placeholder="FreeConvert API token" value="${escapeAttr(config.freeConvertToken)}">
            <div class="twgif-help"><a href="https://www.freeconvert.com/api" target="_blank" rel="noopener noreferrer">Документация FreeConvert API</a>. Конвертация использует лимиты/кредиты сервиса. Файл отправляется на внешний сервер обработки. Токен может синхронизироваться в Gist по отдельной кнопке настроек.</div>
            <button id="twgif-save-convert" class="twgif-small-btn twgif-primary" type="button" style="margin-top:8px">Сохранить правила</button>
          </div>
        </div>`;
    } else if (settingsTab === 'sync') {
      content = `
        <div class="twgif-settings">
          <div class="twgif-section">
            <div class="twgif-section-title">Коллекция и настройки между устройствами</div>
            <label class="twgif-field-label" for="twgif-gist-token">GitHub token (доступ gist)</label>
            <input id="twgif-gist-token" name="twgif-github-gist-token" class="twgif-input" type="text" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" data-1p-ignore="true" data-lpignore="true" data-bwignore="true" data-form-type="other" style="-webkit-text-security:disc" placeholder="GitHub token" value="${escapeAttr(config.gistToken)}">
            <label class="twgif-field-label" for="twgif-gist-id">ID Gist</label>
            <input id="twgif-gist-id" class="twgif-input" type="text" autocomplete="off" spellcheck="false" placeholder="ID Gist" value="${escapeAttr(config.gistId)}">
            <div class="twgif-help"><b>Первое устройство:</b> создай GitHub token с разрешением <code>gist</code>, вставь его сюда, оставь ID Gist пустым и нажми «Создать Gist». Затем нажми «Синхронизировать галерею» и «Синхронизировать настройки».</div>
            <div class="twgif-help"><b>Другое устройство:</b> введи <b>тот же GitHub token</b> и <b>тот же ID Gist</b>, которые использовались на первом устройстве. Нажми «Сохранить доступ», затем «Синхронизировать галерею» и «Синхронизировать настройки». ID Gist — длинная строка из URL Gist; сам GitHub token автоматически на другие устройства не переносится.</div>
            <div class="twgif-help">Gist хранит коллекцию и синхронизируемые настройки. Secret Gist не является приватным для людей, знающих его URL. FreeConvert API-токен попадает в файл настроек Gist в открытом виде; GitHub token в Gist не записывается.</div>
            <div class="twgif-row" style="margin-top:8px">
              <button id="twgif-save-gist" class="twgif-small-btn" type="button">Сохранить доступ</button>
              <button id="twgif-create-gist" class="twgif-small-btn" type="button">Создать Gist</button>
              <button id="twgif-sync-now" class="twgif-small-btn" type="button">Синхронизировать галерею</button>
            </div>
            <button id="twgif-sync-settings" class="twgif-small-btn twgif-primary" type="button" style="margin-top:8px">Синхронизировать настройки</button>
            <div class="twgif-help">Отдельная кнопка синхронизирует настройки отображения, правила конвертации и FreeConvert API-токен. Токен хранится в отдельном файле Gist в открытом виде: любой, у кого есть URL Secret Gist, может прочитать его. GitHub-токен в Gist не записывается.</div>
            <div class="twgif-help"><a href="https://github.com/settings/tokens/new?scopes=gist&description=Twitch%20GIF%20Gallery" target="_blank" rel="noopener noreferrer">Создать GitHub-токен с разрешением gist</a>.</div>
          </div>
        </div>`;
    } else {
      content = `
        <div class="twgif-settings">
          <div class="twgif-section">
            <div class="twgif-section-title">Отладка и резервная копия</div>
            <label class="twgif-check-row"><input id="twgif-debug-toggle" type="checkbox" ${config.debug ? 'checked' : ''}> Подробные записи в консоль и журнал</label>
            <div class="twgif-row" style="margin:7px 0"><button id="twgif-copy-debug" class="twgif-small-btn" type="button">Копировать журнал</button><button id="twgif-clear-debug" class="twgif-small-btn" type="button">Очистить журнал</button><button id="twgif-export" class="twgif-small-btn" type="button">Экспорт JSON</button><button id="twgif-import" class="twgif-small-btn" type="button">Импорт JSON</button><input id="twgif-import-file" type="file" accept="application/json,.json" hidden></div>
            <textarea id="twgif-debug-log" class="twgif-debug-log" readonly spellcheck="false" aria-label="Журнал отладки"></textarea>
            <div class="twgif-help">Токены не записываются в журнал. Экспорт JSON включает коллекцию, но не API-токены.</div>
          </div>
        </div>`;
    }

    body.innerHTML = content;
    const $ = selector => body.querySelector(selector);

    if (settingsTab === 'general') {
      $('#twgif-save-gallery-settings').addEventListener('click', () => {
        saveConfig({
          mediaScale: $('#twgif-media-scale').value,
          tileView: $('#twgif-tile-view').value,
          pageSize: $('#twgif-page-size').value,
          previewScale: $('#twgif-preview-scale').value
        });
        galleryPage = 0;
        setStatus('Настройки галереи сохранены.', 'success');
      });
      $('#twgif-reset-defaults').addEventListener('click', () => {
        const current = loadConfig();
        saveConfig({
          ...DEFAULT_CONFIG(),
          gistToken: current.gistToken,
          gistId: current.gistId,
          freeConvertToken: current.freeConvertToken,
          rendiApiKey: current.rendiApiKey,
          settingsUpdatedAt: Date.now()
        });
        galleryPage = 0;
        settingsTab = 'general';
        setStatus('Настройки отображения и правила конвертации сброшены. API-токены и доступ к Gist сохранены.', 'success', true);
        renderSettings();
      });
    }

    if (settingsTab === 'convert') {
      $('#twgif-save-convert').addEventListener('click', () => {
        saveConfig({
          maxWidth: $('#twgif-max-width').value,
          conversionRules: {
            image: $('#twgif-rule-image').value,
            gif: $('#twgif-rule-gif').value,
            video: $('#twgif-rule-video').value
          },
          freeConvertToken: $('#twgif-freeconvert-token').value,
          rendiApiKey: $('#twgif-rendi-api-key').value
        });
        setStatus('Правила конвертации и API-ключи сохранены локально. Ключ Rendi не синхронизируется в Gist.', 'success');
      });
    }

    if (settingsTab === 'sync') {
      $('#twgif-save-gist').addEventListener('click', () => {
        saveConfig({ gistToken: $('#twgif-gist-token').value, gistId: $('#twgif-gist-id').value });
        setStatus('Данные доступа сохранены локально; действительность токена проверится при создании или синхронизации Gist.', 'success', true);
      });
      $('#twgif-create-gist').addEventListener('click', async event => {
        const button = event.currentTarget;
        const cfg = saveConfig({ gistToken: $('#twgif-gist-token').value, gistId: $('#twgif-gist-id').value });
        if (!cfg.gistToken) { setStatus('Введи GitHub-токен с разрешением gist.', 'error', true); return; }
        if (cfg.gistId) { setStatus('ID Gist уже заполнен. Очисти поле ID, если нужно создать новый.', 'error', true); return; }
        button.disabled = true;
        try {
          setStatus('Создаю Gist…', 'info', true);
          const id = await createGist(cfg, loadData());
          saveConfig({ gistId: id });
          $('#twgif-gist-id').value = id;
          setStatus(`Gist создан: ${id}. Теперь можно синхронизировать коллекцию и настройки.`, 'success', true);
        } catch (error) {
          setStatus(`Не удалось создать Gist: ${formatGitHubSyncError(error)}`, 'error', true);
        } finally { button.disabled = false; }
      });
      $('#twgif-sync-now').addEventListener('click', async () => {
        saveConfig({ gistToken: $('#twgif-gist-token').value, gistId: $('#twgif-gist-id').value });
        try { await syncNow(); } catch (error) { setStatus(`Синхронизация галереи: ${formatGitHubSyncError(error)}`, 'error', true); }
      });
      $('#twgif-sync-settings').addEventListener('click', async () => {
        saveConfig({ gistToken: $('#twgif-gist-token').value, gistId: $('#twgif-gist-id').value });
        try { await syncSettingsNow(); } catch (error) { setStatus(`Синхронизация настроек: ${formatGitHubSyncError(error)}`, 'error', true); }
      });
    }

    if (settingsTab === 'debug') {
      $('#twgif-debug-log').value = debugLogs.join('\n');
      $('#twgif-debug-toggle').addEventListener('change', event => {
        saveConfig({ debug: event.currentTarget.checked });
        logDebug(`Debug mode ${event.currentTarget.checked ? 'enabled' : 'disabled'}`);
        setStatus(`Отладка ${event.currentTarget.checked ? 'включена' : 'выключена'}.`, 'success');
      });
      $('#twgif-copy-debug').addEventListener('click', async () => {
        const text = debugLogs.join('\n') || 'Журнал пуст.';
        try { await navigator.clipboard.writeText(text); setStatus('Журнал скопирован.', 'success'); }
        catch (_) { $('#twgif-debug-log').focus(); $('#twgif-debug-log').select(); setStatus('Нажми Ctrl+C, чтобы скопировать выделенный журнал.', 'info'); }
      });
      $('#twgif-clear-debug').addEventListener('click', () => {
        debugLogs.length = 0;
        $('#twgif-debug-log').value = '';
        setStatus('Журнал очищен.', 'success');
      });
      $('#twgif-export').addEventListener('click', exportBackup);
      $('#twgif-import').addEventListener('click', () => $('#twgif-import-file').click());
      $('#twgif-import-file').addEventListener('change', async event => {
        const file = event.target.files && event.target.files[0];
        event.target.value = '';
        if (!file) return;
        try {
          const json = JSON.parse(await file.text());
          const data = parseDataForMerge(json);
          const merged = mergeData(loadData(), data);
          persistData(merged);
          setStatus(`Коллекция объединена, элементов: ${merged.items.length}.`, 'success');
        } catch (error) { setStatus(`Не удалось импортировать JSON: ${error.message || error}`, 'error', true); }
      });
    }
  }

  function escapeAttr(value) {
    return String(value).replace(/[&<>"']/g, char => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[char]);
  }

  function exportBackup() {
    const payload = { version: VERSION, exportedAt: new Date().toISOString(), ...sortData(loadData()) };
    const blob = new Blob([JSON.stringify(payload, null, 2)], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `twitch-gif-gallery-${new Date().toISOString().slice(0, 10)}.json`;
    document.body.appendChild(link); link.click(); link.remove();
    setTimeout(() => URL.revokeObjectURL(url), 2000);
    setStatus('Резервная копия коллекции подготовлена.', 'success');
  }

  // A document-level capture listener closes the popup without blocking the Twitch chat click below it.
  document.addEventListener('pointerdown', event => {
    const panel = document.getElementById('twgif-panel');
    const trigger = document.getElementById('twgif-trigger');
    if (!panel || panel.hidden) return;
    if (!panel.contains(event.target) && !trigger?.contains(event.target)) closePanel();
  }, true);

  document.addEventListener('paste', event => {
    const clipboard = event.clipboardData;
    if (!clipboard) return;
    const files = [];
    for (const item of Array.from(clipboard.items || [])) {
      if (item.kind !== 'file') continue;
      if (!/^(image|video)\//i.test(item.type || '')) continue;
      const file = item.getAsFile();
      if (file) files.push(file);
    }
    if (!files.length) {
      for (const file of Array.from(clipboard.files || [])) {
        if (/^(image|video)\//i.test(file.type || '') || mimeFromFile(file)) files.push(file);
      }
    }
    if (!files.length) return;
    event.preventDefault();
    event.stopPropagation();
    if (typeof event.stopImmediatePropagation === 'function') event.stopImmediatePropagation();
    if (!isPanelOpen()) openPanel(document.getElementById('twgif-trigger'));
    setStatus('Изображение из буфера получено…', 'info', true);
    processFiles(files);
  }, true);

  document.addEventListener('keydown', event => {
    if (event.key === 'Escape' && isPanelOpen()) closePanel();
  }, true);

  document.addEventListener('selectionchange', captureComposerSelection);
  document.addEventListener('focusin', event => {
    const target = event.target;
    if (target && isEditor(target) && !target.closest('#twgif-panel')) {
      activeComposer = target;
      captureComposerSelection();
    }
  }, true);

  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'visible' && isPanelOpen() && panelView === 'gallery') {
      // Resume the sequential loader after browser timer throttling, without resetting src.
      renderGalleryItems();
      repositionPanel();
    }
  });

  window.addEventListener('resize', repositionPanel, { passive: true });
  window.addEventListener('scroll', repositionPanel, { passive: true, capture: true });

  function installObservers() {
    if (observer) observer.disconnect();
    const target = getChatInput();
    if (target) {
      const toolbar = getToolbar(target);
      const localRoot = toolbar?.parentElement || toolbar || target.parentElement;
      if (localRoot) {
        observer = new MutationObserver(() => scheduleEnsure());
        observer.observe(localRoot, { childList: true, subtree: true });
        installChatMediaObserver();
        return;
      }
    }
    observer = new MutationObserver(() => {
      if (ensureTrigger()) installObservers();
      else installChatMediaObserver();
    });
    observer.observe(document.body || document.documentElement, { childList: true, subtree: true });
    installChatMediaObserver();
  }

  function start() {
    buildStyles();
    buildPanel();
    ensureTrigger();
    installObservers();
    installChatMediaObserver();
    logDebug('Userscript v5.1 started', { href: location.href });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start, { once: true });
  else start();
})();
