// ==UserScript==
// @name         Twitch GIF Gallery + Kappa.lol
// @namespace    https://github.com/BigFluffyCatOnWatermelon/twitch-media-gallery
// @version      5.9.79
// @description  Stream media gallery for Twitch, w.tv, Kick and VK Video Live with Telegram post import, HD imports, FFmpeg conversion and Gist gallery sync.
// @updateURL    https://raw.githubusercontent.com/BigFluffyCatOnWatermelon/twitch-media-gallery/main/twitch-helper.user.js
// @downloadURL  https://raw.githubusercontent.com/BigFluffyCatOnWatermelon/twitch-media-gallery/main/twitch-helper.user.js
// @match        https://www.twitch.tv/*
// @match        https://twitch.tv/*
// @match        https://w.tv/*
// @match        https://www.w.tv/*
// @match        https://kick.com/*
// @match        https://www.kick.com/*
// @match        https://live.vkvideo.ru/*
// @run-at       document-idle
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_deleteValue
// @grant        GM_addValueChangeListener
// @grant        GM_xmlhttpRequest
// @connect      kappa.lol
// @connect      segs.lol
// @connect      api.github.com
// @connect      gist.githubusercontent.com
// @connect      7tv.io
// @connect      7tv.app
// @connect      cdn.7tv.app
// @connect      cdn.jsdelivr.net
// @connect      t.me
// @connect      telegram.me
// @connect      telesco.pe
// @connect      cdn-telegram.org
// @connect      telegram-cdn.org
// @connect      *
// ==/UserScript==

(() => {
  'use strict';

  const APP_VERSION = '5.9.79';
  const VERSION = 23;
  const DEFAULT_MAX_WIDTH = 500;
  const MAX_FILE_BYTES = 100 * 1024 * 1024;
  const DATA_KEY = 'twgif_gallery_data_v1';
  const CONFIG_KEY = 'twgif_gallery_config_v2';
  const LEGACY_SYNC_KEY = 'twgif_gallery_sync_v1';
  const SYNC_FILENAME = 'twitch-gif-gallery.json';
  const KAPPA_UPLOAD_URL = 'https://kappa.lol/api/upload';
  const KAPPA_UPLOAD_MIRROR_URL = 'https://segs.lol/api/upload';
  const GITHUB_API = 'https://api.github.com';
  const FFMPEG_CORE_VERSION = '0.12.10';
  const FFMPEG_CORE_BASE_URL = `https://cdn.jsdelivr.net/npm/@ffmpeg/core@${FFMPEG_CORE_VERSION}/dist/umd`;
  const FFMPEG_CACHE_DB = 'twgif-ffmpeg-assets-v1';
  const MEDIA_CACHE_DB = 'twgif-gallery-media-v1';
  const MEDIA_CACHE_STORE = 'assets';
  const MEDIA_CACHE_MAX_BYTES = 200 * 1024 * 1024;
  const MEDIA_CACHE_MAX_ENTRY_BYTES = 24 * 1024 * 1024;
  const MEDIA_CACHE_MAX_REMOTE_BYTES = 8 * 1024 * 1024;
  const MEDIA_CACHE_MAX_REMOTE_VIDEO_BYTES = 5 * 1024 * 1024;
  // GM storage is shared by this userscript across matched sites. Keep its base64
  // cache bounded; the larger per-site IndexedDB cache remains available as a fallback.
  const SHARED_MEDIA_INDEX_KEY = 'twgif_gallery_shared_media_index_v1';
  const SHARED_MEDIA_ENTRY_PREFIX = 'twgif_gallery_shared_media_v1:';
  const SHARED_MEDIA_CACHE_MAX_BYTES = 24 * 1024 * 1024;
  const SHARED_MEDIA_CACHE_MAX_ENTRY_BYTES = 6 * 1024 * 1024;
  const SETTINGS_SCHEMA_VERSION = 9;
  const COMPRESS_ENABLED_KEY = 'twgif_compress_enabled_v1';
  const MEDIA_EDITOR_ENABLED_KEY = 'twgif_media_editor_enabled_v1';

  let panelView = 'gallery';
  let settingsTab = 'general';
  let galleryTab = 'all';
  // Independent from galleryTab (All / HD / 7TV / Favorites).
  let galleryMediaType = 'all'; // 'all' | 'photos' | 'videos'
  let galleryPage = 0;
  let mediaLoadRun = 0;
  let chatMediaObserver = null;
  let chatMediaScanQueued = false;
  let holdPreviewTimer = 0;
  let holdPreviewItem = null;
  let holdPreviewRestore = null;
  let holdPointerId = null;
  let holdPointerActive = false;
  let holdPreviewStarted = false;
  let holdCandidateCard = null;
  let holdPointerX = 0;
  let holdPointerY = 0;
  let suppressMediaClickUntil = 0;
  const mediaCardCache = new Map();
  const loadedMediaUrls = new Set();
  const cachedMediaObjectUrls = new Map();
  const mediaCachePendingUrls = new Set();
  let mediaCacheDbPromise = null;
  let galleryResizeObserver = null;
  let activeTrigger = null;
  let triggerResultTimer = 0;
  let portalImportDepth = 0;
  let pendingTriggerResult = '';
  let activeComposer = null;
  let savedComposerRange = null;
  let savedComposerOffset = null;
  let lastStatus = '';
  let lastStatusType = 'info';
  let progressActive = false;
  let progressPercent = null;
  let progressHideTimer = 0;
  let progressGeneration = 0;
  let processingRunId = 0;
  let activeProcessingRunId = 0;
  let activeUploadRequest = null;
  let syncTimer = 0;
  let syncRunning = false;
  let syncAgain = false;
  let observer = null;
  let twitchLifecycleObserver = null;
  let twitchRecoveryTimer = 0;
  let ensureQueued = false;
  let lastObservedInput = null;
  const debugLogs = [];
  const debugLogEntries = [];
  let lastLogSignature = '';
  let lastLogTimestamp = 0;
  const processingFiles = new Map();
  const recentFileFingerprints = new Map();
  const mediaSizeCache = new Map();
  const mediaSizeLookupPending = new Map();
  const videoDurationCache = new Map();
  const videoDurationLookupPending = new Map();
  // WebP animation state is separate from duration: some valid animations have zero frame delays.
  const animatedWebPStatusCache = new Map();
  const animatedWebPCheckFailed = new Set();
  const animatedWebPClassificationPending = new Set();
  let localFfmpegAssetsPromise = null;
  let localFfmpegAssets = null;
  let localFfmpegWorker = null;
  let localFfmpegWorkerUrl = '';
  let localFfmpegRequestId = 0;
  const localFfmpegPending = new Map();

  const EMPTY_DATA = () => ({ version: VERSION, items: [], deleted: {} });
  function isCompressionEnabled() {
    try { return GM_getValue(COMPRESS_ENABLED_KEY, true) !== false; }
    catch (_) { return true; }
  }

  const DEFAULT_CONFIG = () => ({
    maxWidth: DEFAULT_MAX_WIDTH,
    columns: 4,
    pageSize: 100,
    tileView: 'masonry',
    previewMaxSize: 1920,
    previewTileBoost: 5,
    conversionRules: { image: 'webp', gif: 'webp', video: 'webp' },
    compression: {
      imageQuality: 82,
      animationQuality: 68,
      videoMaxWidth: 500,
      videoFps: 24,
      animationFps: 10,
      videoBitrateKbps: 1500,
      audioBitrateKbps: 96,
      videoCrf: 28,
      speedPreset: 'fast',
      scaleFilter: 'fast_bilinear',
      webpCompressionLevel: 5
    },
    settingsSchemaVersion: SETTINGS_SCHEMA_VERSION,
    gistToken: '',
    gistId: '',
    debug: false
  });

  function normalizeCompressionSettings(value = {}, fallback = DEFAULT_CONFIG().compression) {
    const raw = value && typeof value === 'object' ? value : {};
    const allowedPresets = ['ultrafast', 'superfast', 'veryfast', 'fast', 'medium'];
    const allowedFilters = ['fast_bilinear', 'bilinear', 'bicubic', 'lanczos'];
    const requestedPreset = String(raw.speedPreset ?? fallback.speedPreset);
    const requestedFilter = String(raw.scaleFilter ?? fallback.scaleFilter);
    return {
      imageQuality: clampInt(raw.imageQuality ?? fallback.imageQuality, 30, 100, fallback.imageQuality),
      animationQuality: clampInt(raw.animationQuality ?? fallback.animationQuality, 10, 100, fallback.animationQuality),
      videoMaxWidth: clampInt(raw.videoMaxWidth ?? fallback.videoMaxWidth, 240, 4000, fallback.videoMaxWidth),
      videoFps: clampInt(raw.videoFps ?? fallback.videoFps, 5, 60, fallback.videoFps),
      animationFps: clampInt(raw.animationFps ?? fallback.animationFps, 3, 30, fallback.animationFps),
      videoBitrateKbps: clampInt(raw.videoBitrateKbps ?? fallback.videoBitrateKbps, 0, 20000, fallback.videoBitrateKbps),
      audioBitrateKbps: clampInt(raw.audioBitrateKbps ?? fallback.audioBitrateKbps, 32, 320, fallback.audioBitrateKbps),
      videoCrf: clampInt(raw.videoCrf ?? fallback.videoCrf, 18, 40, fallback.videoCrf),
      speedPreset: allowedPresets.includes(requestedPreset) ? requestedPreset : fallback.speedPreset,
      scaleFilter: allowedFilters.includes(requestedFilter) ? requestedFilter : fallback.scaleFilter,
      webpCompressionLevel: clampInt(raw.webpCompressionLevel ?? fallback.webpCompressionLevel, 0, 6, fallback.webpCompressionLevel)
    };
  }

  function videoCpuUsedFromPreset(preset) {
    return ({ ultrafast: 8, superfast: 7, veryfast: 6, fast: 5, medium: 4 })[preset] || 8;
  }

  const SVG_GALLERY = '<svg viewBox="0 0 24 24" width="20" height="20" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="6" width="13" height="14" rx="2"></rect><path d="M8 6V4.8A1.8 1.8 0 0 1 9.8 3h9.4A1.8 1.8 0 0 1 21 4.8v10.4a1.8 1.8 0 0 1-1.8 1.8H16"></path><circle cx="7.5" cy="10.5" r="1.3"></circle><path d="m4 17 4.2-4 2.5 2 1.8-1.5 1.5 1.4"></path></svg>';
  const SVG_CROP = '<svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 3v13a2 2 0 0 0 2 2h13"></path><path d="M18 21V8a2 2 0 0 0-2-2H3"></path><path d="M8 3v5M3 8h5M16 16h5M16 16v5"></path></svg>';
  const SVG_SETTINGS = '<svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><circle cx="12" cy="12" r="3"></circle><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 1 1-2.83 2.83l-.06-.06a1.65 1.65 0 0 0-1.82-.33h-.08a1.65 1.65 0 0 0-1 1.51V21a2 2 0 1 1-4 0v-.09a1.65 1.65 0 0 0-1-1.51 1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 1 1-2.83-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82v-.08a1.65 1.65 0 0 0-1.51-1H3a2 2 0 1 1 0-4h.09a1.65 1.65 0 0 0 1.51-1v-.08a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 1 1 2.83-2.83l.06.06a1.65 1.65 0 0 0 1.82.33h.08a1.65 1.65 0 0 0 1-1.51V3a2 2 0 1 1 4 0v.09a1.65 1.65 0 0 0 1 1.51h.08a1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 1 1 2.83 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82v.08a1.65 1.65 0 0 0 1.51 1H21a2 2 0 1 1 0 4h-.09a1.65 1.65 0 0 0-1.51 1z"></path></svg>';
  const SVG_CLOSE = '<svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><path d="m6 6 12 12M18 6 6 18"></path></svg>';
  const SVG_SEARCH = '<svg viewBox="0 0 24 24" width="16" height="16" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" aria-hidden="true"><circle cx="10.5" cy="10.5" r="6.5"></circle><path d="m16 16 4.2 4.2"></path></svg>';

  function parseJson(value, fallback) {
    if (typeof value !== 'string') return value == null ? fallback : value;
    try { return JSON.parse(value); } catch (_) { return fallback; }
  }

  // Persist the result of media classification with each gallery item. This prevents
  // repeated WebP downloads and resorting after every page reload.
  const PERSISTED_MEDIA_KINDS = new Set(['animated', 'photo', 'unknown', 'unavailable']);
  const MEDIA_KIND_RETRY_INTERVAL_MS = 24 * 60 * 60 * 1000;

  function inferInitialMediaKind(item) {
    const type = String(item?.type || '').toLowerCase();
    if (type === 'video' || type === 'gif' || item?.animated === true) return 'animated';

    const candidates = [item?.previewUrl, item?.url, item?.name]
      .map(value => String(value || '').trim())
      .filter(Boolean);
    for (const rawUrl of candidates) {
      let pathname = rawUrl;
      try { pathname = new URL(rawUrl, location.href).pathname; } catch (_) {}
      if (/\.(?:gif|apng|webm|mp4|mov|m4v|mkv|avi|ogv|mpg|mpeg)$/i.test(pathname)) return 'animated';
    }

    // WebP's extension does not reveal whether the container has animation frames.
    let hasUnclassifiedWebP = false;
    for (const rawUrl of candidates) {
      if (!isWebPResource(rawUrl)) continue;
      if (animatedWebPStatusCache.has(rawUrl)) {
        return animatedWebPStatusCache.get(rawUrl) ? 'animated' : 'photo';
      }
      if (Number(videoDurationCache.get(rawUrl)) > 0) return 'animated';
      hasUnclassifiedWebP = true;
    }
    if (hasUnclassifiedWebP) return 'unknown';

    return type === 'image' ? 'photo' : 'unknown';
  }

  function normalizeStoredMediaKind(item) {
    const value = String(item?.mediaKind || '').toLowerCase();
    if (PERSISTED_MEDIA_KINDS.has(value)) {
      // Repair earlier records that marked WebP as a photo before inspecting its bytes.
      // A zero check timestamp means the value was inferred, not verified by the parser.
      if (value === 'photo' && !(Number(item?.mediaKindCheckedAt) > 0)) {
        const candidates = [item?.previewUrl, item?.url, item?.name].filter(Boolean);
        if (candidates.some(isWebPResource)) {
          const inferred = inferInitialMediaKind({ ...item, mediaKind: '' });
          if (inferred === 'unknown' || inferred === 'animated') return inferred;
        }
      }
      return value;
    }
    return inferInitialMediaKind(item);
  }

  // Collection persistence and normalization: callers work with validated, sorted records.
  function loadData() {
    const raw = parseJson(GM_getValue(DATA_KEY, EMPTY_DATA()), EMPTY_DATA());
    const data = EMPTY_DATA();
    if (!raw || typeof raw !== 'object') return data;

    const rawItems = Array.isArray(raw.items) ? raw.items : [];
    let needsMediaMetadataMigration = false;
    const cleaned = rawItems
      .filter(item => item && typeof item.id === 'string' && typeof item.url === 'string')
      .map(item => {
        // Missing legacy timestamps must stay stable between reads. Using Date.now()
        // here made old entries appear new on every gallery refresh.
        const addedAt = Number(item.addedAt) || Number(item.updatedAt) || 0;
        const updatedAt = Number(item.updatedAt) || addedAt;
        if (!PERSISTED_MEDIA_KINDS.has(String(item.mediaKind || '').toLowerCase()) ||
            !Object.prototype.hasOwnProperty.call(item, 'mediaKindCheckedAt')) {
          needsMediaMetadataMigration = true;
        }
        return {
          id: String(item.id),
          url: String(item.url),
          previewUrl: String(item.previewUrl || item.url),
          name: String(item.name || 'Медиафайл').slice(0, 120),
          type: String(item.type || 'image'),
          sourceKey: String(item.sourceKey || ''),
          favorite: Boolean(item.favorite),
          hd: Boolean(item.hd),
          size: Math.max(0, Math.floor(Number(item.size) || 0)),
          addedAt,
          updatedAt,
          mediaKind: normalizeStoredMediaKind(item),
          mediaKindCheckedAt: Math.max(0, Math.floor(Number(item.mediaKindCheckedAt) || 0))
        };
      });

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

    if (data.items.length !== rawItems.length || needsMediaMetadataMigration) {
      GM_setValue(DATA_KEY, sortData(data));
      if (data.items.length !== rawItems.length) {
        logDebug('Removed duplicate local gallery items', { before: rawItems.length, after: data.items.length });
      }
      if (needsMediaMetadataMigration) {
        logDebug('Migrated persistent media classification metadata', { count: data.items.length });
      }
    }
    return data;
  }

  function loadConfig() {
    const raw = parseJson(GM_getValue(CONFIG_KEY, {}), {}) || {};
    const legacy = parseJson(GM_getValue(LEGACY_SYNC_KEY, {}), {}) || {};
    const defaults = DEFAULT_CONFIG();
    const previousSchemaVersion = Number(raw.settingsSchemaVersion) || 0;
    const rules = raw.conversionRules && typeof raw.conversionRules === 'object' ? { ...raw.conversionRules } : {};
    const allowedTargets = {
      image: ['keep', 'webp', 'png', 'jpg', 'gif', 'mp4', 'webm'],
      gif: ['keep', 'gif', 'webp', 'png', 'jpg', 'mp4', 'webm'],
      video: ['keep', 'webp', 'gif', 'mp4', 'webm', 'png', 'jpg']
    };
    const cleanTarget = (key, value) => allowedTargets[key].includes(String(value)) ? String(value) : defaults.conversionRules[key];
    const config = {
      maxWidth: clampInt(raw.maxWidth ?? defaults.maxWidth, 100, 4000, defaults.maxWidth),
      // Migrate the briefly introduced rowsPerPage setting to the intended column count.
      columns: clampInt(raw.columns ?? raw.rowsPerPage ?? defaults.columns, 1, 5, defaults.columns),
      pageSize: clampInt(raw.pageSize ?? defaults.pageSize, 10, 500, defaults.pageSize),
      tileView: raw.tileView === 'grid' ? 'grid' : 'masonry',
      previewMaxSize: clampInt(raw.previewMaxSize ?? defaults.previewMaxSize, 1, 4000, defaults.previewMaxSize),
      previewTileBoost: clampInt(raw.previewTileBoost ?? defaults.previewTileBoost, 0, 100, defaults.previewTileBoost),
      conversionRules: {
        image: cleanTarget('image', rules.image ?? defaults.conversionRules.image),
        gif: cleanTarget('gif', rules.gif ?? defaults.conversionRules.gif),
        video: cleanTarget('video', rules.video ?? defaults.conversionRules.video)
      },
      compression: normalizeCompressionSettings(raw.compression, defaults.compression),
      gistToken: String(raw.gistToken || legacy.token || '').trim(),
      gistId: String(raw.gistId || legacy.gistId || '').trim(),
      debug: Boolean(raw.debug),
      settingsSchemaVersion: SETTINGS_SCHEMA_VERSION
    };
    if (previousSchemaVersion < SETTINGS_SCHEMA_VERSION) {
      // Schema 9: migrate existing users to the new conversion defaults once.
      // Keep gallery layout and sync credentials unchanged.
      if (previousSchemaVersion < 9) {
        config.maxWidth = defaults.maxWidth;
        config.conversionRules = { ...defaults.conversionRules };
        config.compression = { ...defaults.compression };
      } else {
        if (!allowedTargets.image.includes(config.conversionRules.image)) config.conversionRules.image = defaults.conversionRules.image;
        if (!allowedTargets.gif.includes(config.conversionRules.gif)) config.conversionRules.gif = defaults.conversionRules.gif;
        if (!allowedTargets.video.includes(config.conversionRules.video)) config.conversionRules.video = defaults.conversionRules.video;
      }
      GM_setValue(CONFIG_KEY, config);
    }
    return config;
  }

  function saveConfig(next) {
    const current = loadConfig();
    const defaults = DEFAULT_CONFIG();
    const rules = { ...current.conversionRules, ...(next.conversionRules && typeof next.conversionRules === 'object' ? next.conversionRules : {}) };
    const allowedTargets = {
      image: ['keep', 'webp', 'png', 'jpg', 'gif', 'mp4', 'webm'],
      gif: ['keep', 'gif', 'webp', 'png', 'jpg', 'mp4', 'webm'],
      video: ['keep', 'webp', 'gif', 'mp4', 'webm', 'png', 'jpg']
    };
    for (const key of ['image', 'gif', 'video']) if (!allowedTargets[key].includes(String(rules[key]))) rules[key] = defaults.conversionRules[key];
    const compression = normalizeCompressionSettings({
      ...current.compression,
      ...(next.compression && typeof next.compression === 'object' ? next.compression : {})
    }, defaults.compression);
    const config = {
      maxWidth: clampInt(next.maxWidth ?? current.maxWidth, 100, 4000, defaults.maxWidth),
      columns: clampInt(next.columns ?? current.columns, 1, 5, defaults.columns),
      pageSize: clampInt(next.pageSize ?? current.pageSize, 10, 500, defaults.pageSize),
      tileView: (next.tileView ?? current.tileView) === 'grid' ? 'grid' : 'masonry',
      previewMaxSize: clampInt(next.previewMaxSize ?? current.previewMaxSize, 1, 4000, defaults.previewMaxSize),
      previewTileBoost: clampInt(next.previewTileBoost ?? current.previewTileBoost, 0, 100, defaults.previewTileBoost),
      conversionRules: rules,
      compression,
      gistToken: String(next.gistToken ?? current.gistToken).trim(),
      gistId: String(next.gistId ?? current.gistId).trim(),
      debug: Boolean(next.debug ?? current.debug),
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
      // Keep the common case cheap: reuse records that already have normalized metadata.
      items: Array.isArray(data.items) ? data.items.map(item => {
        if (!item || typeof item !== 'object') return item;
        const mediaKind = normalizeStoredMediaKind(item);
        const mediaKindCheckedAt = Math.max(0, Math.floor(Number(item.mediaKindCheckedAt) || 0));
        return item.mediaKind === mediaKind && item.mediaKindCheckedAt === mediaKindCheckedAt
          ? item
          : { ...item, mediaKind, mediaKindCheckedAt };
      }) : [],
      deleted: data.deleted && typeof data.deleted === 'object' ? { ...data.deleted } : {}
    };
    normalized.items.sort(compareGalleryItems);
    normalized.deleted = Object.fromEntries(Object.entries(normalized.deleted).sort(([a], [b]) => a.localeCompare(b)));
    return normalized;
  }

  function compareGalleryItems(a, b) {
    return (Number(b.addedAt) || 0) - (Number(a.addedAt) || 0) ||
      (Number(b.updatedAt) || 0) - (Number(a.updatedAt) || 0);
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
      if (!old) {
        byId.set(item.id, item);
        continue;
      }

      // Media classification is derived metadata, not a user edit. Merge it
      // independently of updatedAt so sync cannot silently erase a verified result.
      const selected = (Number(item.updatedAt) || 0) > (Number(old.updatedAt) || 0) ? item : old;
      const metadataCandidates = [selected, old, item];
      const rankMediaKind = record => {
        const kind = normalizeStoredMediaKind(record);
        return kind === 'photo' || kind === 'animated' ? 2 : kind === 'unavailable' ? 1 : 0;
      };
      let classification = metadataCandidates[0];
      for (const candidate of metadataCandidates.slice(1)) {
        const candidateRank = rankMediaKind(candidate);
        const selectedRank = rankMediaKind(classification);
        const candidateCheckedAt = Number(candidate.mediaKindCheckedAt) || 0;
        const selectedCheckedAt = Number(classification.mediaKindCheckedAt) || 0;
        if (candidateRank > selectedRank ||
            (candidateRank === selectedRank && candidateCheckedAt > selectedCheckedAt)) {
          classification = candidate;
        }
      }
      byId.set(item.id, {
        ...selected,
        mediaKind: normalizeStoredMediaKind(classification),
        mediaKindCheckedAt: Math.max(0, Math.floor(Number(classification.mediaKindCheckedAt) || 0))
      });
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

  function renderDebugLog(target = document.getElementById('twgif-debug-log')) {
    if (!target) return;
    const fragment = document.createDocumentFragment();
    for (const entry of debugLogEntries) {
      const row = document.createElement('div');
      row.className = 'twgif-log-entry';
      row.dataset.type = entry.type;
      const time = document.createElement('span');
      time.className = 'twgif-log-time';
      time.textContent = entry.time + '  ';
      const message = document.createElement('span');
      message.className = 'twgif-log-message';
      message.textContent = entry.message;
      row.append(time, message);
      fragment.appendChild(row);
    }
    target.replaceChildren(fragment);
    target.scrollTop = target.scrollHeight;
  }

  function appendLogEntry(message, type = 'info') {
    const clean = String(message || '').trim();
    if (!clean) return;
    const dedupeText = clean
      .replace(/\b\d{1,3}%\b/g, '{percent}')
      .replace(/кадр\s+\d+\s+из\s+\d+/ig, 'кадр {n} из {n}')
      .replace(/\b\d+\s+из\s+\d+\b/g, '{n} из {n}');
    const signature = type + ':' + dedupeText;
    const now = Date.now();
    // Avoid flooding the log with near-identical repeated status/progress updates.
    if (signature === lastLogSignature && now - lastLogTimestamp < 1800) return;
    lastLogSignature = signature;
    lastLogTimestamp = now;
    const time = new Date(now).toLocaleTimeString();
    const line = time + '  ' + clean;
    debugLogs.push(line);
    debugLogEntries.push({ time, message: clean, type, timestamp: now });
    if (debugLogs.length > 100) debugLogs.shift();
    if (debugLogEntries.length > 100) debugLogEntries.shift();
    renderDebugLog();
  }

  function inferLogType(text) {
    const value = String(text || '');
    if (/\b(error|failed|failure|exception)\b|ошибк|не удалось|отказ|HTTP\s*[45]\d\d/i.test(value)) return 'error';
    if (/\b(warn|warning|fallback)\b|предупреж|не поддерживается|недоступен/i.test(value)) return 'warning';
    if (/\b(success|succeeded)\b|успеш|добавлено|добавлен|готово|завершен|синхронизирован/i.test(value)) return 'success';
    if (/\b(progress|loading)\b|загружа|сжима|конвертир|обработк|подготавливаю|скачиваю|кадр\s+\d+\s+из\s+\d+/i.test(value)) return 'progress';
    return 'info';
  }

  function logDebug(...parts) {
    const text = parts.map(part => {
      if (part instanceof Error) return part.name + ': ' + part.message;
      if (typeof part === 'string') return part;
      try { return JSON.stringify(part); } catch (_) { return String(part); }
    }).join(' ');
    const statusMatch = text.match(/^status:(success|error|warning|progress|info)\s*(.*)$/is);
    if (statusMatch) appendLogEntry(statusMatch[2], statusMatch[1].toLowerCase());
    else appendLogEntry(text, inferLogType(text));
    if (loadConfig().debug) console.debug('[Twitch GIF Gallery]', ...parts);
  }

  function updateStatusIndicator() {
    const button = document.getElementById('twgif-status-indicator');
    if (!button) return;
    const type = progressActive ? 'progress' : lastStatusType;
    const message = lastStatus || (progressActive ? 'Идёт обработка…' : 'Нет новых сообщений');
    button.dataset.type = ['success', 'error', 'warning', 'progress'].includes(type) ? type : 'info';
    button.title = message;
    button.setAttribute('aria-label', 'Статус: ' + message + '. Нажми, чтобы открыть журнал.');
  }

  function setStatus(message, type = 'info', sticky = false) {
    lastStatus = String(message || '');
    lastStatusType = type || 'info';
    updateStatusIndicator();
    if (message) {
      const logType = lastStatusType === 'info' && sticky ? 'progress' : lastStatusType;
      logDebug('status:' + logType, message);
    }
  }

  function syncProgressIndicatorView() {
    const indicator = document.getElementById('twgif-progress');
    if (!indicator) return;
    indicator.hidden = !progressActive;
    if (!progressActive) {
      indicator.dataset.cancelable = 'false';
      return;
    }
    const label = indicator.querySelector('#twgif-progress-label');
    const isDeterminate = progressPercent !== null && progressPercent !== '' && Number.isFinite(Number(progressPercent));
    if (isDeterminate) {
      const value = Math.max(0, Math.min(100, Math.round(Number(progressPercent))));
      indicator.dataset.indeterminate = 'false';
      indicator.style.setProperty('--twgif-progress', String(value));
      if (label) label.textContent = value + '%';
      indicator.setAttribute('aria-label', 'Обработка: ' + value + '%');
    } else {
      indicator.dataset.indeterminate = 'true';
      indicator.style.setProperty('--twgif-progress', '24');
      if (label) label.textContent = '…';
      indicator.setAttribute('aria-label', 'Идёт обработка');
    }
  }

  function setProgress(percent, active = true) {
    if (progressHideTimer) clearTimeout(progressHideTimer);
    progressHideTimer = 0;
    progressGeneration++;
    progressActive = Boolean(active);
    progressPercent = active ? percent : null;
    syncProgressIndicatorView();
    updateStatusIndicator();
  }

  function finishProgress(delayMs = 900) {
    if (progressHideTimer) clearTimeout(progressHideTimer);
    const generation = progressGeneration;
    progressHideTimer = setTimeout(() => {
      if (generation === progressGeneration) setProgress(null, false);
    }, delayMs);
  }

  function setProgressCancelable(active) {
    const indicator = document.getElementById('twgif-progress');
    if (indicator) indicator.dataset.cancelable = String(Boolean(active));
  }

  function isProcessingRunCurrent(runId) {
    return runId == null || Number(runId) === processingRunId;
  }

  function ensureProcessingRun(runId) {
    if (isProcessingRunCurrent(runId)) return;
    const error = new Error('Обработка отменена пользователем.');
    error.name = 'AbortError';
    throw error;
  }

  function terminateLocalFfmpegWorker(reason = 'Обработка отменена пользователем.') {
    const worker = localFfmpegWorker;
    const workerUrl = localFfmpegWorkerUrl;
    localFfmpegWorker = null;
    localFfmpegWorkerUrl = '';
    if (worker) {
      try { worker.terminate(); } catch (_) {}
    }
    if (workerUrl) {
      try { URL.revokeObjectURL(workerUrl); } catch (_) {}
    }
    for (const [id, pending] of Array.from(localFfmpegPending.entries())) {
      clearTimeout(pending.timeout);
      localFfmpegPending.delete(id);
      const error = new Error(reason);
      error.name = 'AbortError';
      pending.reject(error);
    }
  }

  function cancelActiveProcessing() {
    if (!activeProcessingRunId) return;
    const cancelledRun = activeProcessingRunId;
    processingRunId++;
    activeProcessingRunId = 0;
    syncTriggerUploadIndicator();

    const uploadRequest = activeUploadRequest;
    activeUploadRequest = null;
    if (uploadRequest && typeof uploadRequest.abort === 'function') {
      try { uploadRequest.abort(); } catch (_) {}
    }
    terminateLocalFfmpegWorker();

    setProgressCancelable(false);
    setProgress(null, false);
    setStatus('Обработка отменена.', 'info', true);
    logDebug('File processing cancelled by user', { runId: cancelledRun });
  }

  // Network layer: GM_xmlhttpRequest is used for cross-origin media and API requests.
  function request(options) {
    return new Promise((resolve, reject) => {
      const { acceptHttpErrors = false, trackForCancel = false, ...xhrOptions } = options;
      let xhr = null;
      const clearTrackedRequest = () => {
        if (trackForCancel && activeUploadRequest === xhr) activeUploadRequest = null;
      };
      xhr = GM_xmlhttpRequest({
        ...xhrOptions,
        timeout: options.timeout || 35000,
        onload: response => {
          clearTrackedRequest();
          if ((response.status >= 200 && response.status < 300) || acceptHttpErrors) resolve(response);
          else {
            const detail = String(response.responseText || '').slice(0, 500);
            reject(new Error('HTTP ' + response.status + (detail ? ' — ' + detail : '')));
          }
        },
        onerror: () => {
          clearTrackedRequest();
          reject(new Error('Сетевая ошибка. Проверь соединение и доступ к сервису.'));
        },
        ontimeout: () => {
          clearTrackedRequest();
          reject(new Error('Истекло время ожидания ответа сервера.'));
        },
        onabort: () => {
          clearTrackedRequest();
          const error = new Error('Запрос отменён пользователем.');
          error.name = 'AbortError';
          reject(error);
        }
      });
      if (trackForCancel) activeUploadRequest = xhr;
    });
  }

  function requestBlob(url, timeout = 120000, trackForCancel = false) {
    return new Promise((resolve, reject) => {
      let xhr = null;
      const clearTrackedRequest = () => {
        if (trackForCancel && activeUploadRequest === xhr) activeUploadRequest = null;
      };
      xhr = GM_xmlhttpRequest({
        method: 'GET', url, responseType: 'blob', timeout,
        onload: response => {
          clearTrackedRequest();
          if (response.status < 200 || response.status >= 300) {
            reject(new Error('Не удалось скачать медиа по ссылке (HTTP ' + response.status + ').'));
            return;
          }
          const headerMime = String(response.responseHeaders?.match(/content-type:\s*([^;\r\n]+)/i)?.[1] || '').trim().toLowerCase();
          const receivedBlob = response.response instanceof Blob
            ? response.response
            : new Blob([response.response], { type: headerMime || 'application/octet-stream' });
          const receivedMime = String(receivedBlob.type || '').trim().toLowerCase();
          const mime = /^(image|video)\//i.test(headerMime)
            ? headerMime
            : (receivedMime || headerMime || 'application/octet-stream');
          const blob = receivedBlob.type === mime
            ? receivedBlob
            : new Blob([receivedBlob], { type: mime });
          resolve(blob);
        },
        onerror: () => {
          clearTrackedRequest();
          reject(new Error('Не удалось скачать медиа по ссылке.'));
        },
        ontimeout: () => {
          clearTrackedRequest();
          reject(new Error('Истекло время скачивания медиа по ссылке.'));
        },
        onabort: () => {
          clearTrackedRequest();
          const error = new Error('Загрузка медиа по ссылке отменена.');
          error.name = 'AbortError';
          reject(error);
        }
      });
      if (trackForCancel) activeUploadRequest = xhr;
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
      avif: 'image/avif', apng: 'image/png', bmp: 'image/bmp', svg: 'image/svg+xml',
      mp4: 'video/mp4', m4v: 'video/mp4', mov: 'video/quicktime', webm: 'video/webm',
      mkv: 'video/x-matroska', avi: 'video/x-msvideo', ogv: 'video/ogg', mpg: 'video/mpeg', mpeg: 'video/mpeg'
    };
    return map[ext] || '';
  }

  async function isAnimatedWebP(file) {
    if (!file || !file.size || (mimeFromFile(file) !== 'image/webp' && fileExtension(file) !== 'webp')) return false;
    try {
      // The VP8X animation flag is near the beginning of a WebP file. ANIM/ANMF
      // chunks are additional definitive signals for animated containers.
      const buffer = await file.slice(0, Math.min(file.size, 1024 * 1024)).arrayBuffer();
      const bytes = new Uint8Array(buffer);
      if (bytes.length < 16) return false;
      const ascii = (offset, length) => String.fromCharCode(...bytes.subarray(offset, offset + length));
      if (ascii(0, 4) !== 'RIFF' || ascii(8, 4) !== 'WEBP') return false;
      let offset = 12;
      while (offset + 8 <= bytes.length) {
        const chunkType = ascii(offset, 4);
        const chunkLength = bytes[offset + 4] |
          (bytes[offset + 5] << 8) |
          (bytes[offset + 6] << 16) |
          (bytes[offset + 7] << 24);
        const payloadOffset = offset + 8;
        if (chunkType === 'ANIM' || chunkType === 'ANMF') return true;
        if (chunkType === 'VP8X' && chunkLength > 0 &&
            payloadOffset < bytes.length && (bytes[payloadOffset] & 0x02) !== 0) return true;
        if (chunkLength < 0) break;
        const nextOffset = payloadOffset + chunkLength + (chunkLength & 1);
        if (nextOffset <= offset || nextOffset > bytes.length) break;
        offset = nextOffset;
      }
    } catch (error) {
      logDebug('Animated WebP detection failed', error);
    }
    return false;
  }

  function webpReadU24LE(bytes, offset) {
    return (bytes[offset] || 0) | ((bytes[offset + 1] || 0) << 8) | ((bytes[offset + 2] || 0) << 16);
  }

  function webpReadU32LE(bytes, offset) {
    return ((bytes[offset] || 0) | ((bytes[offset + 1] || 0) << 8) |
      ((bytes[offset + 2] || 0) << 16) | ((bytes[offset + 3] || 0) << 24)) >>> 0;
  }

  function webpWriteU24LE(bytes, offset, value) {
    const number = Math.max(0, Math.floor(Number(value) || 0));
    bytes[offset] = number & 255;
    bytes[offset + 1] = (number >>> 8) & 255;
    bytes[offset + 2] = (number >>> 16) & 255;
  }

  function webpWriteU32LE(bytes, offset, value) {
    const number = Math.max(0, Math.floor(Number(value) || 0)) >>> 0;
    bytes[offset] = number & 255;
    bytes[offset + 1] = (number >>> 8) & 255;
    bytes[offset + 2] = (number >>> 16) & 255;
    bytes[offset + 3] = (number >>> 24) & 255;
  }

  function webpAscii(bytes, offset, length) {
    let value = '';
    for (let index = offset; index < offset + length; index++) value += String.fromCharCode(bytes[index] || 0);
    return value;
  }

  function webpJoinBytes(parts) {
    const validParts = parts.filter(part => part && part.byteLength !== 0);
    const size = validParts.reduce((total, part) => total + part.byteLength, 0);
    const output = new Uint8Array(size);
    let offset = 0;
    for (const part of validParts) {
      output.set(part instanceof Uint8Array ? part : new Uint8Array(part), offset);
      offset += part.byteLength;
    }
    return output;
  }

  function webpMakeChunk(type, payload) {
    const data = payload instanceof Uint8Array ? payload : new Uint8Array(payload);
    const header = new Uint8Array(8);
    for (let index = 0; index < 4; index++) header[index] = type.charCodeAt(index);
    webpWriteU32LE(header, 4, data.length);
    const padding = data.length & 1 ? new Uint8Array(1) : null;
    return webpJoinBytes([header, data, padding]);
  }

  function webpMakeRiff(chunks) {
    const webpTag = new Uint8Array([87, 69, 66, 80]); // WEBP
    const body = webpJoinBytes([webpTag, ...chunks]);
    const header = new Uint8Array(8);
    header.set([82, 73, 70, 70], 0); // RIFF
    webpWriteU32LE(header, 4, body.length);
    return new Blob([header, body], { type: 'image/webp' });
  }

  function webpParseChunks(bytes, start = 12, end = bytes.length) {
    const chunks = [];
    let offset = start;
    const safeEnd = Math.min(bytes.length, Math.max(start, end));
    while (offset + 8 <= safeEnd) {
      const type = webpAscii(bytes, offset, 4);
      const length = webpReadU32LE(bytes, offset + 4);
      const payloadStart = offset + 8;
      const payloadEnd = payloadStart + length;
      if (payloadEnd > safeEnd || payloadEnd < payloadStart) break;
      chunks.push({
        type,
        data: bytes.subarray(payloadStart, payloadEnd),
        byteLength: 8 + length + (length & 1)
      });
      offset = payloadEnd + (length & 1);
    }
    return chunks;
  }

  function webpMakeCanvas(width, height) {
    if (typeof OffscreenCanvas === 'function') return new OffscreenCanvas(width, height);
    const canvas = document.createElement('canvas');
    canvas.width = width;
    canvas.height = height;
    return canvas;
  }

  async function webpCanvasToBlob(canvas, quality) {
    if (typeof canvas.convertToBlob === 'function') {
      return canvas.convertToBlob({ type: 'image/webp', quality });
    }
    return new Promise((resolve, reject) => {
      canvas.toBlob(blob => blob ? resolve(blob) : reject(new Error('Браузер не смог сжать кадр в WebP.')), 'image/webp', quality);
    });
  }

  function webpMakeCanvasHeader(width, height, alpha) {
    const payload = new Uint8Array(10);
    payload[0] = alpha ? 0x10 : 0;
    webpWriteU24LE(payload, 4, width - 1);
    webpWriteU24LE(payload, 7, height - 1);
    return webpMakeChunk('VP8X', payload);
  }

  async function compressAnimatedWebP(file, maxWidth, quality, runId = null) {
    if (!file || !file.size) throw new Error('Файл пустой.');
    const inputBytes = new Uint8Array(await file.arrayBuffer());
    ensureProcessingRun(runId);
    if (inputBytes.length < 30 || webpAscii(inputBytes, 0, 4) !== 'RIFF' ||
        webpAscii(inputBytes, 8, 4) !== 'WEBP') {
      throw new Error('Повреждённый заголовок WebP.');
    }

    const topChunks = webpParseChunks(inputBytes, 12, inputBytes.length);
    const sourceVp8x = topChunks.find(chunk => chunk.type === 'VP8X');
    const sourceAnim = topChunks.find(chunk => chunk.type === 'ANIM');
    const sourceFrames = topChunks.filter(chunk => chunk.type === 'ANMF');
    if (!sourceVp8x || !sourceAnim || !sourceFrames.length || sourceVp8x.data.length < 10 || sourceAnim.data.length < 6) {
      throw new Error('Не удалось прочитать структуру кадров анимированного WebP.');
    }

    const originalWidth = webpReadU24LE(sourceVp8x.data, 4) + 1;
    const originalHeight = webpReadU24LE(sourceVp8x.data, 7) + 1;
    if (!originalWidth || !originalHeight) throw new Error('Не удалось определить размеры анимированного WebP.');

    const configuredWidth = clampInt(maxWidth, 100, 4000, DEFAULT_MAX_WIDTH);
    const scale = originalWidth > configuredWidth ? configuredWidth / originalWidth : 1;
    const canvasWidth = Math.max(1, Math.round(originalWidth * scale));
    const canvasHeight = Math.max(1, Math.round(originalHeight * scale));
    const sourceAlpha = (sourceVp8x.data[0] & 0x10) !== 0;
    const iccChunk = topChunks.find(chunk => chunk.type === 'ICCP');
    const iccBlock = iccChunk ? webpMakeChunk('ICCP', iccChunk.data) : null;

    const encodeAtQuality = async encodeQuality => {
      const outputFrames = [];
      for (let index = 0; index < sourceFrames.length; index++) {
        ensureProcessingRun(runId);
        const sourceFrame = sourceFrames[index];
        if (sourceFrame.data.length < 16) throw new Error('Некорректный кадр WebP №' + (index + 1) + '.');

        const sourceX = webpReadU24LE(sourceFrame.data, 0) * 2;
        const sourceY = webpReadU24LE(sourceFrame.data, 3) * 2;
        const sourceWidth = webpReadU24LE(sourceFrame.data, 6) + 1;
        const sourceHeight = webpReadU24LE(sourceFrame.data, 9) + 1;
        const duration = webpReadU24LE(sourceFrame.data, 12);
        const frameFlags = sourceFrame.data[15];
        const frameChunks = webpParseChunks(sourceFrame.data, 16, sourceFrame.data.length);
        const alphaChunk = frameChunks.find(chunk => chunk.type === 'ALPH');
        const encodedImageChunks = frameChunks.filter(chunk =>
          chunk.type === 'ALPH' || chunk.type === 'VP8 ' || chunk.type === 'VP8L'
        );
        if (!encodedImageChunks.some(chunk => chunk.type === 'VP8 ' || chunk.type === 'VP8L')) {
          throw new Error('В кадре WebP №' + (index + 1) + ' не найдено изображение.');
        }

        const standaloneChunks = [
          webpMakeCanvasHeader(sourceWidth, sourceHeight, sourceAlpha || Boolean(alphaChunk)),
          ...encodedImageChunks.map(chunk => webpMakeChunk(chunk.type, chunk.data))
        ];
        const standalone = webpMakeRiff(standaloneChunks);
        let bitmap = null;
        try {
          bitmap = await createImageBitmap(standalone);
          const frameX = Math.min(canvasWidth - 1, Math.max(0, Math.round((sourceX * scale) / 2) * 2));
          const frameY = Math.min(canvasHeight - 1, Math.max(0, Math.round((sourceY * scale) / 2) * 2));
          const frameWidth = Math.max(1, Math.min(canvasWidth - frameX, Math.round(sourceWidth * scale)));
          const frameHeight = Math.max(1, Math.min(canvasHeight - frameY, Math.round(sourceHeight * scale)));
          const canvas = webpMakeCanvas(frameWidth, frameHeight);
          const context = canvas.getContext('2d', { alpha: true });
          if (!context) throw new Error('Canvas недоступен при сжатии анимированного WebP.');
          context.clearRect(0, 0, frameWidth, frameHeight);
          context.drawImage(bitmap, 0, 0, frameWidth, frameHeight);
          const encodedBlob = await webpCanvasToBlob(canvas, encodeQuality);
          if (!encodedBlob || !encodedBlob.size || !/^image\/webp$/i.test(encodedBlob.type || '')) {
            throw new Error('Браузер не вернул WebP при сжатии кадра.');
          }
          const encodedBytes = new Uint8Array(await encodedBlob.arrayBuffer());
          const encodedChunks = webpParseChunks(encodedBytes, 12, encodedBytes.length)
            .filter(chunk => chunk.type === 'ALPH' || chunk.type === 'VP8 ' || chunk.type === 'VP8L');
          if (!encodedChunks.some(chunk => chunk.type === 'VP8 ' || chunk.type === 'VP8L')) {
            throw new Error('Не удалось извлечь сжатый кадр WebP.');
          }

          const frameHeader = new Uint8Array(16);
          webpWriteU24LE(frameHeader, 0, Math.floor(frameX / 2));
          webpWriteU24LE(frameHeader, 3, Math.floor(frameY / 2));
          webpWriteU24LE(frameHeader, 6, frameWidth - 1);
          webpWriteU24LE(frameHeader, 9, frameHeight - 1);
          webpWriteU24LE(frameHeader, 12, duration);
          frameHeader[15] = frameFlags;
          outputFrames.push(webpMakeChunk('ANMF', webpJoinBytes([
            frameHeader,
            ...encodedChunks.map(chunk => webpMakeChunk(chunk.type, chunk.data))
          ])));
        } finally {
          if (bitmap && typeof bitmap.close === 'function') bitmap.close();
        }

        if (index === sourceFrames.length - 1 || index % 8 === 0) {
          setProgress(10 + Math.round(((index + 1) / sourceFrames.length) * 78), true);
          setStatus('Сжимаю анимированный WebP: кадр ' + (index + 1) + ' из ' + sourceFrames.length + '…', 'info', true);
        }
      }

      const vp8xData = new Uint8Array(10);
      vp8xData[0] = 0x02 | (sourceAlpha ? 0x10 : 0) | (iccChunk ? 0x20 : 0);
      webpWriteU24LE(vp8xData, 4, canvasWidth - 1);
      webpWriteU24LE(vp8xData, 7, canvasHeight - 1);
      const outputChunks = [
        webpMakeChunk('VP8X', vp8xData),
        ...(iccBlock ? [iccBlock] : []),
        webpMakeChunk('ANIM', sourceAnim.data),
        ...outputFrames
      ];
      return webpMakeRiff(outputChunks);
    };

    const initialQuality = clampInt(Math.round((Number(quality) || 0.68) * 100), 20, 100, 68) / 100;
    const qualities = [...new Set([
      initialQuality,
      Math.min(initialQuality, 0.54),
      Math.min(initialQuality, 0.40),
      Math.min(initialQuality, 0.28)
    ])];
    let smallest = null;
    for (let attempt = 0; attempt < qualities.length; attempt++) {
      ensureProcessingRun(runId);
      const candidate = await encodeAtQuality(qualities[attempt]);
      if (!smallest || candidate.size < smallest.size) smallest = candidate;
      if (candidate.size < file.size) {
        const baseName = String(file.name || 'animated.webp').replace(/\.[^.]+$/i, '') || 'animated';
        const output = new File([candidate], baseName + '.webp', {
          type: 'image/webp',
          lastModified: Date.now()
        });
        logDebug('Animated WebP compressed', {
          inputBytes: file.size,
          outputBytes: output.size,
          quality: qualities[attempt],
          sourceFrames: sourceFrames.length,
          sourceWidth: originalWidth,
          outputWidth: canvasWidth
        });
        setStatus('Анимированный WebP сжат: ' + formatBytes(file.size) + ' → ' + formatBytes(output.size) + '.', 'success');
        setProgress(95, true);
        return output;
      }
    }

    logDebug('Animated WebP compression was not smaller; original retained', {
      inputBytes: file.size,
      smallestOutputBytes: smallest ? smallest.size : 0,
      sourceFrames: sourceFrames.length
    });
    setStatus('Анимированный WebP уже оптимизирован: оригинал меньше результата сжатия.', 'info');
    setProgress(95, true);
    return file;
  }

  // Local IndexedDB cache is per origin; the bounded GM cache below is shared across matched sites.
  function openMediaCacheDb() {
    if (mediaCacheDbPromise) return mediaCacheDbPromise;
    if (typeof indexedDB === 'undefined') return Promise.resolve(null);
    mediaCacheDbPromise = new Promise(resolve => {
      let request;
      try { request = indexedDB.open(MEDIA_CACHE_DB, 1); }
      catch (_) { mediaCacheDbPromise = null; resolve(null); return; }
      request.onupgradeneeded = () => {
        const db = request.result;
        if (!db.objectStoreNames.contains(MEDIA_CACHE_STORE)) {
          db.createObjectStore(MEDIA_CACHE_STORE, { keyPath: 'url' });
        }
      };
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => { mediaCacheDbPromise = null; resolve(null); };
      request.onblocked = () => { mediaCacheDbPromise = null; resolve(null); };
    });
    return mediaCacheDbPromise;
  }

  function getCachedMediaBlob(url) {
    return openMediaCacheDb().then(db => {
      if (!db) return null;
      return new Promise(resolve => {
        let transaction;
        try { transaction = db.transaction(MEDIA_CACHE_STORE, 'readwrite'); }
        catch (_) { resolve(null); return; }
        const store = transaction.objectStore(MEDIA_CACHE_STORE);
        const request = store.get(String(url));
        request.onsuccess = () => {
          const record = request.result;
          if (!record || !record.blob || typeof record.blob.size !== 'number') { resolve(null); return; }
          record.lastUsedAt = Date.now();
          store.put(record);
          resolve(record.blob);
        };
        request.onerror = () => resolve(null);
        transaction.onabort = () => resolve(null);
      });
    }).catch(() => null);
  }

  function cacheMediaBlob(url, blob) {
    const key = String(url || '').trim();
    if (!key || !(blob instanceof Blob) || !blob.size || blob.size > MEDIA_CACHE_MAX_ENTRY_BYTES) {
      return Promise.resolve(false);
    }
    return openMediaCacheDb().then(db => {
      if (!db) return false;
      return new Promise(resolve => {
        let transaction;
        try { transaction = db.transaction(MEDIA_CACHE_STORE, 'readwrite'); }
        catch (_) { resolve(false); return; }
        const store = transaction.objectStore(MEDIA_CACHE_STORE);
        store.put({ url: key, blob, size: blob.size, mime: blob.type || '', lastUsedAt: Date.now() });
        const allRequest = store.getAll();
        allRequest.onsuccess = () => {
          const records = Array.isArray(allRequest.result) ? allRequest.result.slice() : [];
          let total = records.reduce((sum, record) => sum + (Number(record.size) || Number(record.blob && record.blob.size) || 0), 0);
          records.sort((a, b) => (Number(a.lastUsedAt) || 0) - (Number(b.lastUsedAt) || 0));
          for (const record of records) {
            if (total <= MEDIA_CACHE_MAX_BYTES) break;
            store.delete(record.url);
            total -= Number(record.size) || Number(record.blob && record.blob.size) || 0;
          }
        };
        allRequest.onerror = () => {};
        transaction.oncomplete = () => resolve(true);
        transaction.onerror = () => resolve(false);
        transaction.onabort = () => resolve(false);
      });
    }).catch(() => false);
  }

  function sharedMediaHash(value) {
    const text = String(value || '');
    let first = 0x811c9dc5;
    let second = 0x9e3779b9;
    for (let i = 0; i < text.length; i++) {
      const code = text.charCodeAt(i);
      first = Math.imul(first ^ code, 0x01000193);
      second = Math.imul(second ^ (code + i), 0x85ebca6b);
    }
    return (first >>> 0).toString(36) + (second >>> 0).toString(36);
  }

  function sharedMediaEntryKey(url) {
    return SHARED_MEDIA_ENTRY_PREFIX + sharedMediaHash(url);
  }

  function readSharedMediaIndex() {
    try {
      const raw = GM_getValue(SHARED_MEDIA_INDEX_KEY, []);
      const value = parseJson(raw, []);
      if (!Array.isArray(value)) return [];
      return value.filter(item => item && typeof item.url === 'string' &&
        typeof item.key === 'string' && Number(item.storedSize) > 0);
    } catch (_) {
      return [];
    }
  }

  function writeSharedMediaIndex(entries) {
    try { GM_setValue(SHARED_MEDIA_INDEX_KEY, entries); return true; }
    catch (error) { logDebug('Shared media index write failed', error); return false; }
  }

  async function blobToBase64(blob) {
    const bytes = new Uint8Array(await blob.arrayBuffer());
    let binary = '';
    const chunkSize = 0x8000;
    for (let offset = 0; offset < bytes.length; offset += chunkSize) {
      binary += String.fromCharCode(...bytes.subarray(offset, Math.min(offset + chunkSize, bytes.length)));
    }
    return btoa(binary);
  }

  function sharedBase64ToBlob(base64, mime = 'application/octet-stream') {
    try {
      const binary = atob(base64);
      const bytes = new Uint8Array(binary.length);
      for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
      return new Blob([bytes], { type: mime || 'application/octet-stream' });
    } catch (_) {
      return null;
    }
  }

  async function getSharedMediaBlob(url) {
    const key = String(url || '').trim();
    if (!key) return null;
    const entries = readSharedMediaIndex();
    const entry = entries.find(item => item.url === key);
    if (!entry) return null;
    try {
      const encoded = GM_getValue(entry.key, '');
      if (typeof encoded !== 'string' || !encoded || encoded.length !== Number(entry.storedSize)) {
        writeSharedMediaIndex(entries.filter(item => item.url !== key));
        return null;
      }
      entry.lastUsedAt = Date.now();
      writeSharedMediaIndex(entries);
      return sharedBase64ToBlob(encoded, entry.mime);
    } catch (_) {
      return null;
    }
  }

  async function cacheSharedMediaBlob(url, blob) {
    const key = String(url || '').trim();
    if (!key || !(blob instanceof Blob) || !blob.size || blob.size > SHARED_MEDIA_CACHE_MAX_ENTRY_BYTES) return false;
    const entries = readSharedMediaIndex();
    const existing = entries.find(item => item.url === key);
    if (existing) {
      existing.lastUsedAt = Date.now();
      writeSharedMediaIndex(entries);
      return true;
    }
    let encoded;
    try { encoded = await blobToBase64(blob); }
    catch (_) { return false; }
    if (!encoded || encoded.length > SHARED_MEDIA_CACHE_MAX_BYTES) return false;

    // Re-read after the async encoding step so two tabs caching different files
    // at once are less likely to overwrite each other's index entries.
    const latestEntries = readSharedMediaIndex();
    const latestExisting = latestEntries.find(item => item.url === key);
    if (latestExisting) {
      latestExisting.lastUsedAt = Date.now();
      writeSharedMediaIndex(latestEntries);
      return true;
    }
    let storageKey = sharedMediaEntryKey(key);
    const collision = latestEntries.find(item => item.key === storageKey && item.url !== key);
    if (collision) storageKey += ':' + sharedMediaHash(key + '|collision');
    try { GM_setValue(storageKey, encoded); }
    catch (error) { logDebug('Shared media blob write failed', { url: key, size: blob.size, error: error.message || error }); return false; }

    const next = latestEntries.filter(item => item.url !== key);
    next.push({ url: key, key: storageKey, size: blob.size, storedSize: encoded.length, mime: blob.type || '', lastUsedAt: Date.now() });
    let total = next.reduce((sum, item) => sum + (Number(item.storedSize) || 0), 0);
    next.sort((a, b) => (Number(a.lastUsedAt) || 0) - (Number(b.lastUsedAt) || 0));
    while (total > SHARED_MEDIA_CACHE_MAX_BYTES && next.length) {
      const removed = next.shift();
      total -= Number(removed.storedSize) || 0;
      try { GM_deleteValue(removed.key); } catch (_) {}
    }
    if (!writeSharedMediaIndex(next)) {
      try { GM_deleteValue(storageKey); } catch (_) {}
      return false;
    }
    return next.some(item => item.url === key);
  }
  function cachedObjectUrlFor(url, blob) {
    const key = String(url || '');
    if (cachedMediaObjectUrls.has(key)) return cachedMediaObjectUrls.get(key);
    const objectUrl = URL.createObjectURL(blob);
    cachedMediaObjectUrls.set(key, objectUrl);
    return objectUrl;
  }

  async function cacheRemoteMedia(url, isVideo = false) {
    const key = String(url || '').trim();
    if (!key || mediaCachePendingUrls.has(key) || cachedMediaObjectUrls.has(key)) return;
    mediaCachePendingUrls.add(key);
    try {
      // HEAD prevents large videos from being downloaded a second time just for caching.
      const head = await request({ method: 'HEAD', url: key, timeout: 12000, acceptHttpErrors: true });
      if (head.status < 200 || head.status >= 300) return;
      const match = String(head.responseHeaders || '').match(/content-length:\s*(\d+)/i);
      const size = match ? Number(match[1]) : 0;
      if (!Number.isFinite(size) || size <= 0 || size > MEDIA_CACHE_MAX_REMOTE_BYTES) return;
      if (isVideo && size > MEDIA_CACHE_MAX_REMOTE_VIDEO_BYTES) return;
      const blob = await requestBlob(key, 60000, false);
      if (blob.size > 0 && blob.size <= MEDIA_CACHE_MAX_ENTRY_BYTES) {
        await Promise.all([cacheMediaBlob(key, blob), cacheSharedMediaBlob(key, blob)]);
      }
    } catch (_) {
      // The remote URL remains usable; caching is an optional offline/reload optimization.
    } finally {
      mediaCachePendingUrls.delete(key);
    }
  }
  function mediaTypeFromUrl(rawUrl, responseType = '') {
    let pathname = '';
    try { pathname = new URL(rawUrl).pathname.toLowerCase(); } catch (_) {}
    if (String(responseType).startsWith('video/')) return 'video';
    if (/\.(webm|mp4|mov|m4v|mkv|avi|ogv|mpg|mpeg)(?:$)/i.test(pathname)) return 'video';
    if (/\.gif$/i.test(pathname)) return 'gif';
    return 'image';
  }

  function normalizeKappaLink(data, fallbackMime, fallbackName, baseUrl = KAPPA_UPLOAD_URL) {
    const raw = String(data.link || data.url || '').trim();
    if (!raw) throw new Error('Сервис загрузки не вернул ссылку на файл.');
    let url;
    try { url = new URL(raw, baseUrl); }
    catch (_) { throw new Error('Сервис загрузки вернул некорректную ссылку.'); }
    const allowedHosts = ['kappa.lol', 'segs.lol', 'gachi.gay', 'plink.kappa.lol'];
    if (!allowedHosts.includes(url.hostname.toLowerCase())) {
      throw new Error('Сервис загрузки вернул ссылку с неизвестного домена.');
    }
    if (/^\/api(?:\/|$)/i.test(url.pathname) || /\/api\/upload\/?$/i.test(url.pathname)) {
      throw new Error('Сервис загрузки вернул адрес API вместо ссылки на файл.');
    }
    let ext = String(data.ext || getExtension(data.type || fallbackMime, fallbackName)).trim();
    if (ext && !ext.startsWith('.')) ext = '.' + ext;
    if (ext && !url.pathname.toLowerCase().endsWith(ext.toLowerCase())) url.pathname += ext;
    url.protocol = 'https:';
    url.port = '';
    return url.toString();
  }

  function parseKappaUploadPayload(responseText) {
    const raw = String(responseText || '');
    try {
      const value = JSON.parse(raw);
      if (value && typeof value === 'object') return value;
    } catch (_) {}
    const candidates = raw.match(/\{[^{}]*\}/g) || [];
    for (let index = candidates.length - 1; index >= 0; index--) {
      try {
        const value = JSON.parse(candidates[index]);
        if (value && typeof value === 'object' && (value.link || value.url)) return value;
      } catch (_) {}
    }
    return null;
  }

  // Upload and conversion pipeline: processing run IDs make cancellation safe across awaits.
  async function uploadToKappa(file, onUploadProgress = null, runId = null) {
    const endpoints = [KAPPA_UPLOAD_URL, KAPPA_UPLOAD_MIRROR_URL];
    let lastError = null;
    logDebug('Kappa upload start', { name: file.name, size: file.size, type: file.type });

    for (let index = 0; index < endpoints.length; index++) {
      ensureProcessingRun(runId);
      const endpoint = endpoints[index];
      const form = new FormData();
      form.append('file', file, file.name || 'media');
      const response = await request({
        method: 'POST', url: endpoint, data: form, timeout: 120000, acceptHttpErrors: true,
        trackForCancel: true,
        upload: {
          onprogress: event => {
            const loaded = Number(event && event.loaded);
            const total = Number(event && event.total);
            if (total > 0 && loaded >= 0 && typeof onUploadProgress === 'function') {
              onUploadProgress(Math.max(0, Math.min(100, loaded / total * 100)));
            }
          }
        },
        headers: { 'Accept': 'application/json' }
      });
      const successfulStatus = response.status >= 200 && response.status < 300;
      if (!successfulStatus) {
        const detail = String(response.responseText || '').slice(0, 500);
        lastError = new Error('HTTP ' + response.status + (detail ? ' — ' + detail : ''));
        if (index === 0 && response.status >= 500 && response.status < 600) {
          logDebug('Kappa primary upload endpoint returned a server error; trying fallback endpoint', {
            status: response.status, endpoint, fallback: endpoints[index + 1]
          });
          continue;
        }
        throw lastError;
      }

      const result = parseKappaUploadPayload(response.responseText);
      if (!result || !(result.link || result.url) || result.error) {
        lastError = new Error('Сервис загрузки не вернул корректную ссылку на файл.');
        if (index === 0) {
          logDebug('Kappa upload response did not contain usable file metadata; trying fallback endpoint', endpoint);
          continue;
        }
        throw lastError;
      }
      try {
        return {
          url: normalizeKappaLink(result, file.type || mimeFromFile(file), file.name, endpoint),
          type: String(result.type || file.type || mimeFromFile(file) || 'application/octet-stream'),
          name: file.name || 'Медиафайл'
        };
      } catch (error) {
        lastError = error;
        if (index === 0) {
          logDebug('Kappa returned an invalid file URL; trying fallback endpoint', { endpoint, error: error.message || error });
          continue;
        }
        throw error;
      }
    }

    throw lastError || new Error('Не удалось загрузить файл на kappa.lol или резервный сервер.');
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

  async function resizeStaticImage(file, maxWidth, outputFormat = 'webp', quality = 0.84) {
    // Decode only once: use the same bitmap to read dimensions and draw the output.
    const bitmap = await createImageBitmap(file);
    try {
      const dims = { width: bitmap.width, height: bitmap.height };
      if (!dims.width || !dims.height) throw new Error('Не удалось определить размеры изображения.');

      const sourceMime = mimeFromFile(file);
      const needsResize = dims.width > maxWidth;
      if (outputFormat === 'keep' && !needsResize) return file;

      const targetMime = outputFormat === 'keep'
        ? (['image/webp', 'image/png', 'image/jpeg'].includes(sourceMime) ? sourceMime : 'image/webp')
        : ({ webp: 'image/webp', png: 'image/png', jpg: 'image/jpeg' }[outputFormat] || '');
      if (!targetMime || !['image/webp', 'image/png', 'image/jpeg'].includes(targetMime)) {
        throw new Error('Локальная обработка формата ' + outputFormat + ' недоступна.');
      }

      const needsConvert = sourceMime !== targetMime;
      if (!needsResize && !needsConvert) return file;
      if (dims.width * dims.height > 40_000_000) {
        throw new Error('Изображение слишком большое для локального Canvas. Используй FFmpeg или уменьши исходник.');
      }

      const scale = Math.min(1, maxWidth / dims.width);
      const width = Math.max(1, Math.round(dims.width * scale));
      const height = Math.max(1, Math.round(dims.height * scale));
      const canvas = document.createElement('canvas');
      canvas.width = width;
      canvas.height = height;
      const context = canvas.getContext('2d');
      if (!context) throw new Error('Браузер не смог создать холст для изменения размера изображения.');

      if (targetMime === 'image/jpeg') {
        context.fillStyle = '#fff';
        context.fillRect(0, 0, width, height);
      }
      context.drawImage(bitmap, 0, 0, width, height);

      const blob = await canvasToBlob(canvas, targetMime, targetMime === 'image/png' ? undefined : Math.max(0.3, Math.min(1, Number(quality) || 0.84)));
      if (!blob || blob.size < 20 || blob.type !== targetMime) {
        throw new Error('Браузер не смог создать корректный файл ' + outputFormat.toUpperCase() + '.');
      }
      if (targetMime === 'image/webp') {
        const signature = new Uint8Array(await blob.slice(0, 12).arrayBuffer());
        if (signature.length < 12 || signature[0] !== 0x52 || signature[1] !== 0x49 || signature[2] !== 0x46 || signature[3] !== 0x46 ||
            signature[8] !== 0x57 || signature[9] !== 0x45 || signature[10] !== 0x42 || signature[11] !== 0x50) {
          throw new Error('Браузер вернул невалидный WebP-файл.');
        }
      }
      const baseName = String(file.name || 'image').replace(/\.[^.]+$/, '') || 'image';
      const name = baseName + getExtension(blob.type, file.name);
      logDebug('Static image converted locally with Canvas', { from: dims, to: { width, height }, mime: blob.type, inputBytes: file.size, bytes: blob.size });
      return new File([blob], name, { type: blob.type, lastModified: Date.now() });
    } finally {
      if (typeof bitmap.close === 'function') bitmap.close();
    }
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

  function openFfmpegAssetDb() {
    return new Promise((resolve, reject) => {
      if (!('indexedDB' in window)) {
        reject(new Error('IndexedDB недоступен'));
        return;
      }
      const request = indexedDB.open(FFMPEG_CACHE_DB, 1);
      request.onupgradeneeded = () => {
        const db = request.result;
        if (!db.objectStoreNames.contains('assets')) db.createObjectStore('assets', { keyPath: 'id' });
      };
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error || new Error('Не удалось открыть хранилище FFmpeg.wasm'));
      request.onblocked = () => reject(new Error('Хранилище FFmpeg.wasm заблокировано другой вкладкой'));
    });
  }

  async function readFfmpegAssetCache() {
    const db = await openFfmpegAssetDb();
    return new Promise((resolve, reject) => {
      let value = null;
      const tx = db.transaction('assets', 'readonly');
      const request = tx.objectStore('assets').get('core');
      request.onsuccess = () => { value = request.result || null; };
      request.onerror = () => reject(request.error || new Error('Не удалось прочитать кэш FFmpeg.wasm'));
      tx.oncomplete = () => { db.close(); resolve(value); };
      tx.onerror = () => { db.close(); reject(tx.error || new Error('Ошибка чтения кэша FFmpeg.wasm')); };
      tx.onabort = () => { db.close(); reject(tx.error || new Error('Чтение кэша FFmpeg.wasm отменено')); };
    });
  }

  async function writeFfmpegAssetCache(coreScript, coreWasm) {
    const db = await openFfmpegAssetDb();
    return new Promise((resolve, reject) => {
      const tx = db.transaction('assets', 'readwrite');
      tx.objectStore('assets').put({
        id: 'core',
        version: FFMPEG_CORE_VERSION,
        coreScript,
        coreWasm,
        savedAt: Date.now()
      });
      tx.oncomplete = () => { db.close(); resolve(true); };
      tx.onerror = () => { db.close(); reject(tx.error || new Error('Не удалось сохранить кэш FFmpeg.wasm')); };
      tx.onabort = () => { db.close(); reject(tx.error || new Error('Сохранение кэша FFmpeg.wasm отменено')); };
    });
  }

  async function loadLocalFfmpegAssets() {
    if (localFfmpegAssets) return localFfmpegAssets;
    if (localFfmpegAssetsPromise) return localFfmpegAssetsPromise;

    localFfmpegAssetsPromise = (async () => {
      let coreScript = null;
      let coreWasm = null;
      try {
        const cached = await readFfmpegAssetCache();
        if (cached && cached.version === FFMPEG_CORE_VERSION &&
            cached.coreScript instanceof Blob && cached.coreScript.size > 1000 &&
            cached.coreWasm instanceof Blob && cached.coreWasm.size > 1000000) {
          coreScript = cached.coreScript;
          coreWasm = cached.coreWasm;
          logDebug('FFmpeg.wasm binaries restored from persistent IndexedDB cache', {
            version: FFMPEG_CORE_VERSION,
            coreBytes: coreScript.size,
            wasmBytes: coreWasm.size
          });
          setStatus('Использую сохранённый FFmpeg.wasm — повторная загрузка движка не нужна…', 'info', true);
        }
      } catch (error) {
        logDebug('FFmpeg.wasm cache read failed; downloading core once for this session', error.message || error);
      }

      if (!coreScript || !coreWasm) {
        setStatus('Первый запуск: загружаю FFmpeg.wasm (~31 МБ). Исходное видео останется в браузере…', 'info', true);
        const assets = await Promise.all([
          requestBlob(FFMPEG_CORE_BASE_URL + '/ffmpeg-core.js', 180000),
          requestBlob(FFMPEG_CORE_BASE_URL + '/ffmpeg-core.wasm', 300000)
        ]);
        coreScript = assets[0];
        coreWasm = assets[1];
        try {
          await writeFfmpegAssetCache(coreScript, coreWasm);
          let persistent = false;
          try {
            if (navigator.storage && typeof navigator.storage.persist === 'function') {
              persistent = await navigator.storage.persist();
            }
          } catch (_) {}
          logDebug('FFmpeg.wasm binaries saved to IndexedDB', {
            version: FFMPEG_CORE_VERSION,
            coreBytes: coreScript.size,
            wasmBytes: coreWasm.size,
            persistentStorageGranted: persistent
          });
        } catch (error) {
          logDebug('FFmpeg.wasm cache write failed; using in-memory binaries only', error.message || error);
          setStatus('FFmpeg.wasm загружен, но браузер не разрешил сохранить кэш. Повторная загрузка может понадобиться после закрытия вкладки.', 'info', true);
        }
      }

      const coreUrl = URL.createObjectURL(new Blob([coreScript], { type: 'text/javascript' }));
      const wasmUrl = URL.createObjectURL(new Blob([coreWasm], { type: 'application/wasm' }));
      localFfmpegAssets = { coreUrl, wasmUrl };
      return localFfmpegAssets;
    })().catch(error => {
      localFfmpegAssetsPromise = null;
      throw new Error('Не удалось загрузить FFmpeg.wasm. Проверь доступ к cdn.jsdelivr.net и повтори попытку. ' + (error.message || error));
    });

    return localFfmpegAssetsPromise;
  }

  // Runs inside one long-lived worker; selected media conversion never uses a
  // server-side conversion API.
  function localFfmpegWorkerEntrypoint(coreUrl, wasmUrl) {
    'use strict';
    let engine = null;
    let loadingPromise = null;
    let activeId = null;
    let activeDurationSeconds = 0;
    let lastParsedProgress = 0;
    let recentErrors = [];

    function timecodeToSeconds(match) {
      if (!match) return 0;
      return Number(match[1]) * 3600 + Number(match[2]) * 60 + Number(match[3]);
    }

    function reportProgressFromLog(rawMessage) {
      if (activeId === null) return;
      const message = String(rawMessage || '');
      const durationMatch = message.match(/\bduration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)/i);
      if (durationMatch) {
        const duration = timecodeToSeconds(durationMatch);
        if (duration > 0) activeDurationSeconds = duration;
      }

      // The WebAssembly core's setProgress callback is experimental and may not fire
      // reliably. FFmpeg's own stats lines include time=HH:MM:SS.xx; compare that
      // timestamp to the input duration announced during demuxing.
      const timeMatch = message.match(/\btime\s*=\s*(\d+):(\d+):(\d+(?:\.\d+)?)/i);
      if (!timeMatch || activeDurationSeconds <= 0) return;
      const processedSeconds = timecodeToSeconds(timeMatch);
      const ratio = Math.max(0, Math.min(0.99, processedSeconds / activeDurationSeconds));
      if (ratio < lastParsedProgress + 0.005 && ratio < 0.99) return;
      lastParsedProgress = ratio;
      self.postMessage({
        kind: 'progress',
        id: activeId,
        progress: ratio,
        currentTime: processedSeconds,
        duration: activeDurationSeconds,
        source: 'ffmpeg-log'
      });
    }

    async function loadEngine(id) {
      if (engine) return engine;
      if (loadingPromise) return loadingPromise;
      loadingPromise = (async () => {
        self.postMessage({ kind: 'status', id, text: 'Инициализирую FFmpeg.wasm…' });
        importScripts(coreUrl);
        if (typeof self.createFFmpegCore !== 'function') throw new Error('FFmpeg.wasm core не экспортировал createFFmpegCore.');
        const assetInfo = btoa(JSON.stringify({ wasmURL: wasmUrl, workerURL: coreUrl }));
        engine = await self.createFFmpegCore({ mainScriptUrlOrBlob: coreUrl + '#' + assetInfo });
        engine.setLogger(data => {
          const rawMessage = String(data && data.message || '');
          const message = rawMessage.toLowerCase();
          if (message && (message.includes('error') || message.includes('failed') || message.includes('invalid') ||
              message.includes('unknown decoder') || message.includes('unknown encoder'))) {
            recentErrors.push(message);
            if (recentErrors.length > 8) recentErrors.shift();
          }
          reportProgressFromLog(rawMessage);
        });
        engine.setProgress(data => {
          const ratio = Number(data && data.ratio);
          // Keep core-reported progress as a fallback, but log timestamps are the
          // primary source for videos when this callback only reports 0/1 or nothing.
          if (activeId !== null && Number.isFinite(ratio) && ratio >= 0 && ratio <= 1) {
            self.postMessage({ kind: 'progress', id: activeId, progress: ratio, source: 'core' });
          }
        });
        return engine;
      })();
      try { return await loadingPromise; }
      catch (error) { loadingPromise = null; engine = null; throw error; }
    }

    async function convert(message) {
      const id = message.id;
      activeId = id;
      activeDurationSeconds = 0;
      lastParsedProgress = 0;
      recentErrors = [];
      let wroteInput = false;
      let wroteOutput = false;
      try {
        const ffmpeg = await loadEngine(id);
        self.postMessage({ kind: 'status', id, text: 'Обрабатываю медиа через FFmpeg.wasm…' });
        ffmpeg.FS.writeFile(message.inputName, new Uint8Array(message.inputBuffer));
        wroteInput = true;
        ffmpeg.setTimeout(1200000);
        ffmpeg.exec.apply(ffmpeg, message.args);
        const exitCode = Number(ffmpeg.ret);
        ffmpeg.reset();
        if (exitCode !== 0) {
          const details = recentErrors.slice(-4).join(' | ');
          throw new Error('FFmpeg завершился с кодом ' + exitCode + (details ? ': ' + details : '. Проверь формат исходного файла.'));
        }
        const bytes = ffmpeg.FS.readFile(message.outputName);
        wroteOutput = true;
        const outputBuffer = bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
        self.postMessage({ kind: 'done', id, outputBuffer }, [outputBuffer]);
      } catch (error) {
        try { if (engine) engine.reset(); } catch (_) {}
        self.postMessage({
          kind: 'error',
          id,
          message: String(error && error.message || error || 'Неизвестная ошибка FFmpeg.wasm'),
          details: recentErrors.slice(-4).join(' | ')
        });
      } finally {
        try { if (engine && wroteInput) engine.FS.unlink(message.inputName); } catch (_) {}
        try { if (engine && wroteOutput) engine.FS.unlink(message.outputName); } catch (_) {}
        activeId = null;
      }
    }

    self.onmessage = event => {
      const message = event.data || {};
      if (message.kind === 'convert') convert(message);
    };
  }

  async function getLocalFfmpegWorker() {
    if (localFfmpegWorker) return localFfmpegWorker;
    const assets = await loadLocalFfmpegAssets();
    if (localFfmpegWorker) return localFfmpegWorker;
    const source = '(' + localFfmpegWorkerEntrypoint.toString() + ')(' + JSON.stringify(assets.coreUrl) + ',' + JSON.stringify(assets.wasmUrl) + ');';
    const blobUrl = URL.createObjectURL(new Blob([source], { type: 'text/javascript' }));
    let worker;
    try { worker = new Worker(blobUrl); }
    catch (error) {
      URL.revokeObjectURL(blobUrl);
      throw new Error('Браузер запретил запуск FFmpeg.wasm в Web Worker (возможно, из-за CSP). ' + (error.message || error));
    }
    localFfmpegWorker = worker;
    localFfmpegWorkerUrl = blobUrl;
    worker.addEventListener('message', event => {
      const message = event.data || {};
      const pending = localFfmpegPending.get(message.id);
      if (!pending) return;
      if (message.kind === 'status') {
        pending.onStatus?.(message.text || '');
      } else if (message.kind === 'progress') {
        const ratio = Number(message.progress);
        const source = String(message.source || 'core');
        // The core callback is experimental and can report only 0 or 1 on
        // some videos. Those values are not useful for displaying progression;
        // let the FFmpeg log's time/duration fallback drive the indicator instead.
        if (source === 'core' && (ratio <= 0 || ratio >= 0.99)) return;
        if (Number.isFinite(ratio) && ratio >= 0 && ratio < 1) {
          const percent = Math.min(99, Math.round(ratio * 100));
          if (percent >= pending.lastPercent + 2 || percent === 99) {
            pending.lastPercent = percent;
            // Percent is displayed only beside the ring; status text describes the stage.
            pending.onProgress?.(percent);
          }
        }
      } else if (message.kind === 'done') {
        clearTimeout(pending.timeout);
        localFfmpegPending.delete(message.id);
        pending.resolve(message.outputBuffer);
      } else if (message.kind === 'error') {
        clearTimeout(pending.timeout);
        localFfmpegPending.delete(message.id);
        const details = message.details ? ' Детали: ' + message.details : '';
        pending.reject(new Error('Ошибка FFmpeg.wasm: ' + (message.message || 'не удалось обработать медиа') + '.' + details));
      }
    });
    worker.addEventListener('error', event => {
      logDebug('FFmpeg.wasm worker crashed', event.message || event);
      const error = new Error('FFmpeg.wasm worker завершился с ошибкой. Перезагрузи Twitch и повтори попытку.');
      for (const [id, pending] of localFfmpegPending) {
        clearTimeout(pending.timeout);
        pending.reject(error);
        localFfmpegPending.delete(id);
      }
      worker.terminate();
      if (localFfmpegWorker === worker) localFfmpegWorker = null;
      if (localFfmpegWorkerUrl) URL.revokeObjectURL(localFfmpegWorkerUrl);
      localFfmpegWorkerUrl = '';
    });
    return worker;
  }

  async function ffmpegMediaToFormat(file, outputFormat, maxWidth = loadConfig().maxWidth, compression = loadConfig().compression, runId = null, compressEnabled = true, rawEditOptions = null) {
    if (!file || !file.size) throw new Error('Файл пустой.');
    const inputExt = fileExtension(file).replace(/[^a-z0-9]/gi, '') || 'bin';
    const validFormats = ['webp', 'gif', 'jpg', 'png', 'mp4', 'webm'];
    if (!validFormats.includes(outputFormat)) throw new Error('Этот формат не поддерживается FFmpeg.wasm: ' + outputFormat);

    const originalName = String(file.name || 'media');
    const dot = originalName.lastIndexOf('.');
    const baseName = (dot > 0 ? originalName.slice(0, dot) : originalName) || 'media';
    const outputName = baseName + '.' + outputFormat;
    const width = compressEnabled ? clampInt(maxWidth, 100, 4000, DEFAULT_MAX_WIDTH) : 4000;
    const options = normalizeCompressionSettings(compression, DEFAULT_CONFIG().compression);
    const videoFps = options.videoFps;
    const animationFps = options.animationFps;
    const videoBitrate = options.videoBitrateKbps;
    const audioBitrate = options.audioBitrateKbps;
    const videoCrf = options.videoCrf;
    const speedPreset = options.speedPreset;
    const cpuUsed = videoCpuUsedFromPreset(speedPreset);
    const scaleMethod = options.scaleFilter;
    const animationQuality = options.animationQuality;
    const imageQuality = options.imageQuality;
    const webpCompressionLevel = options.webpCompressionLevel;
    const worker = await getLocalFfmpegWorker();
    ensureProcessingRun(runId);
    const inputBuffer = await file.arrayBuffer();
    ensureProcessingRun(runId);
    const id = ++localFfmpegRequestId;
    const inputName = 'input_' + id + '.' + inputExt;
    const outputPath = 'output_' + id + '.' + outputFormat;
    const mime = mimeFromFile(file);
    const extension = fileExtension(file).toLowerCase();
    const sourceIsGif = mime === 'image/gif' || extension === 'gif';
    const sourceIsAnimatedWebP = await isAnimatedWebP(file);
    const sourceIsAnimatedPng = (mime === 'image/png' || extension === 'apng' || extension === 'png')
      ? await isAnimatedPng(file) : false;
    const sourceIsAnimation = sourceIsGif || sourceIsAnimatedWebP || sourceIsAnimatedPng;
    const sourceIsStillImage = mime.startsWith('image/') && !sourceIsAnimation;
    const editOptions = rawEditOptions ? normalizeMediaEditOptions(rawEditOptions) : null;
    const outputIsVideo = outputFormat === 'mp4' || outputFormat === 'webm';
    const scaleFilter = compressEnabled
      ? 'scale=' + width + ':' + width + ':force_original_aspect_ratio=decrease:force_divisible_by=2:flags=' + scaleMethod
      : '';
    const videoRateArgs = !compressEnabled
      ? ['-crf', '0']
      : (videoBitrate > 0
        ? ['-b:v', videoBitrate + 'k', '-maxrate', Math.round(videoBitrate * 1.25) + 'k', '-bufsize', (videoBitrate * 2) + 'k']
        : ['-crf', String(videoCrf)]);
    const webmRateArgs = !compressEnabled
      ? ['-crf', '0', '-b:v', '0']
      : (videoBitrate > 0
        ? ['-b:v', videoBitrate + 'k', '-maxrate', Math.round(videoBitrate * 1.25) + 'k', '-bufsize', (videoBitrate * 2) + 'k']
        : ['-crf', String(videoCrf), '-b:v', '0']);
    const args = [];
    const videoTransformFilters = [];
    const audioTransformFilters = [];
    if (editOptions) {
      const selectedDuration = Math.max(0, editOptions.end - editOptions.start);
      if (editOptions.duration > 0 && selectedDuration > 0 &&
          (editOptions.start > 0.03 || editOptions.end < editOptions.duration - 0.03)) {
        videoTransformFilters.push('trim=start=' + editOptions.start.toFixed(3) + ':duration=' + selectedDuration.toFixed(3));
        audioTransformFilters.push('atrim=start=' + editOptions.start.toFixed(3) + ':duration=' + selectedDuration.toFixed(3));
      }
      videoTransformFilters.push('setpts=(PTS-STARTPTS)/' + editOptions.speed.toFixed(3));
      if (editOptions.crop.x > 0.5 || editOptions.crop.y > 0.5 ||
          editOptions.crop.w < 99.5 || editOptions.crop.h < 99.5) {
        const sourceWidth = Math.floor(Number(editOptions.sourceWidth) || 0);
        const sourceHeight = Math.floor(Number(editOptions.sourceHeight) || 0);
        if (sourceWidth >= 2 && sourceHeight >= 2) {
          const evenWidth = Math.floor(sourceWidth / 2) * 2;
          const evenHeight = Math.floor(sourceHeight / 2) * 2;
          const cropWidth = Math.max(2, Math.min(evenWidth, Math.floor(sourceWidth * editOptions.crop.w / 100 / 2) * 2));
          const cropHeight = Math.max(2, Math.min(evenHeight, Math.floor(sourceHeight * editOptions.crop.h / 100 / 2) * 2));
          const cropX = Math.max(0, Math.min(evenWidth - cropWidth, Math.floor(sourceWidth * editOptions.crop.x / 100 / 2) * 2));
          const cropY = Math.max(0, Math.min(evenHeight - cropHeight, Math.floor(sourceHeight * editOptions.crop.y / 100 / 2) * 2));
          videoTransformFilters.push('crop=' + cropWidth + ':' + cropHeight + ':' + cropX + ':' + cropY);
        } else {
          const x = (editOptions.crop.x / 100).toFixed(5);
          const y = (editOptions.crop.y / 100).toFixed(5);
          const w = (editOptions.crop.w / 100).toFixed(5);
          const h = (editOptions.crop.h / 100).toFixed(5);
          videoTransformFilters.push(
            'crop=max(2\\,trunc(iw*' + w + '/2)*2):max(2\\,trunc(ih*' + h + '/2)*2):' +
            'trunc(iw*' + x + '/2)*2:trunc(ih*' + y + '/2)*2'
          );
        }
      }
      if (editOptions.speed !== 1) {
        audioTransformFilters.push('asetpts=PTS-STARTPTS');
        let tempo = editOptions.speed;
        while (tempo < 0.5 - 0.0001) {
          audioTransformFilters.push('atempo=0.5');
          tempo /= 0.5;
        }
        while (tempo > 2 + 0.0001) {
          audioTransformFilters.push('atempo=2');
          tempo /= 2;
        }
        audioTransformFilters.push('atempo=' + tempo.toFixed(3));
      } else if (audioTransformFilters.length) {
        audioTransformFilters.push('asetpts=PTS-STARTPTS');
      }
    }
    const videoFiltersWithCompression = extra => videoTransformFilters.concat(extra || []);
    const pingPongEnabled = Boolean(editOptions && editOptions.loop);
    // Animated exports loop indefinitely; ping-pong is encoded as forward + reversed frames.
    const outputLoopCount = '0';
    const webpLoopCount = '0';
    if (pingPongEnabled && outputIsVideo && !sourceIsStillImage) {
      const selectedDuration = Math.max(0, editOptions.end - editOptions.start) / editOptions.speed;
      if (!audioTransformFilters.length) audioTransformFilters.push('asetpts=PTS-STARTPTS');
      audioTransformFilters.push('apad=pad_dur=' + selectedDuration.toFixed(3));
    }

    // When a still image is sent to a video container, create a short 2s clip.
    if (outputIsVideo && sourceIsStillImage) {
      args.push('-loop', '1', '-framerate', String(videoFps), '-i', inputName, '-t', '2');
    } else {
      args.push('-i', inputName);
    }

    if (outputFormat === 'gif') {
      const gifFilters = videoFiltersWithCompression(compressEnabled ? ['fps=' + animationFps, scaleFilter] : []);
      const gifBase = gifFilters.join(',');
      const gifFilter = pingPongEnabled
        ? '[0:v]' + gifBase + ',split[forward][reverseSource];[reverseSource]reverse[reverse];[forward][reverse]concat=n=2:v=1:a=0,split[s0][s1];[s0]palettegen=stats_mode=diff[p];[s1][p]paletteuse=dither=bayer:diff_mode=rectangle'
        : '[0:v]' + gifFilters.concat(['split[s0][s1]']).join(',') +
          ';[s0]palettegen=stats_mode=diff[p];[s1][p]paletteuse=dither=bayer:diff_mode=rectangle';
      args.push('-filter_complex', gifFilter, '-loop', outputLoopCount, outputPath);
    } else if (outputFormat === 'webp') {
      if (sourceIsStillImage) {
        args.push(
          ...(compressEnabled ? ['-vf', scaleFilter] : []),
          '-frames:v', '1', '-an', '-c:v', 'libwebp',
          ...(compressEnabled ? ['-quality', String(imageQuality)] : ['-lossless', '1']),
          '-compression_level', String(webpCompressionLevel), outputPath
        );
      } else {
        const webpFilters = videoFiltersWithCompression(compressEnabled ? ['fps=' + animationFps, scaleFilter] : []);
        const webpArgs = pingPongEnabled
          ? ['-filter_complex', '[0:v]' + webpFilters.join(',') + ',split[forward][reverseSource];[reverseSource]reverse[reverse];[forward][reverse]concat=n=2:v=1:a=0[outv]', '-map', '[outv]']
          : (webpFilters.length ? ['-vf', webpFilters.join(',')] : []);
        args.push(
          ...webpArgs,
          '-an', '-c:v', 'libwebp',
          ...(compressEnabled ? ['-quality', String(animationQuality)] : ['-lossless', '1']),
          '-compression_level', String(webpCompressionLevel), '-loop', webpLoopCount, outputPath
        );
      }
    } else if (outputFormat === 'jpg') {
      const jpgFilters = videoFiltersWithCompression(compressEnabled ? [scaleFilter] : []);
      args.push(
        ...(jpgFilters.length ? ['-vf', jpgFilters.join(',')] : []),
        '-frames:v', '1', '-q:v', compressEnabled ? String(Math.max(2, Math.round((100 - imageQuality) / 7))) : '2',
        outputPath
      );
    } else if (outputFormat === 'png') {
      const pngFilters = videoFiltersWithCompression(compressEnabled ? [scaleFilter] : []);
      args.push(...(pngFilters.length ? ['-vf', pngFilters.join(',')] : []), '-frames:v', '1', outputPath);
    } else if (outputFormat === 'mp4') {
      const videoFilters = videoFiltersWithCompression(compressEnabled ? ['fps=' + videoFps, scaleFilter] : []);
      const pingPongGraph = '[0:v]' + videoFilters.join(',') +
        ',split[forward][reverseSource];[reverseSource]reverse[reverse];[forward][reverse]concat=n=2:v=1:a=0[outv]';
      args.push(
        ...(pingPongEnabled && !sourceIsStillImage
          ? ['-filter_complex', pingPongGraph, '-map', '[outv]', '-map', '0:a?']
          : (videoFilters.length ? ['-vf', videoFilters.join(',')] : [])),
        ...(!pingPongEnabled && audioTransformFilters.length ? ['-af', audioTransformFilters.join(',')] : []),
        ...(pingPongEnabled && audioTransformFilters.length ? ['-af', audioTransformFilters.join(',')] : []),
        '-c:v', 'libx264', '-preset', compressEnabled ? speedPreset : 'medium',
        ...videoRateArgs,
        '-pix_fmt', 'yuv420p', '-movflags', '+faststart',
        '-c:a', 'aac', '-b:a', (compressEnabled ? audioBitrate : 320) + 'k', outputPath
      );
    } else if (outputFormat === 'webm') {
      const videoFilters = videoFiltersWithCompression(compressEnabled ? ['fps=' + videoFps, scaleFilter] : []);
      const pingPongGraph = '[0:v]' + videoFilters.join(',') +
        ',split[forward][reverseSource];[reverseSource]reverse[reverse];[forward][reverse]concat=n=2:v=1:a=0[outv]';
      args.push(
        ...(pingPongEnabled && !sourceIsStillImage
          ? ['-filter_complex', pingPongGraph, '-map', '[outv]', '-map', '0:a?']
          : (videoFilters.length ? ['-vf', videoFilters.join(',')] : [])),
        ...(!pingPongEnabled && audioTransformFilters.length ? ['-af', audioTransformFilters.join(',')] : []),
        ...(pingPongEnabled && audioTransformFilters.length ? ['-af', audioTransformFilters.join(',')] : []),
        '-c:v', 'libvpx', '-deadline', compressEnabled ? 'realtime' : 'good',
        '-cpu-used', String(compressEnabled ? cpuUsed : 0),
        ...webmRateArgs,
        '-c:a', 'libopus', '-b:a', (compressEnabled ? audioBitrate : 320) + 'k', outputPath
      );
    }

    setStatus('FFmpeg.wasm: ' + inputExt.toUpperCase() + ' → ' + outputFormat.toUpperCase() + '…', 'info', true);
    setProgress(null, true);
    const outputBuffer = await new Promise((resolve, reject) => {
      const timeout = setTimeout(() => {
        localFfmpegPending.delete(id);
        reject(new Error('FFmpeg.wasm не завершил конвертацию за 20 минут. Попробуй более короткое видео или меньший файл.'));
      }, 1200000);
      localFfmpegPending.set(id, {
        resolve, reject, timeout, lastPercent: -5,
        onStatus: text => {
          setStatus(text || 'FFmpeg.wasm обрабатывает медиа…', 'info', true);
          if (!/\d{1,3}%/.test(String(text || ''))) setProgress(null, true);
        },
        onProgress: percent => setProgress(8 + Math.round(percent * 0.56), true)
      });
      try {
        worker.postMessage({ kind: 'convert', id, inputName, outputName: outputPath, inputBuffer, args }, [inputBuffer]);
      } catch (error) {
        clearTimeout(timeout);
        localFfmpegPending.delete(id);
        reject(error);
      }
    });
    validateConvertedOutput(outputFormat, outputBuffer);
    setProgress(65, true);
    logDebug('FFmpeg.wasm conversion finished', {
      input: file.name || inputName, output: outputName,
      inputBytes: file.size, outputBytes: outputBuffer.byteLength, maxWidth: width
    });
    const typeMap = {
      webp: 'image/webp', gif: 'image/gif', jpg: 'image/jpeg',
      png: 'image/png', mp4: 'video/mp4', webm: 'video/webm'
    };
    return new File([outputBuffer], outputName, { type: typeMap[outputFormat], lastModified: Date.now() });
  }

  function validateConvertedOutput(format, buffer) {
    if (!buffer || buffer.byteLength < 20) {
      throw new Error('FFmpeg.wasm вернул пустой или повреждённый файл (' + (buffer ? buffer.byteLength : 0) + ' байт). Файл не загружен.');
    }
    const bytes = new Uint8Array(buffer);
    const ascii = (start, length) => String.fromCharCode(...bytes.slice(start, start + length));
    let valid = false;
    switch (format) {
      case 'webp':
        valid = ascii(0, 4) === 'RIFF' && ascii(8, 4) === 'WEBP';
        break;
      case 'png':
        valid = bytes.length >= 24 && bytes[0] === 0x89 && ascii(1, 3) === 'PNG';
        break;
      case 'jpg':
        valid = bytes[0] === 0xff && bytes[1] === 0xd8 && bytes[bytes.length - 2] === 0xff && bytes[bytes.length - 1] === 0xd9;
        break;
      case 'gif':
        valid = ascii(0, 3) === 'GIF' && (ascii(3, 3) === '87a' || ascii(3, 3) === '89a');
        break;
      case 'mp4':
        valid = ascii(4, 4) === 'ftyp';
        break;
      case 'webm':
        valid = bytes[0] === 0x1a && bytes[1] === 0x45 && bytes[2] === 0xdf && bytes[3] === 0xa3;
        break;
    }
    if (!valid) {
      logDebug('Converted output signature invalid', { format, bytes: buffer.byteLength, firstBytes: Array.from(bytes.slice(0, 16)) });
      throw new Error('FFmpeg.wasm создал некорректный файл ' + format.toUpperCase() + '. Файл не загружен; попробуй ещё раз или другой формат.');
    }
  }

  function formatBytes(bytes) {
    if (!Number.isFinite(bytes)) return '';
    if (bytes < 1024) return `${bytes} Б`;
    if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} КБ`;
    return `${(bytes / (1024 * 1024)).toFixed(1)} МБ`;
  }

  function formatVideoDuration(seconds) {
    if (!Number.isFinite(seconds) || seconds < 0) return '';
    const totalSeconds = Math.floor(seconds);
    const hours = Math.floor(totalSeconds / 3600);
    const minutes = Math.floor((totalSeconds % 3600) / 60);
    const rest = totalSeconds % 60;
    return hours > 0
      ? hours + ':' + String(minutes).padStart(2, '0') + ':' + String(rest).padStart(2, '0')
      : minutes + ':' + String(rest).padStart(2, '0');
  }

  function resolveVideoDuration(rawUrl) {
    const url = String(rawUrl || '').trim();
    if (!url) return Promise.resolve(0);
    if (videoDurationCache.has(url)) return Promise.resolve(videoDurationCache.get(url));
    if (videoDurationLookupPending.has(url)) return videoDurationLookupPending.get(url);

    const lookup = new Promise(resolve => {
      const probe = document.createElement('video');
      let settled = false;
      let timeout = 0;
      probe.preload = 'metadata';
      probe.muted = true;
      probe.playsInline = true;

      const finish = duration => {
        if (settled) return;
        settled = true;
        if (timeout) clearTimeout(timeout);
        probe.removeEventListener('loadedmetadata', readDuration);
        probe.removeEventListener('durationchange', readDuration);
        probe.removeEventListener('error', onError);
        try {
          probe.pause();
          probe.removeAttribute('src');
          probe.load();
        } catch (_) {}
        const safeDuration = Number.isFinite(duration) && duration >= 0 ? duration : 0;
        if (safeDuration > 0) videoDurationCache.set(url, safeDuration);
        resolve(safeDuration);
      };
      const readDuration = () => {
        const duration = Number(probe.duration);
        if (Number.isFinite(duration) && duration >= 0) finish(duration);
        else if (duration === Infinity) finish(0);
      };
      const onError = () => finish(0);

      probe.addEventListener('loadedmetadata', readDuration);
      probe.addEventListener('durationchange', readDuration);
      probe.addEventListener('error', onError);
      timeout = window.setTimeout(() => finish(0), 10000);
      const source = cachedMediaObjectUrls.get(url) || url;
      probe.src = source;
      try { probe.load(); } catch (_) { finish(0); }
    }).finally(() => {
      videoDurationLookupPending.delete(url);
    });

    videoDurationLookupPending.set(url, lookup);
    return lookup;
  }

  function isWebPResource(rawUrl) {
    const value = String(rawUrl || '').trim();
    if (!value) return false;
    if (/^data:image\/webp[;,]/i.test(value)) return true;
    try { return /\.webp$/i.test(new URL(value, location.href).pathname); }
    catch (_) { return /\.webp(?:$|[?#])/i.test(value); }
  }

  function isLikelyWebPItem(item, rawUrl) {
    return [rawUrl, item?.url, item?.previewUrl, item?.name].some(value => {
      const text = String(value || '').trim();
      return /^data:image\/webp[;,]/i.test(text) || /\.webp(?:$|[?#])/i.test(text);
    });
  }

  function getAnimatedWebPDurationSeconds(blob) {
    if (!(blob instanceof Blob) || blob.size < 30) return Promise.resolve(0);
    return blob.arrayBuffer().then(buffer => {
      const bytes = new Uint8Array(buffer);
      if (webpAscii(bytes, 0, 4) !== 'RIFF' || webpAscii(bytes, 8, 4) !== 'WEBP') return 0;
      const riffLength = webpReadU32LE(bytes, 4);
      const riffEnd = riffLength > 0 ? Math.min(bytes.length, riffLength + 8) : bytes.length;
      const chunks = webpParseChunks(bytes, 12, riffEnd);
      let totalMilliseconds = 0;
      let frameCount = 0;
      for (const chunk of chunks) {
        if (chunk.type !== 'ANMF' || chunk.data.length < 16) continue;
        totalMilliseconds += webpReadU24LE(chunk.data, 12);
        frameCount++;
      }
      // Some valid animated WebPs have zero frame delays. When frame chunks exist,
      // estimate their duration so the editor can still expose a useful trim range.
      return frameCount > 0 ? (totalMilliseconds > 0 ? totalMilliseconds / 1000 : frameCount * 0.1) : 0;
    }).catch(() => 0);
  }

  async function resolveAnimatedWebPDuration(item, rawUrl) {
    const url = String(rawUrl || '').trim();
    if (!url) return 0;
    if (animatedWebPStatusCache.get(url) === false) return 0;
    if (videoDurationCache.has(url)) {
      const knownDuration = videoDurationCache.get(url);
      if (knownDuration > 0) animatedWebPStatusCache.set(url, true);
      return knownDuration;
    }
    if (videoDurationLookupPending.has(url)) return videoDurationLookupPending.get(url);

    const lookup = (async () => {
      let blob = null;
      const candidateUrls = Array.from(new Set([
        url,
        String(item?.url || '').trim(),
        String(item?.previewUrl || '').trim()
      ].filter(Boolean)));

      // Prefer cached bytes. The animation flag is a property of the WebP container,
      // not its extension and not whether its frame durations happen to be non-zero.
      for (const candidate of candidateUrls) {
        try {
          blob = await getCachedMediaBlob(candidate);
          if (!blob) blob = await getSharedMediaBlob(candidate);
          if (!blob) {
            const objectUrl = cachedMediaObjectUrls.get(candidate);
            if (objectUrl) {
              const response = await fetch(objectUrl);
              if (response.ok) blob = await response.blob();
            }
          }
          if (blob instanceof Blob && blob.size > 0) break;
          blob = null;
        } catch (_) {
          blob = null;
        }
      }

      // Avoid unexpectedly downloading huge images just to classify them.
      if (!blob && /^https?:\/\//i.test(url)) {
        try {
          const head = await request({ method: 'HEAD', url, timeout: 10000, acceptHttpErrors: true });
          const lengthMatch = String(head.responseHeaders || '').match(/content-length:\s*(\d+)/i);
          const contentLength = lengthMatch ? Number(lengthMatch[1]) : 0;
          if (head.status >= 200 && head.status < 300 &&
              contentLength > 0 && contentLength <= 30 * 1024 * 1024) {
            blob = await requestBlob(url, 25000, false);
          }
        } catch (_) {}
      }

      if (!blob) return 0;
      // Some servers return WebP data as application/octet-stream. Normalize the
      // MIME for the signature parser; this does not modify the original media.
      const webpBlob = String(blob.type || '').toLowerCase() === 'image/webp'
        ? blob
        : new Blob([blob], { type: 'image/webp' });
      const containerIsAnimated = await isAnimatedWebP(webpBlob);
      const duration = await getAnimatedWebPDurationSeconds(webpBlob);
      const isAnimated = containerIsAnimated || duration > 0;

      // Cache both true and false results, including alternate URLs for the same item.
      for (const candidate of candidateUrls) {
        if (isWebPResource(candidate)) animatedWebPStatusCache.set(candidate, isAnimated);
      }
      animatedWebPStatusCache.set(url, isAnimated);
      if (duration > 0) videoDurationCache.set(url, duration);
      return duration;
    })().finally(() => {
      videoDurationLookupPending.delete(url);
    });

    videoDurationLookupPending.set(url, lookup);
    return lookup;
  }

  async function resolveMediaSizeBytes(item, rawUrl) {
    const url = String(rawUrl || item?.previewUrl || item?.url || '').trim();
    const knownSize = Math.max(0, Math.floor(Number(item?.size) || 0));
    if (knownSize > 0) {
      mediaSizeCache.set(url, knownSize);
      return knownSize;
    }
    if (!url) return 0;
    const cachedSize = mediaSizeCache.get(url) || 0;
    if (cachedSize > 0) return cachedSize;
    if (mediaSizeLookupPending.has(url)) return mediaSizeLookupPending.get(url);

    const lookup = (async () => {
      try {
        const localBlob = await getCachedMediaBlob(url);
        if (localBlob && localBlob.size > 0) return localBlob.size;
        const sharedBlob = await getSharedMediaBlob(url);
        if (sharedBlob && sharedBlob.size > 0) {
          cacheMediaBlob(url, sharedBlob);
          return sharedBlob.size;
        }

        const parsed = new URL(url, location.href);
        if (parsed.protocol !== 'http:' && parsed.protocol !== 'https:') return 0;
        const response = await request({
          method: 'HEAD',
          url: parsed.href,
          timeout: 9000,
          acceptHttpErrors: true
        });
        if (response.status < 200 || response.status >= 300) return 0;
        const headers = String(response.responseHeaders || '');
        const lengthMatch = headers.match(/content-length:\s*(\d+)/i);
        if (lengthMatch) {
          const size = Number(lengthMatch[1]);
          if (Number.isFinite(size) && size > 0) return size;
        }
        const rangeMatch = headers.match(/content-range:\s*bytes\s+\d+-\d+\/(\d+)/i);
        if (rangeMatch) {
          const size = Number(rangeMatch[1]);
          if (Number.isFinite(size) && size > 0) return size;
        }
      } catch (_) {
        // Some hosts do not support HEAD; a missing size must not affect media loading.
      }
      return 0;
    })().then(size => {
      if (size > 0) mediaSizeCache.set(url, size);
      return size;
    }).finally(() => {
      mediaSizeLookupPending.delete(url);
    });
    mediaSizeLookupPending.set(url, lookup);
    return lookup;
  }

  function isMediaEditorEnabled() {
    // Editor is now launched explicitly from its toolbar icon, never as a surprise
    // side effect of importing files through the normal gallery workflow.
    return false;
  }

  function isAnimatedPng(file) {
    if (!file || !file.size) return Promise.resolve(false);
    const ext = fileExtension(file).toLowerCase();
    if (ext === 'apng') return Promise.resolve(true);
    if (mimeFromFile(file) !== 'image/png' && ext !== 'png') return Promise.resolve(false);
    return file.slice(0, Math.min(file.size, 1024 * 1024)).arrayBuffer().then(buffer => {
      const b = new Uint8Array(buffer);
      if (b.length < 33 || b[0] !== 137 || b[1] !== 80 || b[2] !== 78 || b[3] !== 71) return false;
      let p = 8;
      while (p + 12 <= b.length) {
        const n = ((b[p] << 24) | (b[p + 1] << 16) | (b[p + 2] << 8) | b[p + 3]) >>> 0;
        if (n > b.length || p + 12 + n > b.length) return false;
        const tag = String.fromCharCode(b[p + 4], b[p + 5], b[p + 6], b[p + 7]);
        if (tag === 'acTL') return true;
        if (tag === 'IDAT' || tag === 'IEND') return false;
        p += 12 + n;
      }
      return false;
    }).catch(() => false);
  }

  async function getGifDurationSeconds(file) {
    if (!(file instanceof Blob) || file.size < 13) return 0;
    try {
      const b = new Uint8Array(await file.arrayBuffer());
      const ascii = (p, n) => String.fromCharCode(...b.subarray(p, p + n));
      if (!/^GIF8[79]a$/.test(ascii(0, 6))) return 0;
      let p = 13;
      const packed = b[10];
      if (packed & 128) p += 3 * (1 << ((packed & 7) + 1));
      let delay = 0, total = 0, frames = 0;
      const skip = from => {
        let q = from;
        while (q < b.length) {
          const n = b[q++];
          if (!n) return q;
          q += n;
          if (q > b.length) return b.length;
        }
        return b.length;
      };
      while (p < b.length) {
        const marker = b[p++];
        if (marker === 0x3b) break;
        if (marker === 0x21) {
          if (p >= b.length) break;
          const label = b[p++];
          if (label === 0xf9 && p + 5 < b.length && b[p] >= 4) {
            const blockSize = b[p++];
            delay = ((b[p + 2] << 8) | b[p + 1]) / 100;
            p += blockSize;
            if (p < b.length && b[p] === 0) p++;
          } else p = skip(p);
          continue;
        }
        if (marker === 0x2c) {
          if (p + 9 > b.length) break;
          const local = b[p + 8];
          p += 9;
          if (local & 128) p += 3 * (1 << ((local & 7) + 1));
          if (p >= b.length) break;
          p++;
          p = skip(p);
          total += delay || 0.1;
          delay = 0;
          frames++;
          continue;
        }
        break;
      }
      return frames ? total : 0;
    } catch (_) { return 0; }
  }

  async function getApngDurationSeconds(file) {
    if (!(file instanceof Blob) || file.size < 40) return 0;
    try {
      const b = new Uint8Array(await file.slice(0, Math.min(file.size, 32 * 1024 * 1024)).arrayBuffer());
      if (b.length < 33 || b[0] !== 137 || b[1] !== 80 || b[2] !== 78 || b[3] !== 71) return 0;
      let p = 8, total = 0, frames = 0;
      while (p + 12 <= b.length) {
        const n = ((b[p] << 24) | (b[p + 1] << 16) | (b[p + 2] << 8) | b[p + 3]) >>> 0;
        if (n > b.length || p + 12 + n > b.length) break;
        const tag = String.fromCharCode(b[p + 4], b[p + 5], b[p + 6], b[p + 7]);
        const d = p + 8;
        if (tag === 'fcTL' && n >= 26) {
          const num = (b[d + 20] << 8) | b[d + 21];
          const den = ((b[d + 22] << 8) | b[d + 23]) || 100;
          total += num / den;
          frames++;
        }
        if (tag === 'IEND') break;
        p += 12 + n;
      }
      // A zero-delay APNG still contains frames; use a conservative estimate rather
      // than disabling the timeline completely.
      return frames ? (total > 0 ? total : frames * 0.1) : 0;
    } catch (_) { return 0; }
  }

  async function getEditableMediaInfo(file) {
    if (!(file instanceof Blob) || !file.size) return null;
    const mime = mimeFromFile(file), ext = fileExtension(file).toLowerCase();
    if (mime.startsWith('video/')) return { kind: 'video', mime, extension: ext, duration: 0, width: 0, height: 0 };
    const webp = await isAnimatedWebP(file);
    const apng = !webp && (mime === 'image/png' || ext === 'apng' || ext === 'png') ? await isAnimatedPng(file) : false;
    const gif = mime === 'image/gif' || ext === 'gif';
    if (!webp && !apng && !gif) return null;
    return { kind: 'animation', mime, extension: ext, animationFormat: webp ? 'webp' : apng ? 'apng' : 'gif',
      duration: 0, width: 0, height: 0 };
  }

  function formatEditorTime(seconds) {
    const v = Math.max(0, Number(seconds) || 0);
    return String(Math.floor(v / 60)).padStart(2, '0') + ':' +
      String(Math.floor(v % 60)).padStart(2, '0') + '.' + String(Math.floor((v % 1) * 100)).padStart(2, '0');
  }

  function normalizeMediaEditOptions(raw) {
    const duration = Math.max(0, Number(raw && raw.duration) || 0);
    const start = Math.max(0, Math.min(duration, Number(raw && raw.start) || 0));
    const rawEnd = Number(raw && raw.end);
    const end = duration ? Math.max(start, Math.min(duration, Number.isFinite(rawEnd) ? rawEnd : duration)) : 0;
    const c = raw && raw.crop || {};
    const requestedPingPongMode = String(raw && raw.pingPongMode || '');
    const pingPongMode = requestedPingPongMode === 'eco' ? 'soft' :
      ['linear', 'soft', 'balanced', 'smooth'].includes(requestedPingPongMode)
        ? requestedPingPongMode : raw && raw.loop === true ? 'smooth' : 'off';
    const w = Math.max(5, Math.min(100, Number(c.w) || 100));
    const h = Math.max(5, Math.min(100, Number(c.h) || 100));
    return { kind: raw && raw.kind === 'animation' ? 'animation' : 'video', duration, start, end,
      speed: Math.max(.25, Math.min(4, Number(raw && raw.speed) || 1)),
      loop: pingPongMode !== 'off', pingPongMode,
      crop: { x: Math.max(0, Math.min(100 - w, Number(c.x) || 0)),
        y: Math.max(0, Math.min(100 - h, Number(c.y) || 0)), w, h },
      hd: Boolean(raw && raw.hd),
      sourceWidth: Math.max(0, Math.floor(Number(raw && raw.sourceWidth) || 0)),
      sourceHeight: Math.max(0, Math.floor(Number(raw && raw.sourceHeight) || 0)) };
  }

  function getEditedOutputFormat(file, category, animatedWebP, configuredTarget) {
    if (['webp', 'gif', 'jpg', 'png', 'mp4', 'webm'].includes(configuredTarget) && configuredTarget !== 'keep') return configuredTarget;
    const ext = fileExtension(file).toLowerCase();
    if (category === 'video') return ext === 'webm' ? 'webm' : 'mp4';
    if (animatedWebP || ext === 'webp') return 'webp';
    return 'gif';
  }

  function mediaEditHasChanges(raw, outputFormat) {
    const e = normalizeMediaEditOptions(raw), c = e.crop;
    const pingPongChanged = e.loop === true && ['gif', 'webp', 'mp4', 'webm'].includes(outputFormat);
    return c.x > .5 || c.y > .5 || c.w < 99.5 || c.h < 99.5 ||
      (e.duration > 0 && (e.start > .03 || e.end < e.duration - .03)) ||
      Math.abs(e.speed - 1) > .001 || pingPongChanged;
  }

  // A stale full-screen overlay can sit above every control if an earlier script run
  // was interrupted. Remove orphaned layers before initializing or reopening the editor.
  function clearStaleMediaEditorOverlays() {
    document.getElementById('twgif-media-import-overlay')?.remove();
    document.getElementById('twgif-media-editor-overlay')?.remove();
  }

  function ensureMediaEditorStyles() {
    if (document.getElementById('twgif-media-editor-styles')) return;
    const st = document.createElement('style');
    st.id = 'twgif-media-editor-styles';
    st.textContent = [
      '#twgif-media-editor-overlay,#twgif-media-import-overlay{position:fixed!important;inset:0!important;z-index:2147483647!important;display:flex;align-items:center;justify-content:center;padding:20px;background:#07070acc;backdrop-filter:blur(12px);color:#f4f4f5;font:13px/1.45 Inter,system-ui,sans-serif;pointer-events:auto!important;isolation:isolate!important}',
      '#twgif-media-editor-overlay > #twgif-media-editor,#twgif-media-import-overlay > .twgif-media-import{position:relative!important;z-index:1!important;pointer-events:auto!important}',
      '#twgif-media-editor-overlay button,#twgif-media-editor-overlay input,#twgif-media-editor-overlay select,#twgif-media-editor-overlay textarea,#twgif-media-editor-overlay [role=slider],#twgif-media-import-overlay button,#twgif-media-import-overlay input,#twgif-media-import-overlay [role=button]{pointer-events:auto!important}',
      '#twgif-media-import-overlay .twgif-media-import{width:min(760px,100%);max-height:92vh;overflow:auto;border:1px solid #373741;border-radius:18px;background:linear-gradient(145deg,#1b1b22,#101014);box-shadow:0 30px 100px #000b}',
      '.twgif-media-import-body{padding:22px}.twgif-media-import-drop{display:flex;flex-direction:column;align-items:center;justify-content:center;gap:10px;min-height:285px;padding:24px;border:1px dashed #65517f;border-radius:15px;background:radial-gradient(ellipse at 50% 35%,#9a53ff14,#ffffff03);text-align:center;cursor:pointer;transition:border-color .16s,background .16s,transform .16s}',
      '.twgif-media-import-drop.is-dragging{border-color:#c4a2ff;background:#9147ff22;transform:scale(1.005)}.twgif-media-import-drop strong{font-size:15px;color:#f5f0ff}.twgif-media-import-drop>span{color:#a8a8b6;font-size:11px}',
      '.twgif-media-import-icon{display:grid;place-items:center;width:68px;height:68px;border:1px solid #a970ff3d;border-radius:19px;background:#9147ff14;color:#c7a5ff}.twgif-media-import-limit{margin-top:3px;color:#7f7f8c;font-size:10px}',
      '.twgif-media-import-divider{display:flex;align-items:center;gap:12px;margin:22px 0;color:#858591;font-size:10px}.twgif-media-import-divider:before,.twgif-media-import-divider:after{content:"";height:1px;flex:1;background:#ffffff14}',
      '.twgif-media-import-url label{display:block;margin-bottom:7px;color:#c7c7d2;font-size:11px;font-weight:650}.twgif-media-import-url-row{display:flex;gap:8px}.twgif-media-import-url-row input{flex:1;min-width:0;padding:11px 12px;border:1px solid #3b3b46;border-radius:10px;background:#17171d;color:#f4f4f5;font:inherit;font-size:12px;outline:none}.twgif-media-import-url-row input:focus{border-color:#a970ff;box-shadow:0 0 0 3px #9147ff24}',
      '.twgif-media-import-status{margin-top:9px;color:#8d8d9a;font-size:10px}.twgif-media-import-status.is-error{color:#ff8e9a}',
      '#twgif-media-editor-overlay[hidden],#twgif-media-import-overlay[hidden]{display:none!important}',
      '@media(max-width:650px){#twgif-media-import-overlay{padding:8px;align-items:flex-start}#twgif-media-import-overlay .twgif-media-import{max-height:calc(100vh - 16px)}.twgif-media-import-body{padding:12px}.twgif-media-import-drop{min-height:230px;padding:17px}.twgif-media-import-url-row{flex-direction:column}.twgif-media-import-url-row .twgif-editor-btn{width:100%}}',
      '#twgif-media-editor{width:min(1120px,100%);max-height:92vh;display:flex;flex-direction:column;overflow:hidden;border:1px solid #373741;border-radius:18px;background:linear-gradient(145deg,#1b1b22,#101014);box-shadow:0 30px 100px #000b}',
      '.twgif-editor-header{display:flex;justify-content:space-between;gap:14px;padding:18px 22px;border-bottom:1px solid #ffffff12}.twgif-editor-eyebrow{color:#bd9bff;font-size:10px;font-weight:800;letter-spacing:.15em;text-transform:uppercase}',
      '.twgif-editor-title{margin:5px 0;font-size:21px;letter-spacing:-.03em}.twgif-editor-subtitle{margin:5px 0;color:#a3a3af;font-size:12px}.twgif-editor-safe{display:block;margin-top:8px;color:#8fe0b3;font-size:10px}',
      '.twgif-editor-close{width:34px;height:34px;border:1px solid #ffffff18;border-radius:9px;background:#ffffff08;color:#ddd;font-size:22px;cursor:pointer}',
      '.twgif-editor-body{display:grid;grid-template-columns:minmax(0,1.5fr) minmax(270px,.9fr);gap:16px;min-height:0;padding:16px 22px;overflow:auto}.twgif-editor-preview-column{display:flex;flex-direction:column;gap:10px;min-width:0}',
      '.twgif-editor-stage{position:relative;display:flex;align-items:center;justify-content:center;min-height:210px;height:clamp(220px,43vh,480px);overflow:hidden;border:1px solid #393943;border-radius:13px;background:radial-gradient(ellipse at center,#292933,#08080a 75%);isolation:isolate}',
      '.twgif-editor-preview-media{position:absolute;inset:0;width:100%;height:100%;object-fit:contain;user-select:none;-webkit-user-drag:none}.twgif-editor-crop-frame{position:absolute;z-index:2;box-sizing:border-box;border:1px solid #eadfff;box-shadow:0 0 0 2000px #000a,0 0 0 1px #8b5bd6;cursor:move;touch-action:none;opacity:0;pointer-events:none;transition:opacity .14s}',
      '.twgif-cropping .twgif-editor-crop-frame{opacity:1;pointer-events:auto}.twgif-editor-crop-frame:after{content:"";display:none;position:absolute;inset:0;pointer-events:none;background:linear-gradient(to right,transparent 33%,#ffffff55 33.3%,transparent 33.6%,transparent 66.3%,#ffffff55 66.6%,transparent 66.9%),linear-gradient(to bottom,transparent 33%,#ffffff55 33.3%,transparent 33.6%,transparent 66.3%,#ffffff55 66.6%,transparent 66.9%)}.twgif-cropping .twgif-editor-crop-frame:after{display:block}',
      '.twgif-editor-handle{position:absolute;z-index:4;width:13px;height:13px;border:2px solid white;border-radius:4px;background:#a970ff;touch-action:none}.twgif-editor-handle[data-handle=nw]{left:-6px;top:-6px;cursor:nwse-resize}.twgif-editor-handle[data-handle=ne]{right:-6px;top:-6px;cursor:nesw-resize}.twgif-editor-handle[data-handle=sw]{left:-6px;bottom:-6px;cursor:nesw-resize}.twgif-editor-handle[data-handle=se]{right:-6px;bottom:-6px;cursor:nwse-resize}',
      '.twgif-editor-stage-hint{position:absolute;z-index:1;top:10px;left:10px;padding:5px 8px;border-radius:7px;background:#08080bd9;color:#ccc;font-size:10px;pointer-events:none}',
      '.twgif-editor-player{display:flex;align-items:center;gap:9px;padding:10px;border:1px solid #ffffff12;border-radius:11px;background:#ffffff05}.twgif-editor-play{width:34px;height:34px;border:1px solid #a970ff66;border-radius:9px;background:#9147ff24;color:#eadcff;cursor:pointer}.twgif-editor-play:disabled{opacity:.4;cursor:not-allowed}.twgif-editor-player-time{min-width:70px;color:#c9c9d2;font-size:11px;font-variant-numeric:tabular-nums}.twgif-editor-player-range{width:100%;accent-color:#a970ff}.twgif-editor-player-note{color:#bbbcca;font-size:11px}',
      '.twgif-editor-timeline-wrap{margin-top:2px;padding:12px;border:1px solid #ffffff12;border-radius:13px;background:linear-gradient(135deg,#ffffff07,#ffffff02)}.twgif-editor-timeline-head{display:flex;align-items:center;justify-content:space-between;gap:10px;margin-bottom:28px}',
      '.twgif-editor-timeline-visual{position:relative;height:84px;border:1px solid #3a3a45;border-radius:9px;background:#0c0c10;isolation:isolate;touch-action:pan-y;overflow:visible}',
      '.twgif-editor-storyboard{position:absolute;inset:0;display:grid;grid-template-columns:repeat(12,minmax(0,1fr));overflow:hidden;border-radius:8px}.twgif-editor-storyboard-empty{grid-column:1/-1;display:flex;align-items:center;justify-content:center;padding:8px;color:#777784;font-size:10px;text-align:center}.twgif-editor-frame-thumb{width:100%;height:84px;min-width:0;object-fit:cover;opacity:.87;cursor:pointer}.twgif-editor-frame-thumb:hover{opacity:1;outline:1px solid #d8bdff;outline-offset:-1px}',
      '.twgif-editor-trim-shade{position:absolute;z-index:1;top:0;bottom:0;background:#08080bc9;pointer-events:none}.twgif-editor-trim-shade-left{left:0;width:0}.twgif-editor-trim-shade-right{right:0;width:0}',
      '.twgif-editor-trim-selection{position:absolute;z-index:2;top:0;bottom:0;left:0;width:100%;border:1px solid #bf91ff;background:#a970ff12;pointer-events:none;box-sizing:border-box}',
      '.twgif-editor-playhead{position:absolute;z-index:4;top:-3px;bottom:-3px;left:0;width:2px;background:#ffe3a1;box-shadow:0 0 6px #ffce6a;pointer-events:none}',
      '.twgif-editor-trim-handle{position:absolute;z-index:5;top:0;bottom:0;width:22px;transform:translateX(-50%);padding:0;border:0;background:transparent;color:#f4eaff;cursor:ew-resize;touch-action:none}.twgif-editor-trim-handle:before{content:"";position:absolute;top:0;bottom:0;left:9px;width:4px;border-radius:4px;background:#c9a4ff;box-shadow:0 0 9px #a970ff90}.twgif-editor-trim-handle:after{content:"";position:absolute;top:33px;left:3px;width:16px;height:18px;border:2px solid #f7edff;border-radius:5px;background:#9457ee;box-shadow:0 2px 8px #0009}.twgif-editor-trim-handle:focus-visible{outline:2px solid #f3deff;outline-offset:1px}.twgif-editor-trim-handle:disabled{opacity:.3;cursor:not-allowed}',
      '.twgif-editor-handle-time{position:absolute;top:-25px;left:50%;transform:translateX(-50%);padding:3px 5px;border:1px solid #4e3b67;border-radius:5px;background:#20162d;color:#edddff;font-size:10px;font-variant-numeric:tabular-nums;white-space:nowrap;pointer-events:none}',
      '.twgif-editor-timeline-edges{display:flex;justify-content:space-between;margin:7px 0 8px;color:#a6a6b2;font-size:10px;font-variant-numeric:tabular-nums}.twgif-editor-speed-slider{width:100%;accent-color:#a970ff;cursor:pointer}.twgif-editor-speed-ends{display:flex;justify-content:space-between;color:#888894;font-size:10px}',
      '.twgif-editor-timeline-wrap .twgif-editor-player{padding:5px 0;border:0;background:transparent}.twgif-editor-timeline-wrap .twgif-editor-help{margin-top:7px}',
      '.twgif-editor-section{padding:13px;border:1px solid #ffffff12;border-radius:12px;background:#ffffff05}.twgif-editor-section+.twgif-editor-section{margin-top:9px}.twgif-editor-section-head{display:flex;justify-content:space-between;gap:8px;margin-bottom:9px}.twgif-editor-section-title{font-size:12px;font-weight:750}.twgif-editor-section-meta{color:#a8a8b4;font-size:10px}',
      '.twgif-editor-control-label{display:flex;justify-content:space-between;margin:9px 0 4px;color:#bdbdc8;font-size:11px}.twgif-editor-range{width:100%;accent-color:#a970ff}.twgif-editor-range:disabled{opacity:.4}.twgif-editor-range-values{display:flex;justify-content:space-between;color:#888894;font-size:10px}',
      '.twgif-editor-select{width:100%;padding:9px;border:1px solid #3b3b46;border-radius:9px;background:#202027;color:#f4f4f5;font:inherit;font-size:12px}.twgif-editor-help{margin-top:7px;color:#90909c;font-size:10px;line-height:1.5}',
      '.twgif-editor-presets{display:flex;flex-wrap:wrap;gap:6px;margin-bottom:9px}.twgif-editor-preset{padding:6px 8px;border:1px solid #3b3b46;border-radius:8px;background:#ffffff05;color:#bdbdc8;font-size:10px;cursor:pointer}.twgif-editor-preset[aria-pressed=true],.twgif-editor-preset:hover{border-color:#a970ff;background:#9147ff24;color:#eee2ff}',
      '.twgif-editor-crop-readout{display:flex;justify-content:space-between;color:#bdbdc8;font-size:10px}.twgif-editor-toggle{display:flex;gap:9px;color:#e7e7ed;font-size:11px}.twgif-editor-toggle input{accent-color:#a970ff}.twgif-editor-toggle small{display:block;margin-top:3px;color:#9999a5;font-size:10px}',
      '.twgif-editor-output{display:flex;justify-content:space-between;gap:10px;padding:11px;border:1px solid #a970ff33;border-radius:11px;background:#9147ff12}.twgif-editor-output-label{color:#a4a4b0;font-size:10px}.twgif-editor-output-value{color:#eee2ff;font-size:12px}',
      '.twgif-editor-footer{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:15px 22px;border-top:1px solid #ffffff12}.twgif-editor-summary{color:#aaaab5;font-size:11px}.twgif-editor-summary strong{color:#eee}.twgif-editor-actions{display:flex;gap:8px}.twgif-editor-btn{padding:10px 14px;border:1px solid #3b3b46;border-radius:9px;background:#ffffff08;color:#ddd;font:inherit;font-size:12px;font-weight:650;cursor:pointer}.twgif-editor-btn-primary{border-color:#9147ff;background:linear-gradient(135deg,#9c5bff,#7a32e5);color:white}',
      '@media(max-width:760px){#twgif-media-editor-overlay{padding:7px;align-items:flex-start}#twgif-media-editor{max-height:calc(100vh - 14px)}.twgif-editor-body{grid-template-columns:1fr;padding:10px;gap:10px}.twgif-editor-stage{height:34vh;min-height:175px}.twgif-editor-footer{align-items:flex-start;flex-direction:column;padding:12px 14px}.twgif-editor-actions{width:100%}.twgif-editor-actions .twgif-editor-btn{flex:1}}',
      '#twgif-media-editor{display:flex;flex-direction:column;width:min(1180px,calc(100vw - 32px));height:min(820px,calc(100vh - 32px));max-height:calc(100vh - 32px)}.twgif-editor-header{flex:0 0 auto;align-items:center;padding:10px 16px;gap:10px}.twgif-editor-title{font-size:18px;margin:3px 0}.twgif-editor-subtitle{margin:3px 0}.twgif-editor-safe{margin-top:4px}.twgif-editor-close{display:inline-flex;align-items:center;justify-content:center;box-sizing:border-box;width:34px;height:34px;flex:0 0 34px;padding:0;border:1px solid #ffffff18;border-radius:9px;background:#ffffff08;color:#ddd;font-size:22px;line-height:1;cursor:pointer}.twgif-editor-body{display:grid;flex:1 1 auto;grid-template-columns:minmax(0,1.55fr) minmax(275px,.85fr);grid-template-rows:minmax(180px,1fr) auto;align-content:start;gap:10px 12px;min-height:0;padding:10px 16px;overflow:auto}.twgif-editor-preview-column{grid-column:1;grid-row:1;display:flex;flex-direction:column;gap:8px;min-width:0;min-height:0}.twgif-editor-stage{height:clamp(150px,31vh,320px);min-height:140px;flex:0 1 auto}.twgif-editor-body>aside{grid-column:2;grid-row:1;display:flex;flex-direction:column;gap:6px;min-width:0;min-height:0;overflow-y:auto;overflow-x:hidden}.twgif-editor-body>aside>.twgif-editor-section{padding:8px;margin:0;flex:0 0 auto}.twgif-editor-section+.twgif-editor-section{margin-top:0}.twgif-editor-section-head{align-items:center;margin-bottom:5px}.twgif-editor-help{margin-top:4px;font-size:9px;line-height:1.35}.twgif-editor-speed-ends{font-size:9px}.twgif-editor-crop-readout{margin-bottom:5px}.twgif-editor-output{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:8px;flex:0 0 auto}.twgif-editor-footer{flex:0 0 auto;padding:10px 16px}.twgif-editor-btn{padding:9px 12px}.twgif-editor-play{display:inline-flex;align-items:center;justify-content:center;box-sizing:border-box;width:34px;height:34px;flex:0 0 34px;padding:0;border:1px solid #a970ff66;border-radius:9px;background:#9147ff24;color:#eadcff;line-height:1;cursor:pointer}.twgif-editor-timeline-wrap{grid-column:1/-1;grid-row:2;min-width:0;margin:0;padding:9px 10px;border:1px solid #ffffff12;border-radius:12px;background:linear-gradient(135deg,#ffffff07,#ffffff02)}.twgif-editor-timeline-head{margin-bottom:24px}.twgif-editor-timeline-visual{height:76px;touch-action:none;cursor:crosshair;overflow:visible}.twgif-editor-storyboard{position:absolute;inset:0;display:flex;align-items:stretch;gap:0;overflow:hidden;border-radius:8px;pointer-events:none}.twgif-editor-frame-thumb{display:block;flex:0 0 auto;width:auto;height:100%;max-width:none;object-fit:contain;background:#0c0c10;opacity:.9;user-select:none;-webkit-user-select:none;-webkit-user-drag:none;pointer-events:none;cursor:default}.twgif-editor-playhead{left:0;will-change:transform}.twgif-editor-playhead-label{position:absolute;z-index:7;top:-25px;left:0;transform:translate3d(0,0,0) translateX(-50%);padding:2px 5px;border:1px solid #604783;border-radius:5px;background:#20162d;color:#f0e2ff;font-size:10px;font-variant-numeric:tabular-nums;line-height:1.2;white-space:nowrap;pointer-events:none;will-change:transform}.twgif-editor-timeline-wrap .twgif-editor-player{display:flex;align-items:center;gap:8px;padding:5px 0 0;border:0;background:transparent}.twgif-editor-player-time[hidden],.twgif-editor-player-range[hidden]{display:none!important}.twgif-editor-timeline-wrap .twgif-editor-help{margin-top:5px}.twgif-editor-close:focus-visible,.twgif-editor-play:focus-visible{outline:2px solid #e2c5ff;outline-offset:2px}@media(max-width:760px){#twgif-media-editor-overlay{padding:7px;align-items:flex-start}#twgif-media-editor{height:auto;max-height:calc(100vh - 14px)}.twgif-editor-body{grid-template-columns:minmax(0,1fr);grid-template-rows:auto auto auto;padding:10px;gap:10px;overflow:auto}.twgif-editor-preview-column{grid-column:1;grid-row:1}.twgif-editor-body>aside{grid-column:1;grid-row:2;overflow:visible}.twgif-editor-timeline-wrap{grid-column:1;grid-row:3}.twgif-editor-stage{height:34vh;min-height:175px}.twgif-editor-footer{align-items:flex-start;flex-direction:column;padding:12px 14px}.twgif-editor-actions{width:100%}.twgif-editor-actions .twgif-editor-btn{flex:1}}',
      '#twgif-media-editor{width:min(1380px,calc(100vw - 24px));height:min(940px,calc(100vh - 24px));max-height:calc(100vh - 24px)}.twgif-editor-preview-controls{display:flex;align-items:center;justify-content:center;min-height:46px;gap:8px;flex:0 0 auto}.twgif-editor-preview-controls .twgif-editor-play{display:inline-flex;align-items:center;justify-content:center;width:38px;height:38px;flex:0 0 38px;padding:0;line-height:1}.twgif-editor-timeline-head,.twgif-editor-playhead-label,.twgif-editor-handle-time,.twgif-editor-timeline-edges{display:none!important}#twgif-media-editor .twgif-editor-header{min-height:42px;padding:7px 14px;align-items:center}#twgif-media-editor .twgif-editor-eyebrow,#twgif-media-editor .twgif-editor-subtitle,#twgif-media-editor .twgif-editor-safe{display:none!important}#twgif-media-editor .twgif-editor-title{margin:0;font-size:17px}.twgif-editor-body{grid-template-columns:minmax(0,2.3fr) minmax(230px,.74fr);grid-template-rows:minmax(300px,1fr) auto;gap:8px 12px;padding:8px 14px;overflow:auto}.twgif-editor-preview-column{gap:0;min-height:0}.twgif-editor-stage{height:clamp(300px,52vh,600px);min-height:280px;max-height:none;flex:1 1 auto}.twgif-editor-body>aside{gap:5px;overflow-y:auto;overscroll-behavior:contain}.twgif-editor-body>aside>.twgif-editor-section{padding:8px}.twgif-editor-output{display:none!important}.twgif-editor-timeline-wrap{padding:8px 10px}.twgif-editor-timeline-head{margin-bottom:24px}.twgif-editor-timeline-visual{height:80px}.twgif-editor-frame-thumb{flex:1 1 0;width:0;min-width:0;height:100%;object-fit:contain}.twgif-editor-timeline-wrap .twgif-editor-help{margin-top:3px}.twgif-editor-footer{padding:8px 14px}.twgif-editor-summary{font-size:10px}@media(max-width:760px){#twgif-media-editor{width:100%;height:auto;max-height:calc(100vh - 14px)}.twgif-editor-body{grid-template-columns:minmax(0,1fr);grid-template-rows:auto auto auto;padding:10px;gap:10px;overflow:auto}.twgif-editor-preview-column{grid-column:1;grid-row:1}.twgif-editor-body>aside{grid-column:1;grid-row:2;overflow:visible}.twgif-editor-timeline-wrap{grid-column:1;grid-row:3}.twgif-editor-stage{height:46vh;min-height:220px;flex:none}.twgif-editor-footer{align-items:flex-start;flex-direction:column;padding:12px 14px}.twgif-editor-actions{width:100%}.twgif-editor-actions .twgif-editor-btn{flex:1}}',
    ].join('\n');
    (document.head || document.documentElement).appendChild(st);
  }

  function openMediaEditor(file, runId, info) {
    ensureMediaEditorStyles();
    return new Promise(resolve => {
      const url = URL.createObjectURL(file);
      const overlay = document.createElement('div');
      overlay.id = 'twgif-media-editor-overlay';
      overlay.innerHTML = [
        '<section id="twgif-media-editor" role="dialog" aria-modal="true" aria-labelledby="twgif-editor-title">',
        '<header class="twgif-editor-header"><div><span class="twgif-editor-eyebrow">Перед загрузкой · локально</span><h2 id="twgif-editor-title" class="twgif-editor-title">Редактор медиа</h2>',
        '<p class="twgif-editor-subtitle">Обрезай фрагмент, меняй скорость и кадрируй. Изменения применяются до загрузки.</p><span class="twgif-editor-safe">Файл обрабатывается на устройстве</span></div><button class="twgif-editor-close" data-editor-close aria-label="Закрыть">×</button></header>',
        '<div class="twgif-editor-body"><div class="twgif-editor-preview-column"><div class="twgif-editor-stage" data-stage><div class="twgif-editor-stage-hint">Перетаскивай рамку или её углы</div>',
        '<div class="twgif-editor-crop-frame" data-crop-frame><span class="twgif-editor-handle" data-handle="nw"></span><span class="twgif-editor-handle" data-handle="ne"></span><span class="twgif-editor-handle" data-handle="sw"></span><span class="twgif-editor-handle" data-handle="se"></span></div></div><div class="twgif-editor-preview-controls"><button class="twgif-editor-play" type="button" data-play aria-label="Воспроизвести">▶</button><span class="twgif-editor-player-time" data-current hidden>00:00.00</span><input class="twgif-editor-player-range" type="range" min="0" max="0" step=".01" data-scrub aria-label="Позиция воспроизведения" hidden disabled><span class="twgif-editor-player-time" data-duration hidden>—:—</span></div></div><aside>',
        '<section class="twgif-editor-section"><div class="twgif-editor-section-head"><span class="twgif-editor-section-title">Скорость</span><span class="twgif-editor-section-meta" data-speed-summary>1× · обычная</span></div>',
        '<input class="twgif-editor-speed-slider" type="range" data-speed min=".25" max="4" step=".05" value="1" aria-label="Скорость воспроизведения">',
        '<div class="twgif-editor-speed-ends"><span>0,25×</span><span>4×</span></div><div class="twgif-editor-help">Скорость видна в предпросмотре и применяется к итоговому файлу.</div></section>',
        '<section class="twgif-editor-section"><div class="twgif-editor-section-head"><span class="twgif-editor-section-title">Кадрирование</span><button class="twgif-editor-preset" type="button" data-crop-toggle aria-pressed="false">Включить</button></div>',
        '<div data-crop-controls hidden><div class="twgif-editor-presets"><button class="twgif-editor-preset" type="button" data-preset="free" aria-pressed="true">Свободно</button><button class="twgif-editor-preset" type="button" data-preset="16:9">16:9</button><button class="twgif-editor-preset" type="button" data-preset="9:16">9:16</button><button class="twgif-editor-preset" type="button" data-preset="1:1">1:1</button><button class="twgif-editor-preset" type="button" data-preset="4:3">4:3</button></div>',
        '<div class="twgif-editor-crop-readout"><span>Область кадра</span><strong data-crop-readout>100% × 100%</strong></div><button class="twgif-editor-preset" type="button" data-reset>Сбросить кадрирование</button><div class="twgif-editor-help">Перетаскивай рамку или углы. Сетка видна только в этом режиме.</div></div></section>',
        '<section class="twgif-editor-section"><div class="twgif-editor-section-head"><span class="twgif-editor-section-title">Ping-pong</span><span class="twgif-editor-section-meta">Плавность отскока</span></div><select class="twgif-editor-select" data-loop aria-label="Плавность отскока ping-pong"><option value="off">Выключен</option><option value="linear">Обычный</option><option value="soft">Мягкий отскок</option><option value="balanced">Сбалансированный</option><option value="smooth">Плавный отскок</option></select><div class="twgif-editor-help">В предпросмотре: замедление у края и плавное ускорение после разворота.</div></section>',
        '<section class="twgif-editor-section"><label class="twgif-editor-toggle"><input type="checkbox" data-hd><span><strong>HD</strong><small>Сохранить исходное разрешение и качество без сжатия.</small></span></label></section>',
        '</aside>',
        '<div class="twgif-editor-timeline-wrap">',
        '<div class="twgif-editor-timeline-visual" data-timeline-track>',
        '<div class="twgif-editor-storyboard" data-storyboard><div class="twgif-editor-storyboard-empty" data-storyboard-empty>Раскадровка появится после загрузки</div></div>',
        '<div class="twgif-editor-trim-shade twgif-editor-trim-shade-left" data-trim-shade-left></div><div class="twgif-editor-trim-shade twgif-editor-trim-shade-right" data-trim-shade-right></div>',
        '<div class="twgif-editor-trim-selection" data-trim-selection></div><div class="twgif-editor-playhead" data-playhead></div>',
        '<button class="twgif-editor-trim-handle twgif-editor-trim-start" type="button" role="slider" aria-label="Начало фрагмента" aria-valuemin="0" aria-valuemax="0" aria-valuenow="0" aria-valuetext="00:00.00" data-trim-start disabled></button>',
        '<button class="twgif-editor-trim-handle twgif-editor-trim-end" type="button" role="slider" aria-label="Конец фрагмента" aria-valuemin="0" aria-valuemax="0" aria-valuenow="0" aria-valuetext="—:—" data-trim-end disabled></button>',
        '</div></div></div>',
        '<footer class="twgif-editor-footer"><div class="twgif-editor-summary" data-summary>Итоговая длительность: <strong>—</strong></div><div class="twgif-editor-actions"><button class="twgif-editor-btn" data-cancel>Отмена</button><button class="twgif-editor-btn twgif-editor-btn-primary" data-apply>Применить и продолжить →</button></div></footer></section>'
      ].join('');
      document.body.appendChild(overlay);

      const $ = selector => overlay.querySelector(selector);
      const dialog = $('#twgif-media-editor');
      const stage = $('[data-stage]'), frame = $('[data-crop-frame]');
      const timelineTrack = $('[data-timeline-track]');
      const storyboard = $('[data-storyboard]');
      const scrub = $('[data-scrub]'), startInput = $('[data-trim-start]'), endInput = $('[data-trim-end]');
      const trimSelection = $('[data-trim-selection]');
      const trimShadeLeft = $('[data-trim-shade-left]'), trimShadeRight = $('[data-trim-shade-right]');
      const playhead = $('[data-playhead]');
      const speedInput = $('[data-speed]'), loopInput = $('[data-loop]');
      const hdInput = $('[data-hd]');
      const cropToggle = $('[data-crop-toggle]'), cropControls = $('[data-crop-controls]');
      const playButton = $('[data-play]');
      const currentLabel = $('[data-current]');
      const durationLabel = $('[data-duration]');
      hdInput.checked = !isCompressionEnabled();
      const animationNote = document.createElement('span');
      animationNote.className = 'twgif-editor-player-note';
      animationNote.textContent = 'Анимация воспроизводится браузером';
      animationNote.hidden = true;
      durationLabel.before(animationNote);
      const media = document.createElement(info.kind === 'video' ? 'video' : 'img');
      media.className = 'twgif-editor-preview-media';
      if (info.kind === 'video') { media.preload = 'auto'; media.playsInline = true; }
      else { media.alt = 'Предпросмотр анимации'; media.draggable = false; }
      stage.insertBefore(media, frame);
      const animationCanvas = info.kind === 'animation' ? document.createElement('canvas') : null;
      if (animationCanvas) {
        animationCanvas.className = 'twgif-editor-preview-media';
        animationCanvas.hidden = true;
        animationCanvas.setAttribute('aria-label', 'Покадровый предпросмотр анимации');
        stage.insertBefore(animationCanvas, frame);
      }

      let done = false, duration = 0, width = 0, height = 0, start = 0, end = 0, speed = 1, loop = false;
      let pingPongMode = 'off', videoReverseActive = false, videoReverseGeneration = 0;
      let crop = { x: 0, y: 0, w: 100, h: 100 }, cropMode = false, trimDrag = null;
      let drag = null, dragId = null, resizeObserver = null, resizeHandler = null;
      let playheadDrag = null, seekTimer = 0, pendingSeekTime = null, playheadRaf = 0, isTimelineScrubbing = false;
      let userChangedTrim = false, videoReverseTimer = 0, videoPingPongDirection = 1;
      let animationDecoder = null, animationFrameDurations = [], animationFrameStarts = [];
      let animationFrameIndex = 0, animationPaintedFrameIndex = -1, animationDirection = 1, animationPlaying = false, animationTimer = 0, animationGeneration = 0;
      let animationSeekBusy = false, pendingAnimationSeek = null;
      let animationDecodeQueue = Promise.resolve();
      let storyboardRun = 0;
      const storyboardObjectUrls = [];
      const cleanup = () => {
        animationPlaying = false;
        animationGeneration++;
        storyboardRun++;
        for (const thumbUrl of storyboardObjectUrls) URL.revokeObjectURL(thumbUrl);
        storyboardObjectUrls.length = 0;
        if (videoReverseTimer) clearTimeout(videoReverseTimer);
        videoReverseTimer = 0;
        videoReverseActive = false;
        videoReverseGeneration++;
        if (seekTimer) clearTimeout(seekTimer);
        seekTimer = 0;
        pendingSeekTime = null;
        if (playheadRaf) window.cancelAnimationFrame(playheadRaf);
        playheadRaf = 0;
        if (animationTimer) clearTimeout(animationTimer);
        animationTimer = 0;
        if (animationDecoder) {
          try { animationDecoder.close(); } catch (_) {}
          animationDecoder = null;
        }
        document.removeEventListener('keydown', onKey, true);
        if (resizeObserver) resizeObserver.disconnect();
        if (resizeHandler) window.removeEventListener('resize', resizeHandler);
        if (info.kind === 'video') {
          media.removeEventListener('loadedmetadata', onVideoMeta);
          media.removeEventListener('timeupdate', onVideoTime);
          media.removeEventListener('ended', onVideoEnd);
          media.removeEventListener('play', onPlayState);
          media.removeEventListener('pause', onPlayState);
          try { media.pause(); } catch (_) {}
        }
        media.removeAttribute('src');
        try { if (info.kind === 'video') media.load(); } catch (_) {}
        URL.revokeObjectURL(url);
        overlay.remove();
      };
      const finish = value => { if (done) return; done = true; cleanup(); resolve(value); };
      const contentRect = () => {
        const sw = stage.clientWidth, sh = stage.clientHeight;
        if (!sw || !sh || !width || !height) return { left: 0, top: 0, width: sw, height: sh };
        const aspect = width / height; let w = sw, h = w / aspect;
        if (h > sh) { h = sh; w = h * aspect; }
        return { left: (sw - w) / 2, top: (sh - h) / 2, width: w, height: h };
      };
      const updateFrame = () => {
        const r = contentRect();
        frame.style.left = (r.left + r.width * crop.x / 100) + 'px';
        frame.style.top = (r.top + r.height * crop.y / 100) + 'px';
        frame.style.width = (r.width * crop.w / 100) + 'px';
        frame.style.height = (r.height * crop.h / 100) + 'px';
        $('[data-crop-readout]').textContent = Math.round(crop.w) + '% × ' + Math.round(crop.h) + '%';
        overlay.querySelectorAll('[data-preset]').forEach(b => b.setAttribute('aria-pressed',
          String(b.dataset.preset === 'free' && crop.x === 0 && crop.y === 0 && crop.w === 100 && crop.h === 100)));
      };
      const paintPlayhead = seconds => {
        const safeDuration = Math.max(0, Number(duration) || 0);
        const value = Math.max(0, Math.min(safeDuration || Number(seconds) || 0, Number(seconds) || 0));
        const pct = safeDuration ? Math.max(0, Math.min(100, value / safeDuration * 100)) : 0;
        const translateX = Math.round((timelineTrack.clientWidth || 0) * pct / 100);
        playhead.style.transform = 'translate3d(' + translateX + 'px,0,0)';
      };
      const updateTimelineControls = (timeOverride = null) => {
        const safeDuration = Math.max(0, Number(duration) || 0);
        const startPct = safeDuration ? Math.max(0, Math.min(100, start / safeDuration * 100)) : 0;
        const endPct = safeDuration ? Math.max(startPct, Math.min(100, end / safeDuration * 100)) : 100;
        startInput.style.left = startPct + '%';
        endInput.style.left = endPct + '%';
        trimSelection.style.left = startPct + '%';
        trimSelection.style.width = Math.max(0, endPct - startPct) + '%';
        trimShadeLeft.style.width = startPct + '%';
        trimShadeRight.style.width = (100 - endPct) + '%';
        startInput.setAttribute('aria-valuemax', String(safeDuration));
        startInput.setAttribute('aria-valuenow', String(start));
        startInput.setAttribute('aria-valuetext', formatEditorTime(start));
        endInput.setAttribute('aria-valuemax', String(safeDuration));
        endInput.setAttribute('aria-valuenow', String(end));
        endInput.setAttribute('aria-valuetext', safeDuration ? formatEditorTime(end) : '—:—');
        const previewTime = timeOverride !== null ? timeOverride
          : info.kind === 'video' ? (Number(media.currentTime) || 0)
            : animationDecoder ? (Number(animationFrameStarts[animationFrameIndex]) || 0)
              : (Number(scrub.value) || 0);
        paintPlayhead(previewTime);
        scrub.max = String(safeDuration);
        if (Number.isFinite(previewTime)) scrub.value = String(Math.max(0, Math.min(safeDuration || previewTime, previewTime)));
        startInput.disabled = safeDuration <= 0;
        endInput.disabled = safeDuration <= 0;
        $('[data-duration]').textContent = safeDuration > 0 ? formatEditorTime(safeDuration) : '—:—';
      };
      const updateSummary = () => {
        const selected = duration > 0 ? Math.max(0, end - start) : 0;
        $('[data-summary]').innerHTML = 'Итоговая длительность: <strong>' +
          (selected > 0 ? formatEditorTime(selected / speed) : 'полная') + '</strong> <span style="color:#888">· ' + speed.toLocaleString('ru-RU') + '×</span>';
        $('[data-speed-summary]').textContent = speed.toLocaleString('ru-RU') + '× · ' + (speed < 1 ? 'замедление' : speed > 1 ? 'ускорение' : 'обычная');
        speedInput.value = String(speed);
        updateTimelineControls();
      };
      const setDuration = value => {
        const n = Number(value);
        if (!Number.isFinite(n) || n <= 0) return;
        duration = n; start = Math.min(start, duration); end = end > 0 ? Math.min(end, duration) : duration;
        if (end <= start) { start = 0; end = duration; }
        startInput.disabled = false; endInput.disabled = false;
        scrub.disabled = info.kind !== 'video' && !animationDecoder;
        updateSummary();
      };

      const canvasToStoryboardUrl = canvas => new Promise(resolve => {
        canvas.toBlob(blob => {
          if (!blob || done) { resolve(''); return; }
          const objectUrl = URL.createObjectURL(blob);
          storyboardObjectUrls.push(objectUrl);
          resolve(objectUrl);
        }, 'image/jpeg', 0.66);
      });
      const waitForPreviewIdle = async () => {
        if (info.kind === 'video' && !media.paused) {
          await new Promise(resolve => media.addEventListener('pause', resolve, { once: true }));
        }
        while ((isTimelineScrubbing || (info.kind === 'animation' && animationPlaying) ||
            (info.kind === 'video' && videoReverseActive)) && !done) {
          await new Promise(resolve => window.setTimeout(resolve, 40));
        }
        if (!done) await new Promise(resolve => window.setTimeout(resolve, 0));
      };
      const addStoryboardThumb = (dataUrl, time, index, run) => {
        if (done || run !== storyboardRun || !dataUrl) return;
        const empty = $('[data-storyboard-empty]');
        if (empty) empty.remove();
        const image = document.createElement('img');
        image.className = 'twgif-editor-frame-thumb';
        image.alt = '';
        image.setAttribute('aria-hidden', 'true');
        image.draggable = false;
        image.loading = 'eager';
        image.src = dataUrl;
        storyboard.appendChild(image);
      };
      const drawStoryboardFrame = (context, source, canvas) => {
        const sourceWidth = Number(source.videoWidth || source.displayWidth || source.naturalWidth || source.width) || canvas.width;
        const sourceHeight = Number(source.videoHeight || source.displayHeight || source.naturalHeight || source.height) || canvas.height;
        if (Math.abs(canvas.width / canvas.height - sourceWidth / sourceHeight) > 0.02) {
          canvas.width = Math.max(30, Math.min(360, Math.round(canvas.height * sourceWidth / sourceHeight)));
        }
        const isVideo = source && source.tagName === 'VIDEO';
        if (isVideo && (source.readyState < 2 || !source.videoWidth || !source.videoHeight)) return false;
        const ctx = canvas.getContext('2d');
        if (!ctx) return false;
        ctx.fillStyle = '#0c0c10';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        try { ctx.drawImage(source, 0, 0, canvas.width, canvas.height); }
        catch (_) { return false; }
        return true;
      };

      const populateVideoStoryboard = async () => {
        if (info.kind !== 'video' || !duration || done) return;
        const run = ++storyboardRun;
        storyboard.replaceChildren();
        const probe = document.createElement('video');
        probe.preload = 'metadata'; probe.muted = true; probe.playsInline = true; probe.src = url;
        const waitForEvent = (eventName, timeoutMs = 2200) => new Promise((resolve, reject) => {
          let timer = 0;
          const cleanup = () => {
            probe.removeEventListener(eventName, onDone);
            probe.removeEventListener('error', onError);
            if (timer) clearTimeout(timer);
          };
          const onDone = () => { cleanup(); resolve(); };
          const onError = () => { cleanup(); reject(new Error('Не удалось прочитать кадр видео.')); };
          probe.addEventListener(eventName, onDone, { once: true });
          probe.addEventListener('error', onError, { once: true });
          timer = setTimeout(() => { cleanup(); reject(new Error('Превышено время ожидания кадра.')); }, timeoutMs);
        });
        try {
          const metadataReady = waitForEvent('loadedmetadata', 6000);
          probe.load();
          await metadataReady;
          const aspect = probe.videoWidth && probe.videoHeight ? probe.videoWidth / probe.videoHeight : 16 / 9;
          const thumbHeight = Math.max(40, timelineTrack.clientHeight || 76);
          const thumbWidth = Math.max(30, thumbHeight * aspect);
          const count = Math.max(1, Math.min(36, Math.round((timelineTrack.clientWidth || 840) / thumbWidth)));
          const canvas = document.createElement('canvas');
          canvas.height = 90;
          canvas.width = Math.max(30, Math.min(360, Math.round(canvas.height * aspect)));
          const context = canvas.getContext('2d');
          if (!context) return;
          for (let i = 0; i < count; i++) {
            if (done || run !== storyboardRun) return;
            await waitForPreviewIdle();
            if (done || run !== storyboardRun) return;
            if (isTimelineScrubbing) { i--; continue; }
            const edgeInset = Math.min(0.12, Math.max(0.015, duration * 0.02));
            const sampleStart = Math.min(duration / 2, edgeInset);
            const sampleEnd = Math.max(sampleStart, duration - edgeInset);
            const time = count <= 1 ? duration / 2
              : sampleStart + (sampleEnd - sampleStart) * i / Math.max(1, count - 1);
            if (Math.abs((Number(probe.currentTime) || 0) - time) > 0.015) {
              const seeked = waitForEvent('seeked', 2200);
              try { probe.currentTime = Math.max(0, Math.min(Math.max(0, probe.duration - edgeInset), time)); } catch (_) {}
              await seeked;
            }
            if (probe.readyState < 2) {
              try { await waitForEvent('loadeddata', 900); } catch (_) {}
            }
            await new Promise(resolve => {
              let settled = false;
              const finish = () => { if (settled) return; settled = true; clearTimeout(fallback); resolve(); };
              const fallback = setTimeout(finish, 180);
              if (typeof probe.requestVideoFrameCallback === 'function') {
                try { probe.requestVideoFrameCallback(finish); } catch (_) { requestAnimationFrame(() => requestAnimationFrame(finish)); }
              } else requestAnimationFrame(() => requestAnimationFrame(finish));
            });
            await waitForPreviewIdle();
            if (done || run !== storyboardRun) return;
            if (drawStoryboardFrame(context, probe, canvas)) {
              addStoryboardThumb(await canvasToStoryboardUrl(canvas), time, i, run);
            }
            await new Promise(yieldToBrowser => window.setTimeout(yieldToBrowser, 0));
          }
        } catch (error) {
          if (!done) logDebug('Video storyboard creation stopped', error?.message || error);
        } finally {
          try { probe.pause(); } catch (_) {}
          probe.removeAttribute('src');
          try { probe.load(); } catch (_) {}
        }
      };

      const populateAnimationStoryboard = async () => {
        if (!animationDecoder || !animationFrameStarts.length || done) return;
        const decoderRef = animationDecoder;
        const run = ++storyboardRun;
        storyboard.replaceChildren();
        const aspect = width && height ? width / height : 16 / 9;
        const thumbHeight = Math.max(40, timelineTrack.clientHeight || 80);
        const thumbWidth = Math.max(30, thumbHeight * aspect);
        const count = Math.max(1, Math.min(36, animationFrameStarts.length, Math.round((timelineTrack.clientWidth || 840) / thumbWidth)));
        const thumbSlots = new Map();
        for (let slot = 0; slot < count; slot++) {
          const frameIndex = Math.round(slot * (animationFrameStarts.length - 1) / Math.max(1, count - 1));
          thumbSlots.set(frameIndex, slot);
        }

        let measuredTotal = 0;
        for (let index = 0; index < animationFrameStarts.length; index++) {
          if (done || run !== storyboardRun || animationDecoder !== decoderRef) return;
          while (!done && run === storyboardRun && animationDecoder === decoderRef &&
            (isTimelineScrubbing || animationPlaying || animationSeekBusy || pendingAnimationSeek)) {
            await new Promise(resolve => window.setTimeout(resolve, 28));
          }
          if (done || run !== storyboardRun || animationDecoder !== decoderRef) return;

          let image = null;
          try {
            const result = await decodeAnimationFrame(index);
            image = result && result.image;
            if (image) {
              const durationMicros = Number(image.duration);
              if (Number.isFinite(durationMicros) && durationMicros > 0) {
                animationFrameDurations[index] = Math.max(0.01, Math.min(60, durationMicros / 1000000));
              }
              rebuildAnimationFrameStarts();
              measuredTotal += animationFrameDurations[index] || 0.1;

              if (thumbSlots.has(index)) {
                const imageAspect = image.displayWidth && image.displayHeight
                  ? image.displayWidth / image.displayHeight : aspect;
                const canvas = document.createElement('canvas');
                canvas.height = 90;
                canvas.width = Math.max(30, Math.min(360, Math.round(canvas.height * imageAspect)));
                const context = canvas.getContext('2d');
                if (context && drawStoryboardFrame(context, image, canvas)) {
                  const thumbUrl = await canvasToStoryboardUrl(canvas);
                  addStoryboardThumb(thumbUrl, animationFrameStarts[index] || 0, thumbSlots.get(index), run);
                }
              }
            }
          } catch (error) {
            logDebug('Animation storyboard frame unavailable', error?.message || error);
            measuredTotal += animationFrameDurations[index] || 0.1;
          } finally {
            try { if (image) image.close(); } catch (_) {}
          }
          if (index % 2 === 1) await new Promise(resolve => window.setTimeout(resolve, 12));
        }

        if (!done && run === storyboardRun && animationDecoder === decoderRef) {
          const exactDuration = rebuildAnimationFrameStarts() || measuredTotal;
          if (exactDuration > 0) {
            if (!userChangedTrim) { start = 0; end = exactDuration; }
            setDuration(exactDuration);
            updateSummary();
          }
        }
      };

      const pauseAnimationPreview = () => {
        animationPlaying = false;
        animationGeneration++;
        pendingAnimationSeek = null;
        if (animationTimer) clearTimeout(animationTimer);
        animationTimer = 0;
        playButton.textContent = '▶';
        playButton.setAttribute('aria-label', 'Воспроизвести анимацию');
      };

      const fallbackAnimationPreview = () => {
        if (done) return;
        animationPlaying = false;
        animationGeneration++;
        if (animationTimer) clearTimeout(animationTimer);
        animationTimer = 0;
        if (animationDecoder) {
          try { animationDecoder.close(); } catch (_) {}
          animationDecoder = null;
        }
        if (animationCanvas) animationCanvas.hidden = true;
        media.hidden = false;
        media.src = url;
        playButton.hidden = true;
        scrub.hidden = true;
        currentLabel.hidden = true;
        animationNote.hidden = false;
        animationNote.textContent = 'Анимация · предпросмотр браузера';

      };

      const findAnimationFrameAt = seconds => {
        if (!animationFrameStarts.length) return 0;
        const target = Math.max(0, Number(seconds) || 0);
        let low = 0, high = animationFrameStarts.length - 1;
        while (low < high) {
          const middle = Math.ceil((low + high) / 2);
          if (animationFrameStarts[middle] <= target) low = middle;
          else high = middle - 1;
        }
        return low;
      };

      const rebuildAnimationFrameStarts = () => {
        let elapsed = 0;
        for (let index = 0; index < animationFrameDurations.length; index++) {
          animationFrameStarts[index] = elapsed;
          const frameDuration = Number(animationFrameDurations[index]);
          elapsed += Number.isFinite(frameDuration) && frameDuration > 0 ? frameDuration : 0.1;
        }
        return elapsed;
      };

      const decodeAnimationFrame = async index => {
        const previous = animationDecodeQueue;
        let release;
        animationDecodeQueue = new Promise(resolve => { release = resolve; });
        await previous;
        try {
          if (!animationDecoder || done) return null;
          return await animationDecoder.decode({ frameIndex: index });
        } finally {
          release();
        }
      };

      const drawAnimationFrame = async (index, generation) => {
        if (!animationDecoder || done || generation !== animationGeneration) return false;
        try {
          const result = await decodeAnimationFrame(index);
          const image = result && result.image;
          if (!image) return false;
          if (done || generation !== animationGeneration || !animationCanvas) {
            try { image.close(); } catch (_) {}
            return false;
          }
          const durationMicros = Number(image.duration);
          if (Number.isFinite(durationMicros) && durationMicros > 0 && index < animationFrameDurations.length) {
            animationFrameDurations[index] = Math.max(0.01, Math.min(60, durationMicros / 1000000));
            rebuildAnimationFrameStarts();
          }
          const frameWidth = Number(image.displayWidth || image.codedWidth) || width;
          const frameHeight = Number(image.displayHeight || image.codedHeight) || height;
          const context = animationCanvas.getContext('2d');
          if (!context || frameWidth <= 0 || frameHeight <= 0) {
            try { image.close(); } catch (_) {}
            return false;
          }
          if (animationCanvas.width !== frameWidth) animationCanvas.width = frameWidth;
          if (animationCanvas.height !== frameHeight) animationCanvas.height = frameHeight;
          width = frameWidth;
          height = frameHeight;
          context.clearRect(0, 0, frameWidth, frameHeight);
          context.drawImage(image, 0, 0, frameWidth, frameHeight);
          try { image.close(); } catch (_) {}
          animationFrameIndex = index;
          animationPaintedFrameIndex = index;
          playButton.disabled = false;
          const frameTime = animationFrameStarts[index] || 0;
          currentLabel.textContent = formatEditorTime(frameTime);
          scrub.value = String(frameTime);
          updateTimelineControls();
          updateFrame();
          return true;
        } catch (error) {
          logDebug('Frame preview decode failed; using native animation', error?.message || error);
          fallbackAnimationPreview();
          return false;
        }
      };

      const nextAnimationPlaybackFrame = (firstFrame, lastFrame) => {
        if (lastFrame <= firstFrame) return loop ? firstFrame : -1;
        if (animationDirection >= 0) {
          if (animationFrameIndex >= lastFrame) {
            if (!loop) return -1;
            animationDirection = -1;
            return lastFrame - 1;
          }
          return animationFrameIndex + 1;
        }
        if (animationFrameIndex <= firstFrame) {
          animationDirection = 1;
          return firstFrame + 1;
        }
        return animationFrameIndex - 1;
      };
      const getAnimationPingPongFrameDelay = (currentIndex, nextIndex, previousDirection, nextDirection, firstFrame, lastFrame) => {
        const firstTime = Number(animationFrameStarts[firstFrame]) || 0;
        const lastTime = Number(animationFrameStarts[lastFrame]) || firstTime;
        const span = lastTime - firstTime;
        if (!loop || span <= 0.001) {
          const frameDuration = Math.max(0.01, Number(animationFrameDurations[currentIndex]) || 0.1);
          return Math.max(10, Math.min(10000, frameDuration / speed * 1000));
        }
        const getPositionProgress = index => Math.max(0, Math.min(1,
          ((Number(animationFrameStarts[index]) || firstTime) - firstTime) / span));
        const getLegProgress = (index, direction) => {
          const position = getPositionProgress(index);
          return direction >= 0
            ? getPingPongInverseEaseProgress(position)
            : getPingPongInverseEaseProgress(1 - position);
        };
        const nextProgress = getLegProgress(nextIndex, nextDirection);
        const elapsedProgress = previousDirection === nextDirection
          ? nextProgress - getLegProgress(currentIndex, previousDirection)
          : nextProgress;
        return Math.max(10, Math.min(10000, elapsedProgress * span / speed * 1000));
      };
      const runAnimationPreview = async generation => {
        if (!animationPlaying || !animationDecoder || done || generation !== animationGeneration) return;
        const drawn = animationPaintedFrameIndex === animationFrameIndex
          ? true : await drawAnimationFrame(animationFrameIndex, generation);
        if (!drawn || !animationPlaying || generation !== animationGeneration) return;
        const firstFrame = findAnimationFrameAt(start);
        const lastFrame = Math.max(firstFrame, findAnimationFrameAt(Math.max(start, end - 0.001)));
        if (loop) {
          const previousDirection = animationDirection;
          const nextIndex = nextAnimationPlaybackFrame(firstFrame, lastFrame);
          if (nextIndex < firstFrame || nextIndex > lastFrame) { pauseAnimationPreview(); return; }
          const nextDirection = animationDirection;
          const delay = getAnimationPingPongFrameDelay(
            animationFrameIndex, nextIndex, previousDirection, nextDirection, firstFrame, lastFrame
          );
          animationTimer = window.setTimeout(() => {
            animationTimer = 0;
            if (!animationPlaying || !animationDecoder || done || generation !== animationGeneration) return;
            animationFrameIndex = nextIndex;
            runAnimationPreview(generation).catch(() => pauseAnimationPreview());
          }, delay);
          return;
        }
        const frameDuration = Math.max(0.01, Number(animationFrameDurations[animationFrameIndex]) || 0.1);
        animationTimer = window.setTimeout(() => {
          animationTimer = 0;
          if (!animationPlaying || !animationDecoder || done || generation !== animationGeneration) return;
          const nextIndex = nextAnimationPlaybackFrame(firstFrame, lastFrame);
          if (nextIndex < firstFrame || nextIndex > lastFrame) { pauseAnimationPreview(); return; }
          animationFrameIndex = nextIndex;
          runAnimationPreview(generation).catch(() => pauseAnimationPreview());
        }, Math.max(10, Math.min(10000, frameDuration / speed * 1000)));
      };

      const playAnimationPreview = () => {
        if (!animationDecoder || done) return;
        const firstFrame = findAnimationFrameAt(start);
        const lastFrame = Math.max(firstFrame, findAnimationFrameAt(Math.max(start, end - 0.001)));
        if (duration > 0 && (animationFrameStarts[animationFrameIndex] < start ||
            animationFrameStarts[animationFrameIndex] >= end ||
            animationFrameIndex < firstFrame || animationFrameIndex > lastFrame)) {
          animationFrameIndex = firstFrame;
        } else if (animationFrameIndex >= lastFrame) {
          animationFrameIndex = firstFrame;
        }
        animationDirection = 1;
        animationPlaying = true;
        playButton.textContent = 'Ⅱ';
        playButton.setAttribute('aria-label', 'Приостановить анимацию');
        const generation = ++animationGeneration;
        runAnimationPreview(generation).catch(() => pauseAnimationPreview());
      };

      const seekAnimationPreview = seconds => {
        if (!animationDecoder || done) return;
        const wasPlaying = animationPlaying;
        if (animationTimer) clearTimeout(animationTimer);
        animationTimer = 0;
        const index = findAnimationFrameAt(Math.max(0, Math.min(duration, Number(seconds) || 0)));
        pendingAnimationSeek = { index, wasPlaying };
        animationGeneration++;
        if (animationSeekBusy) return;
        animationSeekBusy = true;
        const drain = async () => {
          try {
            while (!done && animationDecoder && pendingAnimationSeek) {
              const request = pendingAnimationSeek;
              pendingAnimationSeek = null;
              const generation = ++animationGeneration;
              animationFrameIndex = request.index;
              const drawn = await drawAnimationFrame(request.index, generation);
              if (!drawn || generation !== animationGeneration) continue;
              if (!request.wasPlaying || pendingAnimationSeek) continue;
              animationPlaying = true;
              playButton.textContent = 'Ⅱ';
              playButton.setAttribute('aria-label', 'Приостановить анимацию');
              runAnimationPreview(generation).catch(() => pauseAnimationPreview());
            }
          } catch (error) {
            logDebug('Animation seek failed', error?.message || error);
            fallbackAnimationPreview();
          } finally {
            animationSeekBusy = false;
            if (pendingAnimationSeek && !done && animationDecoder) seekAnimationPreview(animationFrameStarts[pendingAnimationSeek.index] || 0);
          }
        };
        drain();
      };

      const setupAnimationPreview = async durationPromise => {
        if (info.kind !== 'animation') return;
        if (typeof ImageDecoder !== 'function' || typeof file.stream !== 'function') {
          fallbackAnimationPreview();
          return;
        }
        let decoder = null;
        try {
          const mime = info.mime || (info.animationFormat === 'webp' ? 'image/webp'
            : info.animationFormat === 'apng' ? 'image/png' : 'image/gif');
          decoder = new ImageDecoder({ data: file.stream(), type: mime });
          await decoder.tracks.ready;
          if (done) { try { decoder.close(); } catch (_) {} return; }
          const track = decoder.tracks.selectedTrack;
          const frameCount = Math.floor(Number(track && track.frameCount) || 0);
          if (!frameCount || frameCount > 1500) {
            try { decoder.close(); } catch (_) {}
            fallbackAnimationPreview();
            return;
          }

          const estimatedDuration = Math.max(0, Number(await durationPromise) || 0);
          const initialDuration = estimatedDuration > 0 ? estimatedDuration : frameCount * 0.1;
          const averageFrameDuration = Math.max(0.01, Math.min(60, initialDuration / frameCount));

          // Make the decoder available immediately. The first visible frame is decoded
          // before the low-priority timing/storyboard pass starts.
          animationDecoder = decoder;
          animationFrameDurations = new Array(frameCount).fill(averageFrameDuration);
          rebuildAnimationFrameStarts();
          if (!userChangedTrim) { start = 0; end = initialDuration; }
          setDuration(initialDuration);
          animationCanvas.hidden = false;
          media.hidden = true;
          animationNote.hidden = true;
          playButton.hidden = false;
          playButton.disabled = true;
          scrub.hidden = true;
          currentLabel.hidden = true;
          scrub.disabled = false;
          updateFrame();
          seekAnimationPreview(start);
          window.setTimeout(() => {
            if (!done && animationDecoder === decoder) {
              populateAnimationStoryboard().catch(error => logDebug('Animation storyboard failed', error?.message || error));
            }
          }, 900);
        } catch (error) {
          try { if (decoder) decoder.close(); } catch (_) {}
          if (animationDecoder === decoder) animationDecoder = null;
          logDebug('Animated preview unavailable; using native animation', error?.message || error);
          fallbackAnimationPreview();
        }
      };

      const syncVideoPosition = seconds => {
        const value = Math.max(0, Math.min(duration || 0, Number(seconds) || 0));
        paintPlayhead(value);
        currentLabel.textContent = formatEditorTime(value);
        scrub.value = String(value);
        updateTimelineControls(value);
      };
      const stopVideoPreview = (atEnd = false) => {
        cancelVideoReverse();
        try { media.pause(); } catch (_) {}
        if (playheadRaf) window.cancelAnimationFrame(playheadRaf);
        playheadRaf = 0;
        const safeEnd = Math.max(start, end - getVideoEndGuard());
        const value = atEnd ? end : Math.max(0, Math.min(duration || 0, Number(media.currentTime) || 0));
        if (atEnd && duration > 0) { try { media.currentTime = safeEnd; } catch (_) {} }
        playButton.textContent = '▶';
        playButton.setAttribute('aria-label', 'Воспроизвести');
        syncVideoPosition(value);
      };
      const animateVideoPlayhead = () => {
        playheadRaf = 0;
        if (done || info.kind !== 'video' || (media.paused && !videoReverseActive) || duration <= 0) return;
        const time = Number(media.currentTime) || 0;
        if (!videoReverseActive && time >= end - getVideoEndGuard()) {
          if (loop) startVideoReverse();
          else stopVideoPreview(true);
          return;
        }
        if (loop && !videoReverseActive) updateVideoPingPongPlaybackRate(time);
        syncVideoPosition(time);
        playheadRaf = window.requestAnimationFrame(animateVideoPlayhead);
      };
      const onPlayState = () => {
        const playing = !media.paused || videoReverseActive;
        playButton.textContent = playing ? 'Ⅱ' : '▶';
        playButton.setAttribute('aria-label', playing ? 'Пауза' : 'Воспроизвести');
        if (playing && !playheadRaf && info.kind === 'video') {
          playheadRaf = window.requestAnimationFrame(animateVideoPlayhead);
        } else if (!playing && playheadRaf) {
          window.cancelAnimationFrame(playheadRaf);
          playheadRaf = 0;
        }
      };
      const onVideoMeta = () => {
        if (Number.isFinite(media.duration) && media.duration > 0) {
          setDuration(media.duration);
          if (!storyboard.dataset.started) {
            storyboard.dataset.started = 'true';
            populateVideoStoryboard().catch(error => logDebug('Video storyboard failed', error?.message || error));
          }
        }
        width = media.videoWidth || width; height = media.videoHeight || height; updateFrame();
      };
      const getPingPongEasePower = () => pingPongMode === 'soft' ? 1.3 :
        pingPongMode === 'balanced' ? 1.65 : pingPongMode === 'smooth' ? 2 : 1;
      const getPingPongEaseProgress = progress => {
        const t = Math.max(0, Math.min(1, Number(progress) || 0));
        const power = getPingPongEasePower();
        if (power <= 1.001) return t;
        const a = Math.pow(t, power), b = Math.pow(1 - t, power);
        return a / Math.max(1e-9, a + b);
      };
      const getPingPongInverseEaseProgress = progress => {
        const t = Math.max(0, Math.min(1, Number(progress) || 0));
        const inversePower = 1 / getPingPongEasePower();
        if (inversePower >= 0.999) return t;
        const a = Math.pow(t, inversePower), b = Math.pow(1 - t, inversePower);
        return a / Math.max(1e-9, a + b);
      };
      const getPingPongVelocityFactor = progress => {
        const power = getPingPongEasePower();
        if (power <= 1.001) return 1;
        const t = getPingPongInverseEaseProgress(progress);
        if (t <= 0 || t >= 1) return 0;
        const a = Math.pow(t, power), b = Math.pow(1 - t, power);
        return power * Math.pow(t * (1 - t), power - 1) / Math.max(1e-9, (a + b) ** 2);
      };
      const getVideoPingPongPlaybackRate = seconds => {
        if (!loop || end <= start) return speed;
        const progress = Math.max(0, Math.min(1, ((Number(seconds) || 0) - start) / (end - start)));
        return Math.max(0.1, Math.min(12, speed * getPingPongVelocityFactor(progress)));
      };
      const updateVideoPingPongPlaybackRate = seconds => {
        if (media.paused || videoReverseActive) return;
        const nextRate = getVideoPingPongPlaybackRate(seconds);
        try {
          if (Math.abs(media.playbackRate - nextRate) > 0.02) media.playbackRate = nextRate;
        } catch (_) {}
      };
      const getVideoEndGuard = () => {
        // Guard against a whole source frame being presented between two UI ticks.
        // This is deliberately independent from the selected reverse-preview cadence.
        const sourceFrameStep = speed / 24;
        return Math.max(0.05, Math.min(0.24, sourceFrameStep * 1.25));
      };
      const waitForVideoSeek = (target, generation) => new Promise(resolve => {
        let settled = false;
        const finish = fromSeeked => {
          if (settled) return;
          settled = true;
          media.removeEventListener('seeked', onSeeked);
          clearTimeout(timeout);
          const stillCurrent = !done && generation === videoReverseGeneration;
          const landed = !media.seeking && Math.abs((Number(media.currentTime) || 0) - target) <= 0.035;
          const success = stillCurrent && (fromSeeked || landed);
          if (success) syncVideoPosition(media.currentTime);
          resolve(success);
        };
        const onSeeked = () => finish(true);
        const timeout = window.setTimeout(() => finish(false), 700);
        media.addEventListener('seeked', onSeeked, { once: true });
        try {
          if (Math.abs((Number(media.currentTime) || 0) - target) < 0.004 && !media.seeking) finish(false);
          else media.currentTime = target;
        } catch (_) { finish(false); }
      });
      const cancelVideoReverse = () => {
        if (videoReverseTimer) clearTimeout(videoReverseTimer);
        videoReverseTimer = 0;
        videoReverseActive = false;
        videoPingPongDirection = 1;
        videoReverseGeneration++;
      };
      const startVideoReverse = (resumeFromCurrent = false) => {
        if (!loop || end <= start + .05 || done || videoReverseActive) return;
        videoReverseActive = true;
        videoPingPongDirection = -1;
        const generation = ++videoReverseGeneration;
        media.pause();
        playButton.textContent = 'Ⅱ';
        playButton.setAttribute('aria-label', 'Пауза');
        const fps = 30;
        const frameInterval = 1000 / fps;
        const safeEnd = resumeFromCurrent
          ? Math.max(start, Math.min(end - getVideoEndGuard(), Number(media.currentTime) || start))
          : Math.max(start, end - getVideoEndGuard());
        const reverseSpan = Math.max(0, safeEnd - start);
        const totalSteps = Math.max(1, Math.ceil(reverseSpan / Math.max(0.25, speed) * fps));
        let stepIndex = 0;
        const reverseStep = async () => {
          videoReverseTimer = 0;
          if (done || !loop || !videoReverseActive || generation !== videoReverseGeneration) return;
          stepIndex++;
          const easedProgress = getPingPongEaseProgress(Math.min(1, stepIndex / totalSteps));
          const reachedStart = stepIndex >= totalSteps;
          const target = reachedStart ? start : Math.max(start, safeEnd - reverseSpan * easedProgress);
          const positioned = await waitForVideoSeek(target, generation);
          if (!positioned || done || !videoReverseActive || generation !== videoReverseGeneration || !loop) {
            if (!done && videoReverseActive && generation === videoReverseGeneration) stopVideoPreview(false);
            return;
          }
          if (reachedStart) {
            videoReverseActive = false;
            videoPingPongDirection = 1;
            videoReverseTimer = 0;
            media.playbackRate = getVideoPingPongPlaybackRate(start);
            try { await media.play(); }
            catch (_) { stopVideoPreview(false); }
            return;
          }
          videoReverseTimer = window.setTimeout(reverseStep, frameInterval);
          playButton.textContent = 'Ⅱ';
          playButton.setAttribute('aria-label', 'Пауза');
        };
        const positionAtSafeEnd = async () => {
          const positioned = await waitForVideoSeek(safeEnd, generation);
          if (!positioned || done || !videoReverseActive || generation !== videoReverseGeneration) {
            if (!done && videoReverseActive && generation === videoReverseGeneration) stopVideoPreview(false);
            return;
          }
          videoReverseTimer = window.setTimeout(reverseStep, frameInterval);
        };
        positionAtSafeEnd().catch(error => {
          logDebug('Ping-pong reverse preview failed', error?.message || error);
          stopVideoPreview(false);
        });
      };
      const onVideoTime = () => {
        if (!Number.isFinite(media.currentTime)) return;
        if (!media.paused && !videoReverseActive && duration > 0 &&
            media.currentTime >= end - getVideoEndGuard()) {
          if (loop) startVideoReverse();
          else stopVideoPreview(true);
          return;
        }
        if (loop && !videoReverseActive) updateVideoPingPongPlaybackRate(media.currentTime);
        syncVideoPosition(media.currentTime);
      };
      const onVideoEnd = () => {
        if (loop && !videoReverseActive) startVideoReverse();
        else if (!videoReverseActive) stopVideoPreview(true);
      };
      const onKey = e => {
        if (e.code === 'Space' || e.key === ' ') {
          e.preventDefault();
          e.stopPropagation();
          if (typeof e.stopImmediatePropagation === 'function') e.stopImmediatePropagation();
          if (!e.repeat && !playButton.disabled) playButton.click();
          return;
        }
        if (e.key === 'Escape') { e.preventDefault(); e.stopPropagation(); finish(null); }
      };
      const preset = value => {
        if (value === 'free') crop = { x: 0, y: 0, w: 100, h: 100 };
        else if (width && height) {
          const a = value.split(':').map(Number), target = a[0] / a[1], sourceAspect = width / height;
          if (target >= sourceAspect) { const h = sourceAspect / target * 100; crop = { x: 0, y: (100 - h) / 2, w: 100, h }; }
          else { const w = target / sourceAspect * 100; crop = { x: (100 - w) / 2, y: 0, w, h: 100 }; }
        }
        updateFrame();
        overlay.querySelectorAll('[data-preset]').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.preset === value)));
      };
      const performPreviewSeek = (value, fast = false) => {
        if (info.kind === 'video') {
          if (fast && typeof media.fastSeek === 'function') media.fastSeek(value);
          else media.currentTime = value;
        } else if (animationDecoder) {
          seekAnimationPreview(value);
        }
      };
      const flushPendingPreviewSeek = (fast = false) => {
        if (seekTimer) clearTimeout(seekTimer);
        seekTimer = 0;
        if (pendingSeekTime === null) return;
        const value = pendingSeekTime;
        pendingSeekTime = null;
        try { performPreviewSeek(value, fast); } catch (_) {}
      };
      const seekPreviewTime = (seconds, defer = false) => {
        const value = Math.max(0, Math.min(duration || 0, Number(seconds) || 0));
        cancelVideoReverse();
        currentLabel.textContent = formatEditorTime(value);
        scrub.value = String(value);
        updateTimelineControls(value);
        paintPlayhead(value);
        if (defer) {
          pendingSeekTime = value;
          if (!seekTimer) seekTimer = window.setTimeout(() => flushPendingPreviewSeek(true), 18);
          return;
        }
        if (seekTimer) clearTimeout(seekTimer);
        seekTimer = 0;
        pendingSeekTime = null;
        try { performPreviewSeek(value, false); } catch (_) {}
      };
      const trimInput = (which, value) => {
        if (!duration) return;
        userChangedTrim = true;
        const gap = Math.min(.05, duration / 10);
        if (which === 'start') start = Math.max(0, Math.min(Number(value) || 0, end - gap));
        else end = Math.max(start + gap, Math.min(Number(value) || 0, duration));
        animationDirection = 1;
        updateSummary();
        seekPreviewTime(which === 'start' ? start : Math.max(start, end - (info.kind === 'video' ? getVideoEndGuard() : 0.001)), true);
      };
      const setTrimValueFromPointer = (which, event) => {
        const rect = timelineTrack.getBoundingClientRect();
        if (!rect.width || !duration) return;
        trimInput(which, Math.max(0, Math.min(duration, (event.clientX - rect.left) / rect.width * duration)));
      };
      const startTrimDrag = (which, event) => {
        if (event.button !== 0 && event.pointerType !== 'touch') return;
        if (!duration) return;
        isTimelineScrubbing = true;
        trimDrag = { which, pointerId: event.pointerId };
        try { event.currentTarget.setPointerCapture(event.pointerId); } catch (_) {}
        event.preventDefault();
      };
      startInput.addEventListener('pointerdown', event => startTrimDrag('start', event));
      endInput.addEventListener('pointerdown', event => startTrimDrag('end', event));
      timelineTrack.addEventListener('pointermove', event => {
        if (trimDrag && event.pointerId === trimDrag.pointerId) {
          setTrimValueFromPointer(trimDrag.which, event);
          return;
        }
        if (playheadDrag && event.pointerId === playheadDrag.pointerId) {
          const rect = timelineTrack.getBoundingClientRect();
          if (rect.width && duration) {
            seekPreviewTime(Math.max(0, Math.min(duration, (event.clientX - rect.left) / rect.width * duration)), true);
          }
        }
      });
      const finishTimelineDrag = event => {
        if (trimDrag && (!event || event.pointerId === trimDrag.pointerId)) trimDrag = null;
        if (playheadDrag && (!event || event.pointerId === playheadDrag.pointerId)) playheadDrag = null;
        if (!trimDrag && !playheadDrag) {
          isTimelineScrubbing = false;
          flushPendingPreviewSeek(false);
        }
      };
      timelineTrack.addEventListener('pointerup', finishTimelineDrag);
      timelineTrack.addEventListener('pointercancel', finishTimelineDrag);
      timelineTrack.addEventListener('lostpointercapture', finishTimelineDrag);
      for (const [handle, which] of [[startInput, 'start'], [endInput, 'end']]) {
        handle.addEventListener('keydown', event => {
          if (!duration) return;
          const step = event.shiftKey ? 1 : event.altKey ? .01 : .1;
          let next = which === 'start' ? start : end;
          if (event.key === 'ArrowLeft' || event.key === 'ArrowDown') next -= step;
          else if (event.key === 'ArrowRight' || event.key === 'ArrowUp') next += step;
          else if (event.key === 'PageDown') next -= 1;
          else if (event.key === 'PageUp') next += 1;
          else if (event.key === 'Home') next = 0;
          else if (event.key === 'End') next = duration;
          else return;
          event.preventDefault();
          trimInput(which, next);
        });
      }
      timelineTrack.addEventListener('pointerdown', event => {
        if (event.target.closest('[data-trim-start],[data-trim-end]')) return;
        if (!duration || (event.button !== 0 && event.pointerType !== 'touch')) return;
        const rect = timelineTrack.getBoundingClientRect();
        if (!rect.width) return;
        isTimelineScrubbing = true;
        playheadDrag = { pointerId: event.pointerId };
        try { timelineTrack.setPointerCapture(event.pointerId); } catch (_) {}
        seekPreviewTime(Math.max(0, Math.min(duration, (event.clientX - rect.left) / rect.width * duration)));
        event.preventDefault();
      });
      frame.addEventListener('pointerdown', e => {
        if (e.button !== 0 && e.pointerType !== 'touch') return;
        const handle = e.target.closest('[data-handle]');
        drag = { mode: handle ? handle.dataset.handle : 'move', sx: e.clientX, sy: e.clientY, crop: { ...crop }, rect: contentRect() };
        dragId = e.pointerId; try { frame.setPointerCapture(e.pointerId); } catch (_) {}
        e.preventDefault();
      });
      frame.addEventListener('pointermove', e => {
        if (!drag || e.pointerId !== dragId) return;
        const dx = (e.clientX - drag.sx) / Math.max(1, drag.rect.width) * 100;
        const dy = (e.clientY - drag.sy) / Math.max(1, drag.rect.height) * 100;
        const c = drag.crop;
        if (drag.mode === 'move') { crop.x = Math.max(0, Math.min(100 - c.w, c.x + dx)); crop.y = Math.max(0, Math.min(100 - c.h, c.y + dy)); }
        else {
          const min = 5; let l = c.x, t = c.y, r = c.x + c.w, b = c.y + c.h;
          if (drag.mode.includes('w')) l = Math.max(0, Math.min(r - min, c.x + dx));
          if (drag.mode.includes('e')) r = Math.min(100, Math.max(l + min, c.x + c.w + dx));
          if (drag.mode.includes('n')) t = Math.max(0, Math.min(b - min, c.y + dy));
          if (drag.mode.includes('s')) b = Math.min(100, Math.max(t + min, c.y + c.h + dy));
          crop = { x: l, y: t, w: r - l, h: b - t };
        }
        updateFrame();
      });
      const endDrag = e => { if (!drag || (e && e.pointerId !== dragId)) return; drag = null; dragId = null; };
      frame.addEventListener('pointerup', endDrag); frame.addEventListener('pointercancel', endDrag); frame.addEventListener('lostpointercapture', endDrag);
      scrub.addEventListener('input', () => seekPreviewTime(Number(scrub.value) || 0));
      speedInput.addEventListener('input', () => {
        speed = Math.max(.25, Math.min(4, Number(speedInput.value) || 1));
        if (info.kind === 'video') {
          if (videoReverseActive) {
            cancelVideoReverse();
            startVideoReverse(true);
          } else {
            try { media.playbackRate = getVideoPingPongPlaybackRate(media.currentTime); } catch (_) {}
          }
        } else if (animationDecoder && animationPlaying) {
          seekAnimationPreview(animationFrameStarts[animationFrameIndex] || start);
        }
        updateSummary();
      });
      loopInput.addEventListener('change', () => {
        const wasVideoReversing = videoReverseActive;
        pingPongMode = ['linear', 'soft', 'balanced', 'smooth'].includes(loopInput.value) ? loopInput.value : 'off';
        loop = pingPongMode !== 'off';
        animationDirection = 1;
        if (!loop && wasVideoReversing) {
          cancelVideoReverse();
          media.playbackRate = speed;
          if (media.paused) media.play().catch(() => {});
        } else if (loop && wasVideoReversing) {
          cancelVideoReverse();
          startVideoReverse(true);
        } else if (info.kind === 'video') {
          try { media.playbackRate = getVideoPingPongPlaybackRate(media.currentTime); } catch (_) {}
        } else if (info.kind === 'animation' && animationPlaying) {
          seekAnimationPreview(animationFrameStarts[animationFrameIndex] || start);
        }
        updateSummary();
      });
      cropToggle.addEventListener('click', () => {
        cropMode = !cropMode;
        dialog.classList.toggle('twgif-cropping', cropMode);
        cropControls.hidden = !cropMode;
        cropToggle.textContent = cropMode ? 'Готово' : 'Включить';
        cropToggle.setAttribute('aria-pressed', String(cropMode));
        updateFrame();
      });
      overlay.querySelectorAll('[data-preset]').forEach(b => b.addEventListener('click', () => preset(b.dataset.preset)));
      $('[data-reset]').addEventListener('click', () => preset('free'));
      playButton.addEventListener('click', () => {
        if (info.kind === 'animation') {
          if (!animationDecoder) return;
          if (animationPlaying) pauseAnimationPreview();
          else playAnimationPreview();
          return;
        }
        if (videoReverseActive) {
          stopVideoPreview(false);
          return;
        }
        if (media.paused) {
          const restartAtStart = duration && (media.currentTime < start || media.currentTime >= end - 0.025 || media.ended);
          const playFromSelection = async () => {
            if (restartAtStart) {
              const target = start;
              if (Math.abs((Number(media.currentTime) || 0) - target) > 0.015 || media.ended) {
                await new Promise(resolve => {
                  let finished = false;
                  const doneSeek = () => {
                    if (finished) return;
                    finished = true;
                    media.removeEventListener('seeked', doneSeek);
                    clearTimeout(timeout);
                    resolve();
                  };
                  const timeout = setTimeout(doneSeek, 350);
                  media.addEventListener('seeked', doneSeek, { once: true });
                  try { media.currentTime = target; } catch (_) { doneSeek(); }
                });
              }
            }
            if (done) return;
            media.playbackRate = getVideoPingPongPlaybackRate(media.currentTime);
            try { await media.play(); }
            catch (error) { logDebug('Could not start preview playback', error?.message || error); }
          };
          playFromSelection();
        } else stopVideoPreview(false);
      });
      overlay.querySelectorAll('[data-editor-close],[data-cancel]').forEach(b => b.addEventListener('click', () => finish(null)));
      overlay.addEventListener('pointerdown', e => { if (e.target === overlay) finish(null); });
      $('[data-apply]').addEventListener('click', () => {
        if (!isProcessingRunCurrent(runId)) { finish(null); return; }
        finish(normalizeMediaEditOptions({ kind: info.kind, duration, start, end, speed, loop, pingPongMode, hd: hdInput.checked, crop, sourceWidth: width, sourceHeight: height }));
      });

      if (info.kind === 'video') {
        media.addEventListener('loadedmetadata', onVideoMeta); media.addEventListener('timeupdate', onVideoTime); media.addEventListener('ended', onVideoEnd);
        media.addEventListener('play', onPlayState); media.addEventListener('pause', onPlayState);
        media.src = url; media.load(); if (media.readyState >= 1) onVideoMeta();
      } else {
        playButton.disabled = true;
        media.addEventListener('load', () => { width = media.naturalWidth || width; height = media.naturalHeight || height; updateFrame(); }, { once: true });
        media.src = url; if (media.complete && media.naturalWidth) { width = media.naturalWidth; height = media.naturalHeight; updateFrame(); }
        const durationPromise = info.animationFormat === 'webp' ? getAnimatedWebPDurationSeconds(file)
          : info.animationFormat === 'apng' ? getApngDurationSeconds(file) : getGifDurationSeconds(file);
        durationPromise.then(setDuration).catch(() => {});
        setupAnimationPreview(durationPromise).catch(error => {
          logDebug('Animation preview setup failed', error?.message || error);
          fallbackAnimationPreview();
        });
      }
      if (typeof ResizeObserver === 'function') { resizeObserver = new ResizeObserver(updateFrame); resizeObserver.observe(stage); }
      else { resizeHandler = updateFrame; window.addEventListener('resize', resizeHandler, { passive: true }); }
      document.addEventListener('keydown', onKey, true); updateSummary();
      window.requestAnimationFrame(() => { updateFrame(); $('[data-cancel]').focus(); });
    });
  }

  function openMediaEditorImportDialog() {
    if (activeProcessingRunId) {
      setStatus('Сначала дождись завершения текущей обработки или отмени её значком стоп.', 'info');
      return;
    }
    clearStaleMediaEditorOverlays();
    ensureMediaEditorStyles();
    const overlay = document.createElement('div');
    overlay.id = 'twgif-media-import-overlay';
    overlay.innerHTML = [
      '<section class="twgif-media-import" role="dialog" aria-modal="true" aria-labelledby="twgif-media-import-title">',
      '<header class="twgif-editor-header"><div><span class="twgif-editor-eyebrow">Редактор · загрузка источника</span><h2 id="twgif-media-import-title" class="twgif-editor-title">Что будем редактировать?</h2>',
      '<p class="twgif-editor-subtitle">Перетащи видео или анимацию сюда, выбери файл на компьютере или вставь прямую ссылку на медиафайл.</p></div>',
      '<button class="twgif-editor-close" type="button" data-import-close aria-label="Закрыть">×</button></header>',
      '<div class="twgif-media-import-body"><div class="twgif-media-import-drop" data-import-drop role="button" tabindex="0">',
      '<div class="twgif-media-import-icon"><svg viewBox="0 0 48 48" width="42" height="42" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="7" y="7" width="34" height="34" rx="10"></rect><path d="M24 31V17M18 23l6-6 6 6"></path></svg></div>',
      '<strong>Перетащи файл сюда</strong><span>Видео · GIF · анимированный WebP · APNG</span>',
      '<button type="button" class="twgif-editor-btn twgif-editor-btn-primary" data-import-browse>Выбрать на компьютере</button>',
      '<span class="twgif-media-import-limit">Файл обрабатывается локально до загрузки результата</span></div>',
      '<div class="twgif-media-import-divider"><span>или открой по прямой ссылке</span></div>',
      '<form class="twgif-media-import-url" data-import-url-form><label for="twgif-media-import-url">Ссылка на видео или анимацию</label>',
      '<div class="twgif-media-import-url-row"><input id="twgif-media-import-url" data-import-url type="url" inputmode="url" placeholder="https://example.com/clip.mp4" autocomplete="url" required>',
      '<button class="twgif-editor-btn twgif-editor-btn-primary" type="submit" data-import-url-submit>Открыть ссылку →</button></div>',
      '<div class="twgif-media-import-status" data-import-status aria-live="polite">Поддерживаются прямые ссылки на файлы, не страницы сайтов.</div></form></div></section>'
    ].join('');
    document.body.appendChild(overlay);

    const fileInput = document.createElement('input');
    fileInput.type = 'file';
    fileInput.accept = 'video/*,image/gif,image/webp,image/png,.apng';
    fileInput.hidden = true;
    overlay.appendChild(fileInput);

    const dropZone = overlay.querySelector('[data-import-drop]');
    const browseButton = overlay.querySelector('[data-import-browse]');
    const urlForm = overlay.querySelector('[data-import-url-form]');
    const urlInput = overlay.querySelector('[data-import-url]');
    const status = overlay.querySelector('[data-import-status]');
    const submitButton = overlay.querySelector('[data-import-url-submit]');
    let closed = false;
    let busy = false;
    let escapeHandler = null;
    const close = () => {
      if (closed) return;
      closed = true;
      if (escapeHandler) document.removeEventListener('keydown', escapeHandler, true);
      overlay.remove();
    };
    const setStatus = (message, isError = false) => {
      status.textContent = message;
      status.classList.toggle('is-error', Boolean(isError));
    };
    const looksLikeFile = event => {
      const transfer = event.dataTransfer;
      return Boolean(transfer && (
        Array.from(transfer.types || []).some(type => String(type).toLowerCase() === 'files') ||
        Array.from(transfer.items || []).some(item => item && item.kind === 'file')
      ));
    };
    const handoffFile = async file => {
      if (busy || closed) return;
      if (!file || !file.size) {
        setStatus('Файл пустой или не читается.', true);
        return;
      }
      if (file.size > MAX_FILE_BYTES) {
        setStatus('Файл больше ' + formatBytes(MAX_FILE_BYTES) + '. Выбери файл меньшего размера.', true);
        return;
      }
      busy = true;
      browseButton.disabled = true;
      submitButton.disabled = true;
      setStatus('Проверяю формат и подготавливаю предпросмотр…');
      try {
        const info = await getEditableMediaInfo(file);
        if (closed) return;
        if (!info) throw new Error('Нужен видеофайл или анимация: GIF, анимированный WebP либо APNG.');
        close();
        const editorRunId = processingRunId;
        const edits = await openMediaEditor(file, editorRunId, info);
        if (edits === null) return;
        await processFiles([file], edits);
      } catch (error) {
        if (closed) {
          // If editor setup throws before its controls are wired, never leave an inert full-screen overlay behind.
          document.getElementById('twgif-media-editor-overlay')?.remove();
          logDebug('Editor import failed after dialog handoff', error?.message || error);
          setStatus((error && error.message) || 'Не удалось открыть медиа. Попробуй другой файл.', true);
          return;
        }
        setStatus((error && error.message) || 'Не удалось открыть медиа.', true);
      } finally {
        if (!closed) {
          busy = false;
          browseButton.disabled = false;
          submitButton.disabled = false;
        }
      }
    };
    const loadUrl = async raw => {
      if (busy || closed) return;
      let parsed;
      try {
        parsed = new URL(String(raw || '').trim());
      } catch (_) {
        setStatus('Вставь корректную ссылку, начинающуюся с https:// или http://.', true);
        return;
      }
      if (!/^https?:$/.test(parsed.protocol)) {
        setStatus('Разрешены только HTTP- и HTTPS-ссылки.', true);
        return;
      }
      busy = true;
      submitButton.disabled = true;
      browseButton.disabled = true;
      setStatus('Скачиваю медиа по ссылке…');
      try {
        const blob = await requestBlob(parsed.href, 180000, false);
        if (closed) return;
        if (!blob || !blob.size) throw new Error('Ссылка вернула пустой файл.');
        if (blob.size > MAX_FILE_BYTES) throw new Error('Файл больше ' + formatBytes(MAX_FILE_BYTES) + '.');
        const file = createLinkedMediaFile(parsed.href, blob);
        busy = false;
        await handoffFile(file);
      } catch (error) {
        if (!closed) setStatus((error && error.message) || 'Не удалось скачать медиа по ссылке.', true);
      } finally {
        if (!closed) {
          busy = false;
          submitButton.disabled = false;
          browseButton.disabled = false;
        }
      }
    };

    browseButton.addEventListener('click', () => fileInput.click());
    dropZone.addEventListener('click', event => {
      if (event.target.closest('button')) return;
      fileInput.click();
    });
    dropZone.addEventListener('keydown', event => {
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        fileInput.click();
      }
    });
    fileInput.addEventListener('change', () => {
      const file = fileInput.files && fileInput.files[0];
      if (file) handoffFile(file);
      fileInput.value = '';
    });
    dropZone.addEventListener('dragenter', event => {
      if (!looksLikeFile(event)) return;
      event.preventDefault();
      dropZone.classList.add('is-dragging');
    });
    dropZone.addEventListener('dragover', event => {
      if (!looksLikeFile(event)) return;
      event.preventDefault();
      if (event.dataTransfer) event.dataTransfer.dropEffect = 'copy';
      dropZone.classList.add('is-dragging');
    });
    dropZone.addEventListener('dragleave', event => {
      if (event.relatedTarget && dropZone.contains(event.relatedTarget)) return;
      dropZone.classList.remove('is-dragging');
    });
    dropZone.addEventListener('drop', event => {
      if (!looksLikeFile(event)) return;
      event.preventDefault();
      event.stopPropagation();
      dropZone.classList.remove('is-dragging');
      const file = event.dataTransfer.files && event.dataTransfer.files[0];
      if (file) handoffFile(file);
    });
    urlForm.addEventListener('submit', event => {
      event.preventDefault();
      loadUrl(urlInput.value);
    });
    overlay.querySelectorAll('[data-import-close]').forEach(button => button.addEventListener('click', close));
    overlay.addEventListener('pointerdown', event => { if (event.target === overlay) close(); });
    escapeHandler = event => {
      if (event.key === 'Escape' && !closed) {
        event.preventDefault();
        close();
      }
    };
    document.addEventListener('keydown', escapeHandler, true);
  }

  async function requestMediaEditIfEnabled(file, runId) {
    return undefined;
  }

  async function prepareUpload(file, runId = null, compressEnabled = isCompressionEnabled(), suppliedEditOptions = undefined) {
    ensureProcessingRun(runId);
    if (!file || !file.size) throw new Error('Файл пустой.');
    if (file.size > MAX_FILE_BYTES) throw new Error('Файл больше ' + formatBytes(MAX_FILE_BYTES) + '. Уменьши его перед загрузкой.');
    const mime = mimeFromFile(file);
    if (!mime || (!mime.startsWith('image/') && !mime.startsWith('video/'))) throw new Error('Поддерживаются изображения, GIF и видео.');

    const extension = fileExtension(file).toLowerCase();
    const animatedWebP = await isAnimatedWebP(file);
    const animatedPng = !animatedWebP && (mime === 'image/png' || extension === 'apng' || extension === 'png')
      ? await isAnimatedPng(file) : false;
    ensureProcessingRun(runId);

    const config = loadConfig();
    const category = mime.startsWith('video/') ? 'video'
      : (mime === 'image/gif' || animatedWebP || animatedPng || ['gif', 'apng'].includes(extension) ? 'gif' : 'image');
    const configuredTarget = config.conversionRules[category] || 'keep';
    let editOptions = suppliedEditOptions;

    if (editOptions === undefined) {
      editOptions = await requestMediaEditIfEnabled(file, runId);
      ensureProcessingRun(runId);
      if (editOptions === null) {
        setStatus('Редактирование отменено — текущий файл пропущен.', 'info');
        return null;
      }
    }

    let target = configuredTarget;
    if (editOptions) {
      const editedFormat = getEditedOutputFormat(file, category, animatedWebP, configuredTarget);
      if (mediaEditHasChanges(editOptions, editedFormat)) {
        target = editedFormat;
      } else {
        // Accepting without edits does not force a lossy transcode.
        editOptions = null;
      }
    }
    if (target === 'keep') return file;

    // The animated-WebP size optimizer cannot apply temporal transforms. Only use it
    // when the editor is off or the user accepted without changing anything.
    if (animatedWebP && !editOptions) {
      if (target === 'webp') {
        if (!compressEnabled) {
          setStatus('Анимированный WebP: исходный размер сохранён (сжатие отключено).', 'info');
          return file;
        }
        setStatus('Подготавливаю сжатие анимированного WebP…', 'info', true);
        setProgress(5, true);
        try {
          const converted = await compressAnimatedWebP(
            file,
            config.maxWidth,
            config.compression.animationQuality / 100,
            runId
          );
          ensureProcessingRun(runId);
          return converted;
        } catch (error) {
          if (!isProcessingRunCurrent(runId)) throw error;
          logDebug('Animated WebP compression failed; original kept to preserve animation', {
            name: file.name,
            error: error.message || String(error)
          });
          setStatus('Не удалось безопасно сжать анимированный WebP; загружаю оригинал.', 'info');
          return file;
        }
      }
      throw new Error('Это анимированный WebP. Чтобы сохранить анимацию, выбери целевой формат WebP или «Оставить исходный формат».');
    }

    if (!editOptions && compressEnabled && category === 'image' && ['webp', 'png', 'jpg'].includes(target)) {
      try {
        setStatus('Конвертирую изображение встроенными средствами браузера…', 'info', true);
        setProgress(null, true);
        const converted = await resizeStaticImage(file, config.maxWidth, target, config.compression.imageQuality / 100);
        ensureProcessingRun(runId);
        return converted;
      } catch (error) {
        if (!isProcessingRunCurrent(runId)) throw error;
        logDebug('Canvas conversion failed; falling back to FFmpeg.wasm', { name: file.name, target, error: error.message || error });
      }
    }
    const conversionWidth = category === 'video' ? config.compression.videoMaxWidth : config.maxWidth;
    return ffmpegMediaToFormat(file, target, conversionWidth, config.compression, runId, compressEnabled, editOptions);
  }



  // Import-result feedback is separate from the portal's in-progress pulse.
  function playTriggerResult(result) {
    const trigger = document.getElementById('twgif-trigger') || activeTrigger;
    if (!trigger || !trigger.isConnected) return;
    if (triggerResultTimer) clearTimeout(triggerResultTimer);
    trigger.classList.remove(
      'twgif-result-success', 'twgif-result-error', 'twgif-result-duplicate',
      'twgif-portal-active', 'twgif-portal-closing'
    );
    void trigger.offsetWidth; // Restart blinking when a batch produces another result.
    const resultClass = result === 'success' ? 'twgif-result-success'
      : result === 'duplicate' ? 'twgif-result-duplicate' : 'twgif-result-error';
    trigger.classList.add(resultClass);
    triggerResultTimer = window.setTimeout(() => {
      trigger.classList.remove('twgif-result-success', 'twgif-result-error', 'twgif-result-duplicate');
      triggerResultTimer = 0;
    }, 1900);
  }

  function flashTriggerResult(result) {
    // Avoid noisy notifications while the gallery itself is visible. Imports can
    // finish after the panel is closed, regardless of how they were started.
    if (isPanelOpen()) {
      pendingTriggerResult = '';
      return;
    }
    if (document.visibilityState === 'hidden' ||
        (typeof document.hasFocus === 'function' && !document.hasFocus())) {
      pendingTriggerResult = result;
      return;
    }
    pendingTriggerResult = '';
    playTriggerResult(result);
  }

  function showPendingTriggerResult() {
    if (!pendingTriggerResult) return;
    // A pending result is no longer useful if the user opens the gallery first.
    if (isPanelOpen()) {
      pendingTriggerResult = '';
      return;
    }
    if (document.visibilityState === 'hidden') return;
    if (typeof document.hasFocus === 'function' && !document.hasFocus()) return;
    const result = pendingTriggerResult;
    pendingTriggerResult = '';
    playTriggerResult(result);
  }

  function syncTriggerUploadIndicator() {
    // The pulse represents active work, not the method used to start the import.
    // Never distract the user with it while the gallery panel is visible.
    const shouldPulse = !isPanelOpen() && (portalImportDepth > 0 || activeProcessingRunId > 0);
    const triggers = new Set([document.getElementById('twgif-trigger'), activeTrigger]);
    for (const trigger of triggers) {
      if (trigger) trigger.classList.toggle('twgif-uploading', shouldPulse);
    }
  }

  function addItem(url, name, type, sourceKey = '', previewUrl = '', mediaBlob = null, isHd = false, forceAdd = false) {
    const data = loadData();
    const normalizedUrl = String(url || '').trim();
    const normalizedPreview = String(previewUrl || normalizedUrl).trim();
    if (!forceAdd) {
      const existing = data.items.find(item =>
        item.url === normalizedUrl ||
        (sourceKey && item.sourceKey === sourceKey) ||
        (normalizedPreview && item.previewUrl === normalizedPreview)
      );
      if (existing) {
        setStatus('Это медиа уже есть в галерее.', 'info');
        flashTriggerResult('duplicate');
        return false;
      }
    }

    const now = Date.now();
    data.items.push({
      id: makeId(),
      url: normalizedUrl,
      previewUrl: normalizedPreview,
      name: String(name || 'Медиафайл').slice(0, 120),
      type: type || 'image',
      sourceKey: String(sourceKey || ''),
      favorite: false,
      hd: Boolean(isHd),
      size: mediaBlob instanceof Blob ? Math.max(0, Number(mediaBlob.size) || 0) : 0,
      addedAt: now,
      updatedAt: now
    });
    galleryPage = 0;
    persistData(data);
    if (mediaBlob instanceof Blob) {
      const cacheUrl = normalizedPreview || normalizedUrl;
      cacheMediaBlob(cacheUrl, mediaBlob);
      cacheSharedMediaBlob(cacheUrl, mediaBlob);
    }
    setStatus('Добавлено в коллекцию.', 'success');
    flashTriggerResult('success');
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

  function is7TVGalleryItem(item) {
    try {
      if (!item) return false;
      const url = new URL(item.url, location.href);
      if (parse7TVEmoteId(url)) return true;
      // Older gallery entries may point straight to a 7TV CDN file rather than the emote page.
      return /(^|\.)7tv\.app$/i.test(url.hostname) &&
        /^\/emote\/[a-z0-9]{20,32}\/\d+x\.(?:webp|gif|png|avif|jpe?g)$/i.test(url.pathname);
    } catch (_) {
      return false;
    }
  }

  function isVideoGalleryItem(item) {
    if (String(item?.type || '').toLowerCase() === 'video') return true;

    const rawUrl = String(item?.previewUrl || item?.url || '');
    if (!rawUrl) return false;
    try {
      const pathname = new URL(rawUrl, location.href).pathname;
      return /\.(?:webm|mp4|mov|m4v|mkv|avi|ogv|mpg|mpeg)$/i.test(pathname);
    } catch (_) {
      // Fallback for unusual/non-standard URL strings.
      return /\.(?:webm|mp4|mov|m4v|mkv|avi|ogv|mpg|mpeg)(?:$|[?#])/i.test(rawUrl);
    }
  }

  // Video mode includes video containers and image animations such as GIF/APNG.
  // WebP is different: inspect its container flags/chunks to distinguish animation from still images.
  function getItemWebPUrl(item) {
    return [item?.previewUrl, item?.url].map(value => String(value || '').trim()).find(isWebPResource) || '';
  }

  function getCachedWebPMediaKind(url) {
    if (animatedWebPStatusCache.has(url)) {
      return animatedWebPStatusCache.get(url) ? 'animated' : 'photo';
    }
    if (Number(videoDurationCache.get(url)) > 0) return 'animated';
    return '';
  }

  function isAnimatedMediaItem(item) {
    const type = String(item?.type || '').toLowerCase();
    if (type === 'video' || type === 'gif' || item?.animated === true) return true;

    const candidates = [item?.previewUrl, item?.url, item?.name]
      .map(value => String(value || '').trim())
      .filter(Boolean);
    for (const rawUrl of candidates) {
      let pathname = rawUrl;
      try { pathname = new URL(rawUrl, location.href).pathname; } catch (_) {}
      if (/\.(?:gif|apng|webm|mp4|mov|m4v|mkv|avi|ogv|mpg|mpeg)$/i.test(pathname)) return true;
    }

    // Positive duration confirms animation; zero/unknown duration is not proof of a still.
    let hasVerifiedStaticWebP = false;
    for (const rawUrl of candidates) {
      if (!isWebPResource(rawUrl)) continue;
      const cachedKind = getCachedWebPMediaKind(rawUrl);
      if (cachedKind === 'animated') return true;
      if (cachedKind === 'photo') hasVerifiedStaticWebP = true;
    }
    if (hasVerifiedStaticWebP) return false;

    return normalizeStoredMediaKind(item) === 'animated';
  }

  function persistMediaKindClassifications(classifications) {
    if (!(classifications instanceof Map) || !classifications.size) return false;
    const data = loadData();
    const now = Date.now();
    let changed = false;

    for (const item of data.items) {
      const url = getItemWebPUrl(item);
      const mediaKind = url ? classifications.get(url) : '';
      if (!mediaKind || !PERSISTED_MEDIA_KINDS.has(mediaKind)) continue;
      const kindChanged = item.mediaKind !== mediaKind;
      const retryResult = mediaKind === 'unavailable';
      if (!kindChanged && !retryResult) continue;

      item.mediaKind = mediaKind;
      item.mediaKindCheckedAt = now;
      changed = true;
    }

    // Classification is cache metadata, so it must not bump an item's edit timestamp.
    // mergeData retains it independently during Gist synchronization.
    if (changed) persistData(data);
    return changed;
  }

  // Inspect only unknown WebPs. Persist the result with the item so reloads reuse it.
  function scheduleAnimatedWebPClassification(items) {
    const candidates = [];
    const seenUrls = new Set();
    const classifications = new Map();
    const now = Date.now();

    for (const item of items) {
      const url = getItemWebPUrl(item);
      if (!url) continue;

      const retryAt = Number(item.mediaKindCheckedAt) || 0;
      const eligible = item.mediaKind === 'unknown' ||
        (item.mediaKind === 'unavailable' && now - retryAt >= MEDIA_KIND_RETRY_INTERVAL_MS);
      if (!eligible) continue;

      const cachedKind = getCachedWebPMediaKind(url);
      if (cachedKind) {
        classifications.set(url, cachedKind);
        continue;
      }
      if (seenUrls.has(url) || animatedWebPClassificationPending.has(url)) continue;
      if (animatedWebPCheckFailed.has(url)) animatedWebPCheckFailed.delete(url);

      animatedWebPClassificationPending.add(url);
      seenUrls.add(url);
      candidates.push({ item, url });
    }

    const finish = () => {
      const changed = persistMediaKindClassifications(classifications);
      if (!changed && galleryMediaType === 'videos' && isPanelOpen() && panelView === 'gallery') {
        renderGalleryItems();
      }
    };

    if (!candidates.length) {
      if (classifications.size) Promise.resolve().then(finish);
      return;
    }

    let nextIndex = 0;
    const worker = async () => {
      while (nextIndex < candidates.length) {
        const candidate = candidates[nextIndex++];
        try {
          await resolveAnimatedWebPDuration(candidate.item, candidate.url);
          const knownKind = getCachedWebPMediaKind(candidate.url);
          if (knownKind) {
            classifications.set(candidate.url, knownKind);
          } else {
            // Failed probes persist as unavailable and are retried only after one day.
            animatedWebPCheckFailed.add(candidate.url);
            classifications.set(candidate.url, 'unavailable');
          }
        } catch (error) {
          animatedWebPCheckFailed.add(candidate.url);
          classifications.set(candidate.url, 'unavailable');
          logDebug('Could not inspect WebP for gallery filter', {
            url: candidate.url,
            error: error?.message || String(error)
          });
        } finally {
          animatedWebPClassificationPending.delete(candidate.url);
        }
      }
    };

    Promise.all(Array.from({ length: Math.min(3, candidates.length) }, () => worker()))
      .then(finish)
      .catch(error => {
        for (const candidate of candidates) {
          animatedWebPClassificationPending.delete(candidate.url);
          animatedWebPCheckFailed.add(candidate.url);
        }
        logDebug('WebP classification queue failed', error);
      });
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


  function parseTelegramPostUrl(url) {
    if (!url || !['http:', 'https:'].includes(url.protocol)) return null;
    const host = String(url.hostname || '').toLowerCase().replace(/^www\./, '');
    if (!['t.me', 'telegram.me'].includes(host)) return null;

    let parts = String(url.pathname || '').split('/').filter(Boolean);
    try { parts = parts.map(part => decodeURIComponent(part)); } catch (_) {}
    if (parts[0] && parts[0].toLowerCase() === 's') parts.shift();
    if (parts.length !== 2) return null;

    const channel = String(parts[0] || '').toLowerCase();
    const postId = String(parts[1] || '');
    if (!/^[a-z0-9_]+$/i.test(channel) || !/^\d+$/.test(postId)) return null;
    if (!Number.isSafeInteger(Number(postId)) || Number(postId) <= 0) return null;

    return {
      channel,
      postId,
      canonicalUrl: 'https://t.me/' + channel + '/' + postId,
      embedUrl: 'https://t.me/' + channel + '/' + postId + '?embed=1&mode=tme',
      previewUrl: 'https://t.me/s/' + channel + '?before=' + (Number(postId) + 1)
    };
  }

  function normalizeTelegramMediaUrl(rawUrl) {
    const value = String(rawUrl || '').trim().replace(/&amp;/gi, '&');
    if (!value || /^(?:blob:|data:|javascript:)/i.test(value)) return '';
    let parsed;
    try { parsed = new URL(value, 'https://t.me/'); } catch (_) { return ''; }
    if (parsed.protocol !== 'https:' || parsed.username || parsed.password) return '';

    const host = String(parsed.hostname || '').toLowerCase();
    const allowedHost = host === 'telesco.pe'
      || host.endsWith('.telesco.pe')
      || host === 'telegram.org'
      || host.endsWith('.telegram.org')
      || host === 'telegram-cdn.org'
      || host.endsWith('.telegram-cdn.org')
      || host === 'cdn-telegram.org'
      || host.endsWith('.cdn-telegram.org');
    if (!allowedHost) return '';

    const path = String(parsed.pathname || '');
    const hasMediaExtension = /\.(?:jpe?g|png|gif|webp|bmp|mp4|webm|mov|m4v|mkv|avi|ogv|mpg|mpeg)(?:$)/i.test(path);
    if (!/\/file\//i.test(path) && !hasMediaExtension) return '';
    parsed.hash = '';
    return parsed.href;
  }

  function telegramCssBackgroundUrl(element) {
    const style = String(element?.getAttribute?.('style') || '');
    const match = /background-image\s*:[^;]*url\(\s*(?:"([^"]+)"|'([^']+)'|([^)\s]+))\s*\)/i.exec(style);
    return match ? String(match[1] || match[2] || match[3] || '').trim() : '';
  }

  function extractTelegramPostMedia(html, target, allowSingleMessage = false) {
    let doc;
    try {
      doc = new DOMParser().parseFromString(String(html || ''), 'text/html');
    } catch (_) {
      return [];
    }

    const messages = Array.from(doc.querySelectorAll('.tgme_widget_message'));
    if (!messages.length) return [];
    const expected = (target.channel + '/' + target.postId).toLowerCase();
    const getDataPost = element => {
      let current = element;
      while (current && current.nodeType === 1) {
        const value = String(current.getAttribute('data-post') || '').trim();
        if (value) return value.toLowerCase();
        current = current.parentElement;
      }
      return '';
    };
    const message = messages.find(element => {
      const value = getDataPost(element);
      return value === expected || value.endsWith('/' + expected);
    }) || (allowSingleMessage && messages.length === 1 && !getDataPost(messages[0]) ? messages[0] : null);
    if (!message) return [];

    const candidates = [];
    const seen = new Set();
    const addCandidate = (rawUrl, type, element, posterOnly = false) => {
      const url = normalizeTelegramMediaUrl(rawUrl);
      if (!url || seen.has(url)) return;
      seen.add(url);
      let resolvedType = type || 'image';
      const pathname = (() => { try { return new URL(url).pathname; } catch (_) { return ''; } })();
      if (/\.(?:mp4|webm|mov|m4v|mkv|avi|ogv|mpg|mpeg)$/i.test(pathname)) resolvedType = 'video';
      else if (/\.gif$/i.test(pathname)) resolvedType = 'gif';
      candidates.push({ url, type: resolvedType, posterOnly: Boolean(posterOnly), element });
    };

    // Prefer the photo anchor URL over its CSS thumbnail when Telegram exposes both.
    for (const photo of Array.from(message.querySelectorAll('.tgme_widget_message_photo_wrap, .tgme_widget_message_photo'))) {
      const href = normalizeTelegramMediaUrl(photo.getAttribute('href') || '');
      if (href) addCandidate(href, 'image', photo, false);
      else addCandidate(telegramCssBackgroundUrl(photo), 'image', photo, false);
    }

    // Telegram sometimes renders downloadable media as a video/source element.
    for (const video of Array.from(message.querySelectorAll('video'))) {
      const videoSources = [video, ...Array.from(video.querySelectorAll('source'))];
      for (const source of videoSources) {
        const src = source.getAttribute('src') || source.getAttribute('data-src') || '';
        addCandidate(src, 'video', video, false);
      }
    }

    // Handle image tags when the post uses an img rather than a photo-wrap background.
    for (const image of Array.from(message.querySelectorAll('img'))) {
      if (image.closest('.tgme_widget_message_user_photo, .tgme_widget_message_author, .tgme_widget_message_photo_wrap, .tgme_widget_message_video_thumb, .tgme_widget_message_sticker, .tgme_widget_message_poll')) continue;
      const src = image.getAttribute('src') || image.getAttribute('data-src') || '';
      if (/\/file\//i.test((() => { try { return new URL(src, 'https://t.me/').pathname; } catch (_) { return ''; } })())) {
        addCandidate(src, 'image', image, false);
      }
    }

    // Some public previews expose a downloadable video link without a <video> tag.
    for (const anchor of Array.from(message.querySelectorAll('a[href]'))) {
      const raw = anchor.getAttribute('href') || '';
      const path = (() => { try { return new URL(raw, 'https://t.me/').pathname; } catch (_) { return ''; } })();
      if (/\.(?:mp4|webm|mov|m4v|mkv|avi|ogv|mpg|mpeg)(?:$)/i.test(path)) {
        addCandidate(raw, 'video', anchor, false);
      }
    }

    if (candidates.length) {
      candidates.sort((a, b) => {
        if (!a.element || !b.element || a.element === b.element || !a.element.compareDocumentPosition) return 0;
        const order = a.element.compareDocumentPosition(b.element);
        if (order & 4) return -1;
        if (order & 2) return 1;
        return 0;
      });
      return candidates.map(({ url, type, posterOnly }) => ({ url, type, posterOnly }));
    }

    // For large videos Telegram may expose only the poster. Keep it as a fallback,
    // and explicitly report that it is a preview rather than the original video.
    for (const thumb of Array.from(message.querySelectorAll('.tgme_widget_message_video_thumb, video[poster]'))) {
      const raw = thumb.tagName && thumb.tagName.toLowerCase() === 'video'
        ? thumb.getAttribute('poster')
        : telegramCssBackgroundUrl(thumb);
      addCandidate(raw, 'image', thumb, true);
    }
    return candidates.map(({ url, type, posterOnly }) => ({ url, type, posterOnly }));
  }

  async function resolveTelegramPostMedia(target, runId) {
    const attempts = [
      { url: target.embedUrl, allowSingleMessage: true },
      { url: target.previewUrl, allowSingleMessage: false }
    ];
    let lastError = null;

    for (const attempt of attempts) {
      ensureProcessingRun(runId);
      try {
        const response = await request({
          method: 'GET',
          url: attempt.url,
          responseType: 'text',
          timeout: 30000,
          trackForCancel: true,
          headers: { Accept: 'text/html,application/xhtml+xml;q=0.9,*/*;q=0.8' }
        });
        ensureProcessingRun(runId);
        const html = String(response.responseText || (typeof response.response === 'string' ? response.response : ''));
        if (!html) continue;
        const media = extractTelegramPostMedia(html, target, attempt.allowSingleMessage);
        if (media.length) return media;
      } catch (error) {
        if (error?.name === 'AbortError' || !isProcessingRunCurrent(runId)) throw error;
        lastError = error;
        logDebug('Telegram post resolver request failed', { url: attempt.url, error: error.message || String(error) });
      }
    }

    if (lastError) logDebug('Telegram post did not expose downloadable media', { post: target.canonicalUrl });
    throw new Error('Не удалось получить медиа из Telegram-поста. Проверь, что канал публичный, пост не удалён и содержит фото или доступное для скачивания видео. Иногда Telegram показывает только превью большого видео.');
  }

  function is7TVUrl(url) {
    return Boolean(url && /(^|\.)7tv\.(?:app|io)$/i.test(url.hostname));
  }

  function mediaTypeFromMime(mime) {
    const normalized = String(mime || '').toLowerCase();
    if (normalized.startsWith('video/')) return 'video';
    if (normalized === 'image/gif') return 'gif';
    return 'image';
  }

  function sourceNameFromUrl(rawUrl) {
    try {
      const parsed = new URL(rawUrl);
      const lastSegment = parsed.pathname.split('/').filter(Boolean).pop() || parsed.hostname || 'media';
      try { return decodeURIComponent(lastSegment).slice(0, 120); }
      catch (_) { return lastSegment.slice(0, 120); }
    } catch (_) {
      return 'media';
    }
  }

  function createLinkedMediaFile(rawUrl, blob, nameHint = '') {
    const parsed = new URL(rawUrl);
    const sourceName = sourceNameFromUrl(rawUrl);
    const contentMime = String(blob.type || '').split(';')[0].trim().toLowerCase();
    const pathMime = mimeFromFile({ name: sourceName, type: '' });
    const mime = /^(image|video)\//i.test(contentMime) ? contentMime : pathMime;
    if (!mime || (!mime.startsWith('image/') && !mime.startsWith('video/'))) {
      throw new Error('По ссылке не найден прямой файл изображения, GIF или видео. Нужна ссылка непосредственно на медиафайл, а не на страницу сайта.');
    }

    let name = String(nameHint || sourceName || parsed.hostname || 'media')
      .trim()
      .replace(/[<>:"/\\|?*\u0000-\u001f]+/g, '_')
      .slice(0, 120) || 'media';
    const extensionMatch = name.match(/\.([a-z0-9]{1,8})$/i);
    const nameMime = mimeFromFile({ name, type: '' });
    const mimeExtension = getExtension(mime, '');
    if (!extensionMatch) {
      name += mimeExtension;
    } else if (mimeExtension !== '.bin' && nameMime !== mime) {
      name = name.replace(/\.[^.]+$/, '') + mimeExtension;
    }
    return new File([blob], name, { type: mime, lastModified: Date.now() });
  }

  // Import entry points share the same core pipeline, whether a file, URL, or supported service link is used.
  async function addUrl(rawUrl, customName = '', runId = null, compressEnabled = isCompressionEnabled()) {
    if (runId !== null && runId !== undefined) return addUrlCore(rawUrl, customName, runId, '', compressEnabled);
    if (activeProcessingRunId) {
      throw new Error('Уже выполняется обработка. Дождись завершения или отмени её значком стоп у кольца прогресса.');
    }
    const ownedRunId = ++processingRunId;
    activeProcessingRunId = ownedRunId;
    syncTriggerUploadIndicator();
    setProgressCancelable(true);
    try {
      return await addUrlCore(rawUrl, customName, ownedRunId, '', compressEnabled);
    } catch (error) {
      if (error?.name !== 'AbortError') {
        flashTriggerResult('error');
        setStatus(error.message || String(error), 'error');
      }
      throw error;
    } finally {
      if (activeProcessingRunId === ownedRunId) {
        activeProcessingRunId = 0;
        syncTriggerUploadIndicator();
        setProgressCancelable(false);
      }
      if (isProcessingRunCurrent(ownedRunId)) finishProgress(1000);
      else setProgress(null, false);
    }
  }

  async function addUrlCore(rawUrl, customName = '', runId = null, sourceKeyOverride = '', compressEnabled = isCompressionEnabled()) {
    const text = String(rawUrl || '').trim().replace(/^<|>$/g, '');
    let parsed;
    try { parsed = new URL(text); }
    catch (_) { throw new Error('Вставь прямую ссылку на медиа или ссылку 7TV вида https://7tv.app/emotes/ID.'); }
    if (!['https:', 'http:'].includes(parsed.protocol)) throw new Error('Разрешены только HTTP- и HTTPS-ссылки.');
    ensureProcessingRun(runId);

    const originalUrl = parsed.toString();
    const sourceKey = String(sourceKeyOverride || ('url:' + originalUrl));
    const alreadyAdded = loadData().items.some(item =>
      item.url === originalUrl || item.previewUrl === originalUrl || item.sourceKey === sourceKey
    );
    if (alreadyAdded) {
      setStatus('Это медиа уже есть в галерее.', 'info');
      flashTriggerResult('duplicate');
      return false;
    }

    const telegramPost = parseTelegramPostUrl(parsed);
    if (telegramPost) {
      setStatus('Получаю медиа из Telegram-поста…', 'info', true);
      const telegramMedia = await resolveTelegramPostMedia(telegramPost, runId);
      ensureProcessingRun(runId);

      let imported = 0;
      let skipped = 0;
      const mediaErrors = [];
      for (let index = 0; index < telegramMedia.length; index++) {
        ensureProcessingRun(runId);
        const media = telegramMedia[index];
        const mediaSourceKey = 'telegram-post:' + telegramPost.canonicalUrl + '#' + encodeURIComponent(media.url);
        try {
          const added = await addUrlCore(media.url, '', runId, mediaSourceKey, compressEnabled);
          if (added) imported++;
          else skipped++;
        } catch (error) {
          if (error?.name === 'AbortError' || !isProcessingRunCurrent(runId)) throw error;
          mediaErrors.push(error.message || String(error));
          logDebug('Telegram media import failed', { post: telegramPost.canonicalUrl, mediaUrl: media.url, error: error.message || String(error) });
        }
      }

      if (imported > 0) {
        const hasPosterOnly = telegramMedia.some(media => media.posterOnly);
        if (hasPosterOnly) {
          setStatus('Добавлено превью видео из Telegram; сам ролик недоступен через публичную страницу.', 'info', true);
        } else if (mediaErrors.length) {
          setStatus('Из Telegram добавлено: ' + imported + '; ошибок: ' + mediaErrors.length + '.', 'success', true);
        } else {
          setStatus('Из Telegram-поста добавлено медиа: ' + imported + '.', 'success', true);
        }
        return true;
      }
      if (skipped === telegramMedia.length && mediaErrors.length === 0) {
        setStatus('Медиа из этого Telegram-поста уже есть в галерее.', 'info');
        return false;
      }
      throw new Error('Не удалось импортировать медиа из Telegram-поста: ' + (mediaErrors[0] || 'не удалось скачать вложение.'));
    }

    // 7TV page links remain the original chat link; all 7TV CDN links also bypass conversion.
    const sevenTvHost = is7TVUrl(parsed);
    const sevenTv = parse7TVEmoteId(parsed) ? await resolve7TVEmote(parsed) : null;
    ensureProcessingRun(runId);
    const hintedName = String(customName || '').trim() || (sevenTv && sevenTv.name) || sourceNameFromUrl(originalUrl);

    if (sevenTvHost) {
      const previewUrl = sevenTv ? sevenTv.url : originalUrl;
      let type = sevenTv ? sevenTv.type : mediaTypeFromUrl(originalUrl);
      if (isMediaEditorEnabled() && /\.(?:gif|apng|webp|mp4|webm|mov|m4v|mkv|avi|ogv|mpg|mpeg)(?:$|[?#])/i.test(previewUrl)) {
        try {
          const blob = await requestBlob(previewUrl, 180000, true);
          ensureProcessingRun(runId);
          if (!blob || !blob.size) throw new Error('Ссылка вернула пустой файл.');
          if (blob.size > MAX_FILE_BYTES) throw new Error('Файл больше ' + formatBytes(MAX_FILE_BYTES) + '.');
          const file = createLinkedMediaFile(previewUrl, blob, hintedName);
          const info = await getEditableMediaInfo(file);
          ensureProcessingRun(runId);
          if (info) {
            const edits = await openMediaEditor(file, runId, info);
            ensureProcessingRun(runId);
            if (edits === null) return false;
            const config = loadConfig();
            const category = info.kind === 'video' ? 'video' : 'gif';
            const outFormat = getEditedOutputFormat(file, category, info.animationFormat === 'webp', config.conversionRules[category] || 'keep');
            if (edits && mediaEditHasChanges(edits, outFormat)) {
              return processSingleFile(file, '', runId, compressEnabled, edits);
            }
            if (info.kind === 'animation') type = 'gif';
          }
        } catch (error) {
          if (error?.name === 'AbortError' || !isProcessingRunCurrent(runId)) throw error;
          logDebug('Could not prepare 7TV media editor preview; keeping direct URL', error.message || error);
        }
      }
      if (type !== 'video') await waitForImage(previewUrl);
      ensureProcessingRun(runId);
      return addItem(originalUrl, hintedName, type, '', previewUrl);
    }

    // If the URL clearly identifies a type whose rule is "keep", keep the remote URL
    // without downloading/re-uploading it. Unknown/extensionless URLs are inspected below.
    const pathName = sourceNameFromUrl(originalUrl);
    const pathMime = mimeFromFile({ name: pathName, type: '' });
    if (pathMime) {
      const pathCategory = mediaTypeFromMime(pathMime);
      const config = loadConfig();
      if ((config.conversionRules[pathCategory] || 'keep') === 'keep') {
        let type = mediaTypeFromMime(pathMime);
        const editorCandidate = isMediaEditorEnabled() &&
          (pathCategory === 'video' || pathCategory === 'gif' || /\.(?:webp|apng)(?:$|[?#])/i.test(originalUrl));
        if (editorCandidate) {
          const blob = await requestBlob(originalUrl, 180000, true);
          ensureProcessingRun(runId);
          if (!blob || !blob.size) throw new Error('Ссылка вернула пустой файл.');
          if (blob.size > MAX_FILE_BYTES) throw new Error('Файл больше ' + formatBytes(MAX_FILE_BYTES) + '. Используй ссылку на файл меньшего размера.');
          const file = createLinkedMediaFile(originalUrl, blob, hintedName);
          const info = await getEditableMediaInfo(file);
          ensureProcessingRun(runId);
          if (info) {
            const edits = await openMediaEditor(file, runId, info);
            ensureProcessingRun(runId);
            if (edits === null) return false;
            const outFormat = getEditedOutputFormat(file, info.kind === 'video' ? 'video' : 'gif',
              info.animationFormat === 'webp', config.conversionRules[pathCategory] || 'keep');
            if (edits && mediaEditHasChanges(edits, outFormat)) {
              return processSingleFile(file, sourceKey, runId, compressEnabled, edits);
            }
            if (info.kind === 'animation') type = 'gif';
          } else if (/\.webp(?:$|[?#])/i.test(originalUrl)) {
            // The file was already downloaded for inspection; avoid a second network
            // probe when the editor correctly identifies a static WebP.
            animatedWebPStatusCache.set(originalUrl, false);
          }
        }
        if (type !== 'video') await waitForImage(originalUrl);
        if (type === 'image' && /\.webp$/i.test(pathName)) {
          await resolveAnimatedWebPDuration({ url: originalUrl, previewUrl: originalUrl, name: hintedName }, originalUrl);
          if (animatedWebPStatusCache.get(originalUrl) === true) type = 'gif';
        }
        ensureProcessingRun(runId);
        return addItem(originalUrl, hintedName, type, sourceKey, originalUrl, null, !compressEnabled);
      }
    }

    setStatus('Скачиваю медиа по ссылке для обработки…', 'info', true);
    setProgress(0, true);
    const blob = await requestBlob(originalUrl, 180000, true);
    ensureProcessingRun(runId);
    if (!blob || !blob.size) throw new Error('Ссылка вернула пустой файл.');
    if (blob.size > MAX_FILE_BYTES) throw new Error('Файл больше ' + formatBytes(MAX_FILE_BYTES) + '. Используй ссылку на файл меньшего размера.');

    const file = createLinkedMediaFile(originalUrl, blob, hintedName);
    const mime = mimeFromFile(file);
    const category = mediaTypeFromMime(mime);
    let type = mediaTypeFromMime(mime);
    const config = loadConfig();
    const target = config.conversionRules[category] || 'keep';

    if (target === 'keep') {
      if (type === 'image' && await isAnimatedWebP(file)) type = 'gif';
      if (type !== 'video') await waitForImage(originalUrl);
      ensureProcessingRun(runId);
      setProgress(100, true);
      finishProgress(700);
      return addItem(originalUrl, hintedName || file.name, type, sourceKey, originalUrl, null, !compressEnabled);
    }

    setStatus('Конвертирую медиа по ссылке: ' + file.name + '…', 'info', true);
    setProgress(8, true);
    const prepared = await prepareUpload(file, runId, compressEnabled);
    ensureProcessingRun(runId);
    if (!prepared) return false;
    setProgress(65, true);
    setStatus('Загружаю обработанное медиа на kappa.lol…', 'info', true);
    setProgress(null, true);
    const uploaded = await uploadToKappa(prepared, percent => {
      setProgress(65 + Math.round(percent * 0.35), true);
    }, runId);
    ensureProcessingRun(runId);

    const ext = fileExtension(prepared);
    const animatedWebPOutput = ext === 'webp' && await isAnimatedWebP(prepared);
    const outputType = animatedWebPOutput || ext === 'gif' ? 'gif'
      : ['webm', 'mp4', 'mov', 'mkv', 'avi', 'ogv', 'mpg', 'mpeg'].includes(ext) ? 'video' : 'image';
    const added = addItem(uploaded.url, prepared.name || hintedName || file.name, outputType, sourceKey, uploaded.url, prepared, !compressEnabled);
    setProgress(100, true);
    finishProgress(1000);
    return added;
  }

  function fileFingerprint(file) {
    return [String(file.name || ''), String(file.size || 0), String(file.lastModified || 0), String(file.type || '')].join('|');
  }

  function makeEditedImportFilename(file) {
    const originalName = String(file && file.name || 'Медиафайл');
    const extension = fileExtension(file).toLowerCase();
    const suffix = 'обрезка ' + Date.now() + '-' + makeId().slice(-4);
    const baseName = extension && originalName.toLowerCase().endsWith('.' + extension)
      ? originalName.slice(0, -(extension.length + 1))
      : originalName;
    return (baseName.slice(0, 80) || 'Медиафайл') + ' (' + suffix + ')' + (extension ? '.' + extension : '');
  }

  async function processSingleFile(file, sourceKey, runId, compressEnabled = isCompressionEnabled(), suppliedEditOptions = undefined) {
    setProgress(0, true);
    try {
      ensureProcessingRun(runId);
      setStatus('Подготавливаю «' + (file.name || 'медиа') + '»…', 'info', true);
      setProgress(4, true);
      let prepared = await prepareUpload(file, runId, compressEnabled, suppliedEditOptions);
      ensureProcessingRun(runId);
      if (!prepared) {
        setStatus('Медиа пропущено: редактирование отменено.', 'info');
        return false;
      }
      const editorImport = suppliedEditOptions !== undefined && suppliedEditOptions !== null;
      if (editorImport) {
        prepared = new File([prepared], makeEditedImportFilename(prepared), {
          type: prepared.type || mimeFromFile(prepared),
          lastModified: Date.now()
        });
        sourceKey = String(sourceKey || '') + ':editor:' + makeId();
      }
      setProgress(65, true);
      setStatus('Загружаю «' + (prepared.name || file.name) + '» на kappa.lol…', 'info', true);
      // Upload byte progress is not consistently exposed by userscript managers,
      // so keep the ring animated rather than showing a fabricated percentage.
      setProgress(null, true);
      const uploaded = await uploadToKappa(prepared, percent => {
        // Conversion occupies the first 65%; upload occupies the last 35%.
        setProgress(65 + Math.round(percent * 0.35), true);
      }, runId);
      ensureProcessingRun(runId);
      const ext = fileExtension(prepared);
      const animatedWebPOutput = ext === 'webp' && await isAnimatedWebP(prepared);
      const type = animatedWebPOutput || ext === 'gif' ? 'gif'
        : ['webm', 'mp4', 'mov', 'mkv', 'avi', 'ogv', 'mpg', 'mpeg'].includes(ext) ? 'video' : 'image';
      const added = addItem(uploaded.url, prepared.name || file.name || 'Медиафайл', type, sourceKey, uploaded.url, prepared, !compressEnabled, editorImport);
      setProgress(100, true);
      if (!added) {
        setStatus('Это медиа уже есть в галерее.', 'info');
        finishProgress(1000);
        return false;
      }
      setStatus('Готово: ' + (prepared.name || file.name) + ' загружен на kappa.lol.', 'success');
      finishProgress(1200);
      return true;
    } catch (error) {
      if (error?.name === 'AbortError' || !isProcessingRunCurrent(runId)) {
        logDebug('File processing cancelled', file.name);
        return false;
      }
      logDebug('File processing failed', file.name, error);
      flashTriggerResult('error');
      setStatus((file.name || 'Файл') + ': ' + (error.message || error), 'error', true);
      finishProgress(2400);
      return false;
    }
  }



  async function processFiles(fileList, suppliedEditOptions = undefined) {
    const files = Array.from(fileList || []).filter(file => {
      const mime = mimeFromFile(file);
      return mime.startsWith('image/') || mime.startsWith('video/');
    });
    if (!files.length) {
      flashTriggerResult('error');
      setStatus('Буфер или перетаскивание не содержат изображение или видео.', 'error');
      return;
    }
    if (activeProcessingRunId) {
      setStatus('Уже выполняется обработка. Её можно отменить значком стоп у кольца прогресса.', 'info', true);
      return;
    }

    const editorImport = suppliedEditOptions !== undefined && suppliedEditOptions !== null;
    const compressEnabled = !(editorImport && suppliedEditOptions.hd === true) && isCompressionEnabled();
    const runId = ++processingRunId;
    activeProcessingRunId = runId;
    syncTriggerUploadIndicator();
    setProgressCancelable(true);
    try {
      for (const file of files) {
        if (!isProcessingRunCurrent(runId)) break;
        const key = editorImport ? fileFingerprint(file) + '|editor:' + makeId() : fileFingerprint(file);
        const now = Date.now();
        for (const [fingerprint, expiresAt] of recentFileFingerprints) {
          if (expiresAt <= now) recentFileFingerprints.delete(fingerprint);
        }
        if (!editorImport && loadData().items.some(item => item.sourceKey && item.sourceKey === key)) {
          logDebug('File fingerprint already exists in collection; upload skipped', { name: file.name, size: file.size });
          setStatus(`«${file.name || 'Файл'}» уже есть в галерее — повторная загрузка пропущена.`, 'info');
          flashTriggerResult('duplicate');
          recentFileFingerprints.set(key, Date.now() + 20000);
          continue;
        }
        if (processingFiles.has(key)) {
          logDebug('Duplicate file event ignored while processing', { name: file.name, size: file.size });
          continue;
        }
        if (!editorImport && (recentFileFingerprints.get(key) || 0) > now) {
          logDebug('Repeated file event ignored after success', { name: file.name, size: file.size });
          continue;
        }

        // Register before the first await so a bubbling/duplicate event cannot
        // create a second converter job and a second Kappa upload.
        const task = processSingleFile(file, key, runId, compressEnabled, suppliedEditOptions);
        processingFiles.set(key, task);
        let succeeded = false;
        try {
          succeeded = await task;
        } finally {
          processingFiles.delete(key);
          if (succeeded && !editorImport) recentFileFingerprints.set(key, Date.now() + 20000);
        }
      }
    } finally {
      if (activeProcessingRunId === runId) {
        activeProcessingRunId = 0;
        syncTriggerUploadIndicator();
        setProgressCancelable(false);
      }
      if (isProcessingRunCurrent(runId)) finishProgress(1000);
      else setProgress(null, false);
    }
  }

  function toggleFavorite(id) {
    const data = loadData();
    const item = data.items.find(entry => entry.id === id);
    if (!item) return;
    item.favorite = !item.favorite;
    item.updatedAt = Math.max(Date.now(), (Number(item.updatedAt) || 0) + 1);
    persistData(data);
    setStatus(item.favorite ? 'Добавлено в избранное.' : 'Удалено из избранного.', 'success');
  }

  function deleteItem(id) {
    const data = loadData();
    const item = data.items.find(entry => entry.id === id);
    if (!item) return;
    data.items = data.items.filter(entry => entry.id !== id);
    data.deleted[id] = Date.now();
    const cachedCard = mediaCardCache.get(id);
    if (cachedCard) {
      if (galleryResizeObserver) galleryResizeObserver.unobserve(cachedCard);
      cachedCard.remove();
    }
    mediaCardCache.delete(id);
    persistData(data);
    setStatus('Удалено из галереи.', 'success');
  }

  // ----- Multi-platform chat composer integration -----

  function isTwitchSite() {
    return /(^|\.)twitch\.tv$/i.test(location.hostname);
  }

  function isTwitchRecordingPage() {
    if (!isTwitchSite()) return false;
    const path = String(location.pathname || '/');
    return /^\/videos?(?:\/|$)/i.test(path) ||
      /^\/[^/]+\/video\/\d+(?:\/|$)/i.test(path) ||
      /^\/clip(?:\/|$)/i.test(path) ||
      /^\/[^/]+\/clips?(?:\/|$)/i.test(path);
  }

  function isWtvSite() {
    return /(^|\.)w\.tv$/i.test(location.hostname);
  }

  function isKickSite() {
    return /(^|\.)kick\.com$/i.test(location.hostname);
  }

  function platformDisplayName() {
    const host = String(location.hostname || '').toLowerCase();
    if (/(^|\.)twitch\.tv$/.test(host)) return 'Twitch';
    if (/(^|\.)kick\.com$/.test(host)) return 'Kick';
    if (/(^|\.)w\.tv$/.test(host)) return 'w.tv';
    if (host === 'live.vkvideo.ru') return 'VK Видео Live';
    return 'сайте';
  }

  // Platform adapter: find and preserve the active chat composer despite SPA DOM replacement.
  function looksLikeChatEditor(element) {
    if (!element || !element.isConnected || !element.getClientRects().length || element.closest('#twgif-panel')) return false;
    const type = String(element.getAttribute('type') || '').toLowerCase();
    if (['search', 'password', 'email', 'checkbox', 'radio', 'button', 'submit'].includes(type)) return false;

    const hint = [
      element.getAttribute('aria-label'),
      element.getAttribute('placeholder'),
      element.getAttribute('data-placeholder'),
      element.getAttribute('data-testid'),
      element.getAttribute('data-a-target'),
      element.id,
      typeof element.className === 'string' ? element.className : ''
    ].filter(Boolean).join(' ');

    if (/(search|поиск)/i.test(hint) && !/(chat|message|сообщ|чат)/i.test(hint)) return false;
    if (/(chat|message|сообщ|чат|комментар|напишите|написать)/i.test(hint)) return true;

    const context = element.closest(
      '[data-testid*="chat" i], [data-a-target*="chat" i], [id*="chat" i], ' +
      '[class*="chat" i], [class*="message-input" i], [class*="composer" i], [class*="comment-input" i]'
    );
    if (context && !context.closest('#twgif-panel')) return true;

    const form = element.closest('form');
    return Boolean(form && form.querySelector(
      'button[type="submit"], [data-testid*="send" i], [aria-label*="send" i], [aria-label*="отправ" i]'
    ));
  }

  function getChatInput() {
    const twitchSelectors = [
      '[data-a-target="chat-input"][contenteditable="true"]',
      '[data-a-target="chat-input"][role="textbox"]',
      '[data-a-target="chat-input"] textarea',
      'textarea[data-a-target="chat-input"]',
      '[contenteditable="true"][data-slate-editor="true"]',
      '[contenteditable="true"][role="textbox"][aria-label*="Send a message"]'
    ];
    if (isTwitchSite()) {
      for (const selector of twitchSelectors) {
        const element = document.querySelector(selector);
        if (element && element.isConnected && element.getClientRects().length && !element.closest('#twgif-panel')) return element;
      }
      return null;
    }

    const specificSelectors = [
      '[data-testid*="chat-input" i] textarea',
      '[data-testid*="chat-input" i] [contenteditable="true"]',
      '[data-testid*="message-input" i] textarea',
      '[data-testid*="message-input" i] [contenteditable="true"]',
      '[data-a-target="chat-input"]',
      '[contenteditable="true"][data-placeholder*="message" i]',
      '[contenteditable="true"][data-placeholder*="сообщ" i]',
      '[contenteditable="true"][aria-label*="message" i]',
      '[contenteditable="true"][aria-label*="сообщ" i]',
      '[contenteditable="true"][aria-label*="чат" i]',
      'textarea[placeholder*="message" i]',
      'textarea[placeholder*="сообщ" i]',
      'textarea[placeholder*="чат" i]',
      'input[placeholder*="message" i]',
      'input[placeholder*="сообщ" i]',
      'input[placeholder*="чат" i]',
      '[contenteditable="true"][role="textbox"]'
    ];
    for (const selector of specificSelectors) {
      for (const element of document.querySelectorAll(selector)) {
        if (looksLikeChatEditor(element)) return element;
      }
    }

    // Last resort: recognize unlabelled editors from their chat/composer ancestors.
    for (const element of document.querySelectorAll('textarea, input[type="text"], [contenteditable="true"]')) {
      if (looksLikeChatEditor(element)) return element;
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
      setStatus('Не нашёл поле ввода чата ' + platformDisplayName() + '. Открой чат и повтори.', 'error', true);
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
    clean.items = Array.isArray(raw.items)
      ? raw.items
        .filter(x => x && typeof x.id === 'string' && typeof x.url === 'string')
        .map(item => ({ ...item, favorite: Boolean(item.favorite) }))
      : [];
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
      #twgif-trigger{appearance:none!important;border:0!important;background:transparent!important;color:var(--color-text-base,#efeff1)!important;display:inline-flex!important;align-items:center!important;justify-content:center!important;flex:0 0 32px!important;width:32px!important;min-width:32px!important;height:32px!important;margin:0!important;padding:0!important;align-self:center!important;vertical-align:middle!important;box-sizing:border-box!important;position:fixed!important;left:var(--twgif-trigger-left,0px)!important;top:var(--twgif-trigger-top,0px)!important;z-index:2147482500!important;transform:none!important;border-radius:50%!important;overflow:hidden!important;cursor:pointer!important;line-height:1!important}
      #twgif-trigger.twgif-inline-trigger{position:relative!important;left:auto!important;top:auto!important;z-index:2!important;transform:none!important;align-self:center!important;margin:0 3px!important;border-radius:50%!important}
      #twgif-trigger.twgif-inline-twitch{flex:0 0 32px!important;width:32px!important;min-width:32px!important;height:32px!important}
      #twgif-trigger.twgif-inline-wtv{flex:0 0 44px!important;width:44px!important;min-width:44px!important;height:44px!important}
      #twgif-trigger.twgif-inline-kick{flex:0 0 32px!important;width:32px!important;min-width:32px!important;height:32px!important}
      #twgif-trigger.twgif-uploading svg{position:relative;z-index:2;transform-origin:center;will-change:transform,opacity,filter;animation:twgif-upload-pulse 1.35s ease-in-out infinite;}
      #twgif-trigger:hover,#twgif-trigger[aria-expanded=true]{background:var(--color-background-button-text-hover,#2b2b2f)!important;color:var(--color-text-link,#bf94ff)!important;border-radius:50%!important}
      #twgif-trigger svg{display:block;width:20px;height:20px;flex:0 0 20px;align-self:center;pointer-events:none}
      #twgif-trigger.twgif-portal-active,#twgif-trigger.twgif-portal-closing{overflow:visible!important;isolation:isolate!important;z-index:2147483500!important;transform:scale(1.08)!important;}
      #twgif-trigger.twgif-portal-active{background:radial-gradient(circle,#26123f 0,#13091f 72%)!important;box-shadow:0 0 0 1px #dabaff55,0 0 22px #a65cffaa,0 0 36px #7437c788!important;color:#f1dfff!important;}
      #twgif-trigger.twgif-portal-active::before,#twgif-trigger.twgif-portal-closing::before{content:"";position:absolute;z-index:0;inset:-11px;border-radius:50%;pointer-events:none;background:conic-gradient(from 0deg,#3b176b,#e2c5ff,#7b35d5,#1b0d35,#bf8dff,#55219a,#3b176b);filter:blur(3.8px) drop-shadow(0 0 7px #ad72ff99);opacity:.92;mask:radial-gradient(circle,transparent 0 39%,#000 49% 64%,transparent 82%);}
      #twgif-trigger.twgif-portal-active::before{animation:twgif-portal-spin .85s linear infinite;}
      #twgif-trigger.twgif-portal-active::after,#twgif-trigger.twgif-portal-closing::after{content:"";position:absolute;z-index:1;inset:-3px;border-radius:50%;pointer-events:none;border:0;background:radial-gradient(circle at 50% 48%,#07030d 0 22%,#170a29b8 35%,#a86aff55 51%,#8e43ed22 62%,transparent 75%),conic-gradient(from 0deg,#12071f,#a86aff,#291142,#e5c7ff,#32134d,#8d43ed,#12071f);filter:blur(1.8px);box-shadow:inset 0 0 7px #030007,0 0 12px #a45cff88;mask:radial-gradient(circle,#000 0 50%,#000c 60%,transparent 78%);}
      #twgif-trigger.twgif-portal-active::after{animation:twgif-portal-vortex 1.45s linear infinite,twgif-portal-breathe .8s ease-in-out infinite alternate;}
      #twgif-trigger.twgif-portal-active svg{position:relative;z-index:2;opacity:.18;transform:scale(.78);filter:drop-shadow(0 0 3px #fff);}
      #twgif-trigger.twgif-portal-closing::before{animation:twgif-portal-close .26s ease-in forwards;}
      #twgif-trigger.twgif-portal-closing::after{animation:twgif-portal-close .22s ease-in forwards;}
      #twgif-trigger.twgif-result-success,#twgif-trigger.twgif-result-error,#twgif-trigger.twgif-result-duplicate{overflow:visible!important;isolation:isolate!important;z-index:2147483500!important;background:transparent!important;box-shadow:none!important;}
      #twgif-trigger.twgif-result-success{color:#75ffad!important;}
      #twgif-trigger.twgif-result-error{color:#ff7885!important;}
      #twgif-trigger.twgif-result-duplicate{color:#fff!important;}
      #twgif-trigger.twgif-result-success::before,#twgif-trigger.twgif-result-success::after,#twgif-trigger.twgif-result-error::before,#twgif-trigger.twgif-result-error::after,#twgif-trigger.twgif-result-duplicate::before,#twgif-trigger.twgif-result-duplicate::after{content:none!important;display:none!important;}
      #twgif-trigger.twgif-result-success svg{position:relative;z-index:2;animation:twgif-success-icon-glow .42s ease-in-out 3;filter:drop-shadow(0 0 2px #28c45c) drop-shadow(0 0 7px #28c45c);}
      #twgif-trigger.twgif-result-error svg{position:relative;z-index:2;animation:twgif-error-icon-glow .42s ease-in-out 3;filter:drop-shadow(0 0 2px #ff4055) drop-shadow(0 0 7px #ff4055);}
      #twgif-trigger.twgif-result-duplicate svg{position:relative;z-index:2;animation:twgif-duplicate-icon-glow .42s ease-in-out 3;filter:drop-shadow(0 0 2px #fff) drop-shadow(0 0 7px #fff);}
      @keyframes twgif-portal-spin{to{transform:rotate(360deg)}}
      @keyframes twgif-portal-vortex{to{transform:rotate(-360deg)}}
      @keyframes twgif-portal-breathe{from{filter:blur(1.8px) brightness(.85);transform:scale(.94)}to{filter:blur(1.8px) brightness(1.3);transform:scale(1.04)}}
      @keyframes twgif-portal-close{to{opacity:0;transform:scale(.12) rotate(180deg)}}
      @keyframes twgif-upload-pulse{0%,100%{opacity:.76;transform:scale(.96);filter:brightness(.98) drop-shadow(0 0 2px #a970ff55) drop-shadow(0 0 3px #a970ff33)}50%{opacity:1;transform:scale(1.08);filter:brightness(1.1) drop-shadow(0 0 3px #d4b5ffb8) drop-shadow(0 0 8px #a970ff99)}}
      @keyframes twgif-success-icon-glow{0%,100%{opacity:.55;filter:drop-shadow(0 0 1px #28c45c) drop-shadow(0 0 2px #28c45c)}50%{opacity:1;filter:drop-shadow(0 0 3px #28c45c) drop-shadow(0 0 10px #28c45c)}}
      @keyframes twgif-error-icon-glow{0%,100%{opacity:.55;filter:drop-shadow(0 0 1px #ff4055) drop-shadow(0 0 2px #ff4055)}50%{opacity:1;filter:drop-shadow(0 0 3px #ff4055) drop-shadow(0 0 10px #ff4055)}}
      @keyframes twgif-duplicate-icon-glow{0%,100%{opacity:.55;filter:drop-shadow(0 0 1px #fff) drop-shadow(0 0 2px #fff)}50%{opacity:1;filter:drop-shadow(0 0 3px #fff) drop-shadow(0 0 10px #fff)}}
      #twgif-panel{position:fixed!important;top:8px;left:8px;bottom:auto;z-index:2147483000!important;width:400px;height:var(--twgif-panel-height,auto);max-width:calc(100vw - 16px);max-height:calc(100vh - 16px);min-height:220px;display:flex;flex-direction:column;overflow:hidden;resize:none!important;color:#efeff1;background:#18181b;border:1px solid #34343b;border-radius:10px;box-shadow:0 10px 34px #0009;font:13px/1.4 Inter,system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;box-sizing:border-box;pointer-events:auto}
      #twgif-panel[hidden]{display:none!important}#twgif-panel *{box-sizing:border-box}
      #twgif-resize-top{position:absolute;top:0;left:0;width:100%;height:14px;z-index:2147483001;display:block;cursor:ns-resize;touch-action:none;user-select:none;pointer-events:auto}
      #twgif-resize-top:after{content:"";position:absolute;top:3px;left:50%;transform:translateX(-50%);display:block;width:38px;height:4px;border-radius:4px;background:#777783;opacity:.9;transition:background .12s,opacity .12s}
      #twgif-resize-top:hover:after{background:#d0d0da;opacity:1}
      #twgif-panel.twgif-resizing{cursor:ns-resize!important;user-select:none!important}
      #twgif-panel.twgif-resizing *{user-select:none!important;cursor:ns-resize!important}
      .twgif-head{display:flex;align-items:center;gap:5px;padding:6px 8px;min-height:42px;border-bottom:1px solid #34343b;flex-shrink:0}
      .twgif-head-brand{display:flex;align-items:center;gap:4px;flex:1;min-width:0;overflow:hidden}
      .twgif-head-brand .twgif-heading{font-size:13px;font-weight:700;flex:0 1 auto;min-width:0;max-width:calc(100% - 33px);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
      .twgif-media-editor-head-btn{width:28px;height:28px;flex:0 0 28px;color:#c4c4cc}
      .twgif-media-editor-head-btn svg{display:block;width:17px;height:17px}
      .twgif-head-btn{appearance:none;border:0;background:transparent;color:#c4c4cc;width:29px;height:29px;display:inline-flex;align-items:center;justify-content:center;padding:0;border-radius:6px;cursor:pointer;flex-shrink:0}
      .twgif-head-btn:hover{background:#303036;color:#fff}.twgif-head-btn[hidden]{display:none!important}
      #twgif-settings-open svg{display:block;flex:0 0 18px;width:18px;height:18px;margin:auto;position:static;transform:none}
      .twgif-settings-tabs{display:flex;align-items:center;gap:1px}.twgif-settings-tabs[hidden]{display:none!important}
      .twgif-tab{appearance:none;border:0;background:transparent;color:#a8a8b3;width:28px;height:28px;border-radius:6px;display:inline-flex;align-items:center;justify-content:center;cursor:pointer;padding:0}
      .twgif-tab:hover{background:#303036;color:#fff}.twgif-tab[aria-selected=true]{background:#392653;color:#d6b4ff}
      .twgif-media-filter{display:flex;align-items:center;gap:4px;margin:0 0 6px}
      .twgif-media-filter-button{appearance:none;display:inline-flex;align-items:center;justify-content:center;min-width:58px;border:1px solid #3c3c44;border-radius:6px;background:#202024;color:#bcbcc6;padding:5px 10px;font:inherit;font-size:11px;font-weight:500;line-height:1.2;cursor:pointer}
      .twgif-media-filter-button:hover{background:#303036;color:#fff}
      .twgif-media-filter-button[data-filter-mode=photos],.twgif-media-filter-button[data-filter-mode=videos]{border-color:#8b5bd4;background:#392653;color:#e8d7ff}
      .twgif-gallery-tabs{display:flex;gap:5px;margin:0 0 8px}
      .twgif-gallery-tab{appearance:none;display:inline-flex;align-items:center;gap:5px;border:1px solid #3c3c44;border-radius:6px;background:#202024;color:#bcbcc6;padding:6px 9px;font:inherit;font-size:11px;font-weight:500;line-height:1.2;cursor:pointer}
      .twgif-gallery-tab:hover{background:#303036;color:#fff}.twgif-gallery-tab[aria-selected=true]{border-color:#8b5bd4;background:#392653;color:#e8d7ff}
      .twgif-gallery-tab-count{font-size:9px;opacity:.75}
      .twgif-panel-body{padding:9px 10px 10px;overflow:auto;min-height:0;overscroll-behavior:contain}
      /* Keep the gallery scrollbar consistent on Twitch regardless of the page's color scheme. */
      #twgif-panel .twgif-panel-body{color-scheme:dark!important;scrollbar-width:thin!important;scrollbar-color:#45454f #18181b!important}
      #twgif-panel .twgif-panel-body::-webkit-scrollbar{width:6px!important;height:6px!important}
      #twgif-panel .twgif-panel-body::-webkit-scrollbar-track{background:#18181b!important;border-radius:6px!important}
      #twgif-panel .twgif-panel-body::-webkit-scrollbar-thumb{background:#45454f!important;border:1px solid #18181b!important;border-radius:6px!important}
      #twgif-panel .twgif-panel-body::-webkit-scrollbar-thumb:hover{background:#62626d!important}
      .twgif-toolbar{display:flex;align-items:center;gap:5px;margin-bottom:8px}
      .twgif-input{display:block;width:100%;min-width:0;background:#0e0e10;color:#efeff1;border:1px solid #3f3f46;border-radius:6px;padding:8px 9px;outline:none;font-family:inherit;font-size:12px;line-height:1.35}
      .twgif-input:focus{border-color:#a970ff;box-shadow:0 0 0 1px #9147ff40}.twgif-url-input{flex:1 1 120px;width:100%}
      .twgif-small-btn{appearance:none;border:1px solid #42424a;background:#252529;color:#efeff1;padding:7px 9px;border-radius:6px;cursor:pointer;font-family:inherit;font-size:11px;font-weight:500;line-height:1.2;white-space:nowrap}
      .twgif-small-btn:hover{background:#34343b;border-color:#65656e}.twgif-small-btn:disabled{opacity:.55;cursor:wait}
      .twgif-primary{background:#9147ff;border-color:#9147ff;color:#fff}.twgif-primary:hover{background:#772ce8;border-color:#772ce8}
      .twgif-toolbar-icon{width:30px;min-width:30px;height:30px;padding:0;display:inline-flex;align-items:center;justify-content:center;font-size:19px}
      .twgif-compress-toggle{display:inline-flex;align-items:center;justify-content:center;gap:3px;flex:0 0 auto;color:#bcbcc6;font-size:10px;white-space:nowrap;cursor:pointer;user-select:none}
      .twgif-compress-toggle input{width:12px;height:12px;margin:0;accent-color:#9147ff;cursor:pointer}
      .twgif-drop{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:6px 7px;margin-bottom:8px;border:1px dashed #41414b;border-radius:7px;color:#a8a8b3;font-size:10px}
      .twgif-drop strong{display:block;color:#d9d9df;font-size:10px;font-weight:600}.twgif-drop span{font-size:9px}.twgif-drop.twgif-drag{border-color:#a970ff;background:#9147ff1a}#twgif-panel.twgif-drag{border-color:#a970ff;box-shadow:0 0 0 2px #9147ff55,0 10px 34px #0009}#twgif-panel.twgif-drag::after{content:'Отпусти файлы для добавления';position:absolute;inset:4px;z-index:20;display:flex;align-items:center;justify-content:center;border:2px dashed #b78cff;border-radius:8px;background:#18181be8;color:#f4eaff;font-size:14px;font-weight:700;pointer-events:none}
      .twgif-masonry{display:grid;grid-template-columns:repeat(var(--twgif-columns,4),minmax(0,1fr));grid-auto-rows:0.25px;align-items:start;gap:6px}.twgif-masonry.twgif-grid-mode{grid-auto-rows:auto;gap:6px}.twgif-masonry[hidden]{display:none!important}
      .twgif-card{display:block;align-self:start;position:relative;width:100%;margin:0;vertical-align:top;border:1px solid #34343b;border-radius:6px;overflow:visible;background:#202024;cursor:pointer;outline:none;transition:border-color .12s,box-shadow .12s}
      .twgif-card[hidden]{display:none!important}.twgif-masonry.twgif-grid-mode .twgif-card{display:block;width:100%;margin:0;overflow:visible;grid-row-end:auto!important}.twgif-card,.twgif-card img,.twgif-card video{user-select:none;-webkit-user-select:none;-webkit-user-drag:none}
      .twgif-media-frame{position:relative;overflow:hidden;border-radius:5px;background:#101012;isolation:isolate}
      .twgif-media{display:block;width:100%;height:auto;max-width:100%;background:#101012;object-fit:contain}.twgif-masonry.twgif-grid-mode .twgif-media{width:100%;height:var(--twgif-thumb-height,90px);object-fit:contain}
      .twgif-file-size{position:absolute;z-index:2;right:4px;bottom:4px;max-width:calc(100% - 8px);padding:2px 4px;border:1px solid #ffffff10;border-radius:4px;background:#09090bd1;color:#c5c5ce;font-size:9px;font-weight:400;line-height:1.25;letter-spacing:.01em;white-space:nowrap;opacity:0;visibility:hidden;transform:translateY(2px);transition:opacity .14s ease,visibility .14s ease,transform .14s ease;pointer-events:none;backdrop-filter:blur(3px);font-variant-numeric:tabular-nums}
      .twgif-card:hover .twgif-file-size,.twgif-card:focus-visible .twgif-file-size,.twgif-card:focus-within .twgif-file-size{opacity:.82;visibility:visible;transform:translateY(0)}
      .twgif-file-size[hidden]{display:none!important}
      .twgif-video-duration{position:absolute;z-index:2;left:50%;bottom:4px;max-width:calc(100% - 12px);padding:2px 5px;border:1px solid #ffffff10;border-radius:4px;background:#09090bd1;color:#c5c5ce;font-size:9px;font-weight:400;line-height:1.25;letter-spacing:.01em;white-space:nowrap;opacity:0;visibility:hidden;transform:translate(-50%,2px);transition:opacity .14s ease,visibility .14s ease,transform .14s ease;pointer-events:none;backdrop-filter:blur(3px);font-variant-numeric:tabular-nums}
      .twgif-card:hover .twgif-video-duration,.twgif-card:focus-visible .twgif-video-duration,.twgif-card:focus-within .twgif-video-duration{opacity:.82;visibility:visible;transform:translate(-50%,0)}
      .twgif-video-duration[hidden]{display:none!important}
      .twgif-media-error{min-height:44px;padding:10px;text-align:center;color:#9c9ca6;font-size:10px}
      .twgif-delete{position:absolute;z-index:3;top:-1px;right:-1px;display:flex;align-items:center;justify-content:center;width:17px;height:17px;padding:0;border:1px solid #ffffff26;border-radius:0 5px 0 6px;background:#18181beF;color:#f2f2f2;opacity:0;pointer-events:none;transition:opacity .13s,background .13s,transform .13s;cursor:pointer}
      .twgif-delete svg{width:10px;height:10px;display:block;pointer-events:none}.twgif-card:hover .twgif-delete,.twgif-card:focus-within .twgif-delete{opacity:1;pointer-events:auto}.twgif-delete:hover{background:#b42335;border-color:#ef4444;transform:scale(1.08)}
      .twgif-favorite{position:absolute;z-index:4;left:4px;bottom:4px;width:23px;height:23px;padding:0;display:flex;align-items:center;justify-content:center;border:1px solid #ffffff28;border-radius:6px;background:#18181be8;color:#eeeef2;opacity:.78;cursor:pointer;transition:opacity .12s,background .12s,color .12s,transform .12s}
      .twgif-favorite svg{width:14px;height:14px;display:block;pointer-events:none}
      .twgif-favorite:hover{opacity:1;background:#3c202c;color:#ff8ca6;transform:scale(1.06)}
      .twgif-favorite[aria-pressed=true]{opacity:1;color:#ff668b;background:#3c202c;border-color:#e85a80}
      .twgif-favorite[aria-pressed=true] svg{fill:currentColor}
      .twgif-pagination{display:flex;align-items:center;justify-content:center;gap:10px;padding:9px 0 0}.twgif-pagination[hidden]{display:none!important}.twgif-page-label{font-size:10px;color:#b7b7c1;min-width:54px;text-align:center}
      .twgif-empty{padding:22px 8px;text-align:center;color:#a8a8b3;font-size:12px}.twgif-empty[hidden]{display:none}
      #twgif-progress{--twgif-progress:0;display:inline-flex;align-items:center;gap:4px;flex:0 0 auto;color:#e1c9ff;font-size:10px;font-variant-numeric:tabular-nums;line-height:1}#twgif-progress[hidden]{display:none!important}
      #twgif-status-indicator{appearance:none;position:relative;display:inline-flex;align-items:center;justify-content:center;flex:0 0 25px;width:25px;height:29px;padding:0;border:0;border-radius:6px;background:transparent;color:#aaaab5;cursor:pointer}
      #twgif-status-indicator:hover{background:#303036}#twgif-status-indicator[hidden]{display:none!important}
      .twgif-status-dot{display:block;width:8px;height:8px;border-radius:50%;background:#85858f;box-shadow:0 0 0 2px #85858f18;transition:background .18s ease,box-shadow .18s ease,transform .18s ease}
      #twgif-status-indicator[data-type=info] .twgif-status-dot{background:#9b9ba7;box-shadow:0 0 0 2px #9b9ba71c}
      #twgif-status-indicator[data-type=success] .twgif-status-dot{background:#45d483;box-shadow:0 0 0 2px #45d48324,0 0 7px #45d48370}
      #twgif-status-indicator[data-type=error] .twgif-status-dot{background:#ff596b;box-shadow:0 0 0 2px #ff596b24,0 0 7px #ff596b70}
      #twgif-status-indicator[data-type=warning] .twgif-status-dot{background:#f4be55;box-shadow:0 0 0 2px #f4be5524,0 0 7px #f4be5570}
      #twgif-status-indicator[data-type=progress] .twgif-status-dot{background:#b78cff;box-shadow:0 0 0 2px #b78cff20,0 0 8px #b78cff80;animation:twgif-status-pulse 1.4s ease-in-out infinite}
      @keyframes twgif-status-pulse{0%,100%{opacity:.7;transform:scale(.88)}50%{opacity:1;transform:scale(1.12)}}
       #twgif-progress-ring{position:relative;display:block;flex:0 0 18px;width:18px;height:18px}
       #twgif-progress-ring>svg{display:block;width:18px;height:18px;overflow:visible}
       #twgif-progress circle{fill:none;stroke-width:3.5}#twgif-progress .twgif-progress-track{stroke:#45414e}#twgif-progress .twgif-progress-value{stroke:#b78cff;stroke-linecap:round;stroke-dasharray:100;stroke-dashoffset:calc(100 - var(--twgif-progress));transform:rotate(-90deg);transform-origin:50% 50%;transition:stroke-dashoffset .12s linear}
       #twgif-progress[data-indeterminate=true] #twgif-progress-ring>svg{animation:twgif-progress-spin .8s linear infinite}#twgif-progress[data-indeterminate=true] .twgif-progress-value{stroke-dasharray:28 72;stroke-dashoffset:0}
       #twgif-progress-cancel{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;width:18px;height:18px;padding:0;border:1px solid #e87382;border-radius:50%;background:#992c3c;color:#fff;opacity:0;visibility:hidden;cursor:pointer;z-index:2;transition:opacity .1s,visibility .1s}
       #twgif-progress-cancel svg{display:block;width:9px;height:9px}
       #twgif-progress[data-cancelable=true] #twgif-progress-ring:hover #twgif-progress-cancel,#twgif-progress[data-cancelable=true] #twgif-progress-ring:focus-within #twgif-progress-cancel{opacity:1;visibility:visible}
       #twgif-progress-cancel:hover{background:#c9364d;border-color:#ff9aa7}
       @keyframes twgif-progress-spin{to{transform:rotate(360deg)}}
      .twgif-settings{display:flex;flex-direction:column;gap:7px}.twgif-section{border:1px solid #33333a;border-radius:7px;padding:8px}.twgif-section-title{margin:0 0 7px;font-size:11px;font-weight:700;color:#dddde5}.twgif-help{color:#a8a8b3;font-size:10px;line-height:1.45;margin:5px 0 0}.twgif-help a{color:#bf94ff;text-decoration:none}.twgif-help a:hover{text-decoration:underline}.twgif-field-label{display:block;margin:6px 0 4px;font-size:10px;color:#c8c8d0}.twgif-row{display:flex;align-items:center;gap:6px;flex-wrap:wrap}.twgif-row>.twgif-input{flex:1 1 145px}.twgif-check-row{display:flex;align-items:center;gap:7px;font-size:11px;color:#dbdbe2;margin:3px 0}.twgif-check-row input{accent-color:#9147ff}
      .twgif-debug-log{display:block;width:100%;height:240px;max-height:38vh;min-height:100px;overflow:auto;resize:vertical;background:#0c0c0e;border:1px solid #36363d;border-radius:5px;padding:6px;font:10px/1.45 ui-monospace,Consolas,monospace;white-space:pre-wrap;overflow-wrap:anywhere;scrollbar-width:thin;scrollbar-color:#45454f #0c0c0e}
      .twgif-log-entry{display:block;margin:0;padding:1px 0;white-space:pre-wrap;overflow-wrap:anywhere}
      .twgif-log-time{color:#777b88}
      .twgif-log-entry[data-type=info]{color:#c0c2cd}
      .twgif-log-entry[data-type=success]{color:#66dfa0}
      .twgif-log-entry[data-type=error]{color:#ff818b}
      .twgif-log-entry[data-type=warning]{color:#f4c66e}
      .twgif-log-entry[data-type=progress]{color:#c7a5ff}
      .twgif-chat-add{appearance:none!important;display:inline-flex!important;align-items:center!important;justify-content:center!important;vertical-align:middle!important;width:16px!important;height:16px!important;margin:0 0 0 4px!important;padding:0!important;border:1px solid #9147ff70!important;border-radius:4px!important;color:#d7b8ff!important;background:#18181bcc!important;font:700 12px/1 system-ui!important;cursor:pointer!important;opacity:.35;transition:opacity .12s,background .12s!important}.twgif-chat-add:hover{opacity:1!important;background:#9147ff!important;color:#fff!important}
      #twgif-hold-preview{position:fixed;z-index:2147483100;pointer-events:none;display:flex;align-items:center;justify-content:center;opacity:0;overflow:hidden;transform:scale(.92);transform-origin:center center;transition:transform .18s ease,opacity .18s ease;filter:drop-shadow(0 12px 30px #000b);max-width:calc(100vw - 16px);max-height:calc(100vh - 16px)}
      #twgif-hold-preview.twgif-preview-visible{opacity:1;transform:scale(1)}#twgif-hold-preview img,#twgif-hold-preview video{display:block;width:100%;height:100%;max-width:100%;max-height:100%;object-fit:contain;border:1px solid #ffffff33;border-radius:8px;background:#111}
      @media(max-width:500px){#twgif-panel{max-height:calc(100vh - 16px);min-height:180px}.twgif-drop{align-items:flex-start;flex-direction:column}.twgif-head{gap:2px;padding-left:6px}.twgif-heading{font-size:12px}}
    `;
    document.head.appendChild(style);

    if (!document.getElementById('twgif-hold-preview')) {
      const preview = document.createElement('div');
      preview.id = 'twgif-hold-preview';
      document.documentElement.appendChild(preview);
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
      <div id="twgif-resize-top" title="Потяните верхнюю границу вверх или вниз, чтобы изменить высоту" aria-hidden="true"></div>
      <div class="twgif-head">
        <button id="twgif-settings-back-top" class="twgif-head-btn" type="button" title="Назад к галерее" aria-label="Назад" hidden>←</button>
        <div class="twgif-head-brand"><div id="twgif-heading" class="twgif-heading">GIF и картинки</div><button id="twgif-media-editor-open" class="twgif-head-btn twgif-media-editor-head-btn" type="button" title="Редактор видео и анимаций" aria-label="Открыть редактор видео и анимаций">${SVG_CROP}</button></div>
        <div id="twgif-settings-tabs" class="twgif-settings-tabs" hidden>
          <button class="twgif-tab" type="button" data-tab="general" title="Вид и общие" aria-label="Общие настройки" aria-selected="false">◫</button>
          <button class="twgif-tab" type="button" data-tab="convert" title="Конвертация" aria-label="Настройки конвертации" aria-selected="false">⇄</button>
          <button class="twgif-tab" type="button" data-tab="sync" title="Синхронизация" aria-label="Синхронизация" aria-selected="false">☁</button>
          <button class="twgif-tab" type="button" data-tab="debug" title="Журнал" aria-label="Журнал" aria-selected="false">≡</button>
        </div>
        <span id="twgif-progress" hidden data-indeterminate="true" data-cancelable="false" aria-label="Идёт обработка">
          <span id="twgif-progress-ring">
            <svg viewBox="0 0 36 36" aria-hidden="true"><circle class="twgif-progress-track" cx="18" cy="18" r="15.5"></circle><circle class="twgif-progress-value" cx="18" cy="18" r="15.5"></circle></svg>
            <button id="twgif-progress-cancel" type="button" title="Отменить обработку" aria-label="Отменить обработку"><svg viewBox="0 0 24 24" aria-hidden="true"><rect x="7" y="7" width="10" height="10" rx="1.5" fill="currentColor"></rect></svg></button>
          </span>
          <span id="twgif-progress-label">…</span>
        </span>
        <button id="twgif-status-indicator" class="twgif-status-indicator" type="button" data-type="info" title="Нет новых сообщений" aria-label="Открыть журнал">
          <span class="twgif-status-dot" aria-hidden="true"></span>
        </button>
        <button id="twgif-settings-open" class="twgif-head-btn" type="button" title="Настройки" aria-label="Настройки">${SVG_SETTINGS}</button>
        <button id="twgif-close" class="twgif-head-btn" type="button" title="Закрыть" aria-label="Закрыть">${SVG_CLOSE}</button>
      </div>
      <div id="twgif-panel-body" class="twgif-panel-body"></div>
    `;
    document.documentElement.appendChild(panel);
    restorePanelSize(panel);
    installPanelResizePersistence(panel);
    installTopEdgeResize(panel);
    updateStatusIndicator();
    syncProgressIndicatorView();

    panel.querySelector('#twgif-close').addEventListener('click', closePanel);
    panel.querySelector('#twgif-media-editor-open').addEventListener('click', event => {
      event.preventDefault();
      event.stopPropagation();
      openMediaEditorImportDialog();
    });
    panel.querySelector('#twgif-status-indicator').addEventListener('click', () => {
      settingsTab = 'debug';
      panelView = 'settings';
      renderPanelView();
    });
    panel.querySelector('#twgif-progress-cancel').addEventListener('click', event => {
      event.preventDefault();
      event.stopPropagation();
      cancelActiveProcessing();
    });
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
      event.preventDefault();
      event.stopPropagation();
      if (event.stopImmediatePropagation) event.stopImmediatePropagation();
      panel.classList.remove('twgif-drag');
      if (files && files.length) {
        await processFiles(files);
        return;
      }
      const uri = (event.dataTransfer.getData('text/uri-list') || event.dataTransfer.getData('text/plain') || '').trim();
      if (uri.startsWith('https://') || uri.startsWith('http://')) {
        try { await addUrl(uri); }
        catch (error) { setStatus(error.message || String(error), 'error', true); }
      }
    });
  }

  function getChatRegion(input) {
    if (isTwitchSite()) {
      // Prefer Twitch's actual stream-chat column so the gallery's upper edge
      // is constrained by the top of the chat, not by the browser viewport.
      return document.querySelector('.Layout-sc-1xcs6mc-0.jUmLZD.stream-chat') ||
        document.querySelector('.Layout-sc-1xcs6mc-0.stream-chat') ||
        document.querySelector('div.stream-chat[class*="Layout-sc-1xcs6mc-0"]') ||
        document.querySelector('[data-a-target="chat-room-component-layout"]') ||
        input?.closest('.chat-room') || input?.closest('[class*="chat-room"]') ||
        input?.closest('[data-a-target="chat-input-container"]')?.parentElement?.parentElement ||
        input?.parentElement?.parentElement?.parentElement || document.body;
    }

    // Kick's stable root covers the whole chat column, unlike the small editor wrapper.
    if (isKickSite()) {
      return document.querySelector('#channel-chatroom') ||
        document.querySelector('#chatroom-footer')?.closest('[id*="chatroom" i]') ||
        document.querySelector('#chatroom-footer')?.parentElement?.parentElement ||
        input?.closest('[id*="chatroom" i]') || input?.parentElement?.parentElement || document.body;
    }

    // On w.tv use the common ancestor of the editor and the exact three-dot button,
    // then choose the widest visible ancestor that still looks like a chat column.
    const anchor = isWtvSite()
      ? (document.querySelector('button[data-testid="chat-options-button"]') ||
         document.querySelector('button[aria-label="toggle settings" i]'))
      : null;
    let common = input;
    if (anchor) {
      while (common && common !== document.body && !common.contains(anchor)) common = common.parentElement;
    }
    const start = common || input;
    const viewportWidth = Math.max(1, document.documentElement.clientWidth || innerWidth);
    const maxColumnWidth = Math.min(1000, viewportWidth * 0.9);
    let best = null;
    let bestWidth = 0;
    for (let node = start; node && node !== document.body && node !== document.documentElement; node = node.parentElement) {
      if (!node.isConnected || node.closest('#twgif-panel')) continue;
      const rect = node.getBoundingClientRect();
      if (!rect.width || !rect.height || rect.width > maxColumnWidth || rect.width < 250) continue;
      if (rect.width > bestWidth) {
        best = node;
        bestWidth = rect.width;
      }
    }
    return best || common || input?.closest(
      '[data-testid*="chat-panel" i], [data-testid*="chat-room" i], [class*="chat-panel" i], [class*="chat-room" i], [class*="chat-container" i]'
    ) || input?.parentElement?.parentElement || document.body;
  }

  function getToolbar(input) {
    if (!input) return null;
    if (isTwitchSite()) {
      // Prefer the toolbar belonging to this exact editor. A global lookup could
      // otherwise bind the icon to a stale/hidden chat or a replay page.
      return input.closest('[data-a-target="chat-input-container"]')?.parentElement?.querySelector('.chat-input__buttons-container') ||
        input.closest('form')?.querySelector('.chat-input__buttons-container') ||
        input.closest('[data-a-target="chat-input-container"]')?.parentElement?.querySelector('[class*="buttons-container"]') ||
        input.closest('form')?.querySelector('[class*="buttons-container"]') ||
        document.querySelector('.chat-input__buttons-container') || null;
    }

    const composer = input.closest(
      '[data-testid*="chat-input" i], [data-testid*="composer" i], ' +
      '[class*="chat-input" i], [class*="chat-composer" i], ' +
      '[class*="message-input" i], [class*="composer" i]'
    );
    const form = input.closest('form');
    const buttonRow = (composer || form)?.querySelector(
      '[data-testid*="toolbar" i], [class*="toolbar" i], [class*="actions" i], [class*="buttons" i]'
    );
    return buttonRow || composer || form || input.parentElement || null;
  }

  function isTwitchChatComposerVisible(input, toolbar) {
    if (!isTwitchSite() || isTwitchRecordingPage() || !input?.isConnected || !toolbar?.isConnected) return false;
    if (!input.getClientRects().length || !toolbar.getClientRects().length) return false;

    for (const element of [input, toolbar]) {
      for (let node = element; node && node !== document.documentElement; node = node.parentElement) {
        // Use visual CSS state only. aria-hidden is also changed by player/chat
        // enhancements and does not necessarily mean the controls are invisible.
        if (node.hidden) return false;
        const style = getComputedStyle(node);
        if (style.display === 'none' || style.visibility === 'hidden') return false;
      }
    }

    const inputRect = input.getBoundingClientRect();
    const toolbarRect = toolbar.getBoundingClientRect();
    // Do not reject a live chat just because an extension animates/moves it outside
    // the viewport while the player is collapsed. The trigger is mounted inline,
    // so it naturally follows the chat's actual position and visibility.
    return inputRect.width >= 100 && inputRect.height >= 12 &&
      toolbarRect.width >= 32 && toolbarRect.height >= 10;
  }

  function clearUnavailableTwitchTrigger() {
    if (!isTwitchSite()) return false;

    // Only remove it for routes where the chat composer must never be shown (VODs/clips).
    // During live stream switches the editor can temporarily disappear or be hidden;
    // leave the button in its toolbar so it returns with the chat, and let the
    // persistent lifecycle observer mount it into the replacement toolbar.
    if (!isTwitchRecordingPage()) return false;

    if (isPanelOpen()) closePanel();
    document.getElementById('twgif-trigger')?.remove();
    activeTrigger = null;
    activeComposer = null;
    return true;
  }

  function hideTwitchSettingsSpacer(toolbar, trigger, settingsButton) {
    if (!toolbar || !trigger || !settingsButton ||
        !toolbar.contains(trigger) || !toolbar.contains(settingsButton)) return;

    const follows = Node.DOCUMENT_POSITION_FOLLOWING;
    for (const spacer of toolbar.querySelectorAll('div[class*="Layout-sc-1xcs6mc-0"]')) {
      if (spacer.contains(trigger) || spacer.contains(settingsButton)) continue;
      const child = spacer.children.length === 1 ? spacer.firstElementChild : null;
      if (!child || child.tagName !== 'P' ||
          !String(child.className || '').includes('CoreText-sc-1txzju1-0') ||
          spacer.textContent.trim() !== '') continue;

      const iconIsBefore = Boolean(trigger.compareDocumentPosition(spacer) & follows);
      const spacerIsBeforeSettings = Boolean(spacer.compareDocumentPosition(settingsButton) & follows);
      if (!iconIsBefore || !spacerIsBeforeSettings) continue;

      // Twitch owns this empty spacer element; hide it instead of detaching a React node.
      spacer.style.setProperty('display', 'none', 'important');
      spacer.setAttribute('data-twgif-hidden-settings-spacer', 'true');
    }
  }

  function mountTwitchTrigger(button, input, toolbar) {
    if (!button || !isTwitchChatComposerVisible(input, toolbar)) return false;

    const settings = findChatSettingsButton(input, toolbar);
    let slot = settings ? findInlineSlot(settings) : null;
    // The settings control can be wrapped in a child container. Constrain the
    // placement to the live chat's own toolbar, never to document.body.
    if (!slot?.parent || !toolbar.contains(slot.parent)) {
      if (settings && toolbar.contains(settings)) {
        let branch = settings;
        while (branch.parentElement && branch.parentElement !== toolbar) branch = branch.parentElement;
        if (branch.parentElement === toolbar) slot = { parent: toolbar, before: branch };
      }
    }
    if (!slot?.parent || !toolbar.contains(slot.parent)) {
      const firstControl = Array.from(toolbar.children).find(node =>
        node !== button && node.isConnected && node.getClientRects().length
      ) || null;
      slot = { parent: toolbar, before: firstControl };
    }

    if (button.parentElement !== slot.parent || (slot.before && button.nextElementSibling !== slot.before)) {
      if (slot.before && slot.before !== button) slot.parent.insertBefore(button, slot.before);
      else slot.parent.appendChild(button);
    }
    button.classList.remove('twgif-inline-kick', 'twgif-inline-wtv');
    button.classList.add('twgif-inline-trigger', 'twgif-inline-twitch');
    hideTwitchSettingsSpacer(toolbar, button, settings);
    button.style.removeProperty('--twgif-trigger-left');
    button.style.removeProperty('--twgif-trigger-top');
    return true;
  }

  // The toolbar trigger is also the file-drop portal; the shared upload indicator
  // covers portal drops, window drops, and URL imports while the panel is closed.
  function createTrigger() {
    const button = document.createElement('button');
    button.id = 'twgif-trigger';
    button.type = 'button';
    // Avoid a native title tooltip overlapping Twitch's chat-settings tooltip.
    button.removeAttribute('title');
    button.setAttribute('aria-label', 'Открыть коллекцию GIF и изображений');
    button.setAttribute('aria-haspopup', 'dialog');
    button.setAttribute('aria-expanded', 'false');
    button.innerHTML = SVG_GALLERY;

    // Treat the toolbar icon as a small drop target. A file hovering over it
    // opens an animated portal; releasing the file closes the portal and starts
    // the same import pipeline used by the gallery's normal drop area.
    let portalCloseTimer = 0;
    const hasFilePayload = event => {
      const transfer = event?.dataTransfer;
      if (!transfer) return false;
      const types = Array.from(transfer.types || []).map(type => String(type).toLowerCase());
      return types.includes('files') || Array.from(transfer.items || []).some(item => item?.kind === 'file');
    };
    const clearPortalCloseTimer = () => {
      if (portalCloseTimer) {
        window.clearTimeout(portalCloseTimer);
        portalCloseTimer = 0;
      }
    };
    const showPortal = () => {
      clearPortalCloseTimer();
      button.classList.remove('twgif-portal-closing');
      button.classList.add('twgif-portal-active');
      button.setAttribute('aria-label', 'Отпусти файл, чтобы импортировать его в галерею');
    };
    const closePortal = animate => {
      clearPortalCloseTimer();
      button.classList.remove('twgif-portal-active');
      button.setAttribute('aria-label', 'Открыть коллекцию GIF и изображений');
      if (animate) {
        button.classList.add('twgif-portal-closing');
        portalCloseTimer = window.setTimeout(() => {
          button.classList.remove('twgif-portal-closing');
          portalCloseTimer = 0;
        }, 280);
      } else {
        button.classList.remove('twgif-portal-closing');
      }
    };
    button.addEventListener('dragenter', event => {
      if (!hasFilePayload(event)) return;
      event.preventDefault();
      event.stopPropagation();
      showPortal();
    });
    button.addEventListener('dragover', event => {
      if (!hasFilePayload(event)) return;
      event.preventDefault();
      event.stopPropagation();
      if (event.dataTransfer) event.dataTransfer.dropEffect = 'copy';
      if (!button.classList.contains('twgif-portal-active')) showPortal();
    });
    button.addEventListener('dragleave', event => {
      if (!hasFilePayload(event)) return;
      event.stopPropagation();
      if (event.relatedTarget && button.contains(event.relatedTarget)) return;
      closePortal(true);
    });
    button.addEventListener('drop', async event => {
      const transfer = event.dataTransfer;
      if (!transfer || !hasFilePayload(event)) {
        closePortal(true);
        return;
      }
      event.preventDefault();
      event.stopPropagation();
      if (typeof event.stopImmediatePropagation === 'function') event.stopImmediatePropagation();
      const files = Array.from(transfer.files || []);
      closePortal(true);
      if (files.length) {
        portalImportDepth++;
        syncTriggerUploadIndicator();
        try {
          await processFiles(files);
        } finally {
          portalImportDepth = Math.max(0, portalImportDepth - 1);
          syncTriggerUploadIndicator();
        }
      }
    });
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

  function hideDropsToolbarButtons(toolbar) {
    if (!toolbar || !isTwitchSite()) return;
    const candidates = toolbar.querySelectorAll('button, [role="button"]');
    for (const candidate of candidates) {
      if (candidate.id === 'twgif-trigger' || candidate.closest('#twgif-panel')) continue;
      const label = [
        candidate.getAttribute('aria-label'),
        candidate.getAttribute('title'),
        candidate.getAttribute('data-a-target'),
        candidate.getAttribute('data-testid'),
        candidate.textContent
      ].filter(Boolean).join(' ');
      if (/\bdrops?\b|\brewards?\b/i.test(label)) {
        candidate.style.setProperty('display', 'none', 'important');
        candidate.setAttribute('data-twgif-hidden-drops', 'true');
      }
    }
  }

  function positionTriggerNearSettings(settingsButton, button = activeTrigger) {
    if (!settingsButton || !button || !settingsButton.isConnected) return;
    const rect = settingsButton.getBoundingClientRect();
    const size = 32;
    const gap = 8;
    const viewportWidth = Math.max(1, document.documentElement.clientWidth || innerWidth);
    const viewportHeight = Math.max(1, document.documentElement.clientHeight || innerHeight);
    const left = Math.max(4, Math.min(viewportWidth - size - 4, rect.left - size - gap));
    const top = Math.max(4, Math.min(viewportHeight - size - 4, rect.top + (rect.height - size) / 2));
    button.style.setProperty('--twgif-trigger-left', Math.round(left) + 'px');
    button.style.setProperty('--twgif-trigger-top', Math.round(top) + 'px');
  }

  function findChatSettingsButton(input, toolbar) {
    if (!input && !toolbar) return null;
    if (isTwitchSite()) {
      return toolbar?.querySelector('[data-a-target="chat-settings-button"], [aria-label*="Chat settings" i], [aria-label*="Настройки чата" i]') || null;
    }
    if (isWtvSite()) {
      return document.querySelector('button[data-testid="chat-options-button"]') ||
        document.querySelector('button[aria-label="toggle settings" i]') || null;
    }

    // On Kick, only search the footer/composer, not the chat header. Otherwise the icon
    // can accidentally attach to the header gear and float above the input row.
    const region = isKickSite()
      ? document.querySelector('#chatroom-footer')
      : (toolbar || input?.closest('form')?.parentElement);
    const inputRect = input?.getBoundingClientRect();
    const selectors = [
      'button[data-testid*="chat-settings" i]',
      'button[data-testid*="settings" i]',
      'button[aria-label*="chat settings" i]',
      'button[aria-label*="settings" i]',
      'button[title*="settings" i]',
      'button[aria-label*="настрой" i]',
      'button[title*="настрой" i]'
    ];
    const roots = [region, toolbar, input?.closest('form')].filter(Boolean);
    const seen = new Set();
    const candidates = [];
    for (const root of roots) {
      for (const selector of selectors) {
        for (const element of root.querySelectorAll(selector)) {
          if (seen.has(element)) continue;
          seen.add(element);
          if (!element.isConnected || !element.getClientRects().length || element.closest('#twgif-panel')) continue;
          candidates.push(element);
        }
      }
    }
    if (!candidates.length) return null;
    if (!inputRect) return candidates[0];
    const score = element => {
      const rect = element.getBoundingClientRect();
      return Math.abs((rect.top + rect.height / 2) - (inputRect.top + inputRect.height / 2)) * 3 +
        Math.abs((rect.left + rect.width / 2) - inputRect.right);
    };
    candidates.sort((a, b) => score(a) - score(b));
    return candidates[0] || null;
  }

  function findChatSendButton(input, toolbar) {
    const root = input?.closest('form') || toolbar?.parentElement || toolbar;
    if (!root) return null;
    return root.querySelector(
      'button[type="submit"], button[data-testid*="send" i], button[aria-label*="send" i], ' +
      'button[title*="send" i], button[aria-label*="отправ" i], button[title*="отправ" i]'
    );
  }

  function findInlineTriggerTarget(input, toolbar) {
    if (isWtvSite()) {
      return document.querySelector('button[data-testid="chat-options-button"]') ||
        document.querySelector('button[aria-label="toggle settings" i]');
    }

    if (isKickSite()) {
      const footer = document.querySelector('#chatroom-footer');
      const settings = findChatSettingsButton(input, toolbar);
      if (settings && footer?.contains(settings)) return settings;
      // If Kick's footer has no labelled settings button, stay in its real control row.
      return footer?.querySelector('#send-message-button, button[data-testid*="send" i], button[aria-label*="send" i]') ||
        footer?.querySelector('.ml-auto button') ||
        null;
    }
    return null;
  }

  function findInlineSlot(anchor) {
    if (!anchor || !anchor.parentElement) return null;
    let branch = anchor;
    for (let parent = anchor.parentElement; parent && parent !== document.body && parent !== document.documentElement; parent = parent.parentElement) {
      const branchRect = branch.getBoundingClientRect();
      const parentRect = parent.getBoundingClientRect();
      const siblings = Array.from(parent.children).filter(node => {
        if (node === branch || !node.isConnected || !node.getClientRects().length || node.closest('#twgif-panel')) return false;
        const rect = node.getBoundingClientRect();
        return rect.width > 0 && rect.height > 0 &&
          Math.abs((rect.top + rect.height / 2) - (branchRect.top + branchRect.height / 2)) <= 18 &&
          (rect.left < branchRect.left || rect.right > branchRect.right);
      });
      if (siblings.length && parentRect.height <= 120 && parentRect.width >= branchRect.width + 30) {
        return { parent, before: branch };
      }
      branch = parent;
    }
    return { parent: anchor.parentElement, before: anchor };
  }

  function mountInlineTrigger(button, anchor, platformClass) {
    if (!button || !anchor || !anchor.isConnected) return false;
    const slot = findInlineSlot(anchor);
    if (!slot?.parent || !slot.before) return false;
    if (button.parentElement !== slot.parent || button.nextElementSibling !== slot.before) {
      slot.parent.insertBefore(button, slot.before);
    }
    button.classList.remove('twgif-inline-kick', 'twgif-inline-wtv');
    button.classList.add('twgif-inline-trigger', platformClass);
    button.style.removeProperty('--twgif-trigger-left');
    button.style.removeProperty('--twgif-trigger-top');
    return true;
  }

  function positionTriggerForSite(input, toolbar, button = activeTrigger) {
    if (!input || !button || !input.isConnected) return;

    // Twitch must use its real live-chat action row. This keeps the icon aligned
    // with channel points and settings and makes it disappear with the chat itself.
    if (isTwitchSite()) {
      // Never delete the trigger because Twitch/RTE temporarily hides or replaces
      // the composer. If it is already inside a hidden toolbar it will follow that
      // toolbar naturally; if detached, the observers retry mounting it later.
      mountTwitchTrigger(button, input, toolbar);
      return;
    }

    // For Kick and w.tv, insert into the actual control row so flex layout reserves
    // space for the icon and neighbouring buttons cannot overlap it.
    if (isWtvSite()) {
      if (mountInlineTrigger(button, findInlineTriggerTarget(input, toolbar), 'twgif-inline-wtv')) {
        return;
      }
    } else if (isKickSite()) {
      if (mountInlineTrigger(button, findInlineTriggerTarget(input, toolbar), 'twgif-inline-kick')) {
        return;
      }
    }

    button.classList.remove('twgif-inline-trigger', 'twgif-inline-kick', 'twgif-inline-wtv');
    if (button.parentElement !== document.body) document.body.appendChild(button);
    const anchor = findChatSettingsButton(input, toolbar) || findChatSendButton(input, toolbar);
    if (anchor && anchor !== input && anchor !== button && anchor.isConnected) {
      positionTriggerNearSettings(anchor, button);
      return;
    }

    // Fallback for layouts without a recognizable control button.
    const rect = input.getBoundingClientRect();
    const size = 32;
    const gap = 6;
    const viewportWidth = Math.max(1, document.documentElement.clientWidth || innerWidth);
    const viewportHeight = Math.max(1, document.documentElement.clientHeight || innerHeight);
    let left = rect.right - size;
    let top = rect.top + rect.height + gap;
    if (top + size > viewportHeight - 4) {
      left = rect.left - size - gap;
      top = rect.top + (rect.height - size) / 2;
    }
    left = Math.max(4, Math.min(viewportWidth - size - 4, left));
    top = Math.max(4, Math.min(viewportHeight - size - 4, top));
    button.style.setProperty('--twgif-trigger-left', Math.round(left) + 'px');
    button.style.setProperty('--twgif-trigger-top', Math.round(top) + 'px');
  }

  function repositionTrigger() {
    if (isTwitchSite() && clearUnavailableTwitchTrigger()) return;
    const button = document.getElementById('twgif-trigger');
    if (!button) return;
    const input = getChatInput();
    if (!input) return;
    const toolbar = getToolbar(input);
    if (!toolbar) return;
    hideDropsToolbarButtons(toolbar);
    positionTriggerForSite(input, toolbar, button);
  }

  function ensureTrigger() {
    if (isTwitchSite() && clearUnavailableTwitchTrigger()) return false;
    const input = getChatInput();
    if (!input) return false;
    activeComposer = input;
    const toolbar = getToolbar(input);
    if (!toolbar) return false;

    let button = document.getElementById('twgif-trigger');
    if (!button) button = createTrigger();
    activeTrigger = button;
    syncTriggerUploadIndicator();

    hideDropsToolbarButtons(toolbar);
    // Placement is inline for Kick/w.tv and independent for Twitch/other sites.
    positionTriggerForSite(input, toolbar, button);
    logDebug('Picker button positioned beside chat controls', {
      platform: platformDisplayName(),
      toolbar: toolbar.className || toolbar.tagName
    });
    return true;
  }

  function scheduleEnsure() {
    if (ensureQueued) return;
    ensureQueued = true;
    requestAnimationFrame(() => {
      ensureQueued = false;
      if (isTwitchSite() && clearUnavailableTwitchTrigger()) return;
      const previousComposer = activeComposer;
      const button = document.getElementById('twgif-trigger');
      if (!button?.isConnected) {
        const mounted = ensureTrigger();
        if (isTwitchSite() && mounted && activeComposer !== previousComposer) installObservers();
        return;
      }

      const input = getChatInput();
      if (!input) return;
      const toolbar = getToolbar(input);
      if (!toolbar) return;
      hideDropsToolbarButtons(toolbar);
      positionTriggerForSite(input, toolbar, button);
      if (isTwitchSite() && input !== previousComposer) installObservers();
    });
  }

  function panelMetrics() {
    const panel = document.getElementById('twgif-panel');
    if (!panel || panel.hidden) return;
    const visibleInput = getChatInput();
    const input = visibleInput || (activeComposer && activeComposer.isConnected ? activeComposer : null);
    if (!input) return;

    const inputRect = input.getBoundingClientRect();
    const region = getChatRegion(input);
    const regionRect = region && region.getBoundingClientRect
      ? region.getBoundingClientRect()
      : { top: 0, left: 0, right: innerWidth, width: innerWidth };
    const viewportWidth = Math.max(1, document.documentElement.clientWidth || innerWidth);
    const viewportHeight = Math.max(1, document.documentElement.clientHeight || innerHeight);
    const rawRegionLeft = Number.isFinite(regionRect.left) ? regionRect.left : 0;
    const rawRegionRight = Number.isFinite(regionRect.right)
      ? regionRect.right
      : rawRegionLeft + (Number.isFinite(regionRect.width) ? regionRect.width : viewportWidth);
    // Keep the panel slightly inset from both the chat boundaries and the viewport.
    const minLeft = Math.max(8, rawRegionLeft + 8);
    const maxRight = Math.min(viewportWidth - 8, rawRegionRight - 8);
    let panelLeft = minLeft;
    let availableWidth = Math.floor(maxRight - minLeft);
    if (availableWidth < 1) {
      panelLeft = 8;
      availableWidth = Math.max(1, viewportWidth - 16);
    }
    panel.style.position = 'fixed';
    panel.style.width = String(availableWidth) + 'px';

    // Keep the bottom above the chat input and stop the top edge at the top
    // of Twitch's stream-chat container.
    const chatTop = Math.max(0, Math.ceil(Number.isFinite(regionRect.top) ? regionRect.top : 0));
    const panelBottom = Math.min(Math.floor(inputRect.top - 8), Math.floor(viewportHeight - 8));
    const maxPanelHeight = Math.max(1, Math.floor(panelBottom - chatTop));
    const standardPanelHeight = Math.max(1, Math.min(520, Math.floor(viewportHeight * 0.68), maxPanelHeight));
    let savedPanelHeight = 0;
    try {
      savedPanelHeight = Number(localStorage.getItem(PANEL_HEIGHT_STORAGE_KEY)) || 0;
    } catch (_) {}
    const panelHeight = Math.max(
      standardPanelHeight,
      Math.min(savedPanelHeight > 0 ? savedPanelHeight : standardPanelHeight, maxPanelHeight)
    );
    panel.style.minHeight = String(standardPanelHeight) + 'px';
    panel.style.height = String(panelHeight) + 'px';
    panel.style.maxHeight = String(maxPanelHeight) + 'px';
    panel.style.bottom = 'auto';

    const maxLeft = Math.max(8, viewportWidth - availableWidth - 8);
    const left = Math.round(Math.max(8, Math.min(maxLeft, panelLeft)));
    const top = Math.max(chatTop, Math.round(panelBottom - panelHeight));
    panel.style.left = String(left) + 'px';
    panel.style.top = String(top) + 'px';
  }

  function repositionPanel() {
    if (!isPanelOpen()) return;
    requestAnimationFrame(panelMetrics);
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

  const PANEL_HEIGHT_STORAGE_KEY = 'twgif-panel-height-v1';

  function restorePanelSize(panel) {
    try {
      const raw = localStorage.getItem(PANEL_HEIGHT_STORAGE_KEY);
      if (!raw) return;
      const height = Number(raw);
      if (!Number.isFinite(height)) return;
      const maxHeight = Math.max(1, window.innerHeight - 16);
      const standardHeight = Math.max(1, Math.min(520, Math.floor(window.innerHeight * 0.68), maxHeight));
      panel.style.minHeight = standardHeight + 'px';
      panel.style.height = Math.max(standardHeight, Math.min(maxHeight, Math.round(height))) + 'px';
    } catch (_) {}
  }

  function savePanelSize(panel) {
    if (!panel || panel.hidden) return;
    const height = Math.round(panel.getBoundingClientRect().height);
    if (!Number.isFinite(height) || height < 100) return;
    try { localStorage.setItem(PANEL_HEIGHT_STORAGE_KEY, String(height)); } catch (_) {}
  }

  function installTopEdgeResize(panel) {
    if (!panel || panel.__twgifTopResizeInstalled) return;
    const handle = panel.querySelector('#twgif-resize-top');
    if (!handle) return;
    panel.__twgifTopResizeInstalled = true;

    let drag = null;
    const finishResize = event => {
      if (!drag) return;
      if (event) {
        event.preventDefault();
        event.stopPropagation();
      }
      try {
        if (handle.hasPointerCapture && handle.hasPointerCapture(drag.pointerId)) {
          handle.releasePointerCapture(drag.pointerId);
        }
      } catch (_) {}
      handle.removeEventListener('pointermove', moveResize);
      handle.removeEventListener('pointerup', finishResize);
      handle.removeEventListener('pointercancel', finishResize);
      panel.classList.remove('twgif-resizing');
      drag = null;
      savePanelSize(panel);
    };
    const moveResize = event => {
      if (!drag || event.pointerId !== drag.pointerId) return;
      event.preventDefault();
      event.stopPropagation();
      // Moving the pointer UP increases height; never shrink below the standard size.
      const deltaUp = drag.startY - event.clientY;
      const nextHeight = Math.max(drag.minHeight, Math.min(drag.maxHeight, Math.round(drag.startHeight + deltaUp)));
      panel.style.bottom = 'auto';
      panel.style.maxHeight = drag.maxHeight + 'px';
      panel.style.minHeight = drag.minHeight + 'px';
      panel.style.height = nextHeight + 'px';
      panel.style.top = Math.round(drag.bottom - nextHeight) + 'px';
    };

    handle.addEventListener('pointerdown', event => {
      if (event.button !== 0 || panel.hidden || drag) return;
      event.preventDefault();
      event.stopPropagation();
      const rect = panel.getBoundingClientRect();
      const input = getChatInput() || (activeComposer && activeComposer.isConnected ? activeComposer : null);
      const region = input ? getChatRegion(input) : null;
      const regionRect = region?.getBoundingClientRect ? region.getBoundingClientRect() : null;
      const chatTop = Math.max(0, Math.ceil(Number.isFinite(regionRect?.top) ? regionRect.top : 0));
      const maxHeight = Math.max(1, Math.floor(rect.bottom - chatTop));
      const minHeight = Math.max(1, Math.min(520, Math.floor(window.innerHeight * 0.68), maxHeight));
      drag = {
        pointerId: event.pointerId,
        startY: event.clientY,
        startHeight: Math.max(minHeight, rect.height),
        bottom: rect.bottom,
        minHeight,
        maxHeight
      };
      panel.classList.add('twgif-resizing');
      handle.addEventListener('pointermove', moveResize);
      handle.addEventListener('pointerup', finishResize);
      handle.addEventListener('pointercancel', finishResize);
      try { handle.setPointerCapture(event.pointerId); } catch (_) {}
    });
  }

  function installPanelResizePersistence(panel) {
    if (panel.__twgifResizePersistenceInstalled) return;
    panel.__twgifResizePersistenceInstalled = true;
    let resizeFrame = 0;
    const observer = new ResizeObserver(() => {
      if (panel.hidden || resizeFrame) return;
      resizeFrame = requestAnimationFrame(() => {
        resizeFrame = 0;
        savePanelSize(panel);
      });
    });
    observer.observe(panel);
    panel.__twgifResizeObserver = observer;
  }

  function openPanel(trigger) {
    buildPanel();
    activeTrigger = trigger || document.getElementById('twgif-trigger');
    panelView = 'gallery';
    const panel = document.getElementById('twgif-panel');
    panel.hidden = false;
    syncTriggerUploadIndicator();
    activeTrigger?.setAttribute('aria-expanded', 'true');
    renderPanelView();
    repositionPanel();
    if (loadConfig().gistToken && loadConfig().gistId) {
      syncNow().catch(error => setStatus(`Синхронизация коллекции: ${formatGitHubSyncError(error)}`, 'error'));
    }
    logDebug('Panel opened');
  }

  function closePanel() {
    const panel = document.getElementById('twgif-panel');
    if (panel) {
      savePanelSize(panel);
      panel.hidden = true;
    }
    syncTriggerUploadIndicator();
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
    const editorOpen = panel.querySelector('#twgif-media-editor-open');
    const statusIndicator = panel.querySelector('#twgif-status-indicator');

    const inSettings = panelView === 'settings';
    heading.textContent = inSettings ? 'Настройки' : 'GIF и картинки';
    settingsBack.hidden = !inSettings;
    settingsTabs.hidden = !inSettings;
    settingsOpen.hidden = inSettings;
    editorOpen.hidden = inSettings;
    statusIndicator.hidden = inSettings;
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

    updateStatusIndicator();
    syncProgressIndicatorView();
  }

  // Gallery shell: filter controls are independent from category tabs and paging.
  function renderGallery() {
    const body = document.getElementById('twgif-panel-body');
    if (!body) return;
    body.innerHTML = `
      <div class="twgif-toolbar">
        <input id="twgif-url-input" class="twgif-input twgif-url-input" type="url" placeholder="Ссылка или несколько ссылок через пробел…" autocomplete="url" aria-label="Ссылка для добавления">
        <button id="twgif-add-url" class="twgif-small-btn twgif-primary twgif-toolbar-icon" type="button" title="Добавить ссылку" aria-label="Добавить ссылку">+</button>
        <label class="twgif-compress-toggle" title="Отключить уменьшение разрешения и ограничение качества" for="twgif-compress-toggle"><input id="twgif-compress-toggle" type="checkbox" ${isCompressionEnabled() ? 'checked' : ''}>сжимать</label>
      </div>
      <div class="twgif-media-filter">
        <button id="twgif-media-filter-toggle" class="twgif-media-filter-button" type="button"
          aria-label="Фильтр медиа: Фото/Видео" title="Переключить фильтр: Фото/Видео → Фото → Видео">Фото/Видео</button>
      </div>
      <div class="twgif-gallery-tabs" role="tablist" aria-label="Категория медиа">
        <button class="twgif-gallery-tab" type="button" data-gallery-tab="all" role="tab" aria-selected="true">Все <span id="twgif-all-count" class="twgif-gallery-tab-count">0</span></button>
        <button class="twgif-gallery-tab" type="button" data-gallery-tab="hd" role="tab" aria-selected="false">HD <span id="twgif-hd-count" class="twgif-gallery-tab-count">0</span></button>
        <button class="twgif-gallery-tab" type="button" data-gallery-tab="7tv" role="tab" aria-selected="false">7TV <span id="twgif-7tv-count" class="twgif-gallery-tab-count">0</span></button>
        <button class="twgif-gallery-tab" type="button" data-gallery-tab="favorites" role="tab" aria-selected="false">Избранное <span id="twgif-favorites-count" class="twgif-gallery-tab-count">0</span></button>
      </div>
      <div id="twgif-drop" class="twgif-drop"><div><strong>Перетащи файлы или нажми Ctrl+V</strong><span>Медиа обрабатывается по правилам во вкладке конвертации</span></div><button id="twgif-file-pick" class="twgif-small-btn" type="button">Выбрать</button><input id="twgif-file-input" type="file" accept="image/*,video/*,.gif,.webm,.mp4,.mov,.mkv,.avi" multiple hidden></div>
      <div id="twgif-masonry" class="twgif-masonry"></div>
      <div id="twgif-empty" class="twgif-empty" hidden></div>
      <div id="twgif-pagination" class="twgif-pagination" hidden><button id="twgif-page-prev" class="twgif-small-btn" type="button">‹</button><span id="twgif-page-label" class="twgif-page-label"></span><button id="twgif-page-next" class="twgif-small-btn" type="button">›</button></div>
    `;

    const urlInput = body.querySelector('#twgif-url-input');
    const addButton = body.querySelector('#twgif-add-url');
    const compressToggle = body.querySelector('#twgif-compress-toggle');
    compressToggle.addEventListener('change', event => {
      try { GM_setValue(COMPRESS_ENABLED_KEY, Boolean(event.currentTarget.checked)); }
      catch (error) { logDebug('Unable to save compression toggle', error); }
    });
    const addLink = async () => {
      const links = urlInput.value.trim().split(/\s+/).filter(Boolean);
      if (!links.length) { urlInput.focus(); return; }
      if (activeProcessingRunId) {
        setStatus('Уже выполняется обработка. Дождись завершения или отмени её значком стоп у кольца прогресса.', 'info', true);
        return;
      }

      const compressEnabled = isCompressionEnabled();
      const runId = ++processingRunId;
      activeProcessingRunId = runId;
      syncTriggerUploadIndicator();
      setProgressCancelable(true);
      addButton.disabled = true;
      let added = 0;
      let skipped = 0;
      const failures = [];
      try {
        for (let i = 0; i < links.length; i++) {
          if (!isProcessingRunCurrent(runId)) break;
          const link = links[i];
          setStatus(`Добавляю ссылки: ${i + 1} из ${links.length}…`, 'info', true);
          try {
            if (await addUrl(link, '', runId, compressEnabled)) added++;
            else skipped++;
          } catch (error) {
            if (error?.name === 'AbortError' || !isProcessingRunCurrent(runId)) break;
            failures.push(`${link}: ${error.message || error}`);
            flashTriggerResult('error');
            logDebug('Bulk URL add failed', { link, error: error.message || error });
          }
        }
        if (isProcessingRunCurrent(runId)) {
          urlInput.value = '';
          urlInput.focus();
          const summary = `Добавлено: ${added}; уже есть: ${skipped}; ошибок: ${failures.length}.`;
          setStatus(failures.length
            ? summary + ' ' + failures.slice(0, 2).join(' | ')
            : summary, failures.length ? 'error' : 'success');
        }
      } finally {
        if (activeProcessingRunId === runId) {
          activeProcessingRunId = 0;
          syncTriggerUploadIndicator();
          setProgressCancelable(false);
        }
        if (isProcessingRunCurrent(runId)) finishProgress(1000);
        else setProgress(null, false);
        addButton.disabled = false;
      }
    };
    addButton.addEventListener('click', addLink);

    body.querySelectorAll('.twgif-gallery-tab').forEach(button => {
      button.addEventListener('click', () => {
        galleryTab = ['7tv', 'favorites', 'hd'].includes(button.dataset.galleryTab) ? button.dataset.galleryTab : 'all';
        galleryPage = 0;
        body.querySelectorAll('.twgif-gallery-tab').forEach(tab => {
          tab.setAttribute('aria-selected', String(tab.dataset.galleryTab === galleryTab));
        });
        renderGalleryItems();
      });
    });
    body.querySelector('#twgif-media-filter-toggle').addEventListener('click', () => {
      // One button cycles through all media, static photos, then videos/animations.
      galleryMediaType = galleryMediaType === 'all'
        ? 'photos'
        : galleryMediaType === 'photos'
          ? 'videos'
          : 'all';
      galleryPage = 0;
      renderGalleryItems();
    });

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
    card.draggable = false;
    card.tabIndex = 0;
    card.setAttribute('role', 'button');
    card.setAttribute('aria-label', 'Вставить ссылку на медиа в чат');
    card.__twgifItem = item;

    const frame = document.createElement('div');
    frame.className = 'twgif-media-frame';
    const previewUrl = item.previewUrl || item.url;
    const isVideo = isVideoGalleryItem(item);
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
    media.draggable = false;
    media.dataset.src = previewUrl;
    const cachedObjectUrl = cachedMediaObjectUrls.get(previewUrl);
    media.dataset.loadState = cachedObjectUrl || loadedMediaUrls.has(previewUrl) ? 'loaded' : 'pending';
    if (cachedObjectUrl) {
      media.src = cachedObjectUrl;
      media.dataset.loadState = 'loaded';
    } else if (loadedMediaUrls.has(previewUrl)) {
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

    const sizeBadge = document.createElement('span');
    sizeBadge.className = 'twgif-file-size';
    sizeBadge.setAttribute('aria-hidden', 'true');
    const knownSize = Math.max(0, Math.floor(Number(item.size) || mediaSizeCache.get(previewUrl) || 0));
    if (knownSize > 0) {
      sizeBadge.textContent = formatBytes(knownSize);
      mediaSizeCache.set(previewUrl, knownSize);
    } else {
      sizeBadge.hidden = true;
    }
    frame.appendChild(media);
    frame.appendChild(sizeBadge);
    const updateFileSizeBadge = async () => {
      if (!sizeBadge.isConnected || (sizeBadge.textContent && !sizeBadge.hidden)) return;
      const size = await resolveMediaSizeBytes(card.__twgifItem, previewUrl);
      if (!size || !sizeBadge.isConnected) return;
      sizeBadge.textContent = formatBytes(size);
      sizeBadge.hidden = false;
    };
    card.addEventListener('mouseenter', updateFileSizeBadge);
    card.addEventListener('focus', updateFileSizeBadge);

    let durationBadge = null;
    const isWebP = !isVideo && isLikelyWebPItem(item, previewUrl);
    if (isVideo || isWebP) {
      durationBadge = document.createElement('span');
      durationBadge.className = 'twgif-video-duration';
      durationBadge.setAttribute('aria-hidden', 'true');
      durationBadge.hidden = true;
      const updateDurationBadge = async () => {
        if (!durationBadge.isConnected || !durationBadge.hidden) return;
        const duration = isVideo
          ? (() => {
              const existingDuration = Number(media.duration);
              return Number.isFinite(existingDuration) && existingDuration >= 0
                ? Promise.resolve(existingDuration)
                : resolveVideoDuration(previewUrl);
            })()
          : resolveAnimatedWebPDuration(item, previewUrl);
        const seconds = await duration;
        if (!durationBadge.isConnected || !Number.isFinite(seconds) || seconds <= 0) return;
        durationBadge.textContent = formatVideoDuration(seconds);
        durationBadge.hidden = false;
      };
      if (isVideo) media.addEventListener('loadedmetadata', updateDurationBadge);
      card.addEventListener('mouseenter', updateDurationBadge);
      card.addEventListener('focus', updateDurationBadge);
    }
    if (durationBadge) frame.appendChild(durationBadge);
    card.appendChild(frame);

    const favorite = document.createElement('button');
    favorite.type = 'button';
    favorite.className = 'twgif-favorite';
    favorite.title = item.favorite ? 'Убрать из избранного' : 'Добавить в избранное';
    favorite.setAttribute('aria-label', favorite.title);
    favorite.setAttribute('aria-pressed', String(Boolean(item.favorite)));
    favorite.innerHTML = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M20.8 4.6a5.5 5.5 0 0 0-7.8 0L12 5.7l-1.1-1.1a5.5 5.5 0 0 0-7.8 7.8l1.1 1.1L12 21l7.8-7.5 1.1-1.1a5.5 5.5 0 0 0-.1-7.8Z"/></svg>';
    favorite.addEventListener('click', event => {
      event.preventDefault();
      event.stopPropagation();
      toggleFavorite(card.__twgifItem.id);
    });
    card.appendChild(favorite);

    const del = document.createElement('button');
    del.type = 'button';
    del.className = 'twgif-delete';
    del.title = 'Удалить из галереи';
    del.setAttribute('aria-label', 'Удалить медиа');
    del.innerHTML = '<svg viewBox="0 0 12 12" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"><path d="m3 3 6 6M9 3 3 9"/></svg>';
    del.addEventListener('click', event => { event.stopPropagation(); deleteItem(card.__twgifItem.id); });
    card.appendChild(del);

    const beginHold = event => {
      if (event.button !== undefined && event.button !== 0) return;
      if (event.target.closest('.twgif-delete, .twgif-favorite')) return;
      if (holdPointerActive) return;

      holdPointerActive = true;
      holdPointerId = event.pointerId;
      holdPreviewStarted = false;
      holdCandidateCard = card;
      holdPointerX = event.clientX;
      holdPointerY = event.clientY;
      if (holdPreviewTimer) clearTimeout(holdPreviewTimer);
      hideHoldPreview();
      holdPreviewTimer = setTimeout(() => {
        holdPreviewTimer = 0;
        if (!holdPointerActive) return;
        const target = cardUnderPointer(holdPointerX, holdPointerY) || holdCandidateCard;
        if (!target || !target.__twgifItem) return;
        holdCandidateCard = target;
        holdPreviewStarted = true;
        showHoldPreview(target.__twgifItem, target);
      }, 260);
    };
    card.addEventListener('pointerdown', beginHold);

    const insert = event => {
      if (Date.now() <= suppressMediaClickUntil) {
        event.preventDefault();
        event.stopPropagation();
        suppressMediaClickUntil = 0;
        return;
      }
      if (event.target.closest('.twgif-delete, .twgif-favorite')) return;
      insertLinkIntoChat(card.__twgifItem.url);
    };

    card.addEventListener('click', insert);
    card.addEventListener('keydown', event => {
      if (event.target.closest('.twgif-delete, .twgif-favorite')) return;
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        insertLinkIntoChat(card.__twgifItem.url);
      }
    });
    return card;
  }

  function restoreHoldPreviewMedia() {
    const saved = holdPreviewRestore;
    if (!saved) return;
    holdPreviewRestore = null;
    const { media, parent, placeholder, nextSibling, styleAttribute } = saved;
    try {
      if (parent) {
        if (placeholder && placeholder.parentNode === parent) parent.replaceChild(media, placeholder);
        else if (!parent.contains(media)) parent.insertBefore(media, nextSibling && nextSibling.parentNode === parent ? nextSibling : null);
      }
    } catch (error) {
      logDebug('Could not restore gallery media after preview', error);
    }
    if (styleAttribute === null) media.removeAttribute('style');
    else if (styleAttribute !== undefined) media.setAttribute('style', styleAttribute);
    if (media.tagName === 'VIDEO') { try { media.pause(); } catch (_) {} }
  }

  function positionHoldPreview(holder, card, media, config = loadConfig()) {
    if (!holder || !card || !media) return;
    const cardRect = card.getBoundingClientRect();
    const tileMedia = card.querySelector('.twgif-media') ||
      (holdPreviewRestore && holdPreviewRestore.card === card ? holdPreviewRestore.placeholder : null);
    const tileRect = tileMedia ? tileMedia.getBoundingClientRect() : cardRect;
    const viewportWidth = Math.max(1, document.documentElement.clientWidth || innerWidth);
    const viewportHeight = Math.max(1, document.documentElement.clientHeight || innerHeight);
    const maxDimension = clampInt(config.previewMaxSize ?? 1920, 1, 4000, 1920);
    const tileBoost = 1 + clampInt(config.previewTileBoost ?? 5, 0, 100, 5) / 100;
    const isVideo = media.tagName === 'VIDEO';
    const nativeWidth = Number(isVideo ? media.videoWidth : media.naturalWidth) || 0;
    const nativeHeight = Number(isVideo ? media.videoHeight : media.naturalHeight) || 0;
    let width;
    let height;

    if (nativeWidth > 0 && nativeHeight > 0) {
      const maxScale = Math.min(maxDimension / Math.max(nativeWidth, nativeHeight),
        (viewportWidth - 16) / nativeWidth, (viewportHeight - 16) / nativeHeight);
      const nativeScale = Math.min(1, maxScale);
      // When the original is tiny, the gallery may upscale it to fit its tile.
      // Match that on-screen size and add the configured extra percentage.
      const tileScale = tileRect.width > 0 && tileRect.height > 0
        ? Math.min(tileRect.width / nativeWidth, tileRect.height / nativeHeight)
        : 0;
      const minimumTileScale = tileScale > 0 ? tileScale * tileBoost : nativeScale;
      const scale = Math.min(maxScale, Math.max(nativeScale, minimumTileScale));
      width = Math.max(1, Math.round(nativeWidth * scale));
      height = Math.max(1, Math.round(nativeHeight * scale));
    } else {
      const fallbackRatio = cardRect.width > 0 && cardRect.height > 0 ? cardRect.height / cardRect.width : 0.75;
      width = Math.min(maxDimension, viewportWidth - 16, Math.max(180, cardRect.width * 3));
      height = width * fallbackRatio;
      const scale = Math.min(tileBoost, maxDimension / Math.max(width, height),
        (viewportWidth - 16) / width, (viewportHeight - 16) / height);
      width = Math.max(1, Math.round(width * scale));
      height = Math.max(1, Math.round(height * scale));
    }

    holder.style.width = String(width) + 'px';
    holder.style.height = String(height) + 'px';
    const left = Math.max(8, Math.min(viewportWidth - width - 8, cardRect.left + cardRect.width / 2 - width / 2));
    const top = Math.max(8, Math.min(viewportHeight - height - 8, cardRect.top + cardRect.height / 2 - height / 2));
    holder.style.left = String(Math.round(left)) + 'px';
    holder.style.top = String(Math.round(top)) + 'px';
    media.style.width = '100%';
    media.style.height = '100%';
    media.style.maxWidth = '100%';
    media.style.maxHeight = '100%';
  }

  function showHoldPreview(item, card) {
    if (!item || !card) return;
    const holder = document.getElementById('twgif-hold-preview');
    if (!holder) return;
    holdPreviewItem = item;
    holder.__twgifCard = card;
    const url = item.previewUrl || item.url;
    let parsedPath = '';
    try { parsedPath = new URL(url, location.href).pathname.toLowerCase(); } catch (_) {}
    const isVideo = item.type === 'video' || ['.webm', '.mp4', '.mov', '.mkv', '.avi', '.ogv'].some(ext => parsedPath.endsWith(ext));
    const wantedTag = isVideo ? 'VIDEO' : 'IMG';
    const config = loadConfig();
    let el = null;

    // If the same tile is already in the preview holder, keep using that exact node.
    if (holdPreviewRestore && holdPreviewRestore.card === card && holdPreviewRestore.url === url &&
        holdPreviewRestore.media.tagName === wantedTag) {
      el = holdPreviewRestore.media;
    } else {
      if (holdPreviewRestore) restoreHoldPreviewMedia();

      // Move the already-loaded tile media into the popup instead of creating a second
      // IMG/VIDEO pointed at the remote URL. This avoids repeat fetches and re-decodes.
      const tileMedia = card.querySelector('.twgif-media');
      if (tileMedia && tileMedia.dataset.src === url && tileMedia.tagName === wantedTag &&
          tileMedia.dataset.loadState !== 'error' && tileMedia.parentNode) {
        const parent = tileMedia.parentNode;
        const rect = tileMedia.getBoundingClientRect();
        const placeholder = document.createElement('span');
        placeholder.className = 'twgif-media-placeholder';
        placeholder.style.cssText = `display:block;width:${Math.max(0, rect.width)}px;height:${Math.max(0, rect.height)}px;flex:0 0 auto;`;
        const saved = {
          media: tileMedia, parent, placeholder, nextSibling: tileMedia.nextSibling,
          styleAttribute: tileMedia.getAttribute('style'), card, url
        };
        parent.replaceChild(placeholder, tileMedia);
        holder.replaceChildren(tileMedia);
        holdPreviewRestore = saved;
        el = tileMedia;
        const updateSize = () => {
          if (holdPreviewItem && holdPreviewItem.id === item.id && holder.firstElementChild === el) {
            positionHoldPreview(holder, card, el, config);
          }
        };
        el.addEventListener(isVideo ? 'loadedmetadata' : 'load', updateSize, { once: true });
      } else {
        // Fallback for missing/failed tile nodes; normal cards use the borrowed node above.
        const current = holder.firstElementChild;
        const currentType = current && current.tagName === 'VIDEO' ? 'video' : 'image';
        const wantedType = isVideo ? 'video' : 'image';
        if (!current || holder.dataset.currentUrl !== url || currentType !== wantedType) {
          holder.replaceChildren();
          el = document.createElement(isVideo ? 'video' : 'img');
          if (isVideo) {
            el.muted = true; el.loop = true; el.autoplay = true; el.playsInline = true; el.preload = 'metadata';
          } else {
            el.alt = '';
            el.decoding = 'async';
          }
          const updateSize = () => {
            if (holdPreviewItem && holdPreviewItem.id === item.id && holder.firstElementChild === el) {
              positionHoldPreview(holder, card, el, config);
            }
          };
          el.addEventListener(isVideo ? 'loadedmetadata' : 'load', updateSize);
          el.addEventListener('error', () => {
            if (holder.firstElementChild === el) {
              holder.style.width = 'min(320px, calc(100vw - 16px))';
              holder.style.height = 'auto';
            }
          }, { once: true });
          holder.dataset.currentUrl = url;
          holder.appendChild(el);
          el.src = url;
        } else {
          el = current;
        }
      }
    }

    holder.dataset.currentUrl = url;
    positionHoldPreview(holder, card, el, config);
    if (isVideo && typeof el.play === 'function') el.play().catch(() => {});
    requestAnimationFrame(() => {
      positionHoldPreview(holder, card, el, config);
      holder.classList.add('twgif-preview-visible');
    });
  }
  function hideHoldPreview() {
    const holder = document.getElementById('twgif-hold-preview');
    if (!holder) return;
    holder.classList.remove('twgif-preview-visible');
    holdPreviewItem = null;
    const media = holder.firstElementChild;
    if (media && media.tagName === 'VIDEO') { try { media.pause(); } catch (_) {} }
    // Return the exact media element to its tile, retaining its decoded image/video buffer.
    if (holdPreviewRestore) restoreHoldPreviewMedia();
    // Fallback previews remain attached so they can be reused without refetching.
  }

  function cardUnderPointer(x, y) {
    const target = document.elementFromPoint(x, y);
    return target && target.closest ? target.closest('.twgif-card') : null;
  }

  function updateHeldPreview(event) {
    if (!holdPointerActive || event.pointerId !== holdPointerId) return;
    if (event.pointerType === 'mouse' && !(event.buttons & 1)) {
      finishHeldPreview(event);
      return;
    }
    holdPointerX = event.clientX;
    holdPointerY = event.clientY;
    const target = cardUnderPointer(holdPointerX, holdPointerY);
    if (!target || !target.__twgifItem) return;
    const changedCard = holdCandidateCard !== target;
    holdCandidateCard = target;
    if (holdPreviewStarted && changedCard) showHoldPreview(target.__twgifItem, target);
  }

  function finishHeldPreview(event) {
    if (!holdPointerActive) return;
    if (event && event.pointerId != null && event.pointerId !== holdPointerId) return;
    if (holdPreviewTimer) clearTimeout(holdPreviewTimer);
    holdPreviewTimer = 0;
    if (holdPreviewStarted) suppressMediaClickUntil = Date.now() + 350;
    holdPointerActive = false;
    holdPointerId = null;
    holdPreviewStarted = false;
    holdCandidateCard = null;
    hideHoldPreview();
  }

  async function loadCardMedia(card, token) {
    const media = card.querySelector('.twgif-media');
    if (!media || media.dataset.loadState === 'loaded' || media.dataset.loadState === 'error' || media.src) return;
    if (token !== mediaLoadRun) return;
    const url = media.dataset.src;
    if (!url) return;
    media.dataset.loadState = 'loading';
    const video = media.tagName === 'VIDEO';
    let cachedBlob = await getCachedMediaBlob(url);
    if (!cachedBlob) {
      cachedBlob = await getSharedMediaBlob(url);
      if (cachedBlob) cacheMediaBlob(url, cachedBlob);
    }
    if (token !== mediaLoadRun) return;
    const sourceUrl = cachedBlob ? cachedObjectUrlFor(url, cachedBlob) : url;
    const promise = new Promise(resolve => {
      let settled = false;
      const done = () => { if (!settled) { settled = true; resolve(); } };
      media.addEventListener(video ? 'loadedmetadata' : 'load', done, { once: true });
      media.addEventListener('error', done, { once: true });
      setTimeout(done, video ? 1800 : 12000);
    });
    media.src = sourceUrl;
    if (video) media.load();
    await promise;
    if (token !== mediaLoadRun) return;
    if (media.naturalWidth > 0 || media.videoWidth > 0) {
      media.dataset.loadState = 'loaded';
      loadedMediaUrls.add(url);
      if (!cachedBlob) cacheRemoteMedia(url, video);
      else cacheSharedMediaBlob(url, cachedBlob);
    }
  }

  async function loadVisibleMediaSequentially(cards) {
    const token = ++mediaLoadRun;
    for (const card of cards) {
      if (token !== mediaLoadRun) return;
      await loadCardMedia(card, token);
    }
  }

  function ensureGalleryResizeObserver() {
    if (galleryResizeObserver || typeof ResizeObserver !== 'function') return;
    galleryResizeObserver = new ResizeObserver(entries => {
      for (const entry of entries) {
        const card = entry.target;
        const masonry = card.parentElement;
        if (!masonry || !masonry.classList.contains('twgif-masonry') ||
            masonry.classList.contains('twgif-grid-mode') || card.hidden) continue;
        const height = card.getBoundingClientRect().height;
        const rowGap = Number.parseFloat(getComputedStyle(masonry).rowGap) || 0;
        const span = Math.max(1, Math.ceil((height + rowGap) / (0.25 + rowGap)));
        if (card.__twgifGridSpan !== span) {
          card.__twgifGridSpan = span;
          card.style.gridRowEnd = 'span ' + span;
        }
      }
    });
  }

  // Gallery renderer: reuse cached cards/media nodes to avoid restarting decoded image/video data.
  function renderGalleryItems() {
    const body = document.getElementById('twgif-panel-body');
    if (!body || panelView !== 'gallery') return;
    const masonry = body.querySelector('#twgif-masonry');
    const empty = body.querySelector('#twgif-empty');
    const pagination = body.querySelector('#twgif-pagination');
    const pageLabel = body.querySelector('#twgif-page-label');
    const prev = body.querySelector('#twgif-page-prev');
    const next = body.querySelector('#twgif-page-next');
    if (!masonry || !empty || !pagination) return;

    const config = loadConfig();
    masonry.classList.toggle('twgif-grid-mode', config.tileView === 'grid');
    // Number of columns directly controls the number of media tiles across the gallery.
    const gap = 6;
    masonry.style.setProperty('--twgif-columns', String(config.columns));
    masonry.style.setProperty('--twgif-thumb-height', '90px');
    masonry.style.columnGap = `${gap}px`;
    masonry.style.rowGap = `${gap}px`;
    masonry.style.gap = `${gap}px`;
    masonry.style.gridAutoRows = config.tileView === 'grid' ? 'auto' : '0.25px';

    const data = loadData();
    const storedItems = data.items.slice().sort(compareGalleryItems);
    const allItems = storedItems.filter(item => !is7TVGalleryItem(item));
    const sevenTvItems = storedItems.filter(is7TVGalleryItem);
    const hdItems = allItems.filter(item => item.hd);
    const favoriteItems = storedItems.filter(item => item.favorite);
    const allTab = body.querySelector('[data-gallery-tab="all"]');
    const hdTab = body.querySelector('[data-gallery-tab="hd"]');
    const sevenTvTab = body.querySelector('[data-gallery-tab="7tv"]');
    const favoritesTab = body.querySelector('[data-gallery-tab="favorites"]');
    if (allTab) allTab.setAttribute('aria-selected', String(galleryTab === 'all'));
    if (hdTab) hdTab.setAttribute('aria-selected', String(galleryTab === 'hd'));
    if (sevenTvTab) sevenTvTab.setAttribute('aria-selected', String(galleryTab === '7tv'));
    if (favoritesTab) favoritesTab.setAttribute('aria-selected', String(galleryTab === 'favorites'));
    const allCount = body.querySelector('#twgif-all-count');
    const hdCount = body.querySelector('#twgif-hd-count');
    const sevenTvCount = body.querySelector('#twgif-7tv-count');
    const favoritesCount = body.querySelector('#twgif-favorites-count');
    if (allCount) allCount.textContent = String(allItems.length);
    if (hdCount) hdCount.textContent = String(hdItems.length);
    if (sevenTvCount) sevenTvCount.textContent = String(sevenTvItems.length);
    if (favoritesCount) favoritesCount.textContent = String(favoriteItems.length);
    const categoryItems = galleryTab === '7tv' ? sevenTvItems
      : galleryTab === 'hd' ? hdItems
      : galleryTab === 'favorites' ? favoriteItems
      : allItems;
    const mediaFilterButton = body.querySelector('#twgif-media-filter-toggle');
    if (mediaFilterButton) {
      const labels = { all: 'Фото/Видео', photos: 'Фото', videos: 'Видео' };
      const label = labels[galleryMediaType] || labels.all;
      mediaFilterButton.textContent = label;
      mediaFilterButton.dataset.filterMode = galleryMediaType;
      mediaFilterButton.setAttribute('aria-label', 'Фильтр медиа: ' + label);
      mediaFilterButton.title = 'Следующий фильтр: ' +
        (galleryMediaType === 'all' ? 'Фото' : galleryMediaType === 'photos' ? 'Видео' : 'Фото/Видео');
    }
    if (galleryMediaType === 'videos') scheduleAnimatedWebPClassification(categoryItems);
    const items = galleryMediaType === 'all'
      ? categoryItems
      : categoryItems.filter(item => galleryMediaType === 'videos'
        ? isAnimatedMediaItem(item)
        : !isAnimatedMediaItem(item));
    const pageSize = config.pageSize;
    const pages = Math.max(1, Math.ceil(items.length / pageSize));
    galleryPage = Math.max(0, Math.min(galleryPage, pages - 1));
    const start = galleryPage * pageSize;
    const visible = items.slice(start, start + pageSize);
    const visibleIds = new Set(visible.map(item => item.id));

    // Preserve card/image DOM nodes across sync refreshes and page switches.
    // Reorder only when the visible page actually changes; repeatedly appending
    // already-mounted <img> nodes can force browsers to drop decoded image data.
    const itemIds = new Set(storedItems.map(item => item.id));
    const orderedVisibleCards = [];
    if (config.tileView !== 'grid') ensureGalleryResizeObserver();
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
          const cachedObjectUrl = cachedMediaObjectUrls.get(newPreview);
          media.dataset.loadState = cachedObjectUrl || loadedMediaUrls.has(newPreview) ? 'loaded' : 'pending';
          if (cachedObjectUrl) media.src = cachedObjectUrl;
          else if (loadedMediaUrls.has(newPreview)) media.src = newPreview;
          else { media.removeAttribute('src'); }
        }
        if (oldItem.url !== item.url) card.setAttribute('aria-label', 'Вставить ссылку на медиа в чат');
      }
      const favoriteButton = card.querySelector('.twgif-favorite');
      if (favoriteButton) {
        favoriteButton.setAttribute('aria-pressed', String(Boolean(item.favorite)));
        favoriteButton.title = item.favorite ? 'Убрать из избранного' : 'Добавить в избранное';
        favoriteButton.setAttribute('aria-label', favoriteButton.title);
      }
      card.hidden = false;
      if (config.tileView === 'grid') {
        card.style.gridRowEnd = 'auto';
        delete card.__twgifGridSpan;
      } else {
        if (!card.style.gridRowEnd || card.style.gridRowEnd === 'auto') {
          card.style.gridRowEnd = 'span 1';
          card.__twgifGridSpan = 1;
        }
        if (galleryResizeObserver) galleryResizeObserver.observe(card);
      }
      orderedVisibleCards.push(card);
    }

    for (let i = 0; i < orderedVisibleCards.length; i++) {
      const card = orderedVisibleCards[i];
      const currentAtPosition = masonry.children[i];
      if (currentAtPosition !== card) masonry.insertBefore(card, currentAtPosition || null);
    }

    for (const [id, card] of mediaCardCache) {
      if (!itemIds.has(id)) {
        if (galleryResizeObserver) galleryResizeObserver.unobserve(card);
        card.remove();
        mediaCardCache.delete(id);
      } else if (!visibleIds.has(id)) {
        card.hidden = true;
      }
    }

    masonry.hidden = visible.length === 0;
    empty.hidden = visible.length > 0;
    const webpClassificationPending = galleryMediaType === 'videos' &&
      categoryItems.some(item => {
        const url = getItemWebPUrl(item);
        return url && animatedWebPClassificationPending.has(url);
      });
    empty.textContent = webpClassificationPending
      ? 'Проверяю WebP на анимацию…'
      : galleryMediaType === 'photos'
        ? 'В выбранной категории нет статичных изображений.'
        : galleryMediaType === 'videos'
          ? 'В выбранной категории нет видео или анимаций.'
        : galleryTab === '7tv'
          ? 'В коллекции пока нет ссылок 7TV.'
          : galleryTab === 'hd'
            ? 'Пока нет HD-медиа. Сними галочку «сжимать» и добавь файлы.'
            : galleryTab === 'favorites'
              ? 'Пока нет избранных медиа. Нажми сердечко на карточке.'
              : 'Коллекция пуста. Добавь ссылку или перетащи файл.';

    pagination.hidden = items.length <= pageSize;
    pageLabel.textContent = `Стр. ${galleryPage + 1} / ${pages}`;
    prev.disabled = galleryPage === 0;
    next.disabled = galleryPage >= pages - 1;
    prev.onclick = () => { if (galleryPage > 0) { galleryPage--; renderGalleryItems(); } };
    next.onclick = () => { if (galleryPage < pages - 1) { galleryPage++; renderGalleryItems(); } };

    loadVisibleMediaSequentially(visible.map(item => mediaCardCache.get(item.id)));
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
            <label class="twgif-field-label" for="twgif-columns">Количество столбцов</label>
            <select id="twgif-columns" class="twgif-input">
              ${targetOptions(String(config.columns), [['1','1 столбец'],['2','2 столбца'],['3','3 столбца'],['4','4 столбца'],['5','5 столбцов']])}
            </select>
            <div class="twgif-help">Определяет, сколько медиа располагается по горизонтали.</div>
            <label class="twgif-field-label" for="twgif-tile-view">Вид плиток</label>
            <select id="twgif-tile-view" class="twgif-input">
              <option value="masonry" ${config.tileView === 'masonry' ? 'selected' : ''}>Плотная мозаика</option>
              <option value="grid" ${config.tileView === 'grid' ? 'selected' : ''}>Ровная сетка</option>
            </select>
            <label class="twgif-field-label" for="twgif-page-size">Медиа на странице (10–500)</label>
            <input id="twgif-page-size" class="twgif-input" type="number" min="10" max="500" step="10" value="${config.pageSize}">
            <label class="twgif-field-label" for="twgif-preview-max-size">Максимальный размер предпросмотра (px)</label>
            <input id="twgif-preview-max-size" class="twgif-input" type="number" min="10" max="4000" step="1" value="${config.previewMaxSize}">
            <label class="twgif-field-label" for="twgif-preview-tile-boost">Увеличение превью относительно плитки (%)</label>
            <input id="twgif-preview-tile-boost" class="twgif-input" type="number" min="0" max="100" step="1" value="${config.previewTileBoost}">
            <div class="twgif-help">Если исходник маленький, при зажатии кнопки превью будет минимум на указанный процент крупнее его изображения в плитке. Максимальный размер и границы экрана соблюдаются.</div>
            <div class="twgif-row" style="margin-top:8px">
              <button id="twgif-save-gallery-settings" class="twgif-small-btn twgif-primary" type="button">Применить</button>
              <button id="twgif-reset-defaults" class="twgif-small-btn" type="button">Настройки по умолчанию</button>
            </div>
          </div>
          <div class="twgif-section">
            <div class="twgif-section-title">О приложении</div>
            <div class="twgif-help">Версия приложения: <strong>${APP_VERSION}</strong></div>
          </div>
        </div>`;
    } else if (settingsTab === 'convert') {
      const compression = config.compression;
      content = '<div class="twgif-settings">' +
        '<div class="twgif-section">' +
          '<div class="twgif-section-title">Форматы и разрешение</div>' +
          '<label class="twgif-field-label" for="twgif-max-width">Максимальная сторона фото/GIF/анимации (px)</label>' +
          '<input id="twgif-max-width" class="twgif-input" type="number" min="100" max="4000" step="50" value="' + config.maxWidth + '">' +
          '<label class="twgif-field-label" for="twgif-video-max-width">Максимальная сторона видео (px)</label>' +
          '<input id="twgif-video-max-width" class="twgif-input" type="number" min="240" max="4000" step="80" value="' + compression.videoMaxWidth + '">' +
          '<label class="twgif-field-label" for="twgif-rule-image">Обычные изображения →</label>' +
          '<select id="twgif-rule-image" class="twgif-input">' + targetOptions(config.conversionRules.image, [['keep','Оставить оригинал'],['webp','WebP'],['jpg','JPG'],['png','PNG'],['gif','GIF'],['mp4','MP4 (2 секунды)'],['webm','WebM (2 секунды)']]) + '</select>' +
          '<label class="twgif-field-label" for="twgif-rule-gif">GIF →</label>' +
          '<select id="twgif-rule-gif" class="twgif-input">' + targetOptions(config.conversionRules.gif, [['keep','Оставить оригинал'],['gif','GIF'],['webp','Анимированный WebP'],['mp4','MP4'],['webm','WebM'],['jpg','JPG (первый кадр)'],['png','PNG (первый кадр)']]) + '</select>' +
          '<label class="twgif-field-label" for="twgif-rule-video">Видео →</label>' +
          '<select id="twgif-rule-video" class="twgif-input">' + targetOptions(config.conversionRules.video, [['keep','Оставить оригинал'],['webp','Анимированный WebP'],['gif','GIF'],['mp4','MP4'],['webm','WebM'],['jpg','JPG (первый кадр)'],['png','PNG (первый кадр)']]) + '</select>' +
        '</div>' +
        '<div class="twgif-section">' +
          '<div class="twgif-section-title">Сжатие фото</div>' +
          '<label class="twgif-field-label" for="twgif-image-quality">Качество JPG/WebP (30–100%)</label>' +
          '<input id="twgif-image-quality" class="twgif-input" type="number" min="30" max="100" step="1" value="' + compression.imageQuality + '">' +
          '<div class="twgif-help">Меньше качество — меньше файл. PNG остаётся без потерь. Обычные фото кодируются Canvas для скорости.</div>' +
        '</div>' +
        '<div class="twgif-section">' +
          '<div class="twgif-section-title">Сжатие видео и анимаций</div>' +
          '<label class="twgif-field-label" for="twgif-video-fps">FPS для MP4/WebM (5–60)</label>' +
          '<input id="twgif-video-fps" class="twgif-input" type="number" min="5" max="60" step="1" value="' + compression.videoFps + '">' +
          '<label class="twgif-field-label" for="twgif-animation-fps">FPS для GIF/анимированного WebP (3–30)</label>' +
          '<input id="twgif-animation-fps" class="twgif-input" type="number" min="3" max="30" step="1" value="' + compression.animationFps + '">' +
          '<label class="twgif-field-label" for="twgif-animation-quality">Качество анимированного WebP (10–100%)</label>' +
          '<input id="twgif-animation-quality" class="twgif-input" type="number" min="10" max="100" step="1" value="' + compression.animationQuality + '">' +
          '<label class="twgif-field-label" for="twgif-video-bitrate">Битрейт видео (кбит/с; 0 = автоматически)</label>' +
          '<input id="twgif-video-bitrate" class="twgif-input" type="number" min="0" max="20000" step="100" value="' + compression.videoBitrateKbps + '">' +
          '<label class="twgif-field-label" for="twgif-video-crf">Качество видео CRF (18–40; ниже = лучше)</label>' +
          '<input id="twgif-video-crf" class="twgif-input" type="number" min="18" max="40" step="1" value="' + compression.videoCrf + '">' +
          '<label class="twgif-field-label" for="twgif-audio-bitrate">Битрейт аудио (кбит/с)</label>' +
          '<input id="twgif-audio-bitrate" class="twgif-input" type="number" min="32" max="320" step="16" value="' + compression.audioBitrateKbps + '">' +
          '<label class="twgif-field-label" for="twgif-speed-preset">Скорость кодирования</label>' +
          '<select id="twgif-speed-preset" class="twgif-input">' + targetOptions(compression.speedPreset, [['ultrafast','Максимальная скорость (файл больше)'],['superfast','Очень быстро'],['veryfast','Быстро'],['fast','Средне-быстро'],['medium','Медленнее, эффективнее сжатие']]) + '</select>' +
          '<label class="twgif-field-label" for="twgif-scale-filter">Фильтр изменения размера</label>' +
          '<select id="twgif-scale-filter" class="twgif-input">' + targetOptions(compression.scaleFilter, [['fast_bilinear','Самый быстрый'],['bilinear','Сбалансированный'],['bicubic','Более чёткий'],['lanczos','Лучшее качество, медленнее']]) + '</select>' +
          '<label class="twgif-field-label" for="twgif-webp-effort">Усилие сжатия WebP (0–6; меньше = быстрее)</label>' +
          '<input id="twgif-webp-effort" class="twgif-input" type="number" min="0" max="6" step="1" value="' + compression.webpCompressionLevel + '">' +
          '<div class="twgif-help">Битрейт задаёт целевой размер видео; CRF регулирует качество в режиме CRF. Эта сборка FFmpeg.wasm однопоточная.</div>' +
          '<div class="twgif-row" style="margin-top:8px">' +
            '<button id="twgif-save-convert" class="twgif-small-btn twgif-primary" type="button">Сохранить настройки сжатия</button>' +
            '<button id="twgif-reset-convert-defaults" class="twgif-small-btn" type="button">Сбросить по умолчанию</button>' +
          '</div>' +
        '</div></div>';

    } else if (settingsTab === 'sync') {
      content = `
        <div class="twgif-settings">
          <div class="twgif-section">
            <div class="twgif-section-title">Синхронизация коллекции</div>
            <label class="twgif-field-label" for="twgif-gist-token">GitHub token (доступ gist)</label>
            <input id="twgif-gist-token" name="twgif-github-gist-token" class="twgif-input" type="text" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" data-1p-ignore="true" data-lpignore="true" data-bwignore="true" data-form-type="other" style="-webkit-text-security:disc" placeholder="GitHub token" value="${escapeAttr(config.gistToken)}">
            <label class="twgif-field-label" for="twgif-gist-id">ID Gist</label>
            <input id="twgif-gist-id" class="twgif-input" type="text" autocomplete="off" spellcheck="false" placeholder="ID Gist" value="${escapeAttr(config.gistId)}">
            <div class="twgif-help"><b>Первое устройство:</b> создай GitHub token с разрешением <code>gist</code>, вставь его сюда, оставь ID Gist пустым и нажми «Создать Gist». Затем нажми «Синхронизировать галерею».</div>
            <div class="twgif-help"><b>Другое устройство:</b> введи <b>тот же GitHub token</b> и <b>тот же ID Gist</b>, которые использовались на первом устройстве. Нажми «Сохранить доступ», затем «Синхронизировать галерею». ID Gist — длинная строка из URL Gist; сам GitHub token автоматически на другие устройства не переносится.</div>
            <div class="twgif-help">Gist хранит только данные коллекции. Настройки отображения и конвертации сохраняются локально на этом устройстве. Secret Gist не является приватным для людей, знающих его URL. GitHub token в Gist не записывается.</div>
            <div class="twgif-row" style="margin-top:8px">
              <button id="twgif-save-gist" class="twgif-small-btn" type="button">Сохранить доступ</button>
              <button id="twgif-create-gist" class="twgif-small-btn" type="button">Создать Gist</button>
              <button id="twgif-sync-now" class="twgif-small-btn" type="button">Синхронизировать галерею</button>
            </div>
            <div class="twgif-help"><a href="https://github.com/settings/tokens/new?scopes=gist&description=Twitch%20GIF%20Gallery" target="_blank" rel="noopener noreferrer">Создать GitHub-токен с разрешением gist</a>.</div>
          </div>
        </div>`;
    } else {
      content = `
        <div class="twgif-settings">
          <div class="twgif-section">
            <div class="twgif-section-title">Журнал и резервная копия</div>
            <label class="twgif-check-row"><input id="twgif-debug-toggle" type="checkbox" ${config.debug ? 'checked' : ''}> Подробные записи в консоль и журнал</label>
            <div class="twgif-row" style="margin:7px 0"><button id="twgif-copy-debug" class="twgif-small-btn" type="button">Копировать журнал</button><button id="twgif-clear-debug" class="twgif-small-btn" type="button">Очистить журнал</button><button id="twgif-export" class="twgif-small-btn" type="button">Экспорт JSON</button><button id="twgif-import" class="twgif-small-btn" type="button">Импорт JSON</button><input id="twgif-import-file" type="file" accept="application/json,.json" hidden></div>
            <div id="twgif-debug-log" class="twgif-debug-log" role="log" aria-live="off" aria-label="Журнал событий"></div>
            <div class="twgif-help">Токены не записываются в журнал. Экспорт JSON включает коллекцию, но не API-токены.</div>
          </div>
        </div>`;
    }

    body.innerHTML = content;
    const $ = selector => body.querySelector(selector);

    if (settingsTab === 'general') {
      $('#twgif-save-gallery-settings').addEventListener('click', () => {
        saveConfig({
          columns: $('#twgif-columns').value,
          pageSize: $('#twgif-page-size').value,
          tileView: $('#twgif-tile-view').value,
          previewMaxSize: $('#twgif-preview-max-size').value,
          previewTileBoost: $('#twgif-preview-tile-boost').value
        });
        galleryPage = 0;
        setStatus('Настройки галереи сохранены.', 'success');
      });
      $('#twgif-reset-defaults').addEventListener('click', () => {
        const current = loadConfig();
        saveConfig({
          ...DEFAULT_CONFIG(),
          gistToken: current.gistToken,
          gistId: current.gistId
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
          compression: {
            imageQuality: $('#twgif-image-quality').value,
            videoMaxWidth: $('#twgif-video-max-width').value,
            videoFps: $('#twgif-video-fps').value,
            animationFps: $('#twgif-animation-fps').value,
            animationQuality: $('#twgif-animation-quality').value,
            videoBitrateKbps: $('#twgif-video-bitrate').value,
            videoCrf: $('#twgif-video-crf').value,
            audioBitrateKbps: $('#twgif-audio-bitrate').value,
            speedPreset: $('#twgif-speed-preset').value,
            scaleFilter: $('#twgif-scale-filter').value,
            webpCompressionLevel: $('#twgif-webp-effort').value
          }
        });
        setStatus('Правила форматов и сжатия сохранены на этом устройстве.', 'success');
      });
      $('#twgif-reset-convert-defaults').addEventListener('click', () => {
        const defaults = DEFAULT_CONFIG();
        saveConfig({
          maxWidth: defaults.maxWidth,
          conversionRules: { ...defaults.conversionRules },
          compression: { ...defaults.compression }
        });
        renderSettings();
        setStatus('Настройки конвертации сброшены к значениям по умолчанию.', 'success', true);
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
          setStatus(`Gist создан: ${id}. Теперь можно синхронизировать коллекцию.`, 'success');
        } catch (error) {
          setStatus(`Не удалось создать Gist: ${formatGitHubSyncError(error)}`, 'error', true);
        } finally { button.disabled = false; }
      });
      $('#twgif-sync-now').addEventListener('click', async () => {
        saveConfig({ gistToken: $('#twgif-gist-token').value, gistId: $('#twgif-gist-id').value });
        try { await syncNow(); } catch (error) { setStatus(`Синхронизация галереи: ${formatGitHubSyncError(error)}`, 'error', true); }
      });

    }

    if (settingsTab === 'debug') {
      renderDebugLog($('#twgif-debug-log'));
      $('#twgif-debug-toggle').addEventListener('change', event => {
        saveConfig({ debug: event.currentTarget.checked });
        logDebug(`Debug mode ${event.currentTarget.checked ? 'enabled' : 'disabled'}`);
        setStatus(`Отладка ${event.currentTarget.checked ? 'включена' : 'выключена'}.`, 'success');
      });
      $('#twgif-copy-debug').addEventListener('click', async () => {
        const text = debugLogs.join('\n') || 'Журнал пуст.';
        try { await navigator.clipboard.writeText(text); setStatus('Журнал скопирован.', 'success'); }
        catch (_) {
          const fallback = document.createElement('textarea');
          fallback.className = 'twgif-input';
          fallback.rows = 5;
          fallback.value = text;
          fallback.setAttribute('aria-label', 'Текст журнала для ручного копирования');
          $('#twgif-debug-log').after(fallback);
          fallback.focus();
          fallback.select();
          setStatus('Автокопирование недоступно. Журнал выделен — нажми Ctrl+C.', 'info');
        }
      });
      $('#twgif-clear-debug').addEventListener('click', () => {
        debugLogs.length = 0;
        $('#twgif-debug-log').replaceChildren();
        debugLogEntries.length = 0;
        lastLogSignature = '';
        lastLogTimestamp = 0;
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

  document.addEventListener('pointermove', updateHeldPreview, true);
  document.addEventListener('pointerup', finishHeldPreview, true);
  document.addEventListener('pointercancel', finishHeldPreview, true);
  document.addEventListener('dragstart', event => {
    if (event.target && event.target.closest && event.target.closest('.twgif-card')) event.preventDefault();
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
    if (document.visibilityState === 'visible') {
      showPendingTriggerResult();
      if (isPanelOpen() && panelView === 'gallery') {
        // Resume the sequential loader after browser timer throttling, without resetting src.
        renderGalleryItems();
      }
    }
  });
  window.addEventListener('focus', showPendingTriggerResult);

  window.addEventListener('resize', () => {
    repositionTrigger();
    repositionPanel();
    if (isPanelOpen() && panelView === 'gallery') renderGalleryItems();
    if (holdPreviewItem) {
      const holder = document.getElementById('twgif-hold-preview');
      if (holder && holder.firstElementChild && holder.__twgifCard) {
        positionHoldPreview(holder, holder.__twgifCard, holder.firstElementChild);
      }
    }
  }, { passive: true });
  window.addEventListener('scroll', repositionTrigger, { capture: true, passive: true });
  window.addEventListener('popstate', () => {
    if (isTwitchSite()) setTimeout(scheduleEnsure, 150);
  });
  document.addEventListener('click', event => {
    if (!isTwitchSite()) return;
    const link = event.target?.closest?.('a[href]');
    if (!link) return;
    let targetHost = '';
    try { targetHost = new URL(link.href, location.href).hostname; } catch (_) {}
    if (/(^|\.)twitch\.tv$/i.test(targetHost)) {
      // Twitch navigation is SPA-based; re-check once the route's React tree updates.
      setTimeout(scheduleEnsure, 500);
    }
  }, true);
  // The popup stays fixed where it was opened; only the toolbar icon follows Twitch layout changes.

  // Lifecycle watchers recover the toolbar and chat media controls after site SPA updates.
  function installObservers() {
    if (observer) observer.disconnect();
    const target = getChatInput();

    if (isTwitchSite()) {
      // Keep one lightweight document-level observer for Twitch SPA stream changes.
      // Twitch replaces the chat composer itself when switching channels, which
      // would disconnect a local-only observer forever.
      if (!twitchLifecycleObserver) {
        twitchLifecycleObserver = new MutationObserver(records => {
          if (isTwitchRecordingPage()) return;
          const currentComposer = activeComposer;
          const currentTrigger = document.getElementById('twgif-trigger');
          const relevantSelector =
            '[data-a-target="chat-input"], [data-a-target="chat-input-container"], ' +
            '[data-a-target="chat-room-component-layout"], .chat-input__buttons-container';

          const containsRelevantChatNode = node => {
            if (!node || node.nodeType !== 1) return false;
            if (node.id === 'twgif-trigger' ||
                node === currentComposer || (currentComposer && node.contains(currentComposer)) ||
                node === currentTrigger || (currentTrigger && node.contains(currentTrigger))) return true;
            if (node.matches(relevantSelector)) return true;
            // Avoid walking Twitch's frequently-mutated message list.
            if (node.matches('[data-a-target="chat-scrollable-area__message-container"], [data-a-target^="chat-line"], [class*="chat-line__message"]')) return false;
            return Boolean(node.querySelector(relevantSelector));
          };

          for (const record of records) {
            if (record.type !== 'childList') continue;
            // A removed composer or toolbar means Twitch is replacing the chat UI.
            if (Array.from(record.removedNodes || []).some(containsRelevantChatNode) ||
                Array.from(record.addedNodes || []).some(containsRelevantChatNode)) {
              scheduleEnsure();
              return;
            }
          }
        });
        twitchLifecycleObserver.observe(document.body || document.documentElement, {
          childList: true,
          subtree: true
        });
      }
    }

    if (target) {
      const toolbar = getToolbar(target);
      const localRoot = toolbar?.parentElement || toolbar || target.parentElement;
      if (localRoot) {
        observer = new MutationObserver(() => scheduleEnsure());
        const visibilityAttributes = {
          attributes: true,
          attributeFilter: ['class', 'style', 'hidden', 'aria-hidden']
        };
        observer.observe(localRoot, {
          childList: true,
          subtree: true,
          ...visibilityAttributes
        });
        if (isTwitchSite()) {
          // Observe current chat ancestors so collapse/expand style changes are detected.
          const watched = new Set([localRoot]);
          for (const startNode of [target, toolbar]) {
            let node = startNode;
            let depth = 0;
            while (node && node !== document.body && depth++ < 12) {
              if (!watched.has(node)) {
                observer.observe(node, visibilityAttributes);
                watched.add(node);
              }
              node = node.parentElement;
            }
          }
        }
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
    // Recover from orphaned max-z-index overlays left by an interrupted previous run.
    clearStaleMediaEditorOverlays();
    // Remove the old chat-toolbar editor icon left by a previously injected script version.
    document.getElementById('twgif-editor-trigger')?.remove();
    buildStyles();
    buildPanel();
    ensureTrigger();
    installObservers();
    installChatMediaObserver();

    // GM storage is script-scoped rather than page-origin-scoped, so this keeps
    // already-open Twitch, Kick and w.tv gallery panels in sync across tabs.
    if (typeof GM_addValueChangeListener === 'function') {
      try {
        GM_addValueChangeListener(DATA_KEY, (_name, _oldValue, _newValue, remote) => {
          if (!remote || !isPanelOpen() || panelView !== 'gallery') return;
          renderGalleryItems();
        });
      } catch (error) {
        logDebug('Cross-tab gallery listener unavailable', error);
      }
    }

    // Reyohoho and Twitch can reparent/rebuild the live-chat action row without
    // producing a stable route event. A lightweight Twitch-only recovery check
    // remounts the trigger once the live composer is available again.
    if (isTwitchSite() && !twitchRecoveryTimer) {
      twitchRecoveryTimer = window.setInterval(() => {
        if (!isTwitchRecordingPage()) scheduleEnsure();
      }, 1200);
    }

    logDebug('Userscript v' + APP_VERSION + ' started', { href: location.href });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start, { once: true });
  else start();
})();
