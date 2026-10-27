// ==UserScript==
// @name         Anime Site Pet — маленькая тянка
// @namespace    https://github.com/BigFluffyCatOnWatermelon/twitch-media-gallery
// @version      0.1.1
// @description  Автономная аниме-питомца: гуляет, прыгает, отдыхает и реагирует на курсор и интерфейс страницы.
// @author       BigFluffyCatOnWatermelon
// @match        *://*/*
// @run-at       document-idle
// @noframes
// @grant        GM_getValue
// @grant        GM_setValue
// @homepageURL  https://github.com/BigFluffyCatOnWatermelon/twitch-media-gallery/tree/anime-site-pet/anime-site-pet
// @supportURL   https://github.com/BigFluffyCatOnWatermelon/twitch-media-gallery/issues
// @updateURL    https://raw.githubusercontent.com/BigFluffyCatOnWatermelon/twitch-media-gallery/anime-site-pet/anime-site-pet/anime-site-pet.user.js
// @downloadURL  https://raw.githubusercontent.com/BigFluffyCatOnWatermelon/twitch-media-gallery/anime-site-pet/anime-site-pet/anime-site-pet.user.js
// ==/UserScript==

(() => {
  'use strict';
  if (window.top !== window.self || document.getElementById('asp-host')) return;

  const VERSION = '0.1.1';
  const KEY = 'anime-site-pet-settings-v1';
  const defaults = { size: 104, speed: 1, activity: 0.72, platforms: true, cursorPlay: true, twitchReactions: true, bubbles: true, reducedMotion: false, showPet: true };
  const clamp = (n, a, b) => Math.max(a, Math.min(b, n));
  const rand = (a, b) => a + Math.random() * (b - a);
  const pick = a => a[Math.floor(Math.random() * a.length)];
  const onTwitch = /(^|\.)twitch\.tv$/i.test(location.hostname);
  let settings = { ...defaults }, dead = false, raf = 0, lastFrame = 0, lastScan = 0, lastChatCheck = 0, lastChatCount = 0, lastVideoState = '', lastClick = 0, mutationTimer = 0, videoTimer = 0;
  let x = Math.max(12, innerWidth * .22), y = 0, vx = 0, vy = 0, face = 1, groundY = 0, petH = 148;
  let action = 'idle', actionUntil = 0, nextDecision = performance.now() + 1200, bubbleUntil = 0, flight = null, destination = null, surfaces = [], currentSurface = null;
  const pointer = { x: -1000, y: -1000, at: 0 };

  const readSettings = async () => {
    try { if (typeof GM_getValue === 'function') return await GM_getValue(KEY, {}); } catch (_) {}
    try { return JSON.parse(localStorage.getItem(KEY) || '{}'); } catch (_) { return {}; }
  };
  const saveSettings = async () => {
    try { if (typeof GM_setValue === 'function') { await GM_setValue(KEY, settings); return; } } catch (_) {}
    try { localStorage.setItem(KEY, JSON.stringify(settings)); } catch (_) {}
  };

  const svg = '<svg class="girl" viewBox="0 0 120 170" role="img" aria-label="Аниме-тянка" xmlns="http://www.w3.org/2000/svg">' +
    '<defs><linearGradient id="hair" x1="0" y1="0" x2="1" y2="1"><stop stop-color="#694578"/><stop offset=".55" stop-color="#a56caf"/><stop offset="1" stop-color="#e2a7d2"/></linearGradient><linearGradient id="dress" x1="0" y1="0" x2=".8" y2="1"><stop stop-color="#ff8fbf"/><stop offset="1" stop-color="#d94f93"/></linearGradient><linearGradient id="sock" x1="0" y1="0" x2="0" y2="1"><stop stop-color="#fff8fc"/><stop offset="1" stop-color="#ddd4eb"/></linearGradient></defs>' +
    '<g class="hairback"><path d="M30 37Q20 13 42 8Q65 -2 82 15Q101 21 92 52L94 78Q82 91 80 68L38 73Q32 88 24 72L22 49Z" fill="url(#hair)" stroke="#62406f" stroke-width="2"/><path d="M31 36Q13 49 25 79Q31 89 35 67L39 47Z" fill="#8d589d"/><path d="M81 32Q105 43 93 73Q90 82 84 62L78 46Z" fill="#cb8cca"/></g>' +
    '<g class="legs"><g class="leg legback"><path d="M43 118Q40 133 41 144L50 145Q54 132 56 120Z" fill="url(#sock)" stroke="#a78ba9"/><path d="M39 142Q48 138 53 144L55 151Q47 157 36 151Z" fill="#594d72"/></g><g class="leg legfront"><path d="M61 117Q64 131 65 143L74 144Q77 130 74 117Z" fill="url(#sock)" stroke="#a78ba9"/><path d="M64 141Q72 138 77 144L82 151Q74 157 63 151Z" fill="#4d426b"/></g></g>' +
    '<g class="body"><path d="M44 65Q59 60 74 66L82 95Q72 105 68 119L43 119Q43 103 34 94Z" fill="url(#dress)" stroke="#a5427c" stroke-width="1.5"/><path d="M44 66Q58 73 74 66L69 79Q57 84 45 78Z" fill="#fff0f8"/><path d="M41 91Q58 98 78 90L82 96Q62 105 37 98Z" fill="#ffb8d8"/><path d="M51 76L56 82L62 76L65 84L57 91L48 84Z" fill="#fff6ff" opacity=".9"/></g>' +
    '<g class="arms"><g class="arm armback"><path d="M41 71Q31 78 28 91Q27 97 32 98Q37 98 39 89L48 80Z" fill="#ffd6c9" stroke="#c987a9" stroke-width="1.4"/></g><g class="arm armfront"><path d="M75 72Q85 77 88 87Q91 94 86 97Q81 99 79 90L69 82Z" fill="#ffd6c9" stroke="#c987a9" stroke-width="1.4"/></g></g>' +
    '<path d="M51 56L51 68Q59 75 67 67L65 55Z" fill="#ffd6c9"/>' +
    '<g class="head"><path d="M36 27Q40 12 59 13Q80 12 82 34L78 52Q74 64 59 65Q43 62 39 49Z" fill="#ffe0d3" stroke="#a36c91" stroke-width="1.5"/>' +
    '<path d="M34 39Q27 17 45 12Q63 4 78 15Q91 23 82 41L75 31Q69 39 61 38L62 27Q51 42 43 38L41 31Z" fill="url(#hair)" stroke="#62406f" stroke-width="1.6" stroke-linejoin="round"/><path d="M40 25Q53 6 72 19" fill="none" stroke="#e5b5e3" stroke-width="3" stroke-linecap="round"/><path d="M31 31Q25 40 33 57Q37 62 39 49L40 37Z" fill="#8f579e"/><path d="M78 35Q85 42 78 57Q75 61 74 49Z" fill="#d89bd0"/>' +
    '<g class="bow"><path d="M75 18Q87 8 90 18Q92 25 80 26Z" fill="#ff8fc5" stroke="#ae4f91" stroke-width="1.3"/><path d="M77 21Q66 11 66 20Q65 27 78 26Z" fill="#ffc0df" stroke="#ae4f91" stroke-width="1.3"/><circle cx="77" cy="22" r="3" fill="#fff1fa"/></g>' +
    '<g class="eyes"><path class="eye-white" d="M42 39Q48 34 55 39Q55 47 48 49Q42 47 42 39Z" fill="#fffafc"/><ellipse class="eye-left" cx="49" cy="42" rx="3.8" ry="5.4" fill="#9e65bd"/><ellipse cx="50" cy="40" rx="1.5" ry="2" fill="#fff"/><path d="M41 39Q47 33 55 38M62 39Q68 33 76 39" fill="none" stroke="#68435e" stroke-width="2" stroke-linecap="round"/><path class="eye-white" d="M63 39Q69 34 76 39Q76 47 69 49Q63 47 63 39Z" fill="#fffafc"/><ellipse class="eye-right" cx="69" cy="42" rx="3.8" ry="5.4" fill="#9e65bd"/><ellipse cx="70" cy="40" rx="1.5" ry="2" fill="#fff"/><path class="sleep-eyes" d="M42 43Q48 48 55 43M62 43Q69 48 76 43" fill="none" stroke="#68435e" stroke-width="2.2" stroke-linecap="round"/></g>' +
    '<path class="mouth" d="M55 54Q59 58 63 54" fill="none" stroke="#b85e83" stroke-width="1.8" stroke-linecap="round"/><g class="blush" fill="#f49cb0" opacity=".72"><ellipse cx="40" cy="49" rx="5" ry="2.4"/><ellipse cx="77" cy="49" rx="5" ry="2.4"/></g></g>' +
    '<path d="M35 31Q34 44 39 48M80 29Q84 38 79 46" fill="none" stroke="#e3addf" stroke-width="1.8" stroke-linecap="round"/><g fill="#fff4b5"><path d="M96 42l2 5 5 2-5 2-2 5-2-5-5-2 5-2Z"/><path d="M20 102l1.5 3.5 3.5 1.5-3.5 1.5-1.5 3.5-1.5-3.5-3.5-1.5 3.5-1.5Z"/></g></svg>';

  const init = async () => {
    settings = { ...defaults, ...(await readSettings()) };
    settings.size = clamp(Number(settings.size) || defaults.size, 70, 155);
    settings.speed = clamp(Number(settings.speed) || defaults.speed, .45, 2.1);
    settings.activity = clamp(Number(settings.activity) || defaults.activity, .1, 1);
    petH = settings.size * 1.42;
    groundY = Math.max(20, innerHeight - petH - 8); y = groundY;

    const host = document.createElement('div'); host.id = 'asp-host';
    host.style.cssText = 'all:initial!important;position:fixed!important;inset:0!important;z-index:2147483647!important;pointer-events:none!important;contain:layout style!important;';
    (document.documentElement || document.body).appendChild(host);
    const root = host.attachShadow({ mode: 'open' });
    root.innerHTML = '<style>' +
      ':host{all:initial;color-scheme:light}*{box-sizing:border-box}.pet{position:fixed;left:0;top:0;width:var(--size);height:calc(var(--size)*1.42);pointer-events:auto;touch-action:manipulation;cursor:pointer;user-select:none;filter:drop-shadow(0 5px 3px #3b1f472a);will-change:transform}.figure{width:100%;height:100%;transform-origin:50% 100%;}.girl{display:block;width:100%;height:100%;overflow:visible}.pet.facing-left .girl{transform:scaleX(-1)}.pet[data-action="idle"] .figure{animation:breathe 2.7s ease-in-out infinite}.pet[data-action="walk"] .figure{animation:walk .24s ease-in-out infinite alternate}.pet[data-action="run"] .figure{animation:run .14s ease-in-out infinite alternate}.pet[data-action="run"] .legfront{animation:leg .14s linear infinite alternate;transform-origin:68px 120px}.pet[data-action="run"] .legback{animation:legback .14s linear infinite alternate;transform-origin:48px 120px}.pet[data-action="walk"] .legfront{animation:leg .28s linear infinite alternate;transform-origin:68px 120px}.pet[data-action="walk"] .legback{animation:legback .28s linear infinite alternate;transform-origin:48px 120px}.pet[data-action="jump"] .figure{animation:air .3s ease-in-out infinite alternate}.pet[data-action="fall"] .figure{animation:fall .5s ease-in-out infinite alternate}.pet[data-action="sit"] .figure{transform:translateY(8px) scale(.96,.94)}.pet[data-action="sleep"] .figure{animation:sleep 1.4s ease-in-out infinite}.pet[data-action="dance"] .figure{animation:dance .22s ease-in-out infinite alternate}.pet[data-action="dance"] .armfront{animation:arm .22s ease-in-out infinite alternate;transform-origin:78px 78px}.pet[data-action="dance"] .armback{animation:armback .22s ease-in-out infinite alternate;transform-origin:34px 79px}.pet[data-action="surprised"] .figure{animation:surprise .42s ease-out 2}.pet[data-action="happy"] .figure{animation:happy .38s ease-in-out 2}.pet[data-action="look"] .figure{animation:look .8s ease-in-out 1}.pet[data-action="embarrassed"] .figure{animation:embarrassed .32s ease-in-out 2}.pet[data-action="blink"] .eyes{animation:blink .18s linear 2}.pet[data-action="wobbly"] .figure{animation:wobbly .24s ease-in-out 3}.pet.reduced *{animation-duration:.01ms!important;animation-iteration-count:1!important}.sleep-eyes{opacity:0}.pet[data-action="sleep"] .sleep-eyes{opacity:1}.pet[data-action="sleep"] .eye-left,.pet[data-action="sleep"] .eye-right,.pet[data-action="sleep"] .eye-white{opacity:0}.pet[data-action="embarrassed"] .blush{opacity:1}.bubble{position:absolute;left:50%;top:-25px;transform:translateX(-50%);max-width:190px;padding:5px 9px;border:1px solid #e9c8df;border-radius:12px;background:#fff7fc;color:#583c59;font:12px/1.25 system-ui,sans-serif;white-space:nowrap;box-shadow:0 3px 12px #48214520;opacity:0;pointer-events:none;transition:opacity .15s,transform .15s}.bubble:after{content:"";position:absolute;left:calc(50% - 5px);bottom:-5px;width:8px;height:8px;background:#fff7fc;border-right:1px solid #e9c8df;border-bottom:1px solid #e9c8df;transform:rotate(45deg)}.bubble.show{opacity:1;transform:translate(-50%,-3px)}.settings{position:fixed;right:16px;top:16px;width:min(320px,calc(100vw - 28px));max-height:calc(100vh - 32px);overflow:auto;padding:15px;border:1px solid #eac9df;border-radius:16px;background:#fff9fd;color:#47354b;box-shadow:0 10px 42px #30152e30;font:13px/1.45 system-ui,sans-serif;pointer-events:auto}.settings[hidden],.summon[hidden]{display:none!important}.settings h2{margin:0 0 3px;font-size:16px;color:#6d3f75}.sub{margin:0 0 12px;color:#927a96;font-size:11px}.settings label{display:flex;align-items:center;justify-content:space-between;gap:10px;margin:11px 0 5px;font-weight:600}.settings input[type=range]{width:100%;accent-color:#cf70ae}.settings input[type=checkbox]{accent-color:#c75ca3}.settings .check{justify-content:flex-start;font-weight:500;margin:8px 0}.buttons{display:flex;flex-wrap:wrap;gap:8px;margin-top:12px}.settings button{border:1px solid #e7c4da;border-radius:10px;padding:7px 10px;background:#fff;color:#68456b;font:600 12px system-ui,sans-serif;cursor:pointer}.settings button.primary{background:#d96aa9;border-color:#d96aa9;color:white}.hint{margin:11px 0 0;color:#947e98;font-size:10.5px}.summon{position:fixed;right:14px;bottom:14px;width:40px;height:40px;border:1px solid #e6c2da;border-radius:50%;background:#fff6fc;color:#bd559d;box-shadow:0 4px 18px #38163226;font:22px/1 system-ui,sans-serif;pointer-events:auto;cursor:pointer}@keyframes breathe{0%,100%{transform:translateY(0) scale(1)}50%{transform:translateY(-1.7%) scale(1.006,1.01)}}@keyframes walk{from{transform:translateY(0) rotate(-1deg)}to{transform:translateY(-2%) rotate(1deg)}}@keyframes run{from{transform:translateY(-1%) rotate(-4deg) scale(1.02,.98)}to{transform:translateY(1%) rotate(4deg) scale(.98,1.02)}}@keyframes leg{from{transform:rotate(-24deg)}to{transform:rotate(25deg)}}@keyframes legback{from{transform:rotate(23deg)}to{transform:rotate(-25deg)}}@keyframes arm{from{transform:rotate(25deg)}to{transform:rotate(-35deg)}}@keyframes armback{from{transform:rotate(-25deg)}to{transform:rotate(35deg)}}@keyframes air{from{transform:rotate(-4deg) scale(1.02,.98)}to{transform:rotate(4deg) scale(.97,1.03)}}@keyframes fall{from{transform:rotate(-10deg) translateX(-2px)}to{transform:rotate(12deg) translateX(2px)}}@keyframes sleep{0%,100%{transform:translateY(4px) rotate(-1deg)}50%{transform:translateY(7px) rotate(1deg)}}@keyframes dance{from{transform:rotate(-7deg)}to{transform:rotate(7deg) translateY(-4px)}}@keyframes surprise{0%,100%{transform:translateY(0) scale(1)}35%{transform:translateY(-10px) scale(1.03,1.08)}}@keyframes happy{0%,100%{transform:translateY(0) rotate(0)}30%{transform:translateY(-8px) rotate(-5deg)}65%{transform:translateY(-4px) rotate(5deg)}}@keyframes look{0%,100%{transform:rotate(0)}35%{transform:rotate(8deg)}65%{transform:rotate(-5deg)}}@keyframes embarrassed{0%,100%{transform:rotate(0)}40%{transform:rotate(5deg) translateX(2px)}70%{transform:rotate(-5deg) translateX(-2px)}}@keyframes blink{0%,100%{opacity:1}50%{opacity:.05}}@keyframes wobbly{0%,100%{transform:rotate(0)}25%{transform:rotate(-8deg)}75%{transform:rotate(8deg)}}@media(prefers-reduced-motion:reduce){.pet *{animation-duration:.01ms!important;animation-iteration-count:1!important}}' +
      '</style><div class="pet" id="pet" data-action="idle" role="button" tabindex="0" aria-label="Аниме-тянка. Клик — погладить, правый клик — настройки"><div class="bubble" id="bubble"></div><div class="figure" id="figure">' + svg + '</div></div><button class="summon" id="summon" title="Показать тянку" hidden>♡</button><section class="settings" id="settings" aria-label="Настройки тянки" hidden><h2>🌸 Anime Site Pet</h2><p class="sub">Версия ' + VERSION + ' · маленькая тянка на сайте</p><label for="size">Размер <span id="sizeValue"></span></label><input id="size" type="range" min="70" max="155" step="1"><label for="speed">Скорость движения <span id="speedValue"></span></label><input id="speed" type="range" min="0.45" max="2.1" step="0.05"><label for="activity">Активность <span id="activityValue"></span></label><input id="activity" type="range" min="0.1" max="1" step="0.05"><label class="check"><input id="platforms" type="checkbox"> Прыгать по кнопкам, панелям и картинкам</label><label class="check"><input id="cursorPlay" type="checkbox"> Реагировать на курсор и играть с ним</label><label class="check"><input id="twitchReactions" type="checkbox"> Специальные реакции Twitch</label><label class="check"><input id="bubbles" type="checkbox"> Реплики и эмоции</label><label class="check"><input id="reducedMotion" type="checkbox"> Уменьшить анимации</label><div class="buttons"><button id="close" class="primary">Готово</button><button id="pause">Пауза</button><button id="reset">Сбросить</button></div><p class="hint">Alt + Shift + P — настройки · Alt + Shift + H — спрятать/показать. Правый клик по тянке открывает настройки. На сайтах кроме Twitch работает универсальное поведение.</p></section>';

    const $ = s => root.querySelector(s), pet = $('#pet'), figure = $('#figure'), bubble = $('#bubble'), panel = $('#settings'), summon = $('#summon');
    const say = (text, duration = 1900) => { if (!settings.bubbles) return; bubble.textContent = text; bubble.classList.add('show'); bubbleUntil = performance.now() + duration; };
    const setAction = (name, duration = 900, line = '') => { action = name; actionUntil = performance.now() + duration; pet.dataset.action = name; if (line) say(line, Math.max(duration, 1300)); };
    const dimensions = () => { petH = settings.size * 1.42; groundY = Math.max(12, innerHeight - petH - 8); pet.style.setProperty('--size', settings.size + 'px'); pet.style.width = settings.size + 'px'; pet.style.height = petH + 'px'; x = clamp(x, -settings.size * .12, innerWidth - settings.size * .75); y = clamp(y, 5, groundY); if (!flight && (!currentSurface || currentSurface.ground)) y = groundY; render(); };
    const render = () => { pet.style.transform = 'translate3d(' + x + 'px,' + y + 'px,0)'; pet.classList.toggle('facing-left', face < 0); pet.style.display = settings.showPet ? 'block' : 'none'; summon.hidden = settings.showPet; pet.classList.toggle('reduced', settings.reducedMotion); };
    const openPanel = () => { panel.hidden = false; syncControls(); }, closePanel = () => { panel.hidden = true; }, togglePanel = () => panel.hidden ? openPanel() : closePanel();
    const syncControls = () => { $('#size').value = settings.size; $('#sizeValue').textContent = settings.size + ' px'; $('#speed').value = settings.speed; $('#speedValue').textContent = settings.speed.toFixed(2) + '×'; $('#activity').value = settings.activity; $('#activityValue').textContent = Math.round(settings.activity * 100) + '%'; for (const k of ['platforms','cursorPlay','twitchReactions','bubbles','reducedMotion']) $('#' + k).checked = !!settings[k]; };
    const react = () => { lastClick = performance.now(); const n = lastClick; setAction('happy', 850, pick(['Эй! 💗','Хи-хи!','Ой!','Привет-привет!','♡','Ты меня заметил!'])); nextDecision = n + rand(900, 1700); };
    const bindRange = (id, key, fmt) => $('#' + id).addEventListener('input', e => { settings[key] = Number(e.target.value); if (fmt) $('#' + id + 'Value').textContent = fmt(settings[key]); if (key === 'size') dimensions(); saveSettings(); });
    bindRange('size','size',v=>v+' px'); bindRange('speed','speed',v=>v.toFixed(2)+'×'); bindRange('activity','activity',v=>Math.round(v*100)+'%');
    for (const k of ['platforms','cursorPlay','twitchReactions','bubbles','reducedMotion']) $('#' + k).addEventListener('change', e => { settings[k] = e.target.checked; saveSettings(); });
    $('#close').addEventListener('click', closePanel);
    $('#pause').addEventListener('click', () => { if (action === 'paused') { setAction('idle', 500); nextDecision = performance.now() + 400; $('#pause').textContent = 'Пауза'; } else { flight = destination = null; vx = vy = 0; setAction('paused', 999999999); $('#pause').textContent = 'Продолжить'; say('Перерыв ☕'); } });
    $('#reset').addEventListener('click', async () => { settings = { ...defaults }; await saveSettings(); syncControls(); dimensions(); setAction('happy',900,'Настройки сброшены!'); });
    summon.addEventListener('click', () => { settings.showPet = true; render(); saveSettings(); openPanel(); });
    pet.addEventListener('click', e => { if (e.button === 0) react(); });
    pet.addEventListener('contextmenu', e => { e.preventDefault(); openPanel(); });
    pet.addEventListener('keydown', e => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); react(); } if (e.key === 'Escape') closePanel(); });
    window.addEventListener('keydown', e => { if (e.altKey && e.shiftKey && e.code === 'KeyP') { e.preventDefault(); togglePanel(); } if (e.altKey && e.shiftKey && e.code === 'KeyH') { e.preventDefault(); settings.showPet = !settings.showPet; render(); saveSettings(); } if (e.key === 'Escape' && !panel.hidden) closePanel(); }, true);

    const getRect = el => { try { return el.getBoundingClientRect(); } catch (_) { return null; } };
    const sameSurface = (a,b) => !!(a && b && ((a.ground && b.ground) || (a.el && b.el && a.el === b.el)));
    const scanPlatforms = (force = false) => {
      const now = performance.now(); if (!settings.platforms && !force) { surfaces = []; return; } if (!force && now - lastScan < 1400) return; lastScan = now;
      const w = innerWidth, h = innerHeight, found = [], nodes = document.querySelectorAll('button,img,video,header,nav,aside,article,[role="button"],[data-a-target*="chat"],[data-a-target="video-player"],[class*="toolbar"],[class*="panel"]');
      let count = 0;
      for (const el of nodes) {
        if (++count > 350) break; if (!(el instanceof HTMLElement) || host.contains(el) || el.closest('#asp-host')) continue;
        if (el.disabled || el.getAttribute('aria-hidden') === 'true') continue;
        const cs = getComputedStyle(el); if (cs.display === 'none' || cs.visibility === 'hidden' || Number(cs.opacity) < .15) continue;
        const r = getRect(el); if (!r || r.width < 76 || r.height < 18 || r.width > w*.82 || r.height > h*.74 || r.right < 10 || r.left > w-10 || r.bottom < 15 || r.top > h-35 || r.top < 25) continue;
        if (el.tagName === 'IMG' && r.width < 100) continue;
        const tag = el.tagName.toLowerCase(), cls = typeof el.className === 'string' ? el.className.toLowerCase() : '', tar = (el.getAttribute('data-a-target') || '').toLowerCase();
        let score = 1; if (tag === 'button' || el.getAttribute('role') === 'button') score += 1.5; if (tag === 'img' || tag === 'video') score += 1.8; if (/player|chat|toolbar|control|header|panel/.test(cls + ' ' + tar)) score += 1.25; if (r.width > w*.6) score -= 1.3;
        found.push({ el, left:r.left, right:r.right, top:r.top, width:r.width, height:r.height, y:r.top-petH+8, cx:(r.left+r.right)/2, score, ground:false });
      }
      found.push({ el:null,left:0,right:w,top:h-2,width:w,height:2,y:groundY,cx:w/2,score:.7,ground:true }); surfaces = found;
      if (currentSurface) { const reb = found.find(s => sameSurface(s,currentSurface)); if (reb) currentSurface = reb; else if (!flight) { currentSurface = found.find(s=>s.ground)||null; y=groundY; setAction('fall',650,pick(['Ой!','Упс!','Не удержалась…'])); nextDecision=now+850; } }
    };
    const chooseSurface = () => { scanPlatforms(); const candidates = surfaces.filter(s => s.ground || (s.y >= 8 && s.y <= groundY+2 && Math.abs(s.cx - x) < innerWidth*.88)); if (!candidates.length) return { left:0,right:innerWidth,y:groundY,cx:innerWidth/2,ground:true,score:1 }; const weighted = candidates.map(s => ({s,w:Math.max(.12,s.score)*(s === currentSurface ? .28 : 1)*(s.ground ? .72 : 1)*(s.y<groundY-25?1.2:1)})); let n=Math.random()*weighted.reduce((a,b)=>a+b.w,0); for (const a of weighted) { n-=a.w; if(n<=0) return a.s; } return candidates[candidates.length-1]; };
    const jumpTo = target => { if (!target) return; const dx = target.x-x, dy = target.y-y, duration = clamp(.5+Math.abs(dx)/1050+Math.abs(dy)/1800,.48,1.08), gravity=1450; vx=dx/duration; vy=clamp((dy-.5*gravity*duration*duration)/duration,-930,500); flight={start:performance.now(),duration,startX:x,startY:y,targetX:target.x,targetY:target.y,gravity,surface:target.surface||null}; destination=target; face=dx<0?-1:1; setAction('jump',duration*1000+100); };
    const startWalk = (tx,ty,surface,running=false) => { destination={x:tx,y:ty,surface}; flight=null; vx=vy=0; setAction(running?'run':'walk',30000); if(tx<x) face=-1; else if(tx>x) face=1; if(Math.abs(ty-y)>28) jumpTo(destination); };
    const finishFlight = () => { if(!flight) return; x=flight.targetX; y=flight.targetY; currentSurface=flight.surface||null; flight=null; vx=vy=0; destination=null; const after=Math.random(); if(after<.18) setAction('wobbly',850,pick(['Фух!','Упс!','Та-дам!'])); else if(after<.38) setAction('happy',700); else setAction('idle',rand(500,1300)); nextDecision=performance.now()+rand(550,1800); };

    const chooseAction = now => {
      if(action==='paused'||!settings.showPet||flight||panel.dataset.freeze==='true') return;
      if(now<actionUntil && ['sit','sleep','dance','surprised','happy','look','embarrassed','wobbly','blink'].includes(action)) return;
      const pointerNear = settings.cursorPlay && now-pointer.at<2200 && Math.hypot(pointer.x-(x+settings.size/2),pointer.y-(y+petH*.47))<210;
      if(pointerNear && Math.random()<.24*settings.activity) {
        const dx=pointer.x-(x+settings.size/2);
        if(Math.abs(dx)>36) { const newX=clamp(pointer.x-settings.size/2+rand(-35,35),4,innerWidth-settings.size-4); startWalk(newX,y,currentSurface,Math.random()<.22); if(Math.random()<.45) say(pick(['Куда ты?','Не убегай!','Ага, вижу тебя!','Лови меня!'])); return; }
        setAction('look',900,pick(['Что там?','Хм-хм…','О, курсор!','👀'])); nextDecision=now+rand(700,1500); return;
      }
      const roll=Math.random(), a=settings.activity;
      if(roll<.09+a*.04) setAction('sleep',rand(4000,9000),pick(['Zzz…','Пять минуточек…','*сладко спит*']));
      else if(roll<.18+a*.08) setAction('sit',rand(2200,5000),pick(['Отдохну немножко','Как уютно…','*болтает ножками*']));
      else if(roll<.24+a*.1) setAction('dance',rand(900,1700),pick(['♪','Танцульки!','♪(๑ᴖ◡ᴖ๑)♪']));
      else if(roll<.3+a*.12) setAction('look',rand(650,1200),pick(['Осматриваюсь…','Интересно!','Куда бы пойти?','👀']));
      else if(roll<.36+a*.12) { setAction('blink',rand(250,450)); nextDecision=now+rand(1600,3000); }
      else if(roll<.43+a*.1) setAction('wobbly',750,pick(['*покачнулась*','Ой, чуть не упала!']));
      else {
        const surf=settings.platforms?chooseSurface():null, ground=!surf||surf.ground;
        const minX=ground?5:clamp(surf.left+4,4,innerWidth-settings.size-4), maxX=ground?innerWidth-settings.size-5:clamp(surf.right-settings.size-4,minX,innerWidth-settings.size-4);
        let tx; if(surf && surf===currentSurface && Math.random()<.58) tx=clamp(x+rand(-260,260),minX,maxX); else tx=rand(minX,Math.max(minX+1,maxX));
        const ty=surf?clamp(surf.y,5,groundY):groundY, target={x:tx,y:ty,surface:surf};
        if(settings.platforms && surf && !sameSurface(surf,currentSurface) && Math.random()<.7) jumpTo(target); else startWalk(tx,ty,surf,Math.random()<.22*a);
      }
      nextDecision=now+rand(1800,5200)/Math.max(.45,a);
    };
    const reactToTwitch = now => {
      if(!settings.twitchReactions||!onTwitch||!settings.showPet||now-lastChatCheck<1800) return; lastChatCheck=now;
      let count=0; for(const sel of ['[data-a-target="chat-line-message"]','[data-test-selector*="chat-line"]','[data-a-target="chat-message"]']) { try { count=Math.max(count,document.querySelectorAll(sel).length); } catch (_) {} }
      const added=Math.abs(count-lastChatCount); lastChatCount=count;
      if(added>=3 && now-lastClick>2600) { setAction('surprised',950,pick(['Как оживлённо!','Сколько сообщений!','Ого, чат разогнался!','Чат сегодня быстрый!'])); nextDecision=now+1300; }
    };
    const observer = new MutationObserver(records => { if(!settings.platforms && !onTwitch) return; let added=false; for(const m of records){for(const n of m.addedNodes||[]){if(n.nodeType===1 && n!==host && !host.contains(n)){added=true;break;}} if(added)break;} if(added) { clearTimeout(mutationTimer); mutationTimer = setTimeout(()=>scanPlatforms(true),900); } });
    observer.observe(document.documentElement,{childList:true,subtree:true});
    document.addEventListener('pointermove',e=>{pointer.x=e.clientX;pointer.y=e.clientY;pointer.at=performance.now();},{passive:true});
    window.addEventListener('resize',()=>{dimensions();scanPlatforms(true);},{passive:true});
    window.addEventListener('scroll',()=>{scanPlatforms(true);},{passive:true,capture:true});
    if(onTwitch && settings.twitchReactions) videoTimer = setInterval(()=>{ const v=document.querySelector('video'); if(!v)return; const state=v.paused?'paused':'playing'; if(state!==lastVideoState){const prev=lastVideoState;lastVideoState=state;if(prev&&performance.now()-lastClick>2600){if(state==='paused'&&Math.random()<.65)setAction('sit',2800,pick(['Пауза? Передохнём!','*усаживается*','Что, перерыв?']));else if(state==='playing'&&prev==='paused')setAction('happy',850,pick(['Стрим продолжается!','Ура, погнали!']));}}},1500);

    const onFrame = ts => {
      if(dead) return; raf=requestAnimationFrame(onFrame); const dt=Math.min(.04,Math.max(0,(ts-(lastFrame||ts))/1000)); lastFrame=ts; if(!settings.showPet) return;
      if(ts>=lastScan+5500) scanPlatforms();
      groundY=Math.max(12,innerHeight-petH-8);
      if(flight){const t=(ts-flight.start)/1000;if(t>=flight.duration)finishFlight();else{x=flight.startX+vx*t;y=flight.startY+vy*t+.5*flight.gravity*t*t;y=Math.min(y,groundY+30);if(x<0||x>innerWidth-settings.size*.55)face=x<0?1:-1;x=clamp(x,-settings.size*.12,innerWidth-settings.size*.75);}}
      else if((action==='walk'||action==='run')&&destination){const dx=destination.x-x,dy=destination.y-y,step=(action==='run'?220:115)*settings.speed*dt;if(Math.abs(dx)<=step+1){x=destination.x;if(Math.abs(dy)>3&&settings.platforms)jumpTo(destination);else{y=destination.y;currentSurface=destination.surface||null;destination=null;setAction('idle',rand(400,1200));nextDecision=ts+rand(650,1600);}}else{x+=Math.sign(dx)*step;if(Math.abs(dy)>4)y+=dy*Math.min(1,dt*1.8);face=dx<0?-1:1;}}
      else if(action!=='paused'&&ts>=nextDecision&&ts>=actionUntil) chooseAction(ts);
      if(bubbleUntil&&ts>bubbleUntil){bubble.classList.remove('show');bubbleUntil=0;} reactToTwitch(ts); render();
    };
    dimensions(); syncControls(); scanPlatforms(true); currentSurface=surfaces.find(s=>s.ground)||null; y=groundY; setAction('look',1200,pick(['Привет! Я тут!','Осматриваюсь…','Привет-привет!','Где это я?','*потягивается*'])); nextDecision=performance.now()+rand(1300,2500); render(); raf=requestAnimationFrame(onFrame);
    try { Object.defineProperty(window,'__animeSitePet',{configurable:true,value:{version:VERSION,openSettings:openPanel,pause:()=>{flight=null;destination=null;setAction('paused',999999999);},resume:()=>{setAction('idle',500);nextDecision=performance.now()+300;},destroy:()=>{dead=true;cancelAnimationFrame(raf);clearInterval(videoTimer);clearTimeout(mutationTimer);observer.disconnect();host.remove();delete window.__animeSitePet;}}}); } catch (_) {}
  };
  init().catch(err=>console.error('[Anime Site Pet] Ошибка запуска:',err));
})();