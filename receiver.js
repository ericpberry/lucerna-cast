// From bobbin@2004efc:receiver/receiver.js, adapted: Lucerna's TV page (SPEC.md R1 to R9). Cast handling patterns
// (fit() stage, want/ended by item id, 2 s finish hold, last-sender rule, key throttle, touch from capabilities) also
// in spool@894e264:receiver/receiver.js; the playback, tiles, snapshots, states and protocol are Lucerna's own.
//
// Messages on urn:x-cast:app.lucerna, parsed and encoded by messages.js (mirror of core/cast/TvMessages.kt):
//   phone → TV  hello item tiles snap snapUrl status queue end ping pong
//   TV → phone  caps state error want ended key ping pong
// The video is the LOAD on Cast's media channel (customData.itemId names the Lucerna item).
// ES2017 only (R8): no optional chaining, no ??, no object spread, no `catch {}` without a binding.
(function () {
  'use strict';

  var M = window.LucernaMessages;
  var NS = M.NAMESPACE;
  var MODE = window.LUCERNA_MODE || 'cast';
  var params = new URLSearchParams(location.search);
  var PREVIEW = MODE === 'preview' ? (params.get('preview') || 'idle') : null;
  /** m11: diagnostics on the TV page (the tiles' snapshot rate) only with ?debug=1. */
  var DEBUG = params.get('debug') === '1';
  var body = document.body;
  function $(id) { return document.getElementById(id); }

  /** Timings (FAMILY-LESSONS § 5 Timings; SPEC C4, R3, R4, Q3). */
  var T = {
    HEARTBEAT_MS: 5000, PHONE_LOST_MS: 15000, STATE_MS: 5000, FINISH_HOLD_MS: 2000, KEY_THROTTLE_MS: 700,
    STARTING_TIMEOUT_MS: 30000, STALL_RECOVER_MS: 10000, OVERLAY_MS: 6000, HUB_HIDE_MS: 5000, BUFFER_SHOW_MS: 400,
    UP_NEXT_S: 15, SNAP_FAILS: 2, SNIFF_MS: 2500,
    // R-67: End, Paused and PhoneLost give way to the idle screen after 5 min (a shared TV is a public screen, and
    // a still board is a burn-in risk). PhoneLost waits out the whole window first: it is still reconnecting.
    REST_MS: 300000,
    // R-89: after a minute of "Trying for", the board says what to do on the phone.
    LOST_HELP_MS: 60000,
    // R-8, R-64: the same "behind live" words on every TV surface (tv/…/ui/ControlsScreen.kt mirrors this).
    AT_LIVE_S: 1.5,
    // m7: the most of the player's own delay counted as its place at live (CastController.MAX_LIVE_BASELINE_S).
    MAX_LIVE_BASE_S: 45
  };

  // ---- state ------------------------------------------------------------------------------------------------------------
  var S = {
    hello: M.decode({ type: 'hello' }),
    helloSeen: false,
    phone: null,            // sender id that last spoke (D-120); until then, every sender
    lastHeard: 0,
    everHeard: false,
    lostSince: 0,           // phone lost since (ms), 0 = not lost
    items: {},              // item messages by id
    itemOrder: [],
    playingId: null,        // customData.itemId of what the player started (D-113)
    endedFor: null,         // the item whose finish was reported (D-114)
    finishTimer: null,
    liveIdle: false,        // a live stream went IDLE and held 2 s: show the reconnecting banner
    media: null,            // MediaInformation of the current LOAD
    live: false,
    loading: false,
    screen: 'idle',         // idle | play | end | cantplay
    updateV: 0,             // hello.v newer than this page: "Update Lucerna on your phone"
    tiles: null,
    tileKey: '',
    bar: null,              // D-89: the tiles' control bar, open: { from: tile index to return to, until: ms }
    snapUrls: {},
    snapTransport: 'http',
    snapFails: 0,
    status: M.decode({ type: 'status' }),
    queue: [],
    end: null,
    cant: null,
    starting: null,
    overlayUntil: 0,
    exitUntil: 0,           // D-94: "Press Back again to exit" shows until then; a Back before it closes the page
    hubUntil: 0,
    pausedLocally: false,
    hidden: false,
    touch: false,
    seq: 0,
    sent: [],
    lastStateKey: '',
    bufferingSince: 0,
    playStartedAt: 0,
    stall: { lastT: -1, stuckMs: 0 },
    recoveries: 0,
    errorKey: '',
    tvName: '',
    lastKeyAt: 0,
    upNextShownFor: null,
    pausedSince: 0,         // R-67: when the current pause began (0 = not paused)
    liveBase: null,         // m7: the player's own delay at live (s), least reported while playing since this LOAD
    endSince: 0,            // R-67: when the end-of-queue board appeared
    fake: null              // preview: the pretend player
  };

  var context = null;
  var player = null;
  var video = $('media');

  // ---- small helpers ----------------------------------------------------------------------------------------------------
  function now() { return Date.now(); }
  function setText(el, s) { s = s === null || s === undefined ? '' : String(s); if (el.textContent !== s) el.textContent = s; }
  function show(el, on) { if (el.hidden === !!on) el.hidden = !on; }
  function cls(el, name, on) { if (el.classList.contains(name) !== !!on) el.classList.toggle(name, !!on); }
  function clamp(v, a, b) { return Math.max(a, Math.min(b, v)); }
  function pad2(n) { return n < 10 ? '0' + n : String(n); }
  /** 52:30, 1:12:40; `hours` forces h:mm:ss. */
  function fmt(sec, hours) {
    sec = Math.max(0, Math.floor(sec || 0));
    var h = Math.floor(sec / 3600), m = Math.floor((sec % 3600) / 60), s = sec % 60;
    if (h > 0 || hours) return h + ':' + pad2(m) + ':' + pad2(s);
    return m + ':' + pad2(s);
  }
  function isPrivateHost(url) {
    try {
      var h = new URL(url, location.href).hostname;
      return /^(localhost|127\.|10\.|192\.168\.|172\.(1[6-9]|2\d|3[01])\.|\[::1\]|\[fe80:)/.test(h);
    } catch (e) { return false; }
  }

  // ---- the stage (Bobbin's fit()): 960 x 540 design, 1024 x 600 on touch displays ---------------------------------------
  var stage = $('stage');
  var view = { s: 1, x: 0, y: 0, W: 960, H: 540 };
  function fit() {
    view.W = S.touch ? 1024 : 960;
    view.H = S.touch ? 600 : 540;
    var w = window.innerWidth || view.W, h = window.innerHeight || view.H;
    view.s = Math.min(w / view.W, h / view.H);
    view.x = (w - view.W * view.s) / 2;
    view.y = (h - view.H * view.s) / 2;
    document.documentElement.style.setProperty('--W', view.W + 'px');
    document.documentElement.style.setProperty('--H', view.H + 'px');
    stage.style.left = view.x + 'px';
    stage.style.top = view.y + 'px';
    stage.style.transform = 'scale(' + view.s + ')';
    // The stage size can change after the tiles were laid out (touch is known only after caps): lay them out again
    // so the slots match the 1024 x 600 stage (R-39).
    if (tileEls && tileEls.length && S.tiles) buildTiles(false);
    placeVideo();
  }
  window.addEventListener('resize', fit);

  // ---- player access (real CAF, the stub, or the preview's pretend player) ----------------------------------------------
  function pState() {
    if (S.fake) return S.fake.state;
    return player ? player.getPlayerState() : 'IDLE';
  }
  function pTime() {
    if (S.fake) return S.fake.time;
    return player ? (player.getCurrentTimeSec() || 0) : 0;
  }
  function pDuration() {
    if (S.fake) return S.fake.duration || 0;
    var d = player ? player.getDurationSec() : 0;
    if (!(d > 0) || !isFinite(d)) d = S.media && S.media.duration > 0 ? S.media.duration : 0;
    if (!(d > 0) || !isFinite(d)) { var it = currentItem(); d = it && it.durationMs ? it.durationMs / 1000 : 0; }
    return d;
  }
  function pRange() {
    if (S.fake) return S.fake.range || null;
    var r = null;
    try { r = player && player.getLiveSeekableRange ? player.getLiveSeekableRange() : null; } catch (e) { r = null; }
    if (r && isFinite(r.start) && isFinite(r.end) && r.end > r.start) return r;
    if (video.seekable && video.seekable.length) {
      var st = video.seekable.start(0), en = video.seekable.end(video.seekable.length - 1);
      if (isFinite(en) && en > st) return { start: st, end: en };
    }
    return null;
  }
  /** Seconds between the live edge and the playhead (live only); null when unknown. Feeds `state.behindLiveS` and the
   *  on-screen "behind live" text alike. */
  function behindLive() {
    if (!S.live) return null;
    if (S.fake && S.fake.behind !== undefined) return S.fake.behind;
    var r = pRange();
    if (r) return Math.max(0, r.end - pTime());
    // Native HLS players (Chromium/Edge's, so the PC bridge) give a live stream no seekable range at all once it plays
    // (duration Infinity, seekable empty). They still fetch each new segment as the playlist grows, so the end of what
    // is buffered tracks the live edge to within a segment.
    var b = video.buffered;
    if (b && b.length) {
      var end = b.end(b.length - 1);
      if (isFinite(end) && end > 0) return Math.max(0, end - pTime());
    }
    return S.status.behindLiveS;
  }
  /**
   * m7: what the phone shows, by the phone's own rule (CastController): a live player sits a few segments behind the
   * playlist's end on purpose, and the least delay it reported while playing since this LOAD (whole seconds, at most
   * [T.MAX_LIVE_BASE_S]) is its place "at live". Only the time behind that counts, on the phone and here alike. The
   * base is taken from the very `state` values the phone gets, so both subtract the same number.
   */
  function shownBehind(b) {
    if (b === null || b === undefined || !isFinite(b)) return b;
    return Math.max(0, Math.round(b) - (S.liveBase || 0));
  }
  /** R-8, R-64: "At live", "12 s behind live", or plain "Live" when nothing says how far behind (never guessed). */
  function behindLiveText(b) {
    b = shownBehind(b);
    if (b === null || b === undefined || !isFinite(b)) return 'Live';
    return b < T.AT_LIVE_S ? 'At live' : Math.round(b) + ' s behind live';
  }
  /** The picture's quality as people name it: its shorter side (a vertical 720 x 1280 clip is 720p, m10). */
  function videoHeight() {
    if (S.fake) return S.fake.height || 0;
    var w = video.videoWidth || 0, h = video.videoHeight || 0;
    return w > 0 && h > 0 ? Math.min(w, h) : h;
  }
  function currentItem() { return S.playingId ? S.items[S.playingId] || null : null; }
  function curTitle() {
    if (S.hello.discreet) return '';
    var it = currentItem();
    if (it && it.title) return it.title;
    var md = S.media && S.media.metadata;
    return md && typeof md.title === 'string' ? M.cap(md.title) : '';
  }
  function curSite() {
    if (S.hello.discreet) return '';
    var it = currentItem();
    if (it && it.site) return it.site;
    var md = S.media && S.media.metadata;
    return md && typeof md.subtitle === 'string' ? M.cap(md.subtitle) : '';
  }

  // ---- sending (answers only the sender that last spoke, D-120) ---------------------------------------------------------
  function senderConnected(id) {
    try { return context.getSenders().some(function (s) { return s.id === id; }); } catch (e) { return false; }
  }
  function send(type, fields) {
    var msg = { type: type, seq: ++S.seq };
    if (fields) Object.keys(fields).forEach(function (k) { msg[k] = fields[k]; });
    var obj = M.encodeObject(msg);
    S.sent.push(obj);
    if (S.sent.length > 300) S.sent.shift();
    if (!context) return obj;
    var to = S.phone && senderConnected(S.phone) ? S.phone : undefined;
    try {
      if (!to && !context.getSenders().length) return obj;
      context.sendCustomMessage(NS, to, obj);
    } catch (e) { console.warn('[lucerna] send failed', e); }
    return obj;
  }

  function stateFields() {
    var st = pState();
    var b = behindLive();
    return {
      itemId: S.playingId, positionMs: Math.max(0, Math.round(pTime() * 1000)), playing: st === 'PLAYING',
      buffering: st === 'BUFFERING' || S.loading, behindLiveS: b === null || b === undefined ? null : Math.round(b * 10) / 10,
      snapTransport: S.snapTransport, hidden: S.hidden, videoHeight: videoHeight() || null
    };
  }
  /** `state` every 5 s and whenever something but the clock changed. */
  function sendState(force) {
    var f = stateFields();
    if (S.live && f.playing && typeof f.behindLiveS === 'number') {
      var r = Math.round(f.behindLiveS);
      S.liveBase = Math.min(S.liveBase === null ? r : S.liveBase, r, T.MAX_LIVE_BASE_S);
    }
    var key = [f.itemId, f.playing, f.buffering, f.snapTransport, f.hidden].join('|');
    if (!force && key === S.lastStateKey) return;
    S.lastStateKey = key;
    send('state', f);
  }

  // ---- capabilities (D7, R7) --------------------------------------------------------------------------------------------
  var PROBE = [
    ['video/mp4', 'avc1.42E01E'], ['video/mp4', 'avc1.4D401F'], ['video/mp4', 'avc1.640028'], ['video/mp4', 'avc1.640033'],
    ['video/mp4', 'hvc1.1.6.L120.90'], ['video/mp4', 'hev1.1.6.L120.90'], ['video/mp4', 'hvc1.2.4.L150.90'],
    ['video/mp4', 'vp09.00.10.08'], ['video/mp4', 'vp09.02.10.10.01.09.16.09.01'], ['video/webm', 'vp8'], ['video/webm', 'vp9'],
    ['video/mp4', 'av01.0.08M.08'], ['video/mp4', 'av01.0.12M.10'],
    ['audio/mp4', 'mp4a.40.2'], ['audio/mp4', 'mp4a.40.5'], ['audio/mp4', 'ac-3'], ['audio/mp4', 'ec-3'], ['audio/mp4', 'opus'], ['audio/mp4', 'flac']
  ];
  function canPlay(mime, codec) {
    var ok = false;
    try { ok = !!(context && context.canDisplayType && context.canDisplayType(mime, codec)); } catch (e) { ok = false; }
    if (!ok) {
      try { ok = !!(window.MediaSource && MediaSource.isTypeSupported(mime + '; codecs="' + codec + '"')); } catch (e2) { ok = false; }
    }
    return ok;
  }
  var codecCache = null;
  function supportedCodecs() {
    if (!codecCache) codecCache = PROBE.filter(function (p) { return canPlay(p[0], p[1]); }).map(function (p) { return p[1]; });
    return codecCache;
  }
  function maxHeight() {
    if (!context || !context.canDisplayType || (window.cast && cast.framework && cast.framework.__stub)) return 1080;
    try {
      if (context.canDisplayType('video/mp4', 'avc1.640033', 3840, 2160, 30)) return 2160;
      if (context.canDisplayType('video/mp4', 'avc1.640028', 1920, 1080, 30)) return 1080;
    } catch (e) { return 1080; }
    return 720;
  }
  function family(codec) {
    if (/^avc|^h264/i.test(codec)) return 'H.264';
    if (/^hvc|^hev|hevc/i.test(codec)) return 'HEVC';
    if (/^vp09|^vp9/i.test(codec)) return 'VP9';
    if (/^av01|av1/i.test(codec)) return 'AV1';
    return null;
  }
  function playsLine() {
    var fams = [];
    supportedCodecs().forEach(function (c) { var f = family(c); if (f && fams.indexOf(f) < 0) fams.push(f); });
    if (!fams.length) return '';
    var last = fams.pop();
    return 'this TV plays ' + (fams.length ? fams.join(', ') + ' and ' + last : last);
  }
  function touchFromCapabilities() {
    if (!context || !context.getDeviceCapabilities) return false;
    var caps = null;
    try { caps = context.getDeviceCapabilities(); } catch (e) { caps = null; }
    if (!caps) return false;
    var sys = (window.cast && cast.framework && cast.framework.system) || {};
    var enumObj = sys.DeviceCapabilities || sys.DeviceCapability || {};
    var key = enumObj.TOUCH_INPUT_SUPPORTED || 'touch_input_supported';
    return !!(caps[key] || caps.touch_input_supported);
  }
  /**
   * D-95: what this TV is, from the DeviceType Cast puts in the browser's user agent: a Google TV / Android TV can
   * install the Lucerna TV app (the phone offers it there); a Chromecast or a Nest Hub can't. Null when unknown.
   */
  var DEVICE_TYPE_RE = /DeviceType\/(\w+)/;
  function deviceType() {
    var m = DEVICE_TYPE_RE.exec(navigator.userAgent || '');
    if (!m) return null;
    var t = m[1].toLowerCase();
    if (t === 'androidtv') return 'androidtv';
    if (t === 'chromecast') return 'chromecast';
    if (t === 'smartdisplay') return 'display';
    return null;
  }
  function sendCaps() {
    var caps = { video: supportedCodecs().slice(), maxHeight: maxHeight(), touch: S.touch, kind: 'web', maxTiles: 4, v: M.VERSION };
    var dt = deviceType();
    if (dt) caps.deviceType = dt;
    send('caps', caps);
  }
  function setTouch(on) {
    S.touch = !!on;
    cls(body, 'touch-ui', S.touch);
    fit();
  }

  // ---- incoming messages -------------------------------------------------------------------------------------------------
  function heard() {
    S.lastHeard = now();
    S.everHeard = true;
    if (S.lostSince) { S.lostSince = 0; }
  }

  function onCustomMessage(event) {
    var data = event.data;
    var m = M.decodeFromPhone(data);
    if (!m) return;   // not JSON, unknown, malformed, or a TV → phone type: ignored
    if (event.senderId) S.phone = event.senderId;
    var first = !S.everHeard;
    heard();
    handle(m);
    // C4: the first word from a phone after this page (re)loaded gets our state at once, so a phone that was casting
    // sees the item is gone and sends it again (no waiting for the 5 s state tick).
    if (first && m.type !== 'hello') sendState(true);
  }

  function handle(m) {
    switch (m.type) {
      case 'hello': onHello(m); break;
      case 'item': onItem(m); break;
      case 'tiles': onTiles(m); break;
      case 'snap': onSnap(m); break;
      case 'snapUrl': onSnapUrl(m); break;
      case 'status': S.status = m; if (m.paused) S.pausedLocally = false; break;
      case 'queue': S.queue = m.upNext.slice(0, M.MAX_UP_NEXT).map(function (q) { return { id: q.id, title: M.cap(q.title), live: q.live, durationMs: q.durationMs }; }); break;
      case 'end': onEnd(m); break;
      case 'ping': send('pong', { at: m.at }); break;
      case 'pong': break;
      default: break;
    }
    render();
  }

  function onHello(m) {
    S.hello = m;
    S.helloSeen = true;
    var scale = clamp(m.textScale || 1, 0.75, 1.5);
    document.documentElement.style.setProperty('--scale', String(scale));
    document.documentElement.style.setProperty('--sub-scale', String(clamp(m.subtitleScale || 1, 0.5, 2)));
    cls(body, 'still', !!m.reducedMotion);
    cls(body, 'discreet', !!m.discreet);
    cls(body, 'sub-plain', !m.subtitleBackground);
    S.updateV = m.v > M.VERSION ? m.v : 0;
    // R-94: the phone knows what this TV is called (Cast doesn't tell a receiver page its own name).
    S.tvName = typeof m.tvName === 'string' ? M.cap(m.tvName) : S.tvName;
    var t = m.snapshot.transport;
    if (t === 'channel') setSnapTransport('channel');
    else if (t === 'http') setSnapTransport('http');
    else if (S.snapFails < T.SNAP_FAILS) setSnapTransport('http');
    sendCaps();
    // C-B1: a phone that (re)joins while this page shows a failure hears about it again (the first word may have been
    // lost with the old connection, e.g. a Wi-Fi drop).
    if (S.screen === 'cantplay' && S.lastError) send('error', S.lastError);
    restartSnapTimers();
  }

  function onItem(m) {
    var it = {
      id: m.id, title: M.cap(m.title), site: M.cap(m.site), live: m.live, durationMs: m.durationMs,
      thumb: typeof m.thumb === 'string' && /^https?:/i.test(m.thumb) ? m.thumb : null,
      next: m.next ? { title: M.cap(m.next.title), startsInS: m.next.startsInS } : null,
      index: m.index, count: m.count, subtitleOffsetMs: m.subtitleOffsetMs
    };
    if (!S.items[m.id]) S.itemOrder.push(m.id);
    S.items[m.id] = it;
    while (S.itemOrder.length > 30) delete S.items[S.itemOrder.shift()];
    if (m.id === S.playingId) {
      if (m.live) S.live = true;
      S.overlayUntil = now() + T.OVERLAY_MS;
      applySubtitleOffset();
    }
  }

  function onEnd(m) {
    var it = currentItem();
    S.end = { played: m.played, title: it ? it.title : curTitle(), site: it ? it.site : curSite(), durationMs: it ? it.durationMs : null, thumb: it ? it.thumb : null, live: S.live };
    S.starting = null;
    S.endSince = now();
    setScreen('end');
    render();
    focusFirst([$('endAgain')]);
  }

  // ---- tiles (R4, R5, T1, T2) ---------------------------------------------------------------------------------------------
  var LAYOUTS = ['two', 'three', 'four', 'onePlusThree'];
  var TILE_COUNT = { two: 2, three: 3, four: 4, onePlusThree: 4 };

  /** C-B4/C-B5: no tiles at all: the grid, its pictures and snapshot addresses go, the video fills the screen again. */
  function resetTiles() {
    S.tiles = null;
    S.tileKey = '';
    S.snapUrls = {};
    snapTimers.forEach(function (id) { clearInterval(id); });
    snapTimers = [];
    tileEls = [];
    $('tiles').textContent = '';
    S.bar = null;
    video.muted = false;   // D-89: mute belongs to the tile with sound; one video plays with sound again
    placeVideo();
  }

  /**
   * C-B5: everything the last cast left on the TV goes (titles, tiles, end board, picture): the next cast starts on a
   * clean page. On Stop from the phone, and when the phone ends its session on purpose.
   */
  function resetAll() {
    resetTiles();
    S.items = {}; S.itemOrder = []; S.playingId = null; S.pendingId = null; S.queue = [];
    S.media = null; S.end = null; S.cant = null; S.starting = null; S.live = false; S.loading = false;
    S.endedFor = null; S.lostSince = 0; S.pausedSince = 0; S.endSince = 0; S.liveIdle = false; S.upNextShownFor = null;
    clearTimeout(S.finishTimer);
    cls(body, 'fresh', true); // no last frame of the old video, ever
    setScreen('idle');
    render();
  }

  function onTiles(m) {
    var filled = m.slots.filter(function (s) { return s && s.itemId; }).length;
    if (m.mode === 'single' || filled < 2 && m.mode !== 'phoneCombines') { if (S.tiles) { resetTiles(); render(); } return; }
    var layout = LAYOUTS.indexOf(m.layout) >= 0 ? m.layout : 'two';
    var slots = m.slots.slice(0, TILE_COUNT[layout]).map(function (s, i) {
      var c = s.crop;
      var l = clamp(c.l, 0, 1), t = clamp(c.t, 0, 1), r = clamp(c.r, 0, 1), b = clamp(c.b, 0, 1);
      if (r - l < 0.05) { l = 0; r = 1; }
      if (b - t < 0.05) { t = 0; b = 1; }
      return { index: i, itemId: s.itemId, title: M.cap(s.title), live: s.live, crop: { l: l, t: t, r: r, b: b }, zoom: clamp(s.zoom || 1, 1, 4), color: s.color, note: s.note ? M.cap(s.note) : '', paused: !!s.paused };
    });
    S.exitUntil = 0;   // D-94: Back brought the grid back (a filled tile), it didn't ask to leave
    var before = S.tiles ? S.tiles.slots : [];
    S.tiles = { layout: layout, slots: slots, focused: clamp(m.focused, 0, Math.max(0, slots.length - 1)), audio: m.audio, mode: m.mode,
      muted: !!m.muted, othersPause: !!m.othersPause };
    // D-89: the page's video is the tile with sound; the phone says whether it is muted.
    video.muted = !!m.muted;
    if (S.bar && !S.tiles.slots[S.bar.from]) S.bar.from = S.tiles.focused;
    var key = layout + '|' + slots.length + '|' + m.mode;
    var rebuilt = key !== S.tileKey;
    // C-B5: a tile that now shows another video (or none) never keeps the old one's picture or snapshot address. M1: a
    // tile that keeps its video keeps its address through a new layout too (it used to go blank when a third was added).
    slots.forEach(function (sl, i) {
      var old = before[i];
      if (old && old.itemId === sl.itemId) return;
      delete S.snapUrls[i];
      var t = !rebuilt && tileEls[i];
      if (t) { t.imgs.forEach(function (img) { cls(img, 'on', false); img.removeAttribute('src'); }); t.since = now(); }
    });
    Object.keys(S.snapUrls).forEach(function (k) { if (!(Number(k) < slots.length)) delete S.snapUrls[k]; });
    S.tileKey = key;
    buildTiles(rebuilt);
    restartSnapTimers();
  }

  function tilesMode() {
    var t = S.tiles;
    if (!t || t.slots.length < 2) return null;
    if (t.mode === 'webFocus' || t.mode === 'tvAppGrid') return 'focus';
    if (t.mode === 'phoneCombines') return 'combines';
    return null;
  }

  /**
   * Touch displays (TvHub) keep a control band under the tiles so the hub's buttons never cover a tile, its LIVE label
   * or its chips (R-39). Tiles keep the same geometry whether the hub is showing or faded.
   */
  var TOUCH_BAND = 112;
  function tileRects() { return layoutRects(S.tiles.layout, view.W, view.H - (S.touch ? TOUCH_BAND : 0)); }
  /** 5% title safe (R-18): text and chips on video never sit closer to the frame edge than this (48 x 27 at 960 x 540). */
  function safeInsets(r, small) {
    var bx = small ? 10 : 16, by = small ? 10 : 14, sx = view.W * 0.05, sy = view.H * 0.05;
    return {
      l: Math.max(bx, sx - r.x), t: Math.max(by, sy - r.y),
      r: Math.max(bx, sx - (view.W - r.x - r.w)), b: Math.max(by, sy - (view.H - r.y - r.h))
    };
  }

  /** Slot rectangles in stage pixels: 16 px margin, 8 px gaps (TvFocus). */
  function layoutRects(layout, W, H) {
    var p = 16, g = 8, iw = W - 2 * p, ih = H - 2 * p, w, h, wl, wr, hr, y;
    if (layout === 'two') {
      w = (iw - g) / 2; h = Math.min(ih, w * 9 / 16); y = p + (ih - h) / 2;
      return [{ x: p, y: y, w: w, h: h }, { x: p + w + g, y: y, w: w, h: h }];
    }
    if (layout === 'three') {
      wl = (iw - g) * 2 / 3; wr = iw - g - wl; hr = (ih - g) / 2;
      return [{ x: p, y: p, w: wl, h: ih }, { x: p + wl + g, y: p, w: wr, h: hr }, { x: p + wl + g, y: p + hr + g, w: wr, h: hr }];
    }
    if (layout === 'four') {
      w = (iw - g) / 2; h = (ih - g) / 2;
      return [{ x: p, y: p, w: w, h: h }, { x: p + w + g, y: p, w: w, h: h }, { x: p, y: p + h + g, w: w, h: h }, { x: p + w + g, y: p + h + g, w: w, h: h }];
    }
    wl = (iw - g) * 3 / 4; wr = iw - g - wl; hr = (ih - 2 * g) / 3;
    return [{ x: p, y: p, w: wl, h: ih }, { x: p + wl + g, y: p, w: wr, h: hr }, { x: p + wl + g, y: p + hr + g, w: wr, h: hr }, { x: p + wl + g, y: p + 2 * (hr + g), w: wr, h: hr }];
  }

  var tileEls = [];
  function el(tag, className, text) {
    var e = document.createElement(tag);
    if (className) e.className = className;
    if (text !== undefined) e.textContent = text;
    return e;
  }
  var PAUSE_GLYPH = '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3" stroke-linecap="round" aria-hidden="true"><path d="M8 5v14M16 5v14"></path></svg>';
  var MUTED_GLYPH = '<svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M11 5L6 9H2v6h4l5 4V5z"></path><path d="M22 9l-6 6M16 9l6 6"></path></svg>';
  function liveLabel() { var s = el('span', 'live-label'); s.appendChild(el('i')); s.appendChild(document.createTextNode('LIVE')); return s; }

  function buildTiles(rebuilt) {
    var box = $('tiles');
    var mode = tilesMode();
    if (!mode) { if (box.childNodes.length) { box.textContent = ''; tileEls = []; } return; }
    var hadFocus = box.contains(document.activeElement);
    if (rebuilt || tileEls.length !== S.tiles.slots.length) {
      box.textContent = '';
      tileEls = S.tiles.slots.map(function (slot, i) {
        var b = el('button', 'tile');
        b.type = 'button';
        b.setAttribute('data-index', String(i));
        var frames = el('div', 'frames');
        var a = el('img'); a.alt = ''; var c = el('img'); c.alt = '';
        frames.appendChild(a); frames.appendChild(c);
        b.appendChild(frames);
        b.appendChild(el('div', 'shade'));
        // One label rule on both TV surfaces (R-18): title pill top-left, LIVE or time pill bottom-left, chips
        // top-right, every one on a 75% black scrim and inside the 5% title-safe area, in every layout.
        var info = el('div', 'info');
        info.appendChild(el('span', 't-title'));
        info.appendChild(el('span', 't-sub'));
        b.appendChild(info);
        var nm = el('span', 'name');
        var spk = el('i', 'spk');
        spk.innerHTML = '<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M11 5L6 9H2v6h4l5 4V5z"></path><path d="M15.5 8.5a5 5 0 0 1 0 7"></path></svg>';
        nm.appendChild(spk);
        nm.appendChild(el('span', 'nt'));
        b.appendChild(nm);
        var status = el('span', 'status');
        status.appendChild(liveLabel());
        status.appendChild(el('span', 'st-time mono'));
        b.appendChild(status);
        b.appendChild(el('span', 'fps'));
        // M1, m11: what a tile without a picture is doing, in plain words ("Loading…", the phone's note, "Add a video").
        b.appendChild(el('span', 'hint'));
        // D-89: paused and muted chips top-right (R-18), Ink on the scrim.
        var chips = el('span', 'chips');
        var cp = el('span', 'chip chip-paused'); cp.innerHTML = PAUSE_GLYPH;
        var cm = el('span', 'chip chip-muted'); cm.innerHTML = MUTED_GLYPH;
        chips.appendChild(cp); chips.appendChild(cm);
        b.appendChild(chips);
        b.appendChild(el('span', 'ring'));
        b.addEventListener('click', function () { if (!S.touch) return; chooseTile(i); });
        var t = { btn: b, frames: frames, imgs: [a, c], front: 0, info: info, status: status, name: b.querySelector('.name'), fps: b.querySelector('.fps'), hint: b.querySelector('.hint'), chipPaused: cp, chipMuted: cm, loading: false, nat: null, since: now() };
        [a, c].forEach(function (img, k) {
          img.addEventListener('load', function () { onFrameLoaded(t, k); });
          img.addEventListener('error', function () { onFrameFailed(t, k); });
        });
        box.appendChild(b);
        return t;
      });
    }
    var rects = tileRects();
    S.tiles.slots.forEach(function (slot, i) {
      var t = tileEls[i], r = rects[i];
      var b = t.btn;
      b.style.left = r.x + 'px'; b.style.top = r.y + 'px'; b.style.width = r.w + 'px'; b.style.height = r.h + 'px';
      var ins = safeInsets(r, r.w < 400);
      b.style.setProperty('--sl', ins.l.toFixed(1) + 'px'); b.style.setProperty('--st', ins.t.toFixed(1) + 'px');
      b.style.setProperty('--sr', ins.r.toFixed(1) + 'px'); b.style.setProperty('--sb', ins.b.toFixed(1) + 'px');
      cls(b, 'chosen', !!S.touch && i === S.tiles.focused);
      var isVideo = mode === 'focus' && i === S.tiles.focused;
      var empty = !slot.itemId && !slot.title && !slot.color;
      cls(b, 'video', isVideo || mode === 'combines');
      cls(b, 'snap', mode === 'focus' && !isVideo);
      cls(b, 'empty', empty && !isVideo);
      cls(b, 'small', r.w < 400);
      b.style.background = slot.color && !isVideo && mode === 'focus' ? slot.color : '';
      t.slot = slot; t.rect = r; t.isVideo = isVideo;
    });
    if (hadFocus || !box.contains(document.activeElement)) focusTileButton(S.tiles.focused);
  }

  function focusTileButton(i) {
    var t = tileEls[i];
    if (t && !S.touch && !S.bar && overlayButtons().length === 0) { try { t.btn.focus({ preventScroll: true }); } catch (e) { t.btn.focus(); } }
  }

  function renderTiles() {
    var mode = tilesMode();
    show($('tiles'), !!mode && S.screen === 'play');
    if (!mode) return;
    var it = currentItem();
    var fps = snapFps();
    tileEls.forEach(function (t, i) {
      var slot = t.slot;
      var title = S.hello.discreet ? '' : slot.title;
      // D-96: one label for every tile, as on the TV app and the phone: a name pill, Lamp with the speaker on the tile with
      // sound (the big title card is gone).
      var showInfo = false;
      var sound = S.tiles.audio === i && !!slot.itemId;
      show(t.info, false);
      show(t.btn.querySelector('.shade'), false);   // the labels carry their own scrim (R-18)
      // LIVE, or the time on the video tile, bottom-left on its own scrim pill: never faded, never moved (R-18).
      var dur = pDuration();
      var timeText = !slot.live && t.isVideo && dur > 0 ? fmt(pTime(), dur >= 3600) + ' / ' + fmt(dur, dur >= 3600) : '';
      show(t.status.querySelector('.live-label'), !!slot.live);
      setText(t.status.querySelector('.st-time'), timeText);
      show(t.status.querySelector('.st-time'), !!timeText);
      show(t.status, !!slot.live || !!timeText);
      setText(t.info.querySelector('.t-title'), title || (t.isVideo ? curTitle() : ''));
      var subParts = [];
      var slotItem = slot.itemId ? S.items[slot.itemId] : null;
      if (showInfo && slotItem && slotItem.site && !S.hello.discreet) subParts.push(slotItem.site);
      if (S.tiles.audio === i) subParts.push(S.tiles.muted ? 'muted' : 'sound on');
      setText(t.info.querySelector('.t-sub'), subParts.join(' · '));
      var nameText = title || (sound && t.isVideo && !S.hello.discreet ? curTitle() : '');
      show(t.name, !!nameText || sound);
      setText(t.name.querySelector('.nt'), nameText);
      cls(t.name, 'sound', sound);
      cls(t.name, 'muted', sound && !!S.tiles.muted);
      var snap = mode === 'focus' && !t.isVideo && !!(slot.itemId || slot.color);
      // m11: the refresh rate is a diagnostic (?debug=1), not something to read on a TV.
      show(t.fps, snap && DEBUG);
      setText(t.fps, fps + ' fps');
      show(t.frames, snap);
      var pictured = t.imgs.some(function (img) { return img.classList.contains('on'); });
      var hint = '';
      if (mode === 'focus' && !t.isVideo) {
        if (!slot.itemId && !slot.color) hint = 'Add a video from your phone';
        else if (slot.note) hint = slot.note;
        else if (slot.itemId && !pictured) hint = 'Loading…';
      }
      setText(t.hint, hint);
      show(t.hint, !!hint);
      cls(t.hint, 'quiet', !slot.itemId);
      // D-89: the paused chip on a paused tile (the video tile also when the session itself is paused); the muted chip
      // on the tile with sound when it is muted.
      var isPaused = !!slot.paused || (t.isVideo && pState() === 'PAUSED');
      var isMuted = !!S.tiles.muted && S.tiles.audio === i;
      show(t.chipPaused, isPaused);
      show(t.chipMuted, isMuted);
      var nChips = (isPaused ? 1 : 0) + (isMuted ? 1 : 0);
      cls(t.btn, 'chips-1', nChips === 1);
      cls(t.btn, 'chips-2', nChips === 2);
    });
    cls(body, 'ov-hidden', now() > S.overlayUntil && mode === 'focus' && !S.fake);
  }

  /**
   * D-94: Back with nothing left to back out of: the first asks ("Press Back again to exit"), a second within 3 s closes
   * the TV page. The phone is told first, so it ends the cast instead of reconnecting to a page that left.
   */
  function backToExit() {
    var t = now();
    if (t < S.exitUntil) {
      S.exitUntil = 0;
      send('key', { action: 'exit' });
      setTimeout(function () { try { if (context && context.stop) context.stop(); } catch (e) { console.warn('[lucerna] stop', e); } }, 300);
      return;
    }
    S.exitUntil = t + 3000;
  }

  function chooseTile(i) {
    if (!S.tiles || !S.tiles.slots[i]) return;
    // Immediate feedback; the phone answers with the new tile state and the tile's stream (T1).
    S.tiles.focused = i;
    S.tiles.audio = i;
    buildTiles(false);
    send('key', { action: 'focusTile', n: i });
    S.overlayUntil = now() + T.OVERLAY_MS;
    render();
  }

  /**
   * Where the media element goes: full-bleed for one video, or into the focused slot with crop and zoom (R4).
   * Placed with plain boxes, never CSS transform or clip-path: Cast and Android TV devices draw video on a hardware
   * plane that can't be scaled or clipped that way, and showed black with the clock running (D-87). #vwrap becomes the
   * slot (a plain rectangle, overflow hidden); the video's box is the whole frame scaled so the crop fills the slot.
   */
  function placeVideo() {
    var target = PREVIEW ? $('fakevideo') : video;
    var wrap = $('vwrap');
    var mode = tilesMode();
    var vw = window.innerWidth || view.W, vh = window.innerHeight || view.H;
    if (mode !== 'focus' || S.screen !== 'play') {
      ['left', 'top', 'width', 'height', 'objectFit'].forEach(function (k) { target.style[k] = ''; wrap.style[k] = ''; });
      return;
    }
    var r = tileRects()[S.tiles.focused];
    var slot = S.tiles.slots[S.tiles.focused];
    var sx = view.x + r.x * view.s, sy = view.y + r.y * view.s, sw = r.w * view.s, sh = r.h * view.s;
    var aspect = (!PREVIEW && video.videoWidth && video.videoHeight) ? video.videoWidth / video.videoHeight : 16 / 9;
    var cw, ch, cx, cy;
    if (vw / vh > aspect) { ch = vh; cw = vh * aspect; cx = (vw - cw) / 2; cy = 0; } else { cw = vw; ch = vw / aspect; cx = 0; cy = (vh - ch) / 2; }
    var c = slot.crop;
    var rx = cx + c.l * cw, ry = cy + c.t * ch, rw = (c.r - c.l) * cw, rh = (c.b - c.t) * ch;
    var k = Math.max(sw / rw, sh / rh) * slot.zoom;
    // The frame's top-left on screen (the crop's centre on the slot's centre), then relative to the slot.
    var fx = sx + sw / 2 - k * (rx + rw / 2) + k * cx, fy = sy + sh / 2 - k * (ry + rh / 2) + k * cy;
    wrap.style.left = sx.toFixed(2) + 'px'; wrap.style.top = sy.toFixed(2) + 'px';
    wrap.style.width = sw.toFixed(2) + 'px'; wrap.style.height = sh.toFixed(2) + 'px';
    target.style.left = (fx - sx).toFixed(2) + 'px'; target.style.top = (fy - sy).toFixed(2) + 'px';
    target.style.width = (k * cw).toFixed(2) + 'px'; target.style.height = (k * ch).toFixed(2) + 'px';
    target.style.objectFit = 'fill';
  }

  // ---- motion snapshots: http first, channel after two failed image loads (R4, P-4) -------------------------------------
  var snapTimers = [];
  function snapFps() {
    var c = S.hello.snapshot;
    if (S.snapTransport === 'channel') {
      var n = Math.max(1, tileEls.filter(function (t) { return !t.isVideo; }).length);
      return Math.max(1, Math.floor(clamp(c.channelFps, 1, 15) / n));
    }
    return clamp(c.fps, 1, 15);
  }
  function setSnapTransport(t) {
    if (S.snapTransport === t) return;
    S.snapTransport = t;
    restartSnapTimers();
    sendState(true);
  }
  function restartSnapTimers() {
    snapTimers.forEach(function (id) { clearInterval(id); });
    snapTimers = [];
    if (PREVIEW || S.snapTransport !== 'http' || tilesMode() !== 'focus') return;
    var every = Math.round(1000 / clamp(S.hello.snapshot.fps, 1, 15));
    tileEls.forEach(function (t, i) {
      if (t.isVideo || !(t.slot && t.slot.itemId)) return;
      snapTimers.push(setInterval(function () { pullSnap(t, i); }, every));
      pullSnap(t, i);
    });
  }
  function pullSnap(t, i) {
    var tmpl = S.snapUrls[i];
    if (!tmpl || S.hidden || t.loading || S.snapTransport !== 'http' || S.screen !== 'play') return;
    // D-93: a paused tile's picture can't change: it keeps the one it has (re-fetching it flashed at the snapshot rate).
    if (t.slot && t.slot.paused && t.imgs.some(function (img) { return img.classList.contains('on'); })) return;
    var back = t.imgs[1 - t.front];
    t.loading = true;
    back.src = tmpl + (tmpl.indexOf('?') >= 0 ? '&' : '?') + 't=' + now();
  }
  function onFrameLoaded(t, k) {
    t.loading = false;
    if (k === t.front && t.imgs[k].classList.contains('on')) return;
    S.snapFails = 0;
    var img = t.imgs[k];
    t.nat = { w: img.naturalWidth || 16, h: img.naturalHeight || 9 };
    cropImage(t, img);
    cls(img, 'on', true);
    cls(t.imgs[1 - k], 'on', false);
    t.front = k;
  }
  function onFrameFailed(t, k) {
    t.loading = false;
    if (!t.imgs[k].src || /^data:/.test(t.imgs[k].src)) return;
    S.snapFails++;
    if (S.snapFails >= T.SNAP_FAILS && S.hello.snapshot.transport !== 'http') setSnapTransport('channel');
  }
  function cropImage(t, img) {
    var r = t.rect, slot = t.slot, nw = t.nat.w, nh = t.nat.h, c = slot.crop;
    var rw = (c.r - c.l) * nw, rh = (c.b - c.t) * nh;
    var k = Math.max(r.w / rw, r.h / rh) * slot.zoom;
    var tx = r.w / 2 - k * (c.l * nw + rw / 2), ty = r.h / 2 - k * (c.t * nh + rh / 2);
    img.style.width = nw + 'px'; img.style.height = nh + 'px';
    img.style.transform = 'translate(' + tx.toFixed(2) + 'px,' + ty.toFixed(2) + 'px) scale(' + k.toFixed(5) + ')';
  }
  function onSnapUrl(m) {
    if (m.url && /^https?:\/\//i.test(m.url)) S.snapUrls[m.tile] = m.url; else delete S.snapUrls[m.tile];
    restartSnapTimers();
  }
  function onSnap(m) {
    var t = tileEls[m.tile];
    if (!t || t.isVideo || typeof m.jpeg !== 'string') return;
    if (m.jpeg.length > M.MAX_SNAP_BASE64 || !/^[A-Za-z0-9+/]+={0,2}$/.test(m.jpeg)) return;
    var back = t.imgs[1 - t.front];
    back.src = 'data:image/jpeg;base64,' + m.jpeg;
  }

  // ---- playback: LOAD, live config, segment format, tracks (R3, D7, S2) -------------------------------------------------
  function fetchText(url, ms) {
    return new Promise(function (resolve) {
      var done = false;
      var timer = setTimeout(function () { if (!done) { done = true; resolve(null); } }, ms);
      fetch(url, { cache: 'no-store', credentials: 'omit' }).then(function (r) { return r.ok ? r.text() : null; })
        .then(function (t) { if (!done) { done = true; clearTimeout(timer); resolve(t); } }, function () { if (!done) { done = true; clearTimeout(timer); resolve(null); } });
    });
  }
  /** Reads the HLS playlist to learn the segment format (EXT-X-MAP = fMP4, never TS) and low-latency parts. */
  function sniffHls(url) {
    return fetchText(url, T.SNIFF_MS).then(function (text) {
      if (!text || text.indexOf('#EXTM3U') < 0) return null;
      if (text.indexOf('#EXT-X-STREAM-INF') >= 0) {
        var lines = text.split(/\r?\n/), uri = null;
        for (var i = 0; i < lines.length; i++) {
          if (lines[i].indexOf('#EXT-X-STREAM-INF') === 0) {
            for (var j = i + 1; j < lines.length; j++) { var l = lines[j].trim(); if (l && l.charAt(0) !== '#') { uri = l; break; } }
            break;
          }
        }
        if (!uri) return null;
        var codecs = (/CODECS="([^"]*)"/.exec(text) || [])[1] || '';
        return fetchText(new URL(uri, url).href, T.SNIFF_MS).then(function (media) {
          if (!media) return null;
          return { fmp4: media.indexOf('#EXT-X-MAP') >= 0, ll: /#EXT-X-PART(-INF)?:/.test(media), codecs: codecs };
        });
      }
      return { fmp4: text.indexOf('#EXT-X-MAP') >= 0, ll: /#EXT-X-PART(-INF)?:/.test(text), codecs: '' };
    });
  }

  function buildPlaybackConfig(o) {
    var cfg = new cast.framework.PlaybackConfig();
    var offset = clamp(S.hello.liveOffsetS || 6, 1, 120);
    cfg.autoResumeNumberOfSegments = 1;
    cfg.initialBandwidth = 8000000;
    // Lucerna's own record of the latency the phone asked for (hello.liveOffsetS); Shaka reads shakaConfig below.
    cfg.liveSyncDuration = o.live ? offset : 0;
    var streaming = {
      rebufferingGoal: o.live ? 1.5 : 2,
      bufferingGoal: o.live ? 12 : 30,
      bufferBehind: 30,
      stallEnabled: true, stallThreshold: 1, stallSkip: 0.1,
      lowLatencyMode: !!o.ll,
      retryParameters: { maxAttempts: o.live ? 6 : 4, baseDelay: 500, backoffFactor: 2, fuzzFactor: 0.5, timeout: 20000 }
    };
    if (o.live) streaming.liveSync = { enabled: true, targetLatency: offset, targetLatencyTolerance: 1, maxPlaybackRate: 1.1, minPlaybackRate: 0.95, panicMode: false };
    cfg.shakaConfig = {
      // HLS live starts 3 segments behind the live edge (R3); DASH uses its suggestedPresentationDelay.
      manifest: { defaultPresentationDelay: 0, hls: { liveSegmentsDelay: 3, ignoreManifestProgramDateTime: false } },
      streaming: streaming
    };
    return cfg;
  }

  var lastCfg = null;
  function onLoadRequest(req) {
    var media = req.media || {};
    var url = media.contentUrl || media.contentId || '';
    var cd = media.customData || {};
    var id = typeof cd.itemId === 'string' ? cd.itemId.slice(0, 200) : null;
    var Msgs = cast.framework.messages;
    S.starting = null; clearTimeout(startTimer);
    S.end = null; S.cant = null; S.liveIdle = false; S.lastError = null;
    S.loading = true;
    cls(body, 'fresh', true); // C-B5/C-B16: the last frame of what played before never shows as this one's first
    S.pendingId = id;
    var live = media.streamType === 'LIVE';
    // m7: a live stream starts at the live edge (the player's own offset), never at a start time: an older phone's
    // `currentTime: 0` meant the start of the relay's whole window (26-34 s behind, minutes after Back to live).
    if (live) delete req.currentTime;
    S.liveBase = null;
    // M2: the stall watch belongs to the new LOAD at once: a live stream's (it seeks to the live edge after 10 s stuck)
    // used to carry over while a video loaded at its place and threw it to its end.
    S.live = live;
    S.stall = { lastT: -1, stuckMs: 0 };
    var ctype = String(media.contentType || '');
    var isHls = /mpegurl/i.test(ctype) || /\.m3u8(\?|#|$)/i.test(url);
    var isDash = /dash/i.test(ctype) || /\.mpd(\?|#|$)/i.test(url);
    // D7: a codec named in the content type that this TV can't decode never reaches the player.
    var codecs = (/codecs="?([^";]+)"?/i.exec(ctype) || [])[1];
    if (codecs) {
      var bad = codecs.split(',').map(function (c) { return c.trim(); }).filter(function (c) { return c && !canPlay(/^mp4a|^ac-3|^ec-3|^opus/i.test(c) ? 'audio/mp4' : 'video/mp4', c); });
      if (bad.length) {
        cantPlay(id, 'format', bad.join(','), bad.map(family).filter(Boolean)[0] || bad[0]);
        var err = new Msgs.ErrorData(Msgs.ErrorType.LOAD_FAILED);
        err.reason = Msgs.ErrorReason ? Msgs.ErrorReason.NOT_SUPPORTED : 'NOT_SUPPORTED';
        S.loading = false;
        return Promise.reject(err);
      }
    }
    // Text tracks (S2): the phone sends the tracks it wants shown; turn the first one on if it didn't say.
    if (Array.isArray(media.tracks) && !req.activeTrackIds) {
      var text = media.tracks.filter(function (t) { return t && t.type === 'TEXT'; });
      if (text.length) req.activeTrackIds = [text[0].trackId];
    }
    var sniff = isHls ? sniffHls(url) : Promise.resolve(null);
    return sniff.then(function (info) {
      if (isHls) {
        var fmp4 = info ? info.fmp4 : String(media.hlsSegmentFormat || '').toLowerCase() === 'fmp4';
        if (info || media.hlsSegmentFormat) {
          // fMP4 is never treated as TS (D7): the playlist's EXT-X-MAP wins over anything else.
          media.hlsSegmentFormat = fmp4 ? Msgs.HlsSegmentFormat.FMP4 : (media.hlsSegmentFormat || Msgs.HlsSegmentFormat.TS);
          media.hlsVideoSegmentFormat = fmp4 ? Msgs.HlsVideoSegmentFormat.FMP4 : Msgs.HlsVideoSegmentFormat.MPEG2_TS;
        }
      }
      var cfg = buildPlaybackConfig({ live: live, ll: !!(info && info.ll), dash: isDash });
      lastCfg = cfg;
      player.setPlaybackConfig(cfg);
      S.media = media;
      S.live = live;
      return req;
    });
  }

  function onLoadComplete() {
    S.loading = false;
    var media = player.getMediaInformation() || S.media || {};
    S.media = media;
    S.live = media.streamType === 'LIVE' || !!(currentItem() && currentItem().live);
    var cd = media.customData || {};
    var id = typeof cd.itemId === 'string' ? cd.itemId.slice(0, 200) : null;
    if (id && id !== S.playingId) {
      S.playingId = id;
      S.endedFor = null;
      S.upNextShownFor = null;
      S.stall = { lastT: -1, stuckMs: 0 };
      send('want', { itemId: id });
    }
    S.playStartedAt = now();
    S.overlayUntil = now() + T.OVERLAY_MS;
    S.hubUntil = now() + T.HUB_HIDE_MS;
    S.cant = null;
    setScreen('play');
    applySubtitleOffset();
    sendState(true);
    render();
  }

  // ---- errors (R3) -------------------------------------------------------------------------------------------------------
  function classify(ev) {
    var e = ev && ev.error;
    var mediaErr = video.error;
    var code = null, detail = '';
    var status = 0;
    if (e && e.data && e.data.length > 1 && typeof e.data[1] === 'number') status = e.data[1];
    if (e && typeof e.status === 'number') status = e.status;
    if (status === 401 || status === 403) code = 'forbidden';
    else if (e && typeof e.code === 'number' && e.code >= 1 && e.code <= 4) code = { 1: 'network', 2: 'network', 3: 'decode', 4: 'format' }[e.code];
    else if (mediaErr && mediaErr.code) code = { 1: 'network', 2: 'network', 3: 'decode', 4: 'format' }[mediaErr.code];
    else if (e && typeof e.category === 'number') code = e.category === 1 ? 'network' : e.category === 3 ? 'decode' : e.category === 4 ? 'format' : 'network';
    else {
      var d = ev && ev.detailedErrorCode;
      code = d === 102 ? 'decode' : d === 104 ? 'format' : 'network';
    }
    if (e && e.message) detail = String(e.message);
    else if (mediaErr && mediaErr.message) detail = mediaErr.message;
    else if (ev && ev.detailedErrorCode) detail = 'Cast error ' + ev.detailedErrorCode;
    if (status) detail = ('HTTP ' + status + ' ' + detail).trim();
    return { code: code || 'network', detail: M.cap(detail, 120) };
  }
  /** The media element calls a 404 "format not supported"; a quick HEAD tells a missing file from a real format problem. */
  function confirmFormat(c) {
    var url = S.media ? (S.media.contentUrl || S.media.contentId || '') : '';
    if (c.code !== 'format' || !/^https?:/i.test(url)) return Promise.resolve(c);
    return new Promise(function (resolve) {
      var done = false;
      var timer = setTimeout(function () { if (!done) { done = true; resolve(c); } }, T.SNIFF_MS);
      fetch(url, { method: 'HEAD', cache: 'no-store', credentials: 'omit' }).then(function (r) {
        if (done) return; done = true; clearTimeout(timer);
        if (r.ok) resolve(c);
        else resolve({ code: r.status === 401 || r.status === 403 ? 'forbidden' : 'network', detail: ('HTTP ' + r.status + ' ' + c.detail).trim() });
      }, function () { if (!done) { done = true; clearTimeout(timer); resolve(c); } });
    });
  }
  function onPlayerError(ev) {
    var id = S.pendingId || S.playingId;
    S.loading = false;
    confirmFormat(classify(ev)).then(function (c) { reportError(id, c); });
  }
  function reportError(id, c) {
    var key = id + '|' + c.code;
    if (key === S.errorKey && now() - S.errorAt < 3000) return;
    S.errorKey = key; S.errorAt = now();
    if (c.code === 'format' || c.code === 'decode') cantPlay(id, c.code, c.detail, null);
    else if (id && id !== S.playingId || !S.live) {
      // C-B1 (TV side): a video that didn't load says so with its own title; the last video's board never stays up.
      S.playingId = id || S.playingId;
      cantPlay(id, c.code, c.detail, null, c.code === 'forbidden' ? 'The link for this video expired' : 'This video didn\'t load',
        'Try again or choose another way on your phone.');
    } else { send('error', { itemId: id, code: c.code, detail: c.detail }); S.liveIdle = true; }
    render();
  }
  function cantPlay(id, code, detail, fam, head, sub) {
    S.lastError = { itemId: id, code: code, detail: detail || '' };
    send('error', S.lastError);
    var it = id ? S.items[id] : null;
    var md = S.media && S.media.metadata;
    var title = S.hello.discreet ? '' : (it && it.title) || (md && md.title ? M.cap(md.title) : '');
    S.cant = { title: title, detail: head ? '' : [fam, playsLine()].filter(Boolean).join(' · '), head: head || null, sub: sub || null };
    setScreen('cantplay');
    render();
  }

  // ---- ended, live IDLE (Spool D-114) -------------------------------------------------------------------------------------
  function onMaybeFinished(idleReason) {
    if (pState() !== 'IDLE') return;
    var was = S.playingId;
    // Repeated IDLE statuses don't restart the hold (CAF can broadcast status more often than every 2 s).
    if (S.finishTimer && S.finishPending === was + '|' + idleReason) return;
    clearTimeout(S.finishTimer);
    S.finishPending = was + '|' + idleReason;
    S.finishTimer = setTimeout(function () {
      S.finishTimer = null; S.finishPending = null;
      if (pState() !== 'IDLE' || S.playingId !== was) return;
      if (idleReason === 'FINISHED' && !S.live) {
        if (was && S.endedFor !== was) { S.endedFor = was; send('ended', { itemId: was }); sendState(true); }
      } else if (S.live && idleReason !== 'CANCELLED') {
        S.liveIdle = true;
        render();
      }
    }, T.FINISH_HOLD_MS);
  }

  // ---- subtitle offset, re-applied after seeks (S2) ----------------------------------------------------------------------
  function applySubtitleOffset() {
    var it = currentItem();
    var off = it ? (it.subtitleOffsetMs || 0) / 1000 : 0;
    var tracks = video.textTracks;
    if (!tracks) return 0;
    var changed = 0;
    for (var i = 0; i < tracks.length; i++) {
      var cues = tracks[i].cues;
      if (!cues) continue;
      for (var j = 0; j < cues.length; j++) {
        var cue = cues[j];
        if (cue.__lucBase === undefined) cue.__lucBase = { s: cue.startTime, e: cue.endTime, off: 0 };
        if (cue.__lucBase.off !== off) {
          cue.startTime = Math.max(0, cue.__lucBase.s + off);
          cue.endTime = Math.max(cue.startTime, cue.__lucBase.e + off);
          cue.__lucBase.off = off;
          changed++;
        }
      }
    }
    return changed;
  }
  video.addEventListener('seeked', function () { applySubtitleOffset(); setTimeout(applySubtitleOffset, 300); });
  video.addEventListener('loadedmetadata', function () { placeVideo(); });

  // ---- "Starting <title>…" for requests the phone must prepare (Spool D-115) ----------------------------------------------
  var startTimer = null;
  function requestStart(action, title) {
    if (S.starting) return;   // repeat presses are ignored while the phone prepares
    send('key', { action: action });
    S.starting = { title: title };
    clearTimeout(startTimer);
    startTimer = setTimeout(function () { S.starting = null; render(); refocus(); }, T.STARTING_TIMEOUT_MS);
    render();
  }

  function setScreen(name) {
    S.screen = name;
    ['idle', 'play', 'end', 'cantplay'].forEach(function (n) { cls(body, 'screen-' + n, n === name); });
    placeVideo();
  }

  // ---- render: everything on screen, from S and the player ---------------------------------------------------------------
  function upNextInfo() {
    if (S.screen !== 'play' || S.live || tilesMode()) return null;
    var it = currentItem();
    var q0 = S.queue[0] || null;
    var next = it && it.next ? it.next : null;
    if (!next && !q0) return null;
    var dur = pDuration();
    if (!(dur > 0)) return null;
    var remaining = dur - pTime();
    var lead = next ? clamp(next.startsInS || T.UP_NEXT_S, 1, 60) : T.UP_NEXT_S;
    if (remaining > lead || remaining <= 0) return null;
    var st = pState();
    if (st !== 'PLAYING' && !S.fake) return null;
    var title = next ? next.title : q0.title;
    var metaParts = [];
    if (q0 && (q0.durationMs || q0.live)) metaParts.push(q0.live ? 'LIVE' : fmt(q0.durationMs / 1000));
    if (q0 && q0.site) metaParts.push(q0.site);
    return { remaining: remaining, title: title, meta: metaParts.join(' · '), then: S.queue[1] || null, dur: dur };
  }

  function overlayButtons() {
    var list = [];
    if (S.screen === 'end' && !S.starting) list.push($('endAgain'), $('endStart'));
    if (!$('upnext').hidden && !S.starting) list.push($('unPlay'));
    if (S.touch && !$('hub').hidden) {
      ['hubTiles', 'hubJump', 'hubBack', 'hubToggle', 'hubNext'].forEach(function (id) { if (!$(id).hidden) list.push($(id)); });
    }
    return list.filter(function (b) { return b && b.offsetParent !== null; });
  }

  function render() {
    var t = now();
    var playing = S.screen === 'play';
    var st = pState();
    var dur = pDuration(), pos = pTime();
    var live = S.live;
    var title = curTitle(), site = curSite();
    var it = currentItem();
    var discreet = !!S.hello.discreet;
    var mode = tilesMode();

    // R-67: the end-of-queue board goes back to idle for good after REST_MS (the phone offers what's next).
    if (S.screen === 'end' && S.endSince && t - S.endSince >= T.REST_MS && !S.starting) {
      S.end = null; S.endSince = 0; setScreen('idle'); playing = false;
    }

    cls(body, 'tiles-on', playing && !!mode);
    show($('exitHint'), t < S.exitUntil);
    show($('gridHint'), playing && mode === 'focus' && !S.touch && !S.bar && !S.starting && t < S.overlayUntil && t >= S.exitUntil);

    // buffering (after a short delay, so a quick hiccup doesn't flash)
    var buffering = playing && (st === 'BUFFERING' || S.loading);
    if (buffering && !S.bufferingSince) S.bufferingSince = t;
    if (!buffering) S.bufferingSince = 0;
    var showBuffering = buffering && (S.fake || t - S.bufferingSince >= T.BUFFER_SHOW_MS) && !mode;
    var paused = playing && st === 'PAUSED' && !buffering;
    var lost = playing && !!S.lostSince;
    var lostForMs = S.fake && S.fake.lostFor !== undefined ? S.fake.lostFor * 1000 : (lost ? t - S.lostSince : 0);
    if (paused && !S.pausedSince) S.pausedSince = t;
    if (!paused) S.pausedSince = 0;
    var reconnecting = playing && !lost && !S.starting && (S.status.relayState === 'refreshing' || S.status.relayState === 'lost' || S.liveIdle);
    // R-67: Paused (unless the stream is reconnecting) and PhoneLost (once its reconnect window is over, and only
    // while nothing plays) give way to the idle screen; play, or the phone coming back, brings the video back.
    var resting = playing && !S.starting && (
      (paused && !reconnecting && t - S.pausedSince >= T.REST_MS) ||
      (lost && lostForMs >= T.REST_MS && st !== 'PLAYING'));
    cls(body, 'resting', resting);
    show($('idle'), (S.screen === 'idle' || resting) && !S.updateV);
    setText($('idleTv'), S.tvName);
    cls($('idleFoot'), 'solo', !S.tvName);
    // R-66: the Up next card never stacks with the reconnecting banner; the banner goes first.
    var un = playing && !showBuffering && !paused && !lost && !reconnecting ? upNextInfo() : null;

    // title overlay (single video)
    var ovOn = playing && !mode && !showBuffering && !paused && !un && !lost && (t < S.overlayUntil || !!(S.fake && S.fake.overlay));
    cls($('ov'), 'show', ovOn && !discreet && !S.touch);
    show($('ovLive'), live);
    setText($('ovTitle'), title);
    var subParts = [];
    if (site) subParts.push(site);
    if (it && it.count > it.index) subParts.push((it.count - it.index) + ' up next'); // C-B13: one count everywhere
    setText($('ovSub'), subParts.join(' · '));

    // discreet pill (TvDiscreet)
    show($('discreetPill'), playing && discreet && !lost && !showBuffering && (t < S.overlayUntil || !!(S.fake && S.fake.overlay)) && !S.touch);
    var elapsed = S.fake && S.fake.elapsed !== undefined ? S.fake.elapsed : (live ? (t - S.playStartedAt) / 1000 : pos);
    setText($('discreetTime'), fmt(elapsed, true));

    // tiles; the first remote press must land on a focused button (Spool D-116)
    renderTiles();
    if (playing && mode && !S.touch && !$('tiles').contains(document.activeElement) && !S.starting && overlayButtons().length === 0) focusTileButton(S.tiles.focused);
    // Back closes it for this pause (then Back again offers the exit); playing again forgets that.
    if (!paused) S.barDismissed = false;
    var holdBar = paused && !mode && !S.touch && !lost && !S.starting && !resting && !S.barDismissed && S.screen === 'play';
    S.barHeld = holdBar;
    if (holdBar && !S.bar) { S.bar = { from: -1, until: now() + BAR_HIDE_MS, last: null, single: true }; S.barFocus = true; }
    renderBar(playing && (!!mode || !!(S.bar && S.bar.single)) && !S.touch && !lost && !S.starting, st, pos, dur);
    if (S.barFocus && S.bar) { S.barFocus = false; if (!$('bar').contains(document.activeElement)) focusFirst([$('barToggle')]); }

    // buffering
    show($('buffering'), showBuffering && !S.starting);
    setText($('bufHead'), live ? 'Catching up to live' : 'Loading…');
    show($('bufLive'), live);
    setText($('bufTitle'), title);
    var url = S.media ? (S.media.contentUrl || S.media.contentId || '') : '';
    // R-75: plain words, no pipeline ("via phone relay" is gone): say where the video comes from, if it's the phone.
    setText($('bufSub'), (S.fake ? S.fake.relay : isPrivateHost(url)) ? 'Getting the video from your phone' : 'This takes a few seconds');
    var vh = videoHeight();
    setText($('bufMeta'), vh ? vh + 'p' : '');

    // paused (TvPaused)
    // D-89: with tiles, a paused tile carries its own chip; the board would cover the whole grid.
    // D-97: with a remote, a paused video shows the control bar (and keeps it up until it plays), never this card.
    show($('paused'), paused && !S.starting && !lost && !mode && S.touch);
    setText($('pauseTitle'), title);
    var fromPhone = !S.pausedLocally;
    setText($('pauseSub'), [site, fromPhone ? 'paused from your phone' : 'paused'].filter(Boolean).join(' · '));
    if (live) {
      var b = behindLive();
      setText($('pauseTime'), behindLiveText(b));
      $('pauseFill').style.width = '100%';
    } else {
      var hours = dur >= 3600;
      setText($('pauseTime'), fmt(pos, hours) + ' / ' + fmt(dur, hours));
      $('pauseFill').style.width = (dur > 0 ? clamp(pos / dur, 0, 1) * 100 : 0).toFixed(2) + '%';
    }

    // up next (TvUpNext, Q3)
    var wasUpNext = !$('upnext').hidden;
    show($('upnext'), !!un && !S.starting);
    if (un) {
      var h2 = un.dur >= 3600;
      setText($('unTime'), fmt(pos, h2) + ' / ' + fmt(un.dur, h2));
      setText($('unNowTitle'), title);
      setText($('unLabel'), 'Up next in ' + fmt(Math.ceil(un.remaining)));
      setText($('unTitle'), discreet ? 'Next video' : un.title);
      setText($('unMeta'), un.meta);
      show($('unMeta'), !!un.meta);
      show($('unThen'), !!un.then);
      if (un.then) { setText($('unThenTitle'), discreet ? 'Next video' : un.then.title); show($('unThenLive'), !!un.then.live); }
      if (!wasUpNext && !S.touch) focusFirst([$('unPlay')]);
    }
    cls($('unCard'), 'focus', document.activeElement === $('unPlay'));

    // reconnecting banner
    show($('banner'), reconnecting);

    // phone lost (TvPhoneLost). R-89: "Trying for 0:24" counts up; after a minute, what to do on the phone.
    show($('phonelost'), lost && !S.starting);
    setText($('lostKept'), title ? 'Your place is kept · ' + title : 'Your place is kept');
    setText($('lostTimer'), 'Trying for ' + fmt(lostForMs / 1000));
    setText($('lostHelp'), lostForMs >= T.LOST_HELP_MS
      ? 'Open Lucerna on your phone to pick up again. It needs the same Wi-Fi as this TV.'
      : 'Keep Lucerna open on the same Wi-Fi. It picks up again by itself.');

    // starting (R-90: one ellipsis on the screen at most; the title has none)
    show($('starting'), !!S.starting);
    if (S.starting) setText($('startTitle'), S.starting.title ? 'Starting ' + S.starting.title : 'Starting…');

    // can't play / update
    show($('cantplay'), S.screen === 'cantplay' && !S.updateV);
    if (S.cant) {
      setText($('cpHead'), S.cant.head || 'This TV can\'t play this video\'s format');
      setText($('cpSub'), S.cant.sub || 'Lucerna can play it on your phone instead. Choose on your phone.');
    }
    if (S.cant) { setText($('cpTitle'), S.cant.title); show($('cpTitle'), !!S.cant.title); setText($('cpDetail'), S.cant.detail); show($('cpDetail'), !!S.cant.detail); }
    setText($('cpTv'), S.tvName);
    show($('update'), !!S.updateV);
    setText($('upDetail'), 'Phone protocol v' + S.updateV + ' · this TV page v' + M.VERSION);
    setText($('upTv'), S.tvName);

    // end of queue (TvEnd)
    show($('end'), S.screen === 'end' && !S.updateV);
    if (S.end) {
      setText($('endTitle'), discreet ? '' : S.end.title);
      var em = [];
      if (S.end.live) em.push('LIVE'); else if (S.end.durationMs) em.push(fmt(S.end.durationMs / 1000));
      if (S.end.site && !discreet) em.push(S.end.site);
      setText($('endMeta'), em.join(' · '));
      show($('endCard'), !!(S.end.title || em.length) && !discreet);
      var img = $('endThumb').querySelector('img');
      if (S.end.thumb && !discreet) { if (img.getAttribute('src') !== S.end.thumb) img.src = S.end.thumb; img.hidden = false; } else img.hidden = true;
      // R-67: no "5 videos played" on a shared screen; just which TV this is.
      setText($('endFoot'), S.tvName);
    }

    // touch display (TvHub)
    renderHub(playing && S.touch && !lost && !S.starting, st, pos, dur, live, title, site, it);

    placeVideo();
    if (!PREVIEW) sendState(false);
  }

  // ---- tiles, controls level (D-89): the bar for the tile with sound -----------------------------------------------------
  var BAR_HIDE_MS = 5000;
  function barSlot() { return S.tiles ? S.tiles.slots[S.tiles.audio] || S.tiles.slots[S.tiles.focused] || null : null; }
  /** The bar's buttons, left to right (only the visible ones); the progress line is the row above them (D-92). */
  function barButtons() {
    return ['barToggle', 'barJump', 'barNext', 'barMute', 'barOthers', 'barFull']
      .map(function (id) { return $(id); }).filter(function (b) { return b.offsetParent !== null; });
  }
  /** [from] is the tile to return to; -1 opens the bar for one video (D-96: the same bar as tiles). */
  function openBar(from) {
    if (S.touch || S.screen !== 'play' || (from >= 0 && !tilesMode())) return;
    S.bar = { from: from, until: now() + BAR_HIDE_MS, last: null, single: from < 0 };
    render();
    focusFirst([$('barToggle')]);   // D-92: on Play/Pause, as YouTube
  }
  function closeBar() {
    if (!S.bar) return;
    if (S.barHeld) S.barDismissed = true;
    var from = S.bar.from;
    S.bar = null;
    render();
    if (from >= 0 && S.tiles) focusTileButton(S.tiles.slots[from] ? from : S.tiles.focused);
    else if (document.activeElement && $('bar').contains(document.activeElement)) document.activeElement.blur();
  }
  function tip(b, words) { b.setAttribute('aria-label', words); b.setAttribute('data-tip', words); }
  function renderBar(on, st, pos, dur) {
    var bar = $('bar');
    // A bar for one video ends when tiles start, and a tiles bar when tiles end (the other kind opens fresh).
    var wrongKind = S.bar && !!S.bar.single === !!tilesMode();
    if (S.bar && (!on || (now() > S.bar.until && !(S.bar.single && S.barHeld)) || wrongKind)) { closeBar(); return; }
    show(bar, on && !!S.bar);
    cls(body, 'bar-open', on && !!S.bar);
    if (!S.bar || !on) return;
    var single = !!S.bar.single;
    var slot = single ? null : barSlot();
    var live = single ? !!S.live : !!(slot && slot.live);
    setText($('barTitle'), S.hello.discreet ? '' : (slot && slot.title) || curTitle());
    setText($('barSite'), single && !S.hello.discreet ? curSite() || '' : '');
    show($('barMute'), !single);
    show($('barOthers'), !single);
    show($('barFull'), !single);
    show($('barNext'), single && !!(S.queue && S.queue.length));
    var isPaused = st === 'PAUSED' || !!(slot && slot.paused);
    cls(bar, 'is-paused', isPaused);
    cls(bar, 'is-live', live);
    cls(bar, 'is-muted', !single && !!S.tiles.muted);
    cls(bar, 'others-pause', !single && !!S.tiles.othersPause);
    tip($('barToggle'), isPaused ? 'Play' : 'Pause');
    if (!single) {
      tip($('barMute'), S.tiles.muted ? 'Unmute' : 'Mute');
      tip($('barOthers'), S.tiles.othersPause ? 'Others pause' : 'Others keep playing');
    }
    show($('barJump'), live);
    show($('barLive'), live);
    var hours = dur >= 3600;
    // m7: a paused live video says how far behind live it is, the same number the phone shows.
    var timeText = !live && dur > 0 ? fmt(pos, hours) + ' / ' + fmt(dur, hours) : live && single && isPaused ? behindLiveText(behindLive()) : '';
    setText($('barTime'), timeText);
    show($('barTime'), !!timeText);
    var frac = live ? 1 : dur > 0 ? clamp(pos / dur, 0, 1) : 0;
    $('barScrubFill').style.width = (frac * 100).toFixed(2) + '%';
    $('barKnob').style.left = (frac * 100).toFixed(2) + '%';
    // A control that went away (the tile turned live, or stopped being live) hands focus to the first one left.
    var a = document.activeElement;
    if (a !== $('barScrub') && (!bar.contains(a) || a.offsetParent === null)) focusFirst(barButtons());
  }
  /**
   * Remote keys while the bar is open (D-92, YouTube): Left/Right between the buttons; Up to the progress line, where
   * Left/Right seek 10 s and Down comes back to the button you left; Up there, or Back anywhere, closes the bar.
   */
  function barKey(k) {
    var list = barButtons();
    var cur = document.activeElement;
    if (k === 'back') { closeBar(); return; }
    if (cur === $('barScrub')) {
      if (k === 'left' || k === 'right') send('key', { action: 'seekBy', n: k === 'left' ? -10 : 10 });
      else if (k === 'down') focusFirst([S.bar.last && S.bar.last.offsetParent !== null ? S.bar.last : $('barToggle')]);
      else if (k === 'up') closeBar();
      else if (k === 'ok') send('key', { action: 'toggle' });
      return;
    }
    var i = list.indexOf(cur);
    if (i < 0) { focusFirst(list); return; }
    if (k === 'left' || k === 'right') { focusFirst([list[clamp(i + (k === 'left' ? -1 : 1), 0, list.length - 1)]]); return; }
    if (k === 'up') { S.bar.last = cur; focusFirst([$('barScrub')]); return; }
    if (k === 'ok') cur.click();
  }

  function renderHub(on, st, pos, dur, live, title, site, it) {
    var hub = $('hub');
    show(hub, on);
    if (!on) return;
    cls(hub, 'faded', !S.fake && st === 'PLAYING' && now() > S.hubUntil);
    cls(hub, 'is-paused', st === 'PAUSED');
    cls(hub, 'over-tiles', !!tilesMode());   // the tiles carry their own titles
    $('hubToggle').setAttribute('aria-label', st === 'PAUSED' ? 'Play' : 'Pause');
    show($('hubLive'), live);
    setText($('hubTitle'), title);
    setText($('hubSub'), [site, 'from your phone'].filter(Boolean).join(' · '));
    show($('hubTitle'), !!title);
    setText($('hubTilesLabel'), tilesMode() ? 'One video' : 'Tiles');
    var frac = 0;
    if (live) {
      var r = pRange(), b = behindLive();
      frac = S.fake && S.fake.frac !== undefined ? S.fake.frac : (r ? clamp((pos - r.start) / (r.end - r.start), 0, 1) : 1);
      // m2: "At live" puts the knob at the right end, never part way along the window.
      if (b !== null && b !== undefined && isFinite(b) && shownBehind(b) < T.AT_LIVE_S) frac = 1;
      setText($('hubBehind'), behindLiveText(b));
    } else {
      frac = dur > 0 ? clamp(pos / dur, 0, 1) : 0;
      var hrs = dur >= 3600;
      setText($('hubBehind'), fmt(pos, hrs) + ' / ' + fmt(dur, hrs));
    }
    show($('hubJump'), live);
    $('hubFill').style.width = (frac * 100).toFixed(2) + '%';
    $('hubKnob').style.left = (frac * 100).toFixed(2) + '%';
    setText($('hubCount'), it && it.count > it.index ? (it.count - it.index) + ' up next' : (S.fake && S.fake.count) || '');
  }

  // ---- input: TV remote keys (R6) -------------------------------------------------------------------------------------------
  function focusFirst(list) {
    var b = list.filter(function (x) { return x && !x.hidden; })[0];
    if (b) { try { b.focus({ preventScroll: true }); } catch (e) { b.focus(); } }
  }
  function refocus() {
    if (S.touch) return;   // nothing to land on without a remote
    var list = overlayButtons();
    if (list.length && list.indexOf(document.activeElement) < 0) focusFirst(list);
    else if (!list.length && tilesMode() && S.screen === 'play') focusTileButton(S.tiles.focused);
  }
  /** Moves DOM focus to the nearest candidate in a direction (D-pad). */
  function moveFocus(dir, cands) {
    var cur = document.activeElement;
    if (cands.indexOf(cur) < 0) { focusFirst(cands); return; }
    var best = nearest(cur, dir, cands);
    if (best) { try { best.focus({ preventScroll: true }); } catch (e) { best.focus(); } }
  }
  /** The nearest candidate from `cur` in a direction, or null when there is none that way. */
  function nearest(cur, dir, cands) {
    var a = cur.getBoundingClientRect(), ax = a.left + a.width / 2, ay = a.top + a.height / 2;
    var best = null, bestScore = Infinity;
    cands.forEach(function (c) {
      if (c === cur) return;
      var r = c.getBoundingClientRect(), x = r.left + r.width / 2, y = r.top + r.height / 2;
      var dx = x - ax, dy = y - ay;
      var along = dir === 'left' ? -dx : dir === 'right' ? dx : dir === 'up' ? -dy : dy;
      var across = dir === 'left' || dir === 'right' ? Math.abs(dy) : Math.abs(dx);
      if (along <= 1) return;
      var score = along + across * 2;
      if (score < bestScore) { bestScore = score; best = c; }
    });
    return best;
  }

  var KEY = {
    Enter: 'ok', Select: 'ok', Accept: 'ok', ' ': 'ok', MediaPlayPause: 'playpause', MediaPlay: 'playpause', MediaPause: 'playpause',
    ArrowLeft: 'left', ArrowRight: 'right', ArrowUp: 'up', ArrowDown: 'down', Left: 'left', Right: 'right', Up: 'up', Down: 'down',
    Escape: 'back', Backspace: 'back', GoBack: 'back', BrowserBack: 'back', MediaTrackNext: 'next', MediaTrackPrevious: 'previous',
    MediaRewind: 'rewind', MediaFastForward: 'forward'
  };
  var KEYCODE = { 13: 'ok', 37: 'left', 38: 'up', 39: 'right', 40: 'down', 8: 'back', 27: 'back', 461: 'back', 10009: 'back', 179: 'playpause', 176: 'next', 177: 'previous', 412: 'rewind', 417: 'forward' };

  function onKey(e) {
    var k = KEY[e.key] || KEYCODE[e.keyCode];
    if (!k) return;
    e.preventDefault();
    var t = now();
    if (S.bar) S.bar.until = t + BAR_HIDE_MS;   // D-89: any key press keeps the bar up
    // Held keys repeat and some remotes send a key twice: one action per press, at most every 0.7 s (Spool D-113).
    // D-89: except Left/Right held on the bar's timeline, which keep seeking at that same 0.7 s rate.
    var scrubbing = !!S.bar && document.activeElement === $('barScrub') && (k === 'left' || k === 'right');
    if (e.repeat && !scrubbing) return;
    if (t - S.lastKeyAt < T.KEY_THROTTLE_MS) return;
    S.lastKeyAt = t;
    S.lastAction = k;
    S.overlayUntil = t + T.OVERLAY_MS;
    if (S.starting) { render(); return; }   // the phone is preparing; repeats are ignored (D-115)
    if (k === 'playpause') { send('key', { action: 'toggle' }); render(); return; }
    if (k === 'next' || k === 'previous') { send('key', { action: k }); render(); return; }
    var buttons = overlayButtons();
    if (buttons.length) {
      if (k === 'ok') {
        var target = buttons.indexOf(document.activeElement) >= 0 ? document.activeElement : buttons[0];
        target.click();
      } else if (k === 'back') {
        if (S.screen === 'end') { send('key', { action: 'back' }); }
        else if (!$('upnext').hidden) { S.upNextDismissed = S.playingId; }
      } else moveFocus(k, buttons);
      render();
      return;
    }
    var mode = S.screen === 'play' ? tilesMode() : null;
    if (mode) {
      // D-89: the remote's rewind and fast-forward seek the tile with sound, at either level.
      if (k === 'rewind' || k === 'forward') { send('key', { action: 'seekBy', n: k === 'rewind' ? -10 : 10 }); render(); return; }
      if (S.bar && !S.touch) { barKey(k); render(); return; }
      var tiles = tileEls.map(function (x) { return x.btn; });
      var i = tiles.indexOf(document.activeElement);
      if (k === 'ok') {
        if (i < 0) i = S.tiles.focused;
        // D-89: OK on the tile that already has sound opens its controls; on another tile, gives that tile the sound.
        if (i === S.tiles.audio && i === S.tiles.focused && !S.touch) openBar(i);
        else chooseTile(i);
      } else if (k === 'back') backToExit();   // D-94: Back backs out (Full screen is in the bar)
      else if (k === 'down' && i >= 0 && !nearest(tiles[i], 'down', tiles)) openBar(i);   // the bottom row: down to the bar
      else moveFocus(k, tiles);
      render();
      return;
    }
    if (S.screen === 'play') {
      // D-96, YouTube style: OK pauses (or plays) and shows the bar on Play/Pause; Down shows it; Left/Right show it on
      // the progress line and skip 10 s. Previous/next are the remote's media keys and the bar's Next.
      if (k === 'rewind' || k === 'forward') { send('key', { action: 'seekBy', n: k === 'rewind' ? -10 : 10 }); render(); return; }
      if (S.bar && !S.touch) { barKey(k); render(); return; }
      if (k === 'ok') { send('key', { action: 'toggle' }); openBar(-1); }
      else if (k === 'down') openBar(-1);
      else if (k === 'left' || k === 'right') { openBar(-1); focusFirst([$('barScrub')]); send('key', { action: 'seekBy', n: k === 'left' ? -10 : 10 }); }
      // A tile filling the screen goes back to the grid (the phone knows; its tiles answer clears the hint).
      else if (k === 'back') { send('key', { action: 'back' }); backToExit(); }
    } else if (k === 'back' && S.screen !== 'end') backToExit();
    render();
  }
  document.addEventListener('keydown', onKey);
  document.addEventListener('focusin', function () { cls($('unCard'), 'focus', document.activeElement === $('unPlay')); });

  // On-screen buttons (remote OK, or a tap on a touch display)
  $('unPlay').addEventListener('click', function () {
    var un = upNextInfo();
    requestStart('next', un && !S.hello.discreet ? un.title : '');
  });
  $('endAgain').addEventListener('click', function () { requestStart('previous', S.end && !S.hello.discreet ? S.end.title : ''); });
  $('endStart').addEventListener('click', function () { send('key', { action: 'back' }); S.end = null; setScreen('idle'); render(); });
  $('hubTiles').addEventListener('click', function () {
    if (tilesMode()) send('key', { action: 'back' });
    else send('key', { action: 'focusTile', n: S.tiles ? S.tiles.focused : 0 });
  });
  $('hubJump').addEventListener('click', function () { seekLiveEdge(); });
  $('hubBack').addEventListener('click', function () { if (player) player.seek(Math.max(0, pTime() - 10)); });
  $('hubToggle').addEventListener('click', function () {
    if (!player) return;
    if (pState() === 'PAUSED') { S.pausedLocally = false; player.play(); } else { S.pausedLocally = true; player.pause(); }
  });
  $('hubNext').addEventListener('click', function () { send('key', { action: 'next' }); });
  // D-89: the tiles' control bar; each button is one key to the phone, which answers with tiles and the session.
  $('barToggle').addEventListener('click', function () { send('key', { action: 'toggle' }); });
  $('barJump').addEventListener('click', function () { send('key', { action: 'jumpLive' }); });
  $('barNext').addEventListener('click', function () { send('key', { action: 'next' }); });
  $('barMute').addEventListener('click', function () { send('key', { action: 'mute' }); });
  $('barOthers').addEventListener('click', function () { send('key', { action: 'othersPause' }); });
  $('barFull').addEventListener('click', function () { send('key', { action: 'fill' }); closeBar(); });
  $('hubTrack').addEventListener('click', function (e) {
    if (!player) return;
    var r = $('hubTrack').getBoundingClientRect();
    var f = clamp((e.clientX - r.left) / r.width, 0, 1);
    if (S.live) { var rg = pRange(); if (rg) player.seek(rg.start + f * (rg.end - rg.start)); } else if (pDuration() > 0) player.seek(f * pDuration());
  });
  document.addEventListener('pointerdown', function () { S.hubUntil = now() + T.HUB_HIDE_MS; render(); }, true);

  function seekLiveEdge() {
    var r = pRange();
    if (!player || !r) return;
    player.seek(Math.max(r.start, r.end - clamp(S.hello.liveOffsetS || 6, 1, 120)));
  }

  // ---- heartbeat, phone lost, state, live stall recovery ---------------------------------------------------------------
  function everySecond() {
    var t = now();
    if (S.everHeard && S.screen === 'play' && !S.lostSince && t - S.lastHeard > T.PHONE_LOST_MS) S.lostSince = t;
    // Live: stuck for 10 s while meant to play → jump to the live edge (R3).
    var st = pState();
    if (S.screen === 'play' && S.live && (st === 'PLAYING' || st === 'BUFFERING')) {
      var pos = pTime();
      if (Math.abs(pos - S.stall.lastT) < 0.05) S.stall.stuckMs += 1000; else { S.stall.stuckMs = 0; S.stall.lastT = pos; }
      if (S.stall.stuckMs >= T.STALL_RECOVER_MS) {
        S.stall.stuckMs = 0;
        S.recoveries++;
        seekLiveEdge();
        try { player.play(); } catch (e) { /* ignore */ }
      }
    } else S.stall.stuckMs = 0;
    if (S.screen === 'play' && video.textTracks && video.textTracks.length) applySubtitleOffset();
    render();
  }

  // ---- visibility (T5: snapshot workers pause while the page is hidden) ----------------------------------------------------
  function setHidden(h) {
    if (S.hidden === !!h) return;
    S.hidden = !!h;
    sendState(true);
  }
  document.addEventListener('visibilitychange', function () { setHidden(document.hidden); });

  // ---- debug handle for tests and the diagnostics overlay ------------------------------------------------------------------
  window.__lucerna = {
    S: S, T: T, render: render, layoutRects: layoutRects, tileRects: function () { return S.tiles ? tileRects() : []; }, supportedCodecs: supportedCodecs,
    lastPlaybackConfig: function () { return lastCfg; }, applySubtitleOffset: applySubtitleOffset, fit: fit
  };

  // ---- start ------------------------------------------------------------------------------------------------------------
  function start() {
    if (!window.cast || !cast.framework) {
      console.warn('[lucerna] Cast receiver library not loaded; showing the idle screen only');
      setScreen('idle'); fit(); render();
      return;
    }
    context = cast.framework.CastReceiverContext.getInstance();
    player = context.getPlayerManager();
    player.setMediaElement(video);
    var Ev = cast.framework.events.EventType;
    var Msg = cast.framework.messages;

    context.addCustomMessageListener(NS, onCustomMessage);
    player.setMessageInterceptor(Msg.MessageType.LOAD, onLoadRequest);
    player.setMessageInterceptor(Msg.MessageType.PAUSE, function (req) { S.pausedLocally = false; return req; });
    player.setMessageInterceptor(Msg.MessageType.STOP, function (req) { resetAll(); return req; });
    if (player.setMediaPlaybackInfoHandler) player.setMediaPlaybackInfoHandler(function (loadRequest, cfg) { return lastCfg || cfg; });

    player.addEventListener(Ev.PLAYER_LOAD_COMPLETE, onLoadComplete);
    player.addEventListener(Ev.ERROR, onPlayerError);
    player.addEventListener(Ev.MEDIA_FINISHED, function () { onMaybeFinished('FINISHED'); });
    player.addEventListener(Ev.MEDIA_STATUS, function (e) {
      var ms = e && e.mediaStatus;
      if (ms && ms.playerState === 'IDLE' && ms.idleReason) onMaybeFinished(ms.idleReason);
      if (ms && ms.playerState === 'PLAYING') { S.liveIdle = false; S.loading = false; cls(body, 'fresh', false); }
      render();
    });
    [Ev.PLAYING, Ev.PAUSE, Ev.BUFFERING, Ev.SEEKED].forEach(function (ev) {
      player.addEventListener(ev, function () {
        if (ev === Ev.PLAYING) { S.liveIdle = false; S.loading = false; cls(body, 'fresh', false); S.overlayUntil = Math.max(S.overlayUntil, now() + 2500); }
        render();
        sendState(false);
      });
    });

    var Sys = cast.framework.system.EventType;
    context.addEventListener(Sys.READY, function () { setTouch(touchFromCapabilities()); render(); });
    context.addEventListener(Sys.SENDER_DISCONNECTED, function (e) {
      if (e && e.senderId === S.phone && e.reason !== 'requested_by_sender' && e.reason !== 'closed' && S.screen === 'play' && !S.lostSince) { S.lostSince = now(); render(); }
    });
    if (Sys.VISIBILITY_CHANGED) context.addEventListener(Sys.VISIBILITY_CHANGED, function (e) { if (e && typeof e.isVisible === 'boolean') setHidden(!e.isVisible); });

    var options = new cast.framework.CastReceiverOptions();
    options.disableIdleTimeout = true;
    options.customNamespaces = {};
    options.customNamespaces[NS] = cast.framework.system.MessageType.JSON;
    options.supportedCommands = Msg.Command.ALL_BASIC_MEDIA | Msg.Command.QUEUE_NEXT | Msg.Command.QUEUE_PREV;
    options.playbackConfig = buildPlaybackConfig({ live: false });
    options.useShakaForHls = true;
    options.touchScreenOptimizedApp = true;
    player.setSupportedMediaCommands(options.supportedCommands, true);
    context.start(options);

    setInterval(everySecond, 1000);
    setInterval(function () { if (S.phone || S.everHeard) send('ping', { at: now() }); }, T.HEARTBEAT_MS);
    setInterval(function () { if (S.everHeard) sendState(true); }, T.STATE_MS);
    setScreen('idle');
    fit();
    render();
  }

  // ---- preview (?preview=<state>): each state with the mockups' own content, no Cast ---------------------------------------
  function preview(state) {
    if (params.get('touch') === '1' || state === 'hub') S.touch = true;
    cls(body, 'touch-ui', S.touch);
    if (params.get('still') === '1') cls(body, 'still', true);
    var sc = parseFloat(params.get('scale') || '1');
    if (sc > 0) document.documentElement.style.setProperty('--scale', String(clamp(sc, 0.75, 1.5)));
    video.hidden = true;
    var fake = $('fakevideo');
    fake.hidden = false;
    var greenBg = 'radial-gradient(ellipse at 40% 35%, #26352D 0%, #1E2A24 50%, #141C18 100%)';
    S.fake = { state: 'PLAYING', time: 0, duration: 0, overlay: true, height: 1080, relay: true };
    function item(id, title, site, live, durMs, extra) {
      var it = { id: id, title: title, site: site, live: live, durationMs: durMs || null, thumb: null, next: null, index: 1, count: 1, subtitleOffsetMs: 0 };
      if (extra) Object.keys(extra).forEach(function (k) { it[k] = extra[k]; });
      S.items[id] = it; S.playingId = id; S.live = live;
      return it;
    }
    function tiles(layout, n) {
      var all = [['q:mile20', 'Mile 20 camera', '#1E2A24'], ['q:finish', 'Finish line', '#3A3326'], ['q:council', 'Council', '#263A4A'], ['q:harbor', 'Harbor cam', '#2C2638']];
      var slots = all.slice(0, n).map(function (a, i) { return { index: i, itemId: a[0], title: a[1], live: true, crop: { l: 0, t: 0, r: 1, b: 1 }, zoom: 1, color: a[2] }; });
      slots[0].title = 'Mile 20 camera';
      onTiles({ layout: layout, slots: slots, focused: 0, audio: 0, mode: state === 'combines' ? 'phoneCombines' : 'webFocus' });
    }
    var bg = '#1E2A24';
    S.tvName = '';
    switch (state) {
      case 'idle':
        S.tvName = 'Office TV'; setScreen('idle'); break;
      case 'playing':
        item('q:mile20', 'Mile 20 camera', 'runnerstv.example', true, null, { index: 1, count: 4 });
        setScreen('play'); break;
      case 'focus': case 'onePlusThree': case 'focus2': case 'focus3': case 'focus4': case 'combines':
        item('q:mile20', 'Mile 20 camera', 'runnerstv.example', true);
        S.fake.site = '';
        S.items['q:mile20'].site = 'runnerstv.example';
        setScreen('play');
        if (state === 'focus2') tiles('two', 2);
        else if (state === 'focus3') tiles('three', 3);
        else if (state === 'focus4') tiles('four', 4);
        else tiles('onePlusThree', 4);
        bg = '#1E2A24';
        if (state === 'combines') bg = 'linear-gradient(90deg, #1E2A24 0 74.5%, #000 74.5% 75.4%, #3A3326 75.4%)';
        break;
      case 'buffering':
        item('q:mile20', 'Mile 20 camera', 'runnerstv.example', true);
        S.fake.state = 'BUFFERING'; bg = greenBg; setScreen('play'); break;
      case 'paused':
        item('q:council', 'Council budget hearing', 'councilmeetings.example', false, 8040000);
        S.fake.state = 'PAUSED'; S.fake.time = 4360; S.fake.duration = 8040;
        bg = 'radial-gradient(ellipse at 40% 35%, #2F4658 0%, #263A4A 45%, #1B2A36 100%)'; setScreen('play'); break;
      case 'upnext':
        item('q:council', 'Council budget hearing', 'councilmeetings.example', false, 8040000, { next: { title: 'The Long Coast, episode 5', startsInS: 15 } });
        S.queue = [{ id: 'q:coast5', title: 'The Long Coast, episode 5', live: false, durationMs: 3150000, site: 'longcoast.example' }, { id: 'q:harbor', title: 'Harbor webcam', live: true, durationMs: null }];
        S.fake.time = 8028; S.fake.duration = 8040;
        bg = '#263A4A'; setScreen('play'); break;   // R-66: never with the reconnecting banner
      case 'reconnecting':
        item('q:mile20', 'Mile 20 camera', 'runnerstv.example', true);
        S.fake.overlay = false;
        S.status = { type: 'status', seq: 0, paused: false, relayState: 'refreshing', behindLiveS: null };
        setScreen('play'); break;
      case 'end':
        S.tvName = 'Living Room TV';
        S.end = { played: 5, title: 'The Long Coast, episode 5', site: 'longcoast.example', durationMs: 3150000, thumb: null, live: false };
        S.endSince = now(); setScreen('end'); break;
      case 'discreet':
        S.hello.discreet = true; cls(body, 'discreet', true);
        item('q:x', '', '', false, 3150000);
        S.fake.elapsed = 4;
        bg = 'radial-gradient(ellipse at 55% 40%, #4A3F2E 0%, #3A3326 50%, #2A251C 100%)'; setScreen('play'); break;
      case 'cantplay':
        S.tvName = 'Office TV';
        S.cant = { title: 'The Long Coast, episode 5', detail: 'HEVC 10-bit · 2160p · this TV plays H.264 and VP9' };
        setScreen('cantplay'); break;
      case 'phonelost':
        item('q:mile20', 'Mile 20 camera', 'runnerstv.example', true);
        S.lostSince = 1; S.fake.lostFor = 24; bg = greenBg; setScreen('play'); break;
      case 'hub':
        item('q:mile20', 'Mile 20 camera', 'runnerstv.example', true, null, { index: 1, count: 4 });
        S.fake.behind = 8; S.fake.frac = 0.96; bg = greenBg; setScreen('play'); break;
      case 'starting':
        item('q:council', 'Council budget hearing', 'councilmeetings.example', false, 8040000);
        S.fake.overlay = false; S.starting = { title: 'The Long Coast, episode 5' }; bg = '#263A4A'; setScreen('play'); break;
      case 'update':
        S.updateV = 2; setScreen('idle'); break;
      default:
        setScreen('idle');
    }
    fake.style.background = bg;
    fit();
    render();
    if (S.screen === 'end') focusFirst([$('endAgain')]);
    else refocus();
  }

  if (PREVIEW) preview(PREVIEW);
  else start();
})();
