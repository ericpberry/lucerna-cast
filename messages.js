// Lucerna TV protocol for the TV page: parse, validate, and encode the JSON messages on urn:x-cast:app.lucerna.
// Mirrors core/src/main/kotlin/app/lucerna/core/cast/TvMessages.kt (same types, field defaults, direction sets, caps);
// both sides are tested from the same files in core/src/test/resources/cast/ (receiver/test/messages.spec.js).
// Rules (FAMILY-LESSONS 1b): every field is optional with a default; unknown keys are ignored; a wrong type for a
// known field rejects the whole message (kotlinx.serialization with isLenient = false); null is accepted only for
// nullable fields; nulls are left out when encoding (explicitNulls = false); text is plain, never HTML.
// ES2017 only (R8): no optional chaining, no ??, no object spread.
(function (root, factory) {
  'use strict';
  var api = factory();
  if (typeof module === 'object' && module.exports) module.exports = api;
  else root.LucernaMessages = api;
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  var NAMESPACE = 'urn:x-cast:app.lucerna';
  /** Highest protocol version this page understands (TvMessages.VERSION). */
  var VERSION = 1;
  var MAX_TEXT = 200;
  var MAX_SNAP_BASE64 = 48 * 1024;
  var MAX_UP_NEXT = 10;
  var PHONE_TO_TV = ['hello', 'item', 'tiles', 'snap', 'snapUrl', 'status', 'queue', 'end', 'ping', 'pong'];
  var TV_TO_PHONE = ['caps', 'state', 'error', 'want', 'ended', 'key', 'ping', 'pong'];

  // ---- schema: [name, kind, default]. Kinds: int, long, float, bool, string, obj:<Name>, list:<Name>; a trailing ?
  // makes the field nullable (Kotlin `T?`). Defaults are the Kotlin defaults; field order is the Kotlin order.
  var S = {};
  S.SnapshotConfig = [['fps', 'int', 4], ['height', 'int', 360], ['maxTiles', 'int', 3], ['transport', 'string', 'auto'], ['channelFps', 'int', 2]];
  S.NextUp = [['title', 'string', ''], ['startsInS', 'int', 15]];
  S.Crop = [['l', 'float', 0], ['t', 'float', 0], ['r', 'float', 1], ['b', 'float', 1]];
  S.TileSlotMsg = [['index', 'int', 0], ['itemId', 'string?', null], ['title', 'string', ''], ['live', 'bool', false],
    ['url', 'string?', null], ['crop', 'obj:Crop', 'new'], ['zoom', 'float', 1]];
  S.QueueEntry = [['id', 'string', ''], ['title', 'string', ''], ['live', 'bool', false], ['durationMs', 'long?', null]];

  var T = {};
  T.hello = [['seq', 'long', 0], ['v', 'int', VERSION], ['app', 'string', ''], ['discreet', 'bool', false], ['textScale', 'float', 1],
    ['reducedMotion', 'bool', false], ['liveOffsetS', 'int', 6], ['snapshot', 'obj:SnapshotConfig', 'new'],
    ['subtitleScale', 'float', 1], ['subtitleBackground', 'bool', true], ['tvName', 'string?', null]];
  T.item = [['seq', 'long', 0], ['id', 'string', ''], ['title', 'string', ''], ['site', 'string', ''], ['live', 'bool', false],
    ['durationMs', 'long?', null], ['thumb', 'string?', null], ['next', 'obj:NextUp?', null], ['index', 'int', 1], ['count', 'int', 1],
    ['subtitleOffsetMs', 'long', 0]];
  T.tiles = [['seq', 'long', 0], ['layout', 'string', 'two'], ['slots', 'list:TileSlotMsg', 'new'], ['focused', 'int', 0],
    ['audio', 'int', 0], ['mode', 'string', 'single']];
  T.snap = [['seq', 'long', 0], ['tile', 'int', 0], ['jpeg', 'string?', null], ['w', 'int', 0], ['h', 'int', 0], ['at', 'long', 0]];
  T.snapUrl = [['seq', 'long', 0], ['tile', 'int', 0], ['url', 'string', '']];
  T.status = [['seq', 'long', 0], ['paused', 'bool', false], ['relayState', 'string', 'ok'], ['behindLiveS', 'float?', null]];
  T.queue = [['seq', 'long', 0], ['upNext', 'list:QueueEntry', 'new']];
  T.end = [['seq', 'long', 0], ['played', 'int', 0]];
  T.caps = [['seq', 'long', 0], ['video', 'list:string', 'new'], ['maxHeight', 'int', 1080], ['touch', 'bool', false],
    ['kind', 'string', 'web'], ['maxTiles', 'int', 1], ['v', 'int', VERSION]];
  T.state = [['seq', 'long', 0], ['itemId', 'string?', null], ['positionMs', 'long', 0], ['playing', 'bool', false],
    ['buffering', 'bool', false], ['behindLiveS', 'float?', null], ['snapTransport', 'string?', null], ['hidden', 'bool', false],
    ['videoHeight', 'int?', null]];
  T.error = [['seq', 'long', 0], ['itemId', 'string?', null], ['code', 'string', 'network'], ['detail', 'string', '']];
  T.want = [['seq', 'long', 0], ['itemId', 'string', '']];
  T.ended = [['seq', 'long', 0], ['itemId', 'string', '']];
  T.key = [['seq', 'long', 0], ['action', 'string', 'toggle'], ['n', 'int?', null]];
  T.ping = [['seq', 'long', 0], ['at', 'long', 0]];
  T.pong = [['seq', 'long', 0], ['at', 'long', 0]];

  var INVALID = {};  // sentinel: the value doesn't fit the field

  function isObject(v) { return v !== null && typeof v === 'object' && !Array.isArray(v); }

  function defaultFor(kind, dflt) {
    if (dflt !== 'new') return dflt;
    if (kind.indexOf('list:') === 0) return [];
    return readObject(S[kind.slice(4)], {});
  }

  /** One value against its kind; INVALID if it doesn't fit (as kotlinx.serialization would refuse it). */
  function readValue(kind, v) {
    var nullable = kind.charAt(kind.length - 1) === '?';
    var k = nullable ? kind.slice(0, -1) : kind;
    if (v === null) return nullable ? null : INVALID;
    if (k === 'int' || k === 'long') {
      if (typeof v !== 'number' || !isFinite(v) || Math.floor(v) !== v) return INVALID;
      if (k === 'int' && (v > 2147483647 || v < -2147483648)) return INVALID;
      return v;
    }
    if (k === 'float') return typeof v === 'number' && isFinite(v) ? v : INVALID;
    if (k === 'bool') return typeof v === 'boolean' ? v : INVALID;
    if (k === 'string') return typeof v === 'string' ? v : INVALID;
    if (k.indexOf('obj:') === 0) return isObject(v) ? readObject(S[k.slice(4)], v) : INVALID;
    if (k.indexOf('list:') === 0) {
      if (!Array.isArray(v)) return INVALID;
      var inner = k.slice(5);
      var out = [];
      for (var i = 0; i < v.length; i++) {
        var x = inner === 'string' ? readValue('string', v[i]) : (isObject(v[i]) ? readObject(S[inner], v[i]) : INVALID);
        if (x === INVALID) return INVALID;
        out.push(x);
      }
      return out;
    }
    return INVALID;
  }

  function readObject(schema, o) {
    var out = {};
    for (var i = 0; i < schema.length; i++) {
      var name = schema[i][0], kind = schema[i][1], dflt = schema[i][2];
      if (Object.prototype.hasOwnProperty.call(o, name) && o[name] !== undefined) {
        var v = readValue(kind, o[name]);
        if (v === INVALID) return INVALID;
        out[name] = v;
      } else {
        out[name] = defaultFor(kind.replace(/\?$/, ''), dflt);
      }
    }
    return out;
  }

  /**
   * Parses any Lucerna TV message from JSON text or an already-parsed object (CAF hands JSON namespaces an object).
   * Returns a plain object with `type` and every field (defaults filled in), or null for non-JSON, unknown types,
   * or malformed fields. Mirrors TvMessages.decode.
   */
  function decode(input) {
    var o = input;
    if (typeof input === 'string') {
      try { o = JSON.parse(input); } catch (e) { return null; }
    }
    if (!isObject(o)) return null;
    var type = o.type;
    if (typeof type !== 'string' || !Object.prototype.hasOwnProperty.call(T, type)) return null;
    var m = readObject(T[type], o);
    if (m === INVALID) return null;
    var out = { type: type };
    Object.keys(m).forEach(function (k) { out[k] = m[k]; });
    return out;
  }

  function decodeFromPhone(input) { var m = decode(input); return m && PHONE_TO_TV.indexOf(m.type) >= 0 ? m : null; }
  function decodeFromTv(input) { var m = decode(input); return m && TV_TO_PHONE.indexOf(m.type) >= 0 ? m : null; }

  function writeValue(kind, v) {
    var k = kind.replace(/\?$/, '');
    if (v === null || v === undefined) return undefined;
    if (k.indexOf('obj:') === 0) return writeObject(S[k.slice(4)], v);
    if (k.indexOf('list:') === 0) {
      var inner = k.slice(5);
      return v.map(function (x) { return inner === 'string' ? x : writeObject(S[inner], x); });
    }
    return v;
  }

  function writeObject(schema, o) {
    var out = {};
    for (var i = 0; i < schema.length; i++) {
      var name = schema[i][0], kind = schema[i][1];
      var v = Object.prototype.hasOwnProperty.call(o, name) ? o[name] : defaultFor(kind.replace(/\?$/, ''), schema[i][2]);
      var w = writeValue(kind, v);
      if (w !== undefined) out[name] = w;   // explicitNulls = false: nulls are left out
    }
    return out;
  }

  /** The JSON object for a message ({type, ...fields}), defaults included, nulls left out. Throws on an unknown type. */
  function encodeObject(m) {
    if (!m || !Object.prototype.hasOwnProperty.call(T, m.type)) throw new Error('unknown Lucerna message type ' + (m && m.type));
    var body = writeObject(T[m.type], m);
    var out = { type: m.type };
    Object.keys(body).forEach(function (k) { out[k] = body[k]; });
    return out;
  }

  function encode(m) { return JSON.stringify(encodeObject(m)); }

  /** ISO control characters (Kotlin Char.isISOControl): U+0000..U+001F and U+007F..U+009F. */
  function isIsoControl(c) { var n = c.charCodeAt(0); return n <= 0x1f || (n >= 0x7f && n <= 0x9f); }

  /** Plain text, control characters dropped, trimmed, capped with an ellipsis. Mirrors TvMessages.cap. */
  function cap(text, max) {
    if (max === undefined) max = MAX_TEXT;
    if (text === null || text === undefined) return '';
    var s = String(text);
    var clean = '';
    for (var i = 0; i < s.length; i++) { var c = s.charAt(i); if (c === ' ' || !isIsoControl(c)) clean += c; }
    clean = clean.trim();
    if (clean.length <= max) return clean;
    return clean.slice(0, max - 1).replace(/\s+$/, '') + '…';
  }

  return {
    NAMESPACE: NAMESPACE, VERSION: VERSION, MAX_TEXT: MAX_TEXT, MAX_SNAP_BASE64: MAX_SNAP_BASE64, MAX_UP_NEXT: MAX_UP_NEXT,
    PHONE_TO_TV: PHONE_TO_TV, TV_TO_PHONE: TV_TO_PHONE, TYPES: Object.keys(T),
    decode: decode, decodeFromPhone: decodeFromPhone, decodeFromTv: decodeFromTv,
    encode: encode, encodeObject: encodeObject, cap: cap
  };
});
