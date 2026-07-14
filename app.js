'use strict';

/* ===================== 헬퍼 ===================== */

const $ = id => document.getElementById(id);
const pad = n => String(n).padStart(2, '0');
const keyOf = d => `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`;
const todayKey = () => keyOf(new Date());
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
const DOW = ['일', '월', '화', '수', '목', '금', '토'];

function fmtDateShort(k) {
  const [y, m, d] = k.split('-').map(Number);
  const dt = new Date(y, m - 1, d);
  const thisYear = new Date().getFullYear() === y;
  return `${thisYear ? '' : y + '. '}${m}/${d} (${DOW[dt.getDay()]})`;
}

function validDateKey(k) {
  if (typeof k !== 'string' || !/^\d{4}-\d{2}-\d{2}$/.test(k)) return false;
  const [y, m, d] = k.split('-').map(Number);
  return m >= 1 && m <= 12 && d >= 1 && d <= new Date(y, m, 0).getDate();
}

function debounce(fn, ms) {
  let t = null;
  const wrapped = (...args) => {
    clearTimeout(t);
    t = setTimeout(() => { t = null; fn(...args); }, ms);
  };
  wrapped.flush = (...args) => { if (t) { clearTimeout(t); t = null; fn(...args); } };
  return wrapped;
}

const GROUP_COLORS = ['#3560e0', '#2e8b57', '#c98a04', '#8b5cf6', '#d6558e', '#0e9394'];

/* ===================== 상태 ===================== */

let data = null;        // { groups:[], todos:[], meta:{savedAt} }
let view = { type: 'today', groupId: null };
let selectedId = null;
let doneOpen = false;
let imgTargetId = null; // 비동기 이미지 삽입이 겨냥한 메모 id
let bc = null;          // 탭 간 동기화 채널
let curDayKey = todayKey();
let calY = new Date().getFullYear();
let calM = new Date().getMonth();
let dirty = false;      // 저장 대기 중인 편집이 있는가 (창 닫기 경고용)
let lastEditorNoteId = null;

// 메모 간 이동 히스토리 (뒤로/앞으로) + 최근 본 메모 (세션 단위)
let navHist = [];       // 방문한 메모 id들 (브라우저 히스토리처럼)
let navPos = -1;        // navHist에서 현재 위치
const RECENT_MAX = 8;   // 최근 본 메모 최대 개수
let recentIds = [];     // 최근 방문 순 (앞이 최신)

// 검색 상태
let search = {
  q: '',
  scope: 'all',            // all | title | body
  group: '',               // '' = 전체 그룹
  includeDone: true,
  page: 1,
  results: [],             // 정렬된 결과 [{t, titleHit, bodyHit}]
  hlTerms: [],             // 열린 메모에서 강조할 검색어
};
let prevView = null;       // 검색 종료 시 복귀할 뷰
const SEARCH_PAGE = 40;
// 본문 텍스트 캐시: id -> { updated, title, titleLc, body, bodyLc }
const searchCache = new Map();

/* ===================== HTML 정화 (메모 본문) =====================
   저장/붙여넣기되는 HTML에서 스크립트·이벤트 속성 등을 제거한다. */

const ALLOWED_TAGS = new Set([
  'P', 'BR', 'DIV', 'SPAN', 'B', 'STRONG', 'I', 'EM', 'U', 'S', 'STRIKE', 'DEL',
  'H1', 'H2', 'H3', 'H4', 'UL', 'OL', 'LI', 'HR', 'A', 'IMG',
  'TABLE', 'THEAD', 'TBODY', 'TR', 'TD', 'TH', 'BLOCKQUOTE', 'PRE', 'CODE', 'FONT',
]);
const ALLOWED_ATTRS = { A: ['href', 'data-todo'], IMG: ['src', 'alt', 'data-ref'], TD: ['colspan', 'rowspan', 'class'], TH: ['colspan', 'rowspan', 'class'] };

// 속성값 안전 이스케이프 (링크 URL 등)
function escapeAttr(s) {
  return String(s).replace(/&/g, '&amp;').replace(/"/g, '&quot;')
    .replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

const DROP_TAGS = new Set(['SCRIPT', 'STYLE', 'IFRAME', 'OBJECT', 'EMBED', 'LINK', 'META', 'FORM']);

function sanitizeHTML(html) {
  const doc = new DOMParser().parseFromString(`<div>${html}</div>`, 'text/html');
  const root = doc.body.firstChild;
  const walk = node => {
    for (const child of Array.from(node.childNodes)) {
      if (child.nodeType === Node.ELEMENT_NODE) {
        if (DROP_TAGS.has(child.tagName)) { // 위험 태그는 내용까지 제거
          node.removeChild(child);
          continue;
        }
        // 먼저 자식을 재귀 정화 — 허용 안 된 태그를 벗겨도 내부가 안전해야 함
        walk(child);
        if (!ALLOWED_TAGS.has(child.tagName)) {
          // 태그는 벗기고 (이미 정화된) 내용은 살림
          while (child.firstChild) node.insertBefore(child.firstChild, child);
          node.removeChild(child);
          continue;
        }
        const keep = ALLOWED_ATTRS[child.tagName] || [];
        for (const attr of Array.from(child.attributes)) {
          if (!keep.includes(attr.name.toLowerCase())) child.removeAttribute(attr.name);
        }
        // 셀 배경색 class만 허용 (그 외 클래스·임시 선택 클래스는 제거)
        if ((child.tagName === 'TD' || child.tagName === 'TH') && child.hasAttribute('class')) {
          const hl = child.getAttribute('class').split(/\s+/).find(c => /^hl-(yellow|green|blue|pink|gray)$/.test(c));
          if (hl) child.setAttribute('class', hl); else child.removeAttribute('class');
        }
        if (child.tagName === 'A') {
          // 제어문자/공백을 제거한 뒤 위험 스킴 차단 (jav\tascript: 등 우회 방지)
          const href = (child.getAttribute('href') || '').replace(/[\u0000-\u0020\u007F]/g, '').toLowerCase();
          if (/^(javascript|data|vbscript):/.test(href)) child.removeAttribute('href');
        }
        if (child.tagName === 'IMG') {
          const src = child.getAttribute('src') || '';
          // 표시용 data:/blob: 과 저장용 images/ 상대참조만 허용
          if (!/^data:image\//i.test(src) && !src.startsWith('blob:') && !IMG_REF_RE.test(src)) {
            child.remove(); continue;
          }
        }
      } else if (child.nodeType !== Node.TEXT_NODE) {
        node.removeChild(child); // 주석 등 제거
      }
    }
  };
  walk(root);
  return root.innerHTML;
}

/* ===================== IndexedDB ===================== */

function idbOpen() {
  return new Promise((res, rej) => {
    const rq = indexedDB.open('todomemo', 1);
    rq.onupgradeneeded = () => rq.result.createObjectStore('kv');
    rq.onsuccess = () => res(rq.result);
    rq.onerror = () => rej(rq.error);
  });
}
async function idbSet(key, val) {
  const db = await idbOpen();
  return new Promise((res, rej) => {
    const tx = db.transaction('kv', 'readwrite');
    tx.objectStore('kv').put(val, key);
    tx.oncomplete = res;
    tx.onerror = () => rej(tx.error);
  });
}
async function idbGet(key) {
  const db = await idbOpen();
  return new Promise((res, rej) => {
    const rq = db.transaction('kv').objectStore('kv').get(key);
    rq.onsuccess = () => res(rq.result);
    rq.onerror = () => rej(rq.error);
  });
}
async function idbDel(key) {
  const db = await idbOpen();
  return new Promise((res, rej) => {
    const tx = db.transaction('kv', 'readwrite');
    tx.objectStore('kv').delete(key);
    tx.oncomplete = res;
    tx.onerror = () => rej(tx.error);
  });
}

/* ===================== 데이터 정규화 ===================== */

function normalize(raw) {
  const d = (raw && typeof raw === 'object') ? raw : {};
  const groups = [];
  if (Array.isArray(d.groups)) {
    for (const g of d.groups) {
      if (!g || typeof g !== 'object' || typeof g.name !== 'string') continue;
      groups.push({
        id: typeof g.id === 'string' ? g.id : uid(),
        name: g.name.slice(0, 40),
        color: /^#[0-9a-fA-F]{6}$/.test(g.color) ? g.color : GROUP_COLORS[groups.length % GROUP_COLORS.length],
      });
    }
  }
  if (groups.length === 0) groups.push({ id: uid(), name: '일반', color: GROUP_COLORS[0] });
  const gids = new Set(groups.map(g => g.id));

  const todos = [];
  if (Array.isArray(d.todos)) {
    for (const t of d.todos) {
      if (!t || typeof t !== 'object' || typeof t.title !== 'string') continue;
      todos.push({
        id: typeof t.id === 'string' ? t.id : uid(),
        title: t.title.slice(0, 300),
        done: !!t.done,
        groupId: gids.has(t.groupId) ? t.groupId : null,
        date: validDateKey(t.date) ? t.date : null,
        note: typeof t.note === 'string' ? t.note : '',
        created: typeof t.created === 'string' ? t.created : new Date().toISOString(),
        updated: typeof t.updated === 'string' ? t.updated : new Date().toISOString(),
      });
    }
  }
  return {
    groups,
    todos,
    meta: { savedAt: (d.meta && typeof d.meta.savedAt === 'string') ? d.meta.savedAt : '' },
  };
}

/* ===================== 저장소: 폴더 분할 저장 =====================
   폴더 하나에  index.json(메타) + notes/<id>.html + images/<해시>.<확장>.
   - 편집한 노트 1개 파일만 쓰기 → 전체 재작성 없음
   - 본문·이미지는 지연 로딩, index.json은 시작 시 한 번만 읽음
   - 폴더가 유일한 저장소(필수). 파일 핸들만 IndexedDB에 보관해 재연결.
   실제 FSA는 rootHandle(FileSystemDirectoryHandle)에 대해 동작하고,
   테스트는 rootHandle에 목 핸들을 주입해 동일 로직을 검증한다. */

const FS_API = typeof window.showDirectoryPicker === 'function';
let rootHandle = null;
let connected = false;
const IMG_REF_RE = /^images\/[A-Za-z0-9._-]+$/;  // 저장된 이미지 상대참조
const imgUrlCache = new Map();   // ref('images/xx') -> objectURL/데이터URL (표시용)
const dataUrlRef = new Map();    // data:URL -> ref (재해시 방지)

function setSaveState(text, ok, err) {
  const el = $('saveState');
  el.textContent = text;
  el.classList.toggle('saved', !!ok);
  el.classList.toggle('err', !!err);
}

/* ---- 파일시스템 헬퍼 (rootHandle 기준) ---- */
async function fsDir(parts, create) {
  let dir = rootHandle;
  for (const p of parts) dir = await dir.getDirectoryHandle(p, { create });
  return dir;
}
async function fsHandle(path, create) {
  const parts = path.split('/');
  const name = parts.pop();
  const dir = parts.length ? await fsDir(parts, create) : rootHandle;
  return dir.getFileHandle(name, { create });
}
async function fsReadText(path) { return (await (await fsHandle(path, false)).getFile()).text(); }
async function fsReadBytes(path) { return new Uint8Array(await (await (await fsHandle(path, false)).getFile()).arrayBuffer()); }
async function fsWrite(path, content) {
  const w = await (await fsHandle(path, true)).createWritable();
  await w.write(content);
  await w.close();
}
async function fsRemove(path) {
  const parts = path.split('/');
  const name = parts.pop();
  const dir = parts.length ? await fsDir(parts, false) : rootHandle;
  await dir.removeEntry(name).catch(() => {});
}

/* ---- index.json (메타데이터) ---- */
function buildIndex() {
  return {
    version: 1,
    savedAt: new Date().toISOString(),
    name: data.name || '',
    groups: data.groups,
    todos: data.todos.map(t => ({
      id: t.id, title: t.title, groupId: t.groupId, date: t.date,
      done: t.done, created: t.created, updated: t.updated, hasNote: !!t.hasNote,
    })),
  };
}

function indexToData(idx) {
  const raw = { groups: idx && idx.groups, todos: [] };
  const norm = normalize(raw); // 그룹 검증·기본 그룹 보장
  const gids = new Set(norm.groups.map(g => g.id));
  const todos = [];
  if (idx && Array.isArray(idx.todos)) {
    for (const t of idx.todos) {
      if (!t || typeof t.id !== 'string' || typeof t.title !== 'string') continue;
      todos.push({
        id: t.id, title: t.title.slice(0, 300), done: !!t.done,
        groupId: gids.has(t.groupId) ? t.groupId : null,
        date: validDateKey(t.date) ? t.date : null,
        created: typeof t.created === 'string' ? t.created : new Date().toISOString(),
        updated: typeof t.updated === 'string' ? t.updated : new Date().toISOString(),
        hasNote: !!t.hasNote,
        note: undefined, noteLoaded: false,
      });
    }
  }
  const name = (idx && typeof idx.name === 'string') ? idx.name.slice(0, 30) : '';
  return { groups: norm.groups, todos, name };
}

// index.json 쓰기는 단일 큐로 직렬화 (노트저장·메타저장이 동시에 같은 파일을 쓰지 않게)
let indexQueue = Promise.resolve();
function writeIndexNow() {
  indexQueue = indexQueue.then(() => fsWrite('index.json', JSON.stringify(buildIndex(), null, 2)));
  return indexQueue;
}
const hhmm = () => new Date().toTimeString().slice(0, 5);
function saveOk() { setSaveState(`저장됨 ${hhmm()}`, true); dirty = false; if (bc) bc.postMessage('saved'); }
function saveFail(msg) { setSaveState('저장 실패', false, true); if (msg) toast(msg, true); }

// index.json 쓰기 — 메타 변경(제목/그룹/날짜/완료/추가/삭제/순서) 시 호출 (디바운스)
const saveIndexQueued = debounce(() => {
  if (!connected) return;
  setSaveState('저장 중…', false);
  writeIndexNow().then(saveOk).catch(() => saveFail('저장 실패 — 폴더 연결을 확인하세요'));
}, 250);

// 메타데이터 저장 진입점 (기존 persist 대체)
function persist() { saveIndexQueued(); }

// 명시적 즉시 저장 — 대기 중인 편집을 모두 반영하고 index.json을 바로 쓴다
async function saveNow() {
  if (!connected) { toast('폴더가 연결되지 않았습니다', true); return; }
  flushPendingEdits();      // 디바운스 대기분(제목·메모) 즉시 실행
  setSaveState('저장 중…', false);
  try {
    await writeIndexNow();  // 큐에 쌓인 노트 저장까지 끝난 뒤 index 확정
    saveOk();
    toast('저장되었습니다');
  } catch (e) { saveFail('저장 실패 — 폴더 연결을 확인하세요'); }
}

/* ---- 이미지: 내용 해시로 파일명, 중복 제거 ---- */
async function sha256Hex(bytes) {
  const buf = await crypto.subtle.digest('SHA-256', bytes);
  return Array.from(new Uint8Array(buf)).map(b => b.toString(16).padStart(2, '0')).join('');
}
function dataUrlToBytes(dataUrl) {
  const m = /^data:([^;,]+)?(;base64)?,(.*)$/s.exec(dataUrl);
  if (!m) return null;
  const mime = m[1] || 'image/png';
  const bytes = m[2] ? Uint8Array.from(atob(m[3]), c => c.charCodeAt(0))
    : new TextEncoder().encode(decodeURIComponent(m[3]));
  return { mime, bytes };
}
const EXT_OF = { 'image/png': 'png', 'image/jpeg': 'jpg', 'image/gif': 'gif', 'image/webp': 'webp', 'image/svg+xml': 'svg' };

async function storeImageBytes(bytes, mime) {
  const hash = await sha256Hex(bytes);
  const ref = `images/${hash}.${EXT_OF[mime] || 'png'}`;
  try { await fsHandle(ref, false); } catch (e) { await fsWrite(ref, new Blob([bytes], { type: mime })); }
  return ref;
}

// 저장용: 에디터 HTML의 <img>를 파일 참조로 바꾼 HTML 반환.
// 로드된 이미지는 data-ref 속성에 원래 참조를 지녀(URL 캐시에 의존 안 함), 새 이미지는 해시 저장.
async function externalizeImages(html) {
  const doc = new DOMParser().parseFromString(`<div>${html}</div>`, 'text/html');
  const root = doc.body.firstChild;
  for (const img of Array.from(root.querySelectorAll('img'))) {
    const dref = img.getAttribute('data-ref') || '';
    if (IMG_REF_RE.test(dref)) { img.setAttribute('src', dref); img.removeAttribute('data-ref'); continue; }
    const src = img.getAttribute('src') || '';
    if (IMG_REF_RE.test(src)) { img.removeAttribute('data-ref'); continue; } // 이미 참조
    if (src.startsWith('data:')) {
      let ref = dataUrlRef.get(src);
      if (!ref) {
        const parsed = dataUrlToBytes(src);
        if (!parsed) { img.remove(); continue; }
        ref = await storeImageBytes(parsed.bytes, parsed.mime);
        dataUrlRef.set(src, ref);
      }
      img.setAttribute('src', ref); img.removeAttribute('data-ref');
    } else if (src.startsWith('blob:')) {
      // data-ref 없는 blob(예외적) → URL 캐시 역매핑 폴백
      let found = '';
      for (const [ref, url] of imgUrlCache) if (url === src) { found = ref; break; }
      if (found) { img.setAttribute('src', found); img.removeAttribute('data-ref'); }
      else img.remove();
    } else {
      img.remove(); // 알 수 없는 src
    }
  }
  // 임시 UI 클래스 제거 (셀 선택·이미지 선택은 저장 대상 아님)
  for (const el of Array.from(root.querySelectorAll('.cell-sel, .img-selected'))) {
    el.classList.remove('cell-sel', 'img-selected');
    if (!el.getAttribute('class')) el.removeAttribute('class');
  }
  return root.innerHTML;
}

// 로드용: 상대참조 <img src="images/..">를 표시 가능한 URL로 치환
async function resolveImages(html) {
  const doc = new DOMParser().parseFromString(`<div>${html}</div>`, 'text/html');
  const root = doc.body.firstChild;
  for (const img of Array.from(root.querySelectorAll('img'))) {
    const ref = img.getAttribute('src') || '';
    if (!IMG_REF_RE.test(ref)) continue;
    let url = imgUrlCache.get(ref);
    if (!url) {
      try {
        const bytes = await fsReadBytes(ref);
        const ext = ref.split('.').pop().toLowerCase();
        const mime = Object.keys(EXT_OF).find(k => EXT_OF[k] === ext) || 'image/png';
        url = URL.createObjectURL(new Blob([bytes], { type: mime }));
        imgUrlCache.set(ref, url);
      } catch (e) { img.remove(); continue; }
    }
    img.setAttribute('data-ref', ref); // 저장 시 원래 참조를 되찾기 위해
    img.setAttribute('src', url);
  }
  return root.innerHTML;
}

/* ---- 노트 본문 로드/저장 ---- */
async function loadNote(t) {
  if (t.noteLoaded) return;
  if (!t.hasNote) { t.note = ''; t.noteLoaded = true; return; }
  try {
    const html = await fsReadText(`notes/${t.id}.html`);
    t.note = await resolveImages(html);
  } catch (e) { t.note = ''; }
  t.noteLoaded = true;
}

// 임의의 할일 t를 주어진 html로 저장 (에디터에 없는 항목도 가능)
async function writeNoteBody(t, html) {
  if (!t || !connected) return;
  const hasContent = notePlainText(html) !== '' || /<(img|table|hr)/i.test(html);
  setSaveState('저장 중…', false);
  try {
    if (hasContent) {
      const stored = await externalizeImages(html); // 이미지 파일로 분리
      await fsWrite(`notes/${t.id}.html`, stored);
      t.note = html; t.noteLoaded = true; t.hasNote = true;
    } else {
      if (t.hasNote) await fsRemove(`notes/${t.id}.html`);
      t.note = ''; t.noteLoaded = true; t.hasNote = false;
    }
    t.updated = new Date().toISOString();
    await writeIndexNow();
    saveOk();
    searchCache.delete(t.id); // 본문 바뀜 → 검색 캐시 무효화
    dirty = false;
  } catch (e) {
    saveFail('노트 저장에 실패했습니다 — 폴더 연결을 확인하세요');
  }
}

// 현재 에디터에 열린 할일 저장
function saveNoteBody(id) {
  const t = data.todos.find(x => x.id === id);
  if (!t) return Promise.resolve();
  return writeNoteBody(t, $('edNote').innerHTML);
}

async function deleteNoteFile(id, hadNote) {
  if (connected && hadNote) { try { await fsRemove(`notes/${id}.html`); } catch (e) {} }
}

/* ---- 폴더 연결 · 시작 ---- */
async function loadFromFolder() {
  // 파일 없음(새 폴더)과 손상된 index.json을 구분 — 손상 시 절대 덮어쓰지 않는다
  let raw = null, missing = false;
  try { raw = await fsReadText('index.json'); }
  catch (e) { missing = true; }

  let idx = null;
  if (!missing) {
    try { idx = JSON.parse(raw); }
    catch (e) {
      showGate('corrupt');   // 손상 → 게이트로 알리고 중단 (덮어쓰기 금지)
      return;
    }
  }

  revokeAllImageUrls();
  data = indexToData(idx);
  connected = true;
  selectedId = null;
  imgUrlCache.clear(); dataUrlRef.clear(); searchCache.clear();
  if (missing) await writeIndexNow();  // 새 폴더만 초기화
  updateFolderUI();
  hideGate();
  renderAll();
  prewarmBodyCache();  // 검색·GC 대비 백그라운드 준비
}

// 캐시된 blob URL 해제 (메모리 누수 방지)
function revokeAllImageUrls() {
  for (const url of imgUrlCache.values()) {
    if (typeof url === 'string' && url.startsWith('blob:')) { try { URL.revokeObjectURL(url); } catch (e) {} }
  }
}

// 노트 재방문 시 이미지 재연결: 노트 전환에서 blob URL을 revoke하므로, t.note에
// 박혀 있던 예전 blob 주소는 무효다. 화면의 각 이미지를 data-ref(images/해시)로
// (캐시에 없으면 파일에서 다시 만들어) 최신 blob에 연결한다.
async function rebindNoteImages() {
  const imgs = Array.from($('edNote').querySelectorAll('img[data-ref]'));
  for (const img of imgs) {
    const ref = img.getAttribute('data-ref');
    if (!IMG_REF_RE.test(ref)) continue;
    let url = imgUrlCache.get(ref);
    if (!url) {
      try {
        const bytes = await fsReadBytes(ref);
        const ext = ref.split('.').pop().toLowerCase();
        const mime = Object.keys(EXT_OF).find(k => EXT_OF[k] === ext) || 'image/png';
        url = URL.createObjectURL(new Blob([bytes], { type: mime }));
        imgUrlCache.set(ref, url);
      } catch (e) { continue; }
    }
    if (img.getAttribute('src') !== url) img.setAttribute('src', url);
  }
}

async function pickFolder() {
  try {
    const h = await window.showDirectoryPicker({ mode: 'readwrite' });
    rootHandle = h;
    try { await idbSet('dirHandle', h); } catch (e) { /* 무시 */ }
    await loadFromFolder();
    toast(`폴더 연결됨: ${h.name}`);
  } catch (e) {
    if (e && e.name === 'AbortError') return;
    toast('폴더 연결에 실패했습니다', true);
  }
}

async function initStorage() {
  if (!FS_API) { showGate('unsupported'); return; }
  try { rootHandle = (await idbGet('dirHandle')) || null; } catch (e) { rootHandle = null; }
  if (rootHandle && typeof rootHandle.queryPermission === 'function') {
    try {
      if ((await rootHandle.queryPermission({ mode: 'readwrite' })) === 'granted') {
        await loadFromFolder();
        return;
      }
    } catch (e) { /* 무시 */ }
    showGate('reconnect');
    armReconnect();
    return;
  }
  showGate('pick');
}

// 저장된 폴더 재연결 — 첫 사용자 제스처에 권한 요청
function armReconnect() {
  const handler = async e => {
    if (e.target && e.target.closest && e.target.closest('#gateBtn')) return;
    document.removeEventListener('pointerdown', handler, true);
    if (!rootHandle || connected) return;
    try {
      const p = await rootHandle.requestPermission({ mode: 'readwrite' });
      if (p === 'granted') await loadFromFolder();
    } catch (e2) { /* 버튼으로 재시도 가능 */ }
  };
  document.addEventListener('pointerdown', handler, true);
}

function updateFolderUI() {
  const btn = $('btnFile');
  if (!btn) return;
  btn.hidden = false;
  btn.textContent = connected && rootHandle ? `📁 ${rootHandle.name}` : '폴더 연결';
  btn.classList.toggle('on', connected);
}

/* ---- 첫 실행 게이트 ---- */
function showGate(mode) {
  const g = $('folderGate');
  if (!g) return;
  const msg = $('gateMsg'), btn = $('gateBtn');
  if (mode === 'unsupported') {
    msg.textContent = '이 브라우저는 폴더 저장을 지원하지 않습니다. Chrome 또는 Edge로 열어 주세요.';
    btn.hidden = true;
  } else if (mode === 'reconnect') {
    msg.textContent = '메모 폴더 접근을 허용해 주세요.';
    btn.textContent = '폴더 다시 연결';
    btn.hidden = false;
  } else if (mode === 'corrupt') {
    msg.textContent = 'index.json 파일을 읽을 수 없습니다(손상 가능성).\n덮어쓰지 않았습니다. 폴더를 확인하거나 백업으로 복구한 뒤 다시 연결하세요.';
    btn.textContent = '다른 폴더 선택';
    btn.hidden = false;
  } else {
    msg.textContent = '메모를 저장할 폴더를 선택하세요.\n선택한 폴더 안에 index.json·notes·images로 저장됩니다.';
    btn.textContent = '폴더 선택';
    btn.hidden = false;
  }
  g.hidden = false;
}
function hideGate() { const g = $('folderGate'); if (g) g.hidden = true; }

/* ===================== 조회 헬퍼 ===================== */

const groupOf = id => data.groups.find(g => g.id === id) || null;

// 뷰에 해당하는 (미완료, 완료, 밀린) 목록
function itemsForView(v) {
  const tk = todayKey();
  const all = data.todos;
  let match;
  if (v.type === 'today') match = t => t.date === tk;
  else if (v.type === 'week') {
    const now = new Date();
    const mon = new Date(now.getFullYear(), now.getMonth(), now.getDate() - ((now.getDay() + 6) % 7));
    const sun = new Date(mon.getFullYear(), mon.getMonth(), mon.getDate() + 6);
    const a = keyOf(mon), b = keyOf(sun);
    match = t => t.date !== null && t.date >= a && t.date <= b;
  } else if (v.type === 'month') {
    const now = new Date();
    const prefix = `${now.getFullYear()}-${pad(now.getMonth() + 1)}-`;
    match = t => t.date !== null && t.date.startsWith(prefix);
  } else if (v.type === 'group') match = t => t.groupId === v.groupId;
  else match = () => true; // all, done, incomplete

  const active = all.filter(t => !t.done && match(t));
  // "밀린 할 일" = 현재 기간 시작 이전의 미완료 (기간 내부의 지난 날짜와 중복되지 않게)
  let overdueBefore = null;
  if (v.type === 'today') overdueBefore = tk;
  else if (v.type === 'week') {
    const now = new Date();
    overdueBefore = keyOf(new Date(now.getFullYear(), now.getMonth(), now.getDate() - ((now.getDay() + 6) % 7)));
  } else if (v.type === 'month') {
    const now = new Date();
    overdueBefore = `${now.getFullYear()}-${pad(now.getMonth() + 1)}-01`;
  }
  const overdue = overdueBefore
    ? all.filter(t => !t.done && t.date !== null && t.date < overdueBefore)
    : [];
  // 각 기간 뷰의 완료함은 그 기간으로만 한정 (오늘=오늘, 주=이번 주, 달=이번 달)
  let done;
  if (v.type === 'incomplete') done = [];                       // 미완료 뷰: 완료 항목 숨김
  else if (v.type === 'today') done = all.filter(t => t.done && t.date === tk);
  else done = all.filter(t => t.done && match(t));               // week/month는 match가 이미 기간 한정
  return { active, done, overdue };
}

const byDate = (a, b) =>
  (a.date === null) - (b.date === null) ||
  (a.date || '').localeCompare(b.date || '') ||
  a.created.localeCompare(b.created);

/* ===================== 렌더링 ===================== */

function renderAll() {
  renderBrand();
  renderSidebar();
  renderList();
  renderEditor();
  renderNavButtons();
}

function renderBrand() {
  const name = (data && data.name || '').trim();
  const label = name ? `${name}의 메모장` : 'TODO 메모장';
  $('brandTitle').textContent = label;
  document.title = label; // 브라우저 탭 라벨도 갱신
}

// 상단 제목 클릭 → 이름 인라인 편집
function editBrandName() {
  const h1 = $('brandTitle');
  const input = document.createElement('input');
  input.className = 'brand-input';
  input.maxLength = 30;
  input.placeholder = '이름 (예: 홍길동)';
  input.value = (data.name || '');
  h1.replaceWith(input);
  input.focus();
  input.select();
  const finish = save => {
    if (save) { data.name = input.value.trim().slice(0, 30); persist(); }
    input.replaceWith(h1);
    renderBrand();
  };
  input.addEventListener('keydown', e => {
    if (e.key === 'Enter') finish(true);
    if (e.key === 'Escape') finish(false);
  });
  input.addEventListener('blur', () => finish(true));
}

function renderSidebar() {
  const tk = todayKey();
  const act = data.todos.filter(t => !t.done);
  $('cntToday').textContent = act.filter(t => t.date !== null && t.date <= tk).length || '';
  const { active: wk } = itemsForView({ type: 'week' });
  $('cntWeek').textContent = wk.length || '';
  const { active: mo } = itemsForView({ type: 'month' });
  $('cntMonth').textContent = mo.length || '';
  $('cntIncomplete').textContent = act.length || '';
  $('cntAll').textContent = act.length || '';
  $('cntDone').textContent = data.todos.filter(t => t.done).length || '';

  document.querySelectorAll('.nav-item[data-view]').forEach(el =>
    el.classList.toggle('active', view.type === el.dataset.view));

  const wrap = $('groupList');
  const savedScroll = wrap.scrollTop;      // 재렌더 시 그룹 목록 스크롤 위치 유지
  wrap.innerHTML = '';
  for (const g of data.groups) {
    const cnt = data.todos.filter(t => !t.done && t.groupId === g.id).length;
    const btn = document.createElement('button');
    btn.type = 'button';
    btn.className = 'nav-item' + (view.type === 'group' && view.groupId === g.id ? ' active' : '');
    btn.dataset.group = g.id;
    btn.innerHTML =
      `<span class="group-dot" style="background:${g.color}"></span>` +
      `<span class="g-name"></span>` +
      `<button class="g-edit" title="이름 변경" tabindex="-1">✎</button>` +
      `<button class="g-del" title="그룹 삭제" tabindex="-1">✕</button>` +
      `<b class="cnt">${cnt || ''}</b>`;
    btn.querySelector('.g-name').textContent = g.name;
    wrap.appendChild(btn);
  }
  wrap.scrollTop = savedScroll;

  renderRecent();
}

function viewTitle() {
  if (view.type === 'today') return ['오늘', fmtDateShort(todayKey())];
  if (view.type === 'week') return ['이번 주', ''];
  if (view.type === 'month') return ['이번 달', `${new Date().getMonth() + 1}월`];
  if (view.type === 'incomplete') return ['미완료', ''];
  if (view.type === 'all') return ['전체', ''];
  if (view.type === 'done') return ['완료됨', ''];
  const g = groupOf(view.groupId);
  return [g ? g.name : '그룹', ''];
}

function renderList() {
  if (view.type === 'search') { renderSearch(); return; }
  if (view.type === 'calendar') { renderCalendar(); return; }
  $('todoList').classList.remove('cal-mode');
  const [title, sub] = viewTitle();
  $('viewTitle').textContent = title;
  $('viewSub').textContent = sub;
  // 완료됨 뷰에서는 새 할일을 추가할 곳이 없으므로 입력창 숨김
  document.querySelector('.quick-add').hidden = (view.type === 'done');

  const { active, done, overdue } = itemsForView(view);
  const list = $('todoList');
  list.innerHTML = '';
  const frag = document.createDocumentFragment();

  const addSec = (label, cls) => {
    const el = document.createElement('div');
    el.className = 'list-sec' + (cls ? ' ' + cls : '');
    el.textContent = label;
    frag.appendChild(el);
  };
  const addRows = items => items.forEach(t => frag.appendChild(rowEl(t)));

  if (view.type === 'done') {
    if (done.length === 0) frag.appendChild(emptyEl('완료된 할 일이 없습니다'));
    addRows(done.sort((a, b) => b.updated.localeCompare(a.updated)));
  } else {
    if (overdue.length > 0) {
      addSec(`밀린 할 일 ${overdue.length}`, 'overdue');
      addRows(overdue.sort(byDate));
    }
    if (view.type === 'week' || view.type === 'month') {
      // 날짜별 섹션
      const byDay = new Map();
      for (const t of active.sort(byDate)) {
        if (!byDay.has(t.date)) byDay.set(t.date, []);
        byDay.get(t.date).push(t);
      }
      if (byDay.size === 0 && overdue.length === 0) {
        frag.appendChild(emptyEl(view.type === 'week' ? '이번 주 할 일이 없습니다' : '이번 달 할 일이 없습니다'));
      }
      for (const [dk, items] of byDay) {
        addSec(fmtDateShort(dk) + (dk === todayKey() ? ' · 오늘' : ''));
        addRows(items);
      }
    } else {
      if (view.type === 'today' && overdue.length > 0 && active.length > 0) addSec('오늘');
      if (active.length === 0 && overdue.length === 0) {
        frag.appendChild(emptyEl(view.type === 'today' ? '오늘 할 일이 없습니다 — 위에 입력해보세요' : '할 일이 없습니다'));
      }
      addRows(active.sort(byDate));
    }
    // 이 뷰의 완료 항목 (접힘)
    if (done.length > 0) {
      const t = document.createElement('button');
      t.type = 'button';
      t.className = 'done-toggle';
      t.textContent = `${doneOpen ? '▾' : '▸'} 완료 ${done.length}`;
      t.addEventListener('click', () => { doneOpen = !doneOpen; renderList(); });
      frag.appendChild(t);
      if (doneOpen) addRows(done.sort((a, b) => b.updated.localeCompare(a.updated)));
    }
  }
  list.appendChild(frag);
}

function emptyEl(msg) {
  const el = document.createElement('div');
  el.className = 'list-empty';
  el.textContent = msg;
  return el;
}

/* ---------- 달력 뷰 ---------- */

function renderCalendar() {
  $('viewTitle').textContent = '달력';
  $('viewSub').textContent = `${calY}년 ${calM + 1}월`;
  document.querySelector('.quick-add').hidden = true;

  const host = $('todoList');
  host.classList.add('cal-mode');
  host.innerHTML = '';

  // 헤더 (월 이동)
  const head = document.createElement('div');
  head.className = 'cal-head';
  head.innerHTML =
    `<button class="cal-nav" data-cal="prev" title="이전 달">◀</button>` +
    `<span class="cal-title">${calY}년 ${calM + 1}월</span>` +
    `<button class="cal-nav" data-cal="next" title="다음 달">▶</button>` +
    `<button class="cal-today" data-cal="today">오늘</button>`;
  host.appendChild(head);

  // 이 달 날짜별 할일 모으기
  const prefix = `${calY}-${pad(calM + 1)}-`;
  const byDay = {};
  for (const t of data.todos) {
    if (t.date && t.date.startsWith(prefix)) (byDay[t.date] ||= []).push(t);
  }

  const dowRow = document.createElement('div');
  dowRow.className = 'cal-dow-row';
  for (const [i, name] of DOW.entries()) {
    const h = document.createElement('div');
    h.className = 'cal-dow' + (i === 0 ? ' sun' : i === 6 ? ' sat' : '');
    h.textContent = name;
    dowRow.appendChild(h);
  }
  host.appendChild(dowRow);

  const grid = document.createElement('div');
  grid.className = 'cal-grid';

  const firstDow = new Date(calY, calM, 1).getDay();
  const daysInMonth = new Date(calY, calM + 1, 0).getDate();
  const tk = todayKey();

  for (let i = 0; i < firstDow; i++) {
    const e = document.createElement('div');
    e.className = 'cal-cell empty';
    grid.appendChild(e);
  }

  for (let d = 1; d <= daysInMonth; d++) {
    const dk = `${calY}-${pad(calM + 1)}-${pad(d)}`;
    const dow = (firstDow + d - 1) % 7;
    const items = (byDay[dk] || []).sort((a, b) => a.created.localeCompare(b.created));

    const cell = document.createElement('div');
    cell.className = 'cal-cell'
      + (dow === 0 ? ' sun' : dow === 6 ? ' sat' : '')
      + (dk === tk ? ' today' : '');
    cell.dataset.day = dk;

    let html = `<div class="cal-daynum"><span>${d}</span>` +
      `<button class="cal-add" data-add="${dk}" title="이 날 할 일 추가" tabindex="-1">＋</button></div>`;
    html += '<div class="cal-chips">';
    const MAX = 4;
    items.slice(0, MAX).forEach(t => {
      const g = groupOf(t.groupId);
      const dot = g ? `<span class="chip-dot" style="background:${g.color}"></span>` : '';
      html += `<button class="cal-chip${t.done ? ' done' : ''}${t.id === selectedId ? ' sel' : ''}" ` +
        `data-id="${t.id}" title="${escapeText(t.title)}">${dot}<span class="chip-t"></span></button>`;
    });
    if (items.length > MAX) html += `<span class="cal-more">+${items.length - MAX}개</span>`;
    html += '</div>';
    cell.innerHTML = html;
    // 제목은 textContent로 안전하게
    const chips = cell.querySelectorAll('.cal-chip .chip-t');
    items.slice(0, MAX).forEach((t, i) => { chips[i].textContent = t.title || '(제목 없음)'; });
    grid.appendChild(cell);
  }

  const used = firstDow + daysInMonth;
  const trailing = (7 - (used % 7)) % 7;
  for (let i = 0; i < trailing; i++) {
    const e = document.createElement('div');
    e.className = 'cal-cell empty';
    grid.appendChild(e);
  }

  host.appendChild(grid);
}

function moveCalMonth(delta) {
  const d = new Date(calY, calM + delta, 1);
  calY = d.getFullYear(); calM = d.getMonth();
  renderCalendar();
}

// 특정 날짜에 새 할 일 추가 후 편집기 제목에 포커스
function addTodoOnDate(dateKey) {
  flushPendingEdits();
  const t = {
    id: uid(), title: '', done: false,
    groupId: view.type === 'group' ? view.groupId : null,
    date: dateKey,
    note: '', noteLoaded: true, hasNote: false,
    created: new Date().toISOString(), updated: new Date().toISOString(),
  };
  data.todos.push(t);
  selectedId = t.id;
  persist();
  renderAll();
  $('edTitle').focus();
}

function rowEl(t) {
  const row = document.createElement('div');
  row.className = 'todo-row' + (t.done ? ' done' : '') + (t.id === selectedId ? ' selected' : '');
  row.dataset.id = t.id;
  row.tabIndex = 0; // 키보드 선택 가능

  const g = groupOf(t.groupId);
  const tk = todayKey();
  const hasNote = !!t.hasNote;

  const metas = [];
  if (g && !(view.type === 'group')) {
    metas.push(`<span class="meta-group"><span class="group-dot" style="background:${g.color}"></span>${escapeText(g.name)}</span>`);
  }
  if (t.date && view.type !== 'week') {
    const od = !t.done && t.date < tk;
    metas.push(`<span class="meta-date${od ? ' overdue' : ''}">${fmtDateShort(t.date)}</span>`);
  }
  if (hasNote) metas.push(`<span class="meta-note">📄</span>`);

  row.innerHTML =
    `<button class="todo-check" type="button" title="완료">✓</button>` +
    `<div class="todo-main">` +
      `<div class="todo-title"></div>` +
      (metas.length ? `<div class="todo-meta">${metas.join('')}</div>` : '') +
    `</div>` +
    `<button class="row-del" type="button" title="삭제">✕</button>`;
  row.querySelector('.todo-title').textContent = t.title || '(제목 없음)';
  return row;
}

function escapeText(s) {
  const d = document.createElement('div');
  d.textContent = s;
  return d.innerHTML;
}

/* ===================== 검색 =====================
   성능: 본문 순수텍스트(태그·base64 제외)를 캐시하고 할일 수정 시에만 재계산.
   검색 자체는 캐시된 소문자 문자열 indexOf 대조라 문서가 많아도 빠르다. */

// <template>은 비활성(browsing context 없는) 문서 소속이라 innerHTML에 담긴
// <img src="images/..">·<img src="http..">가 실제 리소스를 로드(GET)하지 않는다.
// (일반 div는 현재 문서 소속이라 prewarm/검색이 모든 노트를 훑을 때 이미지마다
//  서버로 GET을 날려 404 로그가 대량으로 쌓였다.)
const _stripEl = document.createElement('template');
function notePlainText(html) {
  _stripEl.innerHTML = html || '';
  // textContent는 속성(img src의 base64 등)을 포함하지 않아 안전·경량
  return _stripEl.content.textContent.replace(/\s+/g, ' ').trim();
}

// 캐시 조회(동기) — 없으면 제목만 있는 임시 항목 (본문은 ensureBodyCache가 채움)
function getCache(t) {
  const c = searchCache.get(t.id);
  if (c && c.updated === t.updated) return c;
  const title = t.title || '';
  return { updated: t.updated, title, titleLc: title.toLowerCase(), body: '', bodyLc: '' };
}

// 본문 검색 준비: 노트 파일을 읽어 텍스트 캐시 (수정된 것만, 동시성 제한)
let prewarming = false, prewarmDone = 0, prewarmTotal = 0;
async function ensureBodyCache(onProgress) {
  if (!connected) return;
  const need = data.todos.filter(t => {
    const c = searchCache.get(t.id);
    return !c || c.updated !== t.updated;
  });
  prewarmTotal = need.length; prewarmDone = 0;
  const CHUNK = 24;
  for (let i = 0; i < need.length; i += CHUNK) {
    await Promise.all(need.slice(i, i + CHUNK).map(async t => {
      const title = t.title || '';
      let body = '';
      if (t.hasNote) { try { body = notePlainText(await fsReadText(`notes/${t.id}.html`)); } catch (e) {} }
      searchCache.set(t.id, { updated: t.updated, title, titleLc: title.toLowerCase(), body, bodyLc: body.toLowerCase() });
      prewarmDone++;
    }));
    if (onProgress) onProgress(prewarmDone, prewarmTotal);
  }
}

// 시작 직후 유휴 시간에 본문 캐시를 미리 채우고, 참조 없는 이미지 파일 정리(GC)
function prewarmBodyCache() {
  if (prewarming || !connected) return;
  prewarming = true;
  const run = async () => {
    try {
      await ensureBodyCache();
      await gcImages();
    } catch (e) { /* 무시 */ }
    prewarming = false;
  };
  if (window.requestIdleCallback) requestIdleCallback(run, { timeout: 3000 });
  else setTimeout(run, 800);
}

// 어떤 노트에서도 참조하지 않는 images/ 파일 삭제 (노트 캐시가 준비된 뒤 실행)
async function gcImages() {
  if (!connected || !rootHandle) return;
  // 참조된 해시 수집: 저장된 노트 HTML을 읽어 images/ 참조 추출
  const used = new Set();
  for (const t of data.todos) {
    if (!t.hasNote) continue;
    try {
      const html = await fsReadText(`notes/${t.id}.html`);
      for (const m of html.matchAll(/images\/([A-Za-z0-9._-]+)/g)) used.add(m[1]);
    } catch (e) { return; } // 하나라도 못 읽으면 안전하게 중단(오삭제 방지)
  }
  let imgDir;
  try { imgDir = await rootHandle.getDirectoryHandle('images', { create: false }); }
  catch (e) { return; }
  const toDelete = [];
  try {
    for await (const [name, h] of imgDir.entries()) {
      if (h.kind === 'file' && !used.has(name)) toDelete.push(name);
    }
  } catch (e) { return; }
  for (const name of toDelete) { try { await imgDir.removeEntry(name); imgUrlCache.delete(`images/${name}`); } catch (e) {} }
}

// 질의를 검색어 조각으로 분해: "a and b" → ['a','b'] (각 조각은 소문자 부분일치 대상)
function parseQuery(q) {
  return q.split(/\s+and\s+/i).map(s => s.trim().toLowerCase()).filter(Boolean);
}

// 수정일 기준 최신 가점 (0~30, 최근일수록 높음)
function recencyBonus(updated) {
  const ageDays = (Date.now() - new Date(updated).getTime()) / 86400000;
  if (!isFinite(ageDays) || ageDays < 0) return 15;
  return Math.max(0, 30 - ageDays * 0.3); // ~100일이면 0
}

function runSearch() {
  const terms = parseQuery(search.q);
  search.hlTerms = terms;
  if (terms.length === 0) { search.results = []; return; }
  const scope = search.scope;
  const scoreList = [];

  for (const t of data.todos) {
    if (!search.includeDone && t.done) continue;
    if (search.group && t.groupId !== search.group) continue;
    const c = getCache(t);

    // AND: 모든 조각이 범위 안 어딘가에 있어야 함
    let ok = true, titleHit = false, bodyHit = false;
    for (const term of terms) {
      const inTitle = scope !== 'body' && c.titleLc.includes(term);
      const inBody = scope !== 'title' && c.bodyLc.includes(term);
      if (!inTitle && !inBody) { ok = false; break; }
      if (inTitle) titleHit = true;
      if (inBody && !inTitle) bodyHit = true;
    }
    if (!ok) continue;

    // 점수: 제목 매칭 > 본문, 제목 시작 일치 보너스 + 최신 가점
    const allInTitle = terms.every(term => c.titleLc.includes(term));
    let score = allInTitle ? 100 : (titleHit ? 70 : 40);
    if (c.titleLc.startsWith(terms[0])) score += 20;
    score += recencyBonus(t.updated);

    scoreList.push({ t, titleHit, bodyHit, score });
  }

  scoreList.sort((a, b) =>
    b.score - a.score || (b.t.updated || '').localeCompare(a.t.updated || ''));
  search.results = scoreList;
}

// 텍스트에서 검색어들을 <mark>로 강조 (이스케이프 후)
function highlight(text, terms) {
  let html = escapeText(text);
  if (!terms.length) return html;
  // 이스케이프된 텍스트 위에서 대소문자 무시 치환
  const esc = terms.map(t => escapeText(t)).filter(Boolean)
    .sort((a, b) => b.length - a.length)
    .map(t => t.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'));
  if (!esc.length) return html;
  const re = new RegExp('(' + esc.join('|') + ')', 'gi');
  return html.replace(re, '<mark>$1</mark>');
}

// 본문에서 첫 매칭 주변 스니펫
function bodySnippet(bodyLc, body, terms) {
  let pos = -1;
  for (const term of terms) {
    const i = bodyLc.indexOf(term);
    if (i >= 0 && (pos < 0 || i < pos)) pos = i;
  }
  if (pos < 0) return '';
  const start = Math.max(0, pos - 30);
  const end = Math.min(body.length, pos + 70);
  return (start > 0 ? '…' : '') + body.slice(start, end) + (end < body.length ? '…' : '');
}

function renderSearch() {
  document.querySelector('.quick-add').hidden = true;
  $('todoList').classList.remove('cal-mode');
  const n = search.results.length;
  $('viewTitle').textContent = '검색';
  $('viewSub').textContent = search.q.trim() ? `${n}개 결과` : '검색어를 입력하세요';

  const list = $('todoList');
  list.innerHTML = '';

  // 필터 줄
  const bar = document.createElement('div');
  bar.className = 'search-filter';
  const groupOpts = ['<option value="">모든 그룹</option>']
    .concat(data.groups.map(g => `<option value="${g.id}"${search.group === g.id ? ' selected' : ''}>${escapeText(g.name)}</option>`))
    .join('');
  bar.innerHTML =
    `<select id="sfGroup" aria-label="그룹 필터">${groupOpts}</select>` +
    `<label class="sf-check"><input type="checkbox" id="sfDone"${search.includeDone ? ' checked' : ''}> 완료 포함</label>`;
  list.appendChild(bar);

  if (!search.q.trim()) {
    list.appendChild(emptyEl('제목·본문에서 검색합니다'));
    return;
  }
  if (n === 0) {
    list.appendChild(emptyEl('일치하는 할 일이 없습니다'));
    return;
  }

  const frag = document.createDocumentFragment();
  const shown = search.results.slice(0, search.page * SEARCH_PAGE);
  for (const r of shown) frag.appendChild(searchRow(r));
  list.appendChild(frag);

  if (search.results.length > shown.length) {
    const more = document.createElement('button');
    more.type = 'button';
    more.className = 'search-more';
    more.id = 'searchMore';
    more.textContent = `더보기 (남은 ${search.results.length - shown.length}개)`;
    list.appendChild(more);
  }
}

function searchRow(r) {
  const t = r.t;
  const c = getCache(t);
  const terms = search.hlTerms;
  const row = document.createElement('div');
  row.className = 'todo-row search-row' + (t.done ? ' done' : '') + (t.id === selectedId ? ' selected' : '');
  row.dataset.id = t.id;
  row.tabIndex = 0;

  const g = groupOf(t.groupId);
  const metas = [];
  if (g) metas.push(`<span class="meta-group"><span class="group-dot" style="background:${g.color}"></span>${escapeText(g.name)}</span>`);
  if (t.date) metas.push(`<span class="meta-date">${fmtDateShort(t.date)}</span>`);
  if (t.done) metas.push(`<span class="meta-done">완료</span>`);

  const snip = r.bodyHit ? bodySnippet(c.bodyLc, c.body, terms) : '';
  row.innerHTML =
    `<button class="todo-check" type="button" title="완료">✓</button>` +
    `<div class="todo-main">` +
      `<div class="todo-title">${highlight(t.title || '(제목 없음)', terms)}</div>` +
      (snip ? `<div class="search-snip">${highlight(snip, terms)}</div>` : '') +
      (metas.length ? `<div class="todo-meta">${metas.join('')}</div>` : '') +
    `</div>`;
  return row;
}

// 검색 실행(디바운스) — 본문 범위면 노트 캐시를 먼저 준비
const doSearch = debounce(async () => {
  if (search.scope !== 'title' && search.q.trim()) {
    await ensureBodyCache((done, total) => {
      if (total > 40 && view.type === 'search') $('viewSub').textContent = `검색 색인 준비 중… ${done}/${total}`;
    });
  }
  runSearch();
  search.page = 1;
  renderSearch();
}, 150);

// 범위/필터 변경 시 재검색 (본문 캐시 필요하면 준비)
async function rerunSearch() {
  if (search.scope !== 'title' && search.q.trim()) await ensureBodyCache();
  runSearch();
  search.page = 1;
  renderSearch();
}

function enterSearch() {
  if (view.type !== 'search') { prevView = view; view = { type: 'search' }; }
  renderSidebarActive();
}

function exitSearch() {
  $('searchInput').value = '';
  search.q = '';
  $('searchClear').hidden = true;
  view = prevView || { type: 'today', groupId: null };
  prevView = null;
  search.hlTerms = [];
  renderAll();
}

function renderSidebarActive() {
  document.querySelectorAll('.nav-item[data-view]').forEach(el =>
    el.classList.toggle('active', view.type === el.dataset.view));
}

// 에디터에서 검색어 첫 위치로 스크롤 + 강조 (저장에 영향 없음)
function highlightInNote() {
  const terms = search.hlTerms;
  if (!terms.length) return;
  const note = $('edNote');
  const walker = document.createTreeWalker(note, NodeFilter.SHOW_TEXT);
  let node;
  while ((node = walker.nextNode())) {
    const lc = node.nodeValue.toLowerCase();
    let idx = -1;
    for (const term of terms) { const i = lc.indexOf(term); if (i >= 0 && (idx < 0 || i < idx)) { idx = i; var hitTerm = term; } }
    if (idx >= 0) {
      const range = document.createRange();
      range.setStart(node, idx);
      range.setEnd(node, idx + hitTerm.length);
      const sel = window.getSelection();
      sel.removeAllRanges();
      sel.addRange(range);
      const sp = range.getBoundingClientRect ? range.getClientRects()[0] : null;
      (node.parentElement || note).scrollIntoView({ block: 'center' });
      return;
    }
  }
}

/* ===================== 에디터 ===================== */

function renderEditor() {
  const t = data.todos.find(x => x.id === selectedId) || null;
  $('editorEmpty').hidden = !!t;
  $('editorBody').hidden = !t;
  hideTableBar();
  if (!t) return;

  // 다른 노트로 전환 시 이전 노트의 blob URL 해제 (메모리 누수 방지)
  if (t.id !== lastEditorNoteId) {
    revokeAllImageUrls();
    imgUrlCache.clear(); dataUrlRef.clear();
    cellSel = []; cellAnchor = null;  // 선택 상태 초기화(요소는 새 렌더로 사라짐)
    lastEditorNoteId = t.id;
  }

  $('edDone').checked = t.done;
  $('edTitle').value = t.title;
  $('edDate').value = t.date || '';

  const sel = $('edGroup');
  sel.innerHTML = '<option value="">미분류</option>' +
    data.groups.map(g => `<option value="${g.id}">${escapeText(g.name)}</option>`).join('');
  sel.value = t.groupId || '';

  const note = $('edNote');
  if (t.noteLoaded) {
    note.innerHTML = sanitizeHTML(t.note || '');
    refreshTodoLinks(note);
    rebindNoteImages();  // 재방문 시 revoke된 blob을 data-ref로 다시 연결
    if (view.type === 'search' && search.hlTerms.length) highlightInNote();
  } else {
    // 본문 지연 로딩 — 로드 후 (여전히 선택돼 있으면) 다시 그림
    note.innerHTML = '<p class="note-loading">불러오는 중…</p>';
    const id = t.id;
    loadNote(t).then(() => { if (selectedId === id) renderEditor(); });
  }
}

// 할일 링크 텍스트를 대상 할일의 현재 제목으로 갱신 (삭제됐으면 표시)
function refreshTodoLinks(note) {
  note.querySelectorAll('a[data-todo]').forEach(a => {
    const lt = data.todos.find(x => x.id === a.dataset.todo);
    a.textContent = lt ? (lt.title || '(제목 없음)') : '(삭제된 할 일)';
  });
}

// contenteditable가 비었으면(잔여 <br> 포함) placeholder가 다시 뜨도록 완전히 비움
function normalizeEmptyNote() {
  const n = $('edNote');
  if (n.querySelector('img, table, hr')) return;
  if (n.textContent.trim() === '') n.innerHTML = '';
}

const saveNote = debounce(() => {
  const t = data.todos.find(x => x.id === selectedId);
  if (!t || !t.noteLoaded) return;
  normalizeEmptyNote();
  const html = $('edNote').innerHTML;
  if (html === t.note) return;
  const hadNote = !!t.hasNote;
  // 노트 파일 + index.json 저장 (이미지는 파일로 분리)
  saveNoteBody(t.id).then(() => {
    if (hadNote !== !!t.hasNote) renderList(); // 📄 표시 변화 때만 목록 갱신
  });
}, 600);

const saveTitle = debounce(() => {
  const t = data.todos.find(x => x.id === selectedId);
  if (!t) return;
  t.title = $('edTitle').value.trim().slice(0, 300);
  t.updated = new Date().toISOString();
  persist();
  renderList();
}, 350);

function flushPendingEdits() {
  saveNote.flush();
  saveTitle.flush();
  if (saveIndexQueued.flush) saveIndexQueued.flush();
}

/* ---------- 링크 (할일 · 문서/웹) ---------- */

let linkRange = null; // 링크 모달 열 때의 캐럿 위치 저장

function openLinkDialog() {
  const sel = window.getSelection();
  linkRange = (sel.rangeCount && $('edNote').contains(sel.anchorNode))
    ? sel.getRangeAt(0).cloneRange() : null;
  const selText = sel && !sel.isCollapsed ? sel.toString() : '';

  const others = data.todos.filter(t => t.id !== selectedId);
  $('linkTodo').innerHTML = others.length
    ? others.map(t => `<option value="${t.id}">${escapeText(t.title || '(제목 없음)')}</option>`).join('')
    : '<option value="">(연결할 다른 할 일이 없어요)</option>';
  $('linkUrl').value = '';
  $('linkText').value = selText;
  document.querySelector('input[name=linkMode][value=todo]').checked = others.length > 0;
  document.querySelector('input[name=linkMode][value=url]').checked = others.length === 0;
  updateLinkMode();
  $('linkModal').hidden = false;
  (others.length ? $('linkTodo') : $('linkUrl')).focus();
}

function updateLinkMode() {
  const mode = document.querySelector('input[name=linkMode]:checked').value;
  $('linkTodoWrap').hidden = mode !== 'todo';
  $('linkUrlWrap').hidden = mode !== 'url';
}

// 입력 경로를 열 수 있는 URL로 정규화 (UNC·윈도우 경로 지원)
function normalizeLinkUrl(u) {
  u = u.trim();
  if (/^\\\\/.test(u)) return 'file:' + u.replace(/\\/g, '/');        // \\서버\공유 → file://서버/공유
  if (/^[a-zA-Z]:[\\/]/.test(u)) return 'file:///' + u.replace(/\\/g, '/'); // C:\... → file:///C:/...
  if (/^(https?|file|mailto):/i.test(u)) return u;
  if (/^www\./i.test(u)) return 'http://' + u;
  return u;
}

function insertLink() {
  const mode = document.querySelector('input[name=linkMode]:checked').value;
  let html;
  if (mode === 'todo') {
    const id = $('linkTodo').value;
    const t = data.todos.find(x => x.id === id);
    if (!t) { toast('연결할 할 일을 선택하세요', true); return; }
    html = `<a data-todo="${escapeAttr(id)}">${escapeText(t.title || '(제목 없음)')}</a>`;
  } else {
    const raw = $('linkUrl').value.trim();
    if (!raw) { toast('주소나 파일 경로를 입력하세요', true); return; }
    const url = normalizeLinkUrl(raw);
    const text = $('linkText').value.trim() || raw;
    html = `<a href="${escapeAttr(url)}">${escapeText(text)}</a>`;
  }
  $('linkModal').hidden = true;
  $('edNote').focus();
  if (linkRange) {
    const s = window.getSelection();
    s.removeAllRanges();
    s.addRange(linkRange);
  }
  // 링크 뒤에 공백을 넣어 이어지는 입력이 링크 안으로 들어가지 않게
  document.execCommand('insertHTML', false, sanitizeHTML(html) + ' ');
  saveNote();
}

function openExternal(href) {
  try {
    const w = window.open(href, '_blank');
    if (!w) toast('링크를 열지 못했어요 (팝업 차단?): ' + href, true);
  } catch (e) {
    toast('링크를 열지 못했어요: ' + href, true);
  }
}

// HTML+plain 두 형식으로 클립보드에 복사 (붙여넣기 위치에 맞게 브라우저가 선택)
async function copyRich(html, plain) {
  try {
    if (navigator.clipboard && window.ClipboardItem) {
      await navigator.clipboard.write([new ClipboardItem({
        'text/html': new Blob([html], { type: 'text/html' }),
        'text/plain': new Blob([plain], { type: 'text/plain' }),
      })]);
      return true;
    }
  } catch (e) { /* 아래 폴백 */ }
  try {
    const tmp = document.createElement('div');
    tmp.setAttribute('contenteditable', 'true');
    tmp.style.cssText = 'position:fixed;left:-9999px;top:0;opacity:0';
    tmp.innerHTML = html;
    document.body.appendChild(tmp);
    const sel = window.getSelection();
    const saved = sel.rangeCount ? sel.getRangeAt(0).cloneRange() : null;
    const r = document.createRange();
    r.selectNodeContents(tmp);
    sel.removeAllRanges();
    sel.addRange(r);
    const ok = document.execCommand('copy');
    sel.removeAllRanges();
    if (saved) sel.addRange(saved);
    tmp.remove();
    return ok;
  } catch (e) { return false; }
}

// 현재 할 일로 연결되는 링크를 복사
async function copyLinkFor(id) {
  const t = data.todos.find(x => x.id === id);
  if (!t) return;
  const title = t.title || '(제목 없음)';
  const html = `<a data-todo="${escapeAttr(t.id)}">${escapeText(title)}</a>`;
  const ok = await copyRich(html, title);
  toast(ok ? '링크 복사됨 — 다른 메모에 붙여넣으면 이 할 일로 연결돼요' : '복사하지 못했어요', !ok);
}
function copyCurrentLink() { return copyLinkFor(selectedId); }

/* ---------- 이미지 ---------- */

const IMG_MAX = 1200;       // 최대 변 (px)
const IMG_DIRECT = 300 * 1024; // 이 크기 이하면 변환 없이 그대로 내장
// GIF/WebP 등은 캔버스 변환 시 애니메이션·투명도가 깨지므로 원본 그대로 내장
const KEEP_ORIGINAL = /^image\/(gif|webp|svg\+xml)$/i;
const IMG_HARD_MAX = 6 * 1024 * 1024;

function insertImageFile(file) {
  if (!file || !file.type.startsWith('image/')) return;
  if (file.size > IMG_HARD_MAX) { toast('이미지가 너무 큽니다 (6MB 초과)', true); return; }
  if (file.size <= IMG_DIRECT || KEEP_ORIGINAL.test(file.type)) {
    const r = new FileReader();
    r.onload = () => insertImageData(r.result);
    r.onerror = () => toast('이미지를 읽지 못했습니다', true);
    r.readAsDataURL(file);
    return;
  }
  // 큰 png/jpeg는 축소해서 내장 (JSON 비대 방지)
  const img = new Image();
  const url = URL.createObjectURL(file);
  img.onload = () => {
    const scale = Math.min(1, IMG_MAX / Math.max(img.width, img.height));
    const c = document.createElement('canvas');
    c.width = Math.round(img.width * scale);
    c.height = Math.round(img.height * scale);
    c.getContext('2d').drawImage(img, 0, 0, c.width, c.height);
    const isPng = file.type === 'image/png';
    const dataUrl = isPng ? c.toDataURL('image/png') : c.toDataURL('image/jpeg', 0.85);
    URL.revokeObjectURL(url);
    insertImageData(dataUrl);
  };
  img.onerror = () => { URL.revokeObjectURL(url); toast('이미지를 읽지 못했습니다', true); };
  img.src = url;
}

// 비동기 디코드가 끝났을 때 선택이 바뀌었으면, 처음 대상 메모에 안전하게 덧붙인다
function insertImageData(dataUrl) {
  const targetId = imgTargetId;
  if (targetId && targetId === selectedId && document.activeElement === $('edNote')) {
    insertHTMLAtCaret(`<img src="${dataUrl}">`);
  } else if (targetId) {
    const t = data.todos.find(x => x.id === targetId);
    if (!t) { toast('이미지를 넣을 항목을 찾지 못했습니다', true); return; }
    if (!t.noteLoaded) { toast('이미지를 넣지 못했습니다 — 항목을 다시 열어 주세요', true); return; }
    const html = (t.note || '') + `<img src="${dataUrl}">`;
    // 노트 본문 파일까지 저장 (메타만 저장하면 이미지가 유실됨)
    writeNoteBody(t, html).then(() => {
      if (targetId === selectedId) $('edNote').innerHTML = sanitizeHTML(t.note);
      else toast('이미지가 원래 항목에 추가되었습니다');
      renderList();
    });
  }
}

function insertHTMLAtCaret(html) {
  $('edNote').focus();
  document.execCommand('insertHTML', false, sanitizeHTML(html));
  saveNote();
}

// 붙여넣은 HTML을 라이브 에디터에 넣기 전 방어:
// sanitize(외부 img 제거) 후 resolveImages로 images/ 상대참조를 blob으로 치환(파일 없으면 제거).
// resolveImages는 비활성 DOMParser를 쓰고 FSA로 로컬 파일만 읽으므로 서버 GET을 내지 않는다.
// → bare한 images/ 참조가 그대로 삽입돼 브라우저가 서버로 GET(404)하는 것을 막는다.
async function insertPastedHTML(html) {
  const targetId = selectedId;
  let safe;
  try { safe = await resolveImages(sanitizeHTML(html)); }
  catch (e) { return; } // 실패 시 삽입 안 함(안전) — 어차피 서버 GET은 없음
  if (selectedId !== targetId || document.activeElement !== $('edNote')) return; // 붙여넣기 도중 이탈
  document.execCommand('insertHTML', false, safe);
  saveNote();
}

/* ---------- 표 ---------- */

function insertTable() {
  const cell = '<td><br></td>'.repeat(3);
  const head = '<th><br></th>'.repeat(3);
  insertHTMLAtCaret(
    `<table><tbody><tr>${head}</tr><tr>${cell}</tr><tr>${cell}</tr></tbody></table><p><br></p>`);
}

function currentCell() {
  const sel = window.getSelection();
  if (!sel.rangeCount) return null;
  let node = sel.anchorNode;
  if (node && node.nodeType === Node.TEXT_NODE) node = node.parentElement;
  if (!node || !$('edNote').contains(node)) return null;
  return node.closest('td, th');
}

// 표를 그리드로 매핑 — colspan/rowspan을 반영해 각 (행,열) 슬롯이 어느 셀인지 기록
function buildGrid(table) {
  const grid = [];
  Array.from(table.rows).forEach((tr, r) => {
    if (!grid[r]) grid[r] = [];
    let c = 0;
    for (const cell of tr.cells) {
      while (grid[r][c]) c++; // 위쪽 rowspan이 차지한 칸 건너뛰기
      const cs = cell.colSpan || 1, rs = cell.rowSpan || 1;
      for (let dr = 0; dr < rs; dr++) {
        if (!grid[r + dr]) grid[r + dr] = [];
        for (let dc = 0; dc < cs; dc++) grid[r + dr][c + dc] = cell;
      }
      c += cs;
    }
  });
  return grid;
}
const gridCols = grid => grid.reduce((m, row) => Math.max(m, row.length), 0);

function cellPos(table, cell) {
  const grid = buildGrid(table);
  for (let r = 0; r < grid.length; r++) {
    for (let c = 0; c < (grid[r] || []).length; c++) {
      if (grid[r][c] === cell) {
        return { grid, r, c, rs: cell.rowSpan || 1, cs: cell.colSpan || 1 };
      }
    }
  }
  return null;
}

// 셀 내용을 to로 옮겨 붙임 (둘 다 내용이 있으면 줄바꿈으로 구분)
function moveCellContent(from, to) {
  const fromEmpty = from.textContent.trim() === '' && !from.querySelector('img, table');
  const toEmpty = to.textContent.trim() === '' && !to.querySelector('img, table');
  if (fromEmpty) return;
  if (toEmpty) to.innerHTML = '';
  else to.appendChild(document.createElement('br'));
  while (from.firstChild) to.appendChild(from.firstChild);
}

// 표 r행의 그리드 열 c 위치에 빈 셀 삽입
function insertCellAt(table, r, c) {
  const grid = buildGrid(table);
  const tr = table.rows[r];
  if (!tr) return;
  let ref = null;
  for (let cc = c; cc < (grid[r] || []).length; cc++) {
    if (grid[r][cc] && grid[r][cc].parentElement === tr) { ref = grid[r][cc]; break; }
  }
  const td = document.createElement('td');
  td.innerHTML = '<br>';
  if (ref) tr.insertBefore(td, ref); else tr.appendChild(td);
}

function tableOp(op) {
  // 병합은 드래그 선택으로 동작 (캐럿이 없어도 됨)
  if (op === 'merge') { mergeSelection(); clearCellSel(); hideTableBar(); saveNote(); return; }
  // 나머지는 현재 셀(캐럿) 또는 선택 앵커 기준
  const cell = currentCell() || cellSel[0] || null;
  if (!cell) return;
  const row = cell.closest('tr');
  const table = cell.closest('table');
  const pos = cellPos(table, cell);
  if (!pos) return;
  const cols = gridCols(pos.grid);

  if (op === 'rowAdd') {
    const nr = document.createElement('tr');
    for (let i = 0; i < cols; i++) nr.insertAdjacentHTML('beforeend', '<td><br></td>');
    row.after(nr);

  } else if (op === 'colAdd') {
    // 현재 셀 오른쪽에 한 열 추가 (병합 셀은 넓혀서 유지)
    const at = pos.c + pos.cs; // 새 열의 그리드 위치
    const seen = new Set();
    for (let r = 0; r < table.rows.length; r++) {
      const occ = pos.grid[r] && pos.grid[r][at - 1];      // at 왼쪽 칸을 차지한 셀
      const rightOcc = pos.grid[r] && pos.grid[r][at];
      if (occ && occ === rightOcc) {                        // 이 열 경계를 가로지르는 병합 셀 → 넓힘
        if (!seen.has(occ)) { occ.colSpan = (occ.colSpan || 1) + 1; seen.add(occ); }
      } else {
        insertCellAt(table, r, at);
      }
    }

  } else if (op === 'rowDel') {
    if (table.rows.length <= 1) { table.remove(); }
    else {
      // 이 행을 지나는 rowspan은 줄이고, 이 행에서 시작한 병합은 다음 행으로 내림
      for (let c = 0; c < cols; c++) {
        const occ = pos.grid[pos.r][c];
        if (!occ) continue;
        const op2 = cellPos(table, occ);
        if (op2.r < pos.r) { occ.rowSpan = (occ.rowSpan || 1) - 1; }
        else if (op2.rs > 1 && table.rows[pos.r + 1]) {
          // 다음 행 같은 위치에 남은 병합 잔여를 셀로 복원
          const rem = op2.rs - 1;
          const nc = document.createElement(occ.tagName.toLowerCase());
          nc.innerHTML = '<br>';
          if (op2.cs > 1) nc.colSpan = op2.cs;
          if (rem > 1) nc.rowSpan = rem;
          insertCellReplacing(table, pos.r + 1, c, nc);
          c += op2.cs - 1;
        }
      }
      row.remove();
    }

  } else if (op === 'colDel') {
    if (cols <= 1) { table.remove(); }
    else {
      const c = pos.c;
      const handled = new Set();
      for (let r = 0; r < table.rows.length; r++) {
        const occ = pos.grid[r] && pos.grid[r][c];
        if (!occ || handled.has(occ)) continue;
        handled.add(occ);
        if ((occ.colSpan || 1) > 1) occ.colSpan -= 1;   // 병합 셀은 폭만 줄임
        else if (occ.parentElement) occ.remove();        // 단일 셀은 제거
      }
    }

  } else if (op === 'merge') {
    mergeSelection();

  } else if (op === 'split') {
    if (pos.rs === 1 && pos.cs === 1) { toast('병합된 셀이 아니에요'); hideTableBar(); return; }
    cell.rowSpan = 1; cell.colSpan = 1;
    for (let dr = 0; dr < pos.rs; dr++) {
      for (let dc = 0; dc < pos.cs; dc++) {
        if (dr === 0 && dc === 0) continue;
        insertCellAt(table, pos.r + dr, pos.c + dc);
      }
    }

  } else if (op === 'tblDel') {
    table.remove();
  }
  clearCellSel();
  hideTableBar();
  saveNote();
}

/* ---- 셀 드래그 다중 선택 · 영역 병합 · 배경색 ---- */
let cellSel = [], cellAnchor = null, cellDragging = false;
const HL_CLASSES = ['hl-yellow', 'hl-green', 'hl-blue', 'hl-pink', 'hl-gray'];

function clearCellSel() {
  for (const c of cellSel) c.classList.remove('cell-sel');
  cellSel = []; cellAnchor = null;
}

// 두 셀의 그리드 바운딩 박스
function gridBox(table, cells) {
  let r0 = Infinity, r1 = -1, c0 = Infinity, c1 = -1;
  for (const cl of cells) {
    const p = cellPos(table, cl); if (!p) continue;
    r0 = Math.min(r0, p.r); c0 = Math.min(c0, p.c);
    r1 = Math.max(r1, p.r + p.rs - 1); c1 = Math.max(c1, p.c + p.cs - 1);
  }
  return { r0, r1, c0, c1 };
}

function setRectSel(anchor, cur) {
  const table = anchor.closest('table');
  if (!table || cur.closest('table') !== table) return;
  const box = gridBox(table, [anchor, cur]);
  const grid = buildGrid(table);
  const set = new Set();
  for (let r = box.r0; r <= box.r1; r++)
    for (let c = box.c0; c <= box.c1; c++) { const cl = grid[r] && grid[r][c]; if (cl) set.add(cl); }
  for (const c of cellSel) c.classList.remove('cell-sel');
  cellSel = [...set];
  for (const c of cellSel) c.classList.add('cell-sel');
}

// 선택 영역(또는 현재 셀)에 배경색 적용
function applyHighlight(hl) {
  const cells = cellSel.length ? cellSel.slice() : (currentCell() ? [currentCell()] : []);
  if (!cells.length) return;
  for (const cl of cells) {
    cl.classList.remove(...HL_CLASSES);
    if (hl) cl.classList.add('hl-' + hl);
  }
  saveNote();
}

// 선택한 직사각형 영역 병합
function mergeSelection() {
  const cells = cellSel.length >= 2 ? cellSel.slice() : [];
  if (cells.length < 2) { toast('여러 셀을 드래그해서 선택한 뒤 병합하세요'); return; }
  const table = cells[0].closest('table');
  const box = gridBox(table, cells);
  const grid = buildGrid(table);
  const inBox = new Set();
  for (let r = box.r0; r <= box.r1; r++)
    for (let c = box.c0; c <= box.c1; c++) { const cl = grid[r] && grid[r][c]; if (cl) inBox.add(cl); }
  // 직사각형 검증: 모든 셀이 박스 안에 완전히 들어와야
  for (const cl of inBox) {
    const p = cellPos(table, cl);
    if (p.r < box.r0 || p.c < box.c0 || p.r + p.rs - 1 > box.r1 || p.c + p.cs - 1 > box.c1) {
      toast('직사각형 형태로 선택해 주세요'); return;
    }
  }
  let top = null, topP = null;
  for (const cl of inBox) {
    const p = cellPos(table, cl);
    if (!topP || p.r < topP.r || (p.r === topP.r && p.c < topP.c)) { top = cl; topP = p; }
  }
  for (const cl of inBox) if (cl !== top) moveCellContent(cl, top);
  for (const cl of inBox) if (cl !== top && cl.parentElement) cl.remove();
  top.colSpan = box.c1 - box.c0 + 1;
  top.rowSpan = box.r1 - box.r0 + 1;
}

// r행 그리드 열 c 위치에 특정 셀을 삽입 (rowDel 병합 복원용)
function insertCellReplacing(table, r, c, newCell) {
  const grid = buildGrid(table);
  const tr = table.rows[r];
  if (!tr) return;
  let ref = null;
  for (let cc = c; cc < (grid[r] || []).length; cc++) {
    if (grid[r][cc] && grid[r][cc].parentElement === tr) { ref = grid[r][cc]; break; }
  }
  if (ref) tr.insertBefore(newCell, ref); else tr.appendChild(newCell);
}

function updateTableBar() {
  const cell = currentCell() || (cellSel.length ? cellSel[0] : null);
  const bar = $('tableBar');
  if (!cell) { bar.hidden = true; return; }
  const table = cell.closest('table');
  if (!table) { bar.hidden = true; return; }
  const pane = $('editorPane').getBoundingClientRect();
  const rect = table.getBoundingClientRect();
  bar.hidden = false;
  bar.style.left = Math.max(8, rect.left - pane.left) + 'px';
  bar.style.top = Math.max(4, rect.top - pane.top - 34) + 'px';
}

function hideTableBar() { $('tableBar').hidden = true; }

/* ===================== 할일 · 그룹 조작 ===================== */

function addTodo(title) {
  const t = {
    id: uid(),
    title: title.trim().slice(0, 300),
    done: false,
    groupId: view.type === 'group' ? view.groupId : null,
    date: (view.type === 'today' || view.type === 'week' || view.type === 'month') ? todayKey() : null,
    note: '', noteLoaded: true, hasNote: false,
    created: new Date().toISOString(),
    updated: new Date().toISOString(),
  };
  if (!t.title) return;
  flushPendingEdits(); // 편집 중이던 메모를 먼저 저장 (재렌더로 유실 방지)
  data.todos.push(t);
  persist();
  selectedId = t.id;
  renderAll();
}

function toggleDone(id) {
  flushPendingEdits(); // 다른 항목 편집 중 체크 시 편집 내용 보존
  const t = data.todos.find(x => x.id === id);
  if (!t) return;
  t.done = !t.done;
  t.updated = new Date().toISOString();
  persist();
  renderAll();
}

function deleteTodo(id) {
  const t = data.todos.find(x => x.id === id);
  if (!t) return;
  confirmBox(`"${t.title || '(제목 없음)'}" 할 일을 삭제할까요?\n메모 내용도 함께 삭제됩니다.`, () => {
    const hadNote = t.hasNote;
    data.todos = data.todos.filter(x => x.id !== id);
    if (selectedId === id) selectedId = null;
    // 히스토리·최근 목록에서 삭제된 메모 제거 (navPos는 현재 위치 유지하도록 보정)
    const keptBefore = navHist.slice(0, navPos + 1).filter(x => x !== id).length;
    navHist = navHist.filter(x => x !== id);
    navPos = Math.min(keptBefore - 1, navHist.length - 1);
    recentIds = recentIds.filter(x => x !== id);
    searchCache.delete(id);
    deleteNoteFile(id, hadNote);
    persist();
    renderAll();
    toast('삭제되었습니다');
  }, '삭제');
}

function selectTodo(id, viaHistory) {
  if (selectedId === id) return;
  flushPendingEdits();
  selectedId = id;
  markVisited(id, viaHistory);
  renderAll();
}

// 메모 방문 기록: 최근 목록 갱신 + (뒤로/앞으로가 아닌 실제 이동이면) 히스토리에 push
function markVisited(id, viaHistory) {
  recentIds = [id, ...recentIds.filter(x => x !== id)].slice(0, RECENT_MAX);
  if (!viaHistory && navHist[navPos] !== id) {
    navHist = navHist.slice(0, navPos + 1); // 앞으로 기록은 잘라내고
    navHist.push(id);
    navPos = navHist.length - 1;
  }
}

function navBack() {
  if (navPos <= 0) return;
  navPos--;
  selectTodo(navHist[navPos], true);
}
function navForward() {
  if (navPos >= navHist.length - 1) return;
  navPos++;
  selectTodo(navHist[navPos], true);
}

function renderNavButtons() {
  const b = $('navBack'), f = $('navFwd');
  if (b) b.disabled = navPos <= 0;
  if (f) f.disabled = navPos >= navHist.length - 1;
}

// 사이드바 "최근 본 메모" 목록 (삭제된 메모는 제외, 비어있으면 섹션 숨김)
function renderRecent() {
  const sec = document.querySelector('.nav-section[data-section="recent"]');
  const wrap = $('recentList');
  if (!sec || !wrap) return;
  const items = recentIds.map(id => data.todos.find(t => t.id === id)).filter(Boolean);
  sec.hidden = items.length === 0;
  wrap.innerHTML = '';
  for (const t of items) {
    const g = groupOf(t.groupId);
    const btn = document.createElement('button');
    btn.type = 'button';
    btn.className = 'nav-item recent-item' + (t.id === selectedId ? ' active' : '');
    btn.dataset.recent = t.id;
    btn.innerHTML =
      (g ? `<span class="group-dot" style="background:${g.color}"></span>`
         : `<span class="nav-ico">▪</span>`) +
      `<span class="g-name"></span>`;
    btn.querySelector('.g-name').textContent = t.title || '(제목 없음)';
    wrap.appendChild(btn);
  }
}

function addGroupInline() {
  const btn = $('btnAddGroup');
  const input = document.createElement('input');
  input.className = 'group-input';
  input.placeholder = '그룹 이름';
  input.maxLength = 40;
  btn.replaceWith(input);
  input.focus();
  const finish = save => {
    const name = input.value.trim();
    input.replaceWith(btn);
    if (save && name) {
      data.groups.push({
        id: uid(), name,
        color: GROUP_COLORS[data.groups.length % GROUP_COLORS.length],
      });
      persist();
      renderSidebar();
    }
  };
  input.addEventListener('keydown', e => {
    if (e.key === 'Enter') finish(true);
    if (e.key === 'Escape') finish(false);
  });
  input.addEventListener('blur', () => finish(true));
}

// 그룹 이름 인라인 편집 — 그룹 버튼을 입력창으로 치환(중첩 버튼 회피)
function renameGroupInline(item) {
  const id = item.dataset.group;
  const g = groupOf(id);
  if (!g) return;
  const input = document.createElement('input');
  input.className = 'group-input';
  input.maxLength = 40;
  input.value = g.name;
  item.replaceWith(input);
  input.focus();
  input.select();
  let done = false;
  const finish = save => {
    if (done) return;
    done = true;
    const name = input.value.trim().slice(0, 40);
    if (save && name && name !== g.name) {
      g.name = name;
      persist();
      afterGroupRename(id);
    } else {
      renderSidebar(); // 취소/무변경 → 원래 목록 복원
    }
  };
  input.addEventListener('keydown', e => {
    if (e.key === 'Enter') { e.preventDefault(); finish(true); }
    else if (e.key === 'Escape') { e.preventDefault(); finish(false); }
  });
  input.addEventListener('blur', () => finish(true));
}

// 그룹 이름이 쓰이는 모든 곳 갱신 (노트 본문은 건드리지 않음)
function afterGroupRename(id) {
  const g = groupOf(id);
  renderSidebar();                 // 사이드바 그룹 이름
  renderList();                    // 할일 행의 그룹 뱃지 + (그 그룹 보기 중이면) 헤더
  const sel = $('edGroup');        // 에디터 그룹 드롭다운 옵션 이름
  if (sel && g) {
    const opt = Array.from(sel.options).find(o => o.value === id);
    if (opt) opt.textContent = g.name;
  }
}

function deleteGroup(id) {
  const g = groupOf(id);
  if (!g) return;
  const n = data.todos.filter(t => t.groupId === id).length;
  confirmBox(
    `"${g.name}" 그룹을 삭제할까요?` + (n ? `\n포함된 할 일 ${n}개는 미분류로 이동합니다.` : ''),
    () => {
      flushPendingEdits();
      data.groups = data.groups.filter(x => x.id !== id);
      data.todos.forEach(t => { if (t.groupId === id) t.groupId = null; });
      if (view.type === 'group' && view.groupId === id) view = { type: 'today', groupId: null };
      persist();
      renderAll();
    }, '삭제');
}

/* ===================== 모달 · 토스트 ===================== */

let confirmAction = null;
let cancelAction = null;

function confirmBox(msg, onOk, okLabel, onCancel) {
  $('confirmMsg').textContent = msg;
  $('confirmOk').textContent = okLabel || '확인';
  confirmAction = onOk;
  cancelAction = onCancel || null;
  $('confirmModal').hidden = false;
  $('confirmOk').focus();
}

function toast(msg, isError) {
  const wrap = $('toastWrap');
  const el = document.createElement('div');
  el.className = 'toast' + (isError ? ' error' : '');
  el.textContent = msg;
  wrap.appendChild(el);
  setTimeout(() => el.classList.add('gone'), 2400);
  setTimeout(() => el.remove(), 3000);
}

/* ---------- 우클릭 컨텍스트 메뉴 ---------- */
let ctxTargetId = null;
function showCtxMenu(x, y, id) {
  ctxTargetId = id;
  const m = $('ctxMenu');
  m.hidden = false;
  const mw = m.offsetWidth, mh = m.offsetHeight;
  m.style.left = Math.min(x, window.innerWidth - mw - 6) + 'px';
  m.style.top = Math.min(y, window.innerHeight - mh - 6) + 'px';
}
function hideCtxMenu() { $('ctxMenu').hidden = true; ctxTargetId = null; }

/* ============ 사이드바 섹션 접기 ============ */

function applyNavCollapsed(sec, collapsed) {
  sec.classList.toggle('collapsed', collapsed);
  const btn = sec.querySelector('.sep-toggle');
  if (btn) btn.setAttribute('aria-expanded', String(!collapsed));
}

function loadNavCollapsed() {
  let saved = {};
  try { saved = JSON.parse(localStorage.getItem('navCollapsed') || '{}') || {}; } catch (e) {}
  document.querySelectorAll('.nav-section[data-section]').forEach(sec => {
    const k = sec.dataset.section;
    // 저장값 우선, 없으면 기본값(상태별 분류만 접힘)
    const collapsed = (k in saved) ? !!saved[k] : (k === 'status');
    applyNavCollapsed(sec, collapsed);
  });
}

function saveNavCollapsed() {
  const out = {};
  document.querySelectorAll('.nav-section[data-section]').forEach(sec => {
    out[sec.dataset.section] = sec.classList.contains('collapsed');
  });
  try { localStorage.setItem('navCollapsed', JSON.stringify(out)); } catch (e) {}
}

/* ===================== 이벤트 ===================== */

function bindEvents() {
  // 사이드바
  document.querySelectorAll('.nav-item[data-view]').forEach(el =>
    el.addEventListener('click', () => {
      flushPendingEdits();
      if (view.type === 'search') { $('searchInput').value = ''; search.q = ''; $('searchClear').hidden = true; prevView = null; }
      view = { type: el.dataset.view, groupId: null };
      doneOpen = false;
      renderAll();
    }));

  $('groupList').addEventListener('click', e => {
    const editBtn = e.target.closest('.g-edit');
    const del = e.target.closest('.g-del');
    const item = e.target.closest('.nav-item[data-group]');
    if (!item) return;
    if (editBtn) { renameGroupInline(item); return; }
    if (del) { deleteGroup(item.dataset.group); return; }
    flushPendingEdits();
    view = { type: 'group', groupId: item.dataset.group };
    doneOpen = false;
    renderAll();
  });

  $('btnAddGroup').addEventListener('click', addGroupInline);

  // 섹션 헤더 클릭 → 접기/펼치기 (상태는 이 기기에만 저장)
  document.querySelectorAll('.nav-section .sep-toggle').forEach(btn =>
    btn.addEventListener('click', () => {
      const sec = btn.closest('.nav-section');
      applyNavCollapsed(sec, !sec.classList.contains('collapsed'));
      saveNavCollapsed();
    }));

  // 최근 본 메모 클릭 → 이동
  $('recentList').addEventListener('click', e => {
    const item = e.target.closest('.recent-item[data-recent]');
    if (item) selectTodo(item.dataset.recent);
  });

  // 뒤로/앞으로 (에디터 상단 버튼)
  $('navBack').addEventListener('click', navBack);
  $('navFwd').addEventListener('click', navForward);
  // Alt+←/→ 로도 이동 (갈 곳이 있을 때만 기본 동작 가로챔)
  document.addEventListener('keydown', e => {
    if (!e.altKey || e.ctrlKey || e.metaKey || e.shiftKey) return;
    if (e.key === 'ArrowLeft' && navPos > 0) { e.preventDefault(); navBack(); }
    else if (e.key === 'ArrowRight' && navPos < navHist.length - 1) { e.preventDefault(); navForward(); }
  });

  // 상단 제목 클릭 → 이름 설정
  $('brandTitle').addEventListener('click', editBrandName);

  // 리스트/에디터 크기 조절 (핸들 드래그) — 폭은 이 기기에만 저장
  try { const w = localStorage.getItem('editorW'); if (w) document.documentElement.style.setProperty('--editor-w', w); } catch (e) {}
  let resizing = false;
  $('paneResizer').addEventListener('pointerdown', e => {
    resizing = true;
    document.body.classList.add('resizing');
    $('paneResizer').setPointerCapture(e.pointerId);
  });
  $('paneResizer').addEventListener('pointermove', e => {
    if (!resizing) return;
    const w = Math.max(360, Math.min(window.innerWidth - 560, window.innerWidth - e.clientX));
    document.documentElement.style.setProperty('--editor-w', w + 'px');
  });
  $('paneResizer').addEventListener('pointerup', e => {
    if (!resizing) return;
    resizing = false;
    document.body.classList.remove('resizing');
    try { localStorage.setItem('editorW', getComputedStyle(document.documentElement).getPropertyValue('--editor-w').trim()); } catch (e2) {}
    updateTableBar();
  });

  // 명시적 저장 버튼 + Ctrl/Cmd+S
  $('btnSave').addEventListener('click', saveNow);
  document.addEventListener('keydown', e => {
    if ((e.ctrlKey || e.metaKey) && (e.key === 's' || e.key === 'S')) { e.preventDefault(); saveNow(); }
  });

  // 우클릭 컨텍스트 메뉴 (할일 행·달력칩·검색결과). 에디터 안은 네이티브 메뉴(붙여넣기) 유지
  document.addEventListener('contextmenu', e => {
    if (e.target.closest('#editorBody')) { hideCtxMenu(); return; }
    const el = e.target.closest('.todo-row[data-id], .cal-chip[data-id]');
    const id = el && el.dataset.id;
    if (!id) { hideCtxMenu(); return; }
    e.preventDefault();
    showCtxMenu(e.clientX, e.clientY, id);
  });
  $('ctxMenu').addEventListener('click', e => {
    const btn = e.target.closest('button[data-act]');
    if (!btn) return;
    const id = ctxTargetId;
    hideCtxMenu();
    if (btn.dataset.act === 'copyLink') copyLinkFor(id);
    else if (btn.dataset.act === 'delete') deleteTodo(id);
  });
  document.addEventListener('pointerdown', e => {
    if (!$('ctxMenu').hidden && !e.target.closest('#ctxMenu')) hideCtxMenu();
  });
  window.addEventListener('blur', hideCtxMenu);
  document.addEventListener('keydown', e => { if (e.key === 'Escape') hideCtxMenu(); });
  document.addEventListener('scroll', hideCtxMenu, true);

  // 빠른 추가
  $('quickInput').addEventListener('keydown', e => {
    if (e.key === 'Enter' && !e.isComposing) {
      addTodo(e.target.value);
      e.target.value = '';
    }
  });

  // 리스트
  $('todoList').addEventListener('click', e => {
    // 검색 뷰 상호작용
    if (view.type === 'search') {
      if (e.target.closest('#searchMore')) { search.page++; renderSearch(); return; }
      const row = e.target.closest('.todo-row');
      if (!row) return;
      if (e.target.closest('.todo-check')) { toggleDone(row.dataset.id); return; }
      selectTodo(row.dataset.id);
      highlightInNote(); // 본문 매칭 위치로 스크롤·강조
      return;
    }
    // 달력 뷰 상호작용
    if (view.type === 'calendar') {
      const nav = e.target.closest('[data-cal]');
      if (nav) {
        const a = nav.dataset.cal;
        if (a === 'prev') moveCalMonth(-1);
        else if (a === 'next') moveCalMonth(1);
        else { calY = new Date().getFullYear(); calM = new Date().getMonth(); renderCalendar(); }
        return;
      }
      const add = e.target.closest('[data-add]');
      if (add) { addTodoOnDate(add.dataset.add); return; }
      const chip = e.target.closest('.cal-chip');
      if (chip) { selectTodo(chip.dataset.id); return; }
      const cell = e.target.closest('.cal-cell:not(.empty)');
      if (cell) { addTodoOnDate(cell.dataset.day); return; } // 빈 칸 클릭 → 그 날 추가
      return;
    }
    const row = e.target.closest('.todo-row');
    if (!row) return;
    if (e.target.closest('.todo-check')) { toggleDone(row.dataset.id); return; }
    if (e.target.closest('.row-del')) { deleteTodo(row.dataset.id); return; }
    selectTodo(row.dataset.id);
  });
  // 키보드: Enter=열기, Space=완료 토글
  $('todoList').addEventListener('keydown', e => {
    const row = e.target.closest('.todo-row');
    if (!row) return;
    if (e.key === 'Enter') {
      e.preventDefault(); selectTodo(row.dataset.id);
      if (view.type === 'search') highlightInNote();
    } else if (e.key === ' ') { e.preventDefault(); toggleDone(row.dataset.id); }
  });

  // 검색 결과 필터(그룹/완료) — 위임
  $('todoList').addEventListener('change', e => {
    if (e.target.id === 'sfGroup') { search.group = e.target.value; rerunSearch(); }
    else if (e.target.id === 'sfDone') { search.includeDone = e.target.checked; rerunSearch(); }
  });

  // 검색바
  $('searchInput').addEventListener('input', e => {
    search.q = e.target.value;
    $('searchClear').hidden = !search.q;
    if (search.q.trim()) { enterSearch(); doSearch(); }
    else if (view.type === 'search') { renderSearch(); } // 빈 검색어: 안내만
  });
  $('searchInput').addEventListener('keydown', e => {
    if (e.key === 'Escape') { e.preventDefault(); exitSearch(); $('searchInput').blur(); }
  });
  $('searchScope').addEventListener('change', e => {
    search.scope = e.target.value;
    if (view.type === 'search') rerunSearch();
  });
  $('searchClear').addEventListener('click', () => { exitSearch(); $('searchInput').focus(); });
  document.addEventListener('keydown', e => {
    if ((e.ctrlKey || e.metaKey) && e.key === 'f') { e.preventDefault(); $('searchInput').focus(); $('searchInput').select(); }
  });

  // 에디터 메타
  $('edDone').addEventListener('change', () => {
    const t = data.todos.find(x => x.id === selectedId);
    if (!t) return;
    t.done = $('edDone').checked;
    t.updated = new Date().toISOString();
    persist();
    renderSidebar();
    renderList();
  });
  $('edTitle').addEventListener('input', () => { dirty = true; saveTitle(); });
  $('edDate').addEventListener('change', () => {
    const t = data.todos.find(x => x.id === selectedId);
    if (!t) return;
    t.date = validDateKey($('edDate').value) ? $('edDate').value : null;
    t.updated = new Date().toISOString();
    persist();
    renderSidebar();
    renderList();
  });
  $('edGroup').addEventListener('change', () => {
    const t = data.todos.find(x => x.id === selectedId);
    if (!t) return;
    t.groupId = $('edGroup').value || null;
    t.updated = new Date().toISOString();
    persist();
    renderSidebar();
    renderList();
  });
  $('edDelete').addEventListener('click', () => deleteTodo(selectedId));
  $('edCopyLink').addEventListener('click', copyCurrentLink);

  // 툴바
  $('edToolbar').addEventListener('click', e => {
    const btn = e.target.closest('button[data-cmd]');
    if (!btn) return;
    const cmd = btn.dataset.cmd;
    if (cmd === 'link') { openLinkDialog(); return; } // 선택 영역을 잃지 않도록 focus 전에
    $('edNote').focus();
    if (cmd === 'table') insertTable();
    else if (cmd === 'image') $('imgFile').click();
    else if (cmd === 'h') {
      const block = document.queryCommandValue('formatBlock');
      document.execCommand('formatBlock', false, /h3/i.test(block) ? '<p>' : '<h3>');
      saveNote();
    } else {
      document.execCommand(cmd, false, null);
      saveNote();
    }
  });

  $('imgFile').addEventListener('change', e => {
    imgTargetId = selectedId;
    for (const f of e.target.files) insertImageFile(f);
    e.target.value = '';
  });

  // 에디터 본문
  const note = $('edNote');
  note.addEventListener('input', () => { dirty = true; clearCellSel(); saveNote(); });
  note.addEventListener('blur', () => { if (dirty) flushPendingEdits(); });

  note.addEventListener('paste', e => {
    imgTargetId = selectedId;
    const html = e.clipboardData.getData('text/html');
    // 엑셀/HWP는 표 HTML과 셀 비트맵을 함께 넣음 → 표가 있으면 표를 우선
    if (html && /<table[\s>]/i.test(html)) {
      e.preventDefault();
      insertPastedHTML(html);
      return;
    }
    const items = Array.from(e.clipboardData.items || []);
    const imgs = items.filter(it => it.type.startsWith('image/'));
    if (imgs.length > 0) {
      e.preventDefault();
      imgs.forEach(it => insertImageFile(it.getAsFile()));
      return;
    }
    if (html) {
      e.preventDefault();
      insertPastedHTML(html);
    }
    // 일반 텍스트는 기본 동작
  });

  note.addEventListener('drop', e => {
    e.preventDefault(); // 어떤 파일이든 브라우저가 페이지를 벗어나지 않도록
    imgTargetId = selectedId;
    const files = Array.from(e.dataTransfer.files || []);
    const imgs = files.filter(f => f.type.startsWith('image/'));
    if (imgs.length > 0) imgs.forEach(insertImageFile);
    else if (files.length > 0) toast('이미지 파일만 첨부할 수 있어요', true);
  });
  note.addEventListener('dragover', e => {
    if (Array.from(e.dataTransfer.items || []).some(it => it.kind === 'file')) e.preventDefault();
  });

  // 이미지 클릭 선택 → Delete로 삭제
  note.addEventListener('click', e => {
    // 링크 클릭 → 할일 이동 / 문서·웹 열기 (편집하려면 Alt+클릭)
    const a = e.target.closest('a');
    if (a && note.contains(a) && !e.altKey) {
      const tid = a.dataset.todo;
      if (tid) {
        e.preventDefault();
        data.todos.some(x => x.id === tid) ? selectTodo(tid) : toast('삭제된 할 일이에요', true);
        return;
      }
      const href = a.getAttribute('href');
      if (href) { e.preventDefault(); openExternal(href); return; }
    }
    note.querySelectorAll('img.img-selected').forEach(i => i.classList.remove('img-selected'));
    if (e.target.tagName === 'IMG') {
      e.target.classList.add('img-selected');
      const r = document.createRange();
      r.selectNode(e.target);
      const sel = window.getSelection();
      sel.removeAllRanges();
      sel.addRange(r);
    }
  });
  note.addEventListener('keydown', e => {
    if ((e.key === 'Delete' || e.key === 'Backspace')) {
      // 클릭으로 선택된 이미지가 있고, 현재 선택이 실제로 그 이미지일 때만 삭제
      const img = note.querySelector('img.img-selected');
      const sel = window.getSelection();
      const onImg = img && sel.rangeCount &&
        (sel.getRangeAt(0).commonAncestorContainer === img ||
         (sel.anchorNode && (sel.anchorNode === img || sel.anchorNode.contains?.(img))));
      if (img && onImg) { e.preventDefault(); img.remove(); saveNote(); return; }
      if (img) img.classList.remove('img-selected'); // 캐럿이 이미지 밖 → 선택 해제 후 기본 동작
    } else if (!e.key.startsWith('Arrow') && !e.shiftKey && !e.ctrlKey && !e.metaKey) {
      note.querySelectorAll('img.img-selected').forEach(i => i.classList.remove('img-selected'));
    }
    if (e.key === 'Tab' && currentCell()) {
      // 표 안에서 Tab으로 셀 이동은 브라우저 기본에 맡기지 않고 들여쓰기 방지만
      e.preventDefault();
      const cell = currentCell();
      const cells = Array.from(cell.closest('table').querySelectorAll('td, th'));
      const i = cells.indexOf(cell);
      const next = cells[e.shiftKey ? i - 1 : i + 1];
      if (next) {
        const r = document.createRange();
        r.selectNodeContents(next);
        r.collapse(true);
        const sel = window.getSelection();
        sel.removeAllRanges();
        sel.addRange(r);
      }
    }
  });

  // 표 플로팅 바 + 이미지 선택 정리
  document.addEventListener('selectionchange', () => {
    if ($('editorBody').hidden) return;
    updateTableBar();
    // 캐럿이 선택된 이미지 밖으로 이동하면(방향키 등) 선택 해제
    const img = note.querySelector('img.img-selected');
    if (img) {
      const sel = window.getSelection();
      const stillOn = sel.rangeCount &&
        (sel.getRangeAt(0).commonAncestorContainer === img ||
         (sel.anchorNode === img));
      if (!stillOn) img.classList.remove('img-selected');
    }
  });
  note.addEventListener('scroll', updateTableBar);
  $('tableBar').addEventListener('click', e => {
    const hl = e.target.closest('button[data-hl]');
    if (hl) { applyHighlight(hl.dataset.hl); return; }
    const btn = e.target.closest('button[data-t]');
    if (btn) tableOp(btn.dataset.t);
  });
  // 팔레트 클릭이 편집기 포커스를 뺏겨 선택이 풀리지 않게
  $('tableBar').addEventListener('mousedown', e => e.preventDefault());

  // 셀 드래그 다중 선택
  note.addEventListener('mousedown', e => {
    const cell = e.target.closest('td, th');
    if (cell && note.contains(cell)) {
      cellAnchor = cell; cellDragging = true;
      clearCellSel(); cellAnchor = cell;
    } else if (!e.target.closest('#tableBar')) {
      clearCellSel();
    }
  });
  note.addEventListener('mousemove', e => {
    if (!cellDragging || !cellAnchor) return;
    const cur = e.target.closest('td, th');
    if (!cur || cur.closest('table') !== cellAnchor.closest('table')) return;
    if (cur !== cellAnchor || cellSel.length) {
      setRectSel(cellAnchor, cur);
      if (cellSel.length > 1) { e.preventDefault(); window.getSelection().removeAllRanges(); }
    }
  });
  document.addEventListener('mouseup', () => {
    if (!cellDragging) return;
    cellDragging = false;
    if (cellSel.length <= 1) clearCellSel();
    else updateTableBar();
  });

  // 폴더 연결/변경
  $('btnFile').addEventListener('click', () => { if (FS_API) pickFolder(); });
  $('gateBtn').addEventListener('click', pickFolder);

  // 링크 모달
  document.querySelectorAll('input[name=linkMode]').forEach(r =>
    r.addEventListener('change', updateLinkMode));
  $('linkInsert').addEventListener('click', insertLink);
  $('linkCancel').addEventListener('click', () => { $('linkModal').hidden = true; });
  $('linkModal').addEventListener('mousedown', e => {
    if (e.target === $('linkModal')) $('linkModal').hidden = true;
  });
  $('linkUrl').addEventListener('keydown', e => { if (e.key === 'Enter') insertLink(); });
  document.addEventListener('keydown', e => {
    if (e.key === 'Escape' && !$('linkModal').hidden) $('linkModal').hidden = true;
  });

  // 확인 모달
  const runCancel = () => {
    const fn = cancelAction; confirmAction = null; cancelAction = null;
    $('confirmModal').hidden = true;
    if (fn) fn();
  };
  $('confirmOk').addEventListener('click', () => {
    $('confirmModal').hidden = true;
    const fn = confirmAction; confirmAction = null; cancelAction = null;
    if (fn) fn();
  });
  $('confirmCancel').addEventListener('click', runCancel);
  $('confirmModal').addEventListener('mousedown', e => {
    if (e.target === $('confirmModal')) runCancel();
  });
  document.addEventListener('keydown', e => {
    if (e.key === 'Escape' && !$('confirmModal').hidden) runCancel();
  });

  // 창이 숨겨질 때(전환·닫기 직전) 미저장 내용 저장 — 백그라운드 전환은 페이지가 살아있어 완료됨
  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'hidden') flushPendingEdits();
  });
  // 창을 닫을 때: 저장(비동기)을 시작하되, 아직 미저장분이 있으면 경고 대화상자로 완료 시간 확보
  window.addEventListener('beforeunload', e => {
    flushPendingEdits();
    if (dirty) { e.preventDefault(); e.returnValue = ''; }
  });

  // 다른 탭/창에서 저장하면 알림 받아 최신 내용으로 갱신 (편집 중이 아닐 때만)
  if ('BroadcastChannel' in window) {
    bc = new BroadcastChannel('todomemo');
    bc.onmessage = e => {
      if (e.data !== 'saved' || !connected) return;
      const editing = document.activeElement === $('edNote') || document.activeElement === $('edTitle');
      if (editing) return; // 내가 편집 중이면 덮어쓰지 않음
      fsReadText('index.json').then(txt => {
        const keep = selectedId;
        data = indexToData(JSON.parse(txt));
        selectedId = data.todos.some(t => t.id === keep) ? keep : null;
        renderAll();
      }).catch(() => {});
    };
  }
}

/* ===================== 시작 ===================== */

async function init() {
  data = indexToData(null); // 폴더 로드 전 임시 빈 상태 (기본 그룹 포함)
  bindEvents();
  loadNavCollapsed();   // 섹션 접힘 상태 적용 (기본: 상태별 분류 접힘)
  renderAll();          // 빈 화면(게이트가 위에 덮음)
  await initStorage();  // 폴더 연결/로드 (게이트 처리 포함)

  try {
    if (navigator.storage && navigator.storage.persist) navigator.storage.persist();
  } catch (e) { /* 무시 */ }

  // PWA 오프라인 지원 — https(호스팅)에서만 등록. file:// 더블클릭 사용에는 영향 없음.
  if ('serviceWorker' in navigator &&
      (location.protocol === 'https:' ||
       ['localhost', '127.0.0.1'].includes(location.hostname))) {
    navigator.serviceWorker.register('./sw.js').catch(() => { /* 무시 */ });
  }

  setInterval(() => {
    if (curDayKey !== todayKey()) { curDayKey = todayKey(); renderAll(); }
  }, 30000);
}

init();
