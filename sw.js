// TODO 메모장 서비스 워커
// 전략: 앱 셸(화면 코드)만 캐시 → 첫 접속 후엔 네트워크 없이도 열림(stale-while-revalidate).
// 주의: 메모 데이터는 여기서 캐시하지 않는다. 데이터는 File System Access로
//       사용자가 고른 로컬 폴더에만 저장되며, 네트워크/캐시를 거치지 않는다.

const CACHE = 'todomemo-v1';
const ASSETS = [
  './',
  './index.html',
  './style.css',
  './app.js',
  './manifest.json',
  './icon.png',
  './icon-192.png',
  './icon-512.png',
];

self.addEventListener('install', e => {
  e.waitUntil(
    caches.open(CACHE)
      .then(c => c.addAll(ASSETS))
      .then(() => self.skipWaiting())
  );
});

self.addEventListener('activate', e => {
  e.waitUntil(
    caches.keys()
      .then(keys => Promise.all(
        keys.filter(k => k !== CACHE).map(k => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

self.addEventListener('fetch', e => {
  if (e.request.method !== 'GET') return;
  const url = new URL(e.request.url);
  // 같은 오리진의 화면 코드만 처리 (그 외는 브라우저 기본 동작에 맡김)
  if (url.origin !== location.origin) return;
  e.respondWith(
    caches.match(e.request, { ignoreSearch: true }).then(cached => {
      const fetched = fetch(e.request)
        .then(r => {
          if (r.ok) {
            const copy = r.clone();
            caches.open(CACHE).then(c => c.put(e.request, copy));
          }
          return r;
        })
        .catch(() => cached || caches.match('./index.html'));
      // 캐시가 있으면 즉시 반환, 갱신은 백그라운드에서
      return cached || fetched;
    })
  );
});
