const CACHE_NAME = 'shufflebox-v1';

// 安装阶段：不强制缓存大量资源，保持轻量
self.addEventListener('install', (event) => {
    self.skipWaiting();
});

// 激活阶段：清理旧缓存
self.addEventListener('activate', (event) => {
    event.waitUntil(clients.claim());
});

// 核心：必须有 fetch 处理器才能触发安卓 Chrome 的安装横幅
self.addEventListener('fetch', (event) => {
    // 默认直接透传，不做离线缓存以节省空间和避免版本更新延迟
    event.respondWith(fetch(event.request));
});
