// service-worker.js

// Increment version on updates to trigger cache invalidation and fresh content fetching.
// This is critical for ensuring users get the latest version of your PWA.
const CACHE_NAME = 'glyphmotion-pwa-cache-v1.0.7'; // Updated to v1.0.7 to force cache refresh
const OFFLINE_URL = '/offline.html'; // Path to your custom offline page

// List of URLs to cache when the service worker is installed.
// These are your app's core "shell" files. Use absolute paths relative to the domain root.
const urlsToCache = [
    '.', // Caches the root HTML file (often resolves to index.html)
    '/index.html',
    '/admin.html',
    '/admin_tracker.html',
    '/documentation.html',
    '/offline.html',
    '/manifest.json',
    '/images/project-glyph-motion.ico', // Favicon
    '/images/thumbnail_fallback.jpg', // Fallback thumbnail image
    // Add other essential static assets (e.g., specific font files if self-hosted)
    // '/fonts/SFPROTEXTREGULAR.OTF',
    // '/fonts/SFPROTEXTMEDIUM.OTF',
    // '/fonts/SFPROTEXTSEMIBOLD.OTF',
    // '/fonts/SFPROTEXTBOLD.OTF',
];

// Define assets that should use a "network first, then cache" strategy.
// This is crucial for HTML and other frequently updated core files to ensure users
// always see the latest content when online.
const networkFirstUrls = [
    '.',
    '/index.html',
    '/admin.html',
    '/admin_tracker.html',
    '/documentation.html',
    '/offline.html', // While offline.html is for offline, it should still be network-first when online to get updates
    '/manifest.json',
];

// Install event: caches the static assets and forces activation immediately.
self.addEventListener('install', (event) => {
    console.log('[Service Worker] Installing service worker...');
    event.waitUntil(
        caches.open(CACHE_NAME)
            .then((cache) => {
                console.log('[Service Worker] Caching all app shell content during install');
                // Cache the initial set of URLs
                return cache.addAll(urlsToCache);
            })
            .then(() => self.skipWaiting()) // Forces the waiting service worker to become the active service worker immediately.
            .catch((error) => {
                console.error('[Service Worker] Caching during install failed:', error);
            })
    );
});

// Activate event: cleans up old caches and immediately takes control of clients.
self.addEventListener('activate', (event) => {
    console.log('[Service Worker] Activating service worker...');
    event.waitUntil(
        caches.keys().then((cacheNames) => {
            return Promise.all(
                cacheNames.map((cacheName) => {
                    // Delete old caches that do not match the current CACHE_NAME
                    if (cacheName.startsWith('glyphmotion-pwa-cache-') && cacheName !== CACHE_NAME) {
                        console.log('[Service Worker] Deleting old cache:', cacheName);
                        return caches.delete(cacheName);
                    }
                    return null;
                })
            );
        })
        .then(() => clients.claim()) // Immediately takes control of all clients within its scope.
        .catch((error) => {
            console.error('[Service Worker] Activation failed:', error);
        })
    );
});

// Fetch event: intercepts network requests and applies caching strategies.
self.addEventListener('fetch', (event) => {
    // Only handle GET requests, ignore others (e.g., POST from forms)
    if (event.request.method !== 'GET') {
        return;
    }

    // Filter out non-HTTP/HTTPS requests (e.g., chrome-extension://) or requests to external CDNs
    // This is important for cdn.tailwindcss.com and fonts.googleapis.com
    if (!event.request.url.startsWith(self.location.origin + '/') &&
        !event.request.url.startsWith('https://fonts.googleapis.com/') &&
        !event.request.url.startsWith('https://fonts.gstatic.com/') &&
        !event.request.url.startsWith('https://cdnjs.cloudflare.com/')) { // Add Font Awesome CDN
        console.warn(`[Service Worker] Skipping cache for external or unsupported scheme/origin: ${event.request.url}`);
        return; // Do not handle these requests with caching logic
    }
    // Note: If you still use cdn.tailwindcss.com, it will be excluded by the above filter.
    // This is aligned with the recommendation to self-host Tailwind in production.

    // Determine if the request URL should use a network-first strategy
    const requestUrl = new URL(event.request.url);
    const pathname = requestUrl.pathname;

    // Check if the exact pathname (including leading slash) is in networkFirstUrls
    const isNetworkFirst = networkFirstUrls.includes(pathname);

    if (isNetworkFirst) {
        // Network First, then Cache strategy for core HTML files and manifest
        event.respondWith(
            fetch(event.request)
                .then((networkResponse) => {
                    // Check if we received a valid response.
                    // A response with status 0 (e.g., due to CORS issues) should not be cached.
                    if (!networkResponse || networkResponse.status !== 200 || networkResponse.type !== 'basic') {
                        // Attempt to serve from cache if network response is invalid
                        return caches.match(event.request).then(cachedResponse => {
                            if (cachedResponse) {
                                console.log(`[Service Worker] Network First failed for ${event.request.url}, serving from cache.`);
                                return cachedResponse;
                            }
                            console.log(`[Service Worker] Network First failed for ${event.request.url}, no cache fallback.`);
                            return networkResponse; // Return original network response even if invalid
                        });
                    }

                    // If valid, clone the response and put it in the cache for future use
                    const responseToCache = networkResponse.clone();
                    caches.open(CACHE_NAME).then((cache) => {
                        cache.put(event.request, responseToCache);
                    });
                    console.log(`[Service Worker] Network First successful for ${event.request.url}, updated cache.`);
                    return networkResponse; // Return the network response
                })
                .catch((error) => {
                    // Network failed (e.g., offline), try to get from cache
                    console.log(`[Service Worker] Network failed for ${event.request.url}, falling back to cache.`, error);
                    return caches.match(event.request).then((cachedResponse) => {
                        if (cachedResponse) {
                            return cachedResponse;
                        }
                        // If no cache, and it's a navigation request, serve the offline page
                        if (event.request.mode === 'navigate') {
                            console.log('[Service Worker] No cache for navigation, serving offline page.');
                            return caches.match(OFFLINE_URL);
                        }
                        // For other types of requests without cache, just return a generic error or null
                        console.log('[Service Worker] No cache for non-navigation request, returning default error.');
                        return new Response(null, { status: 503, statusText: 'Service Unavailable' });
                    });
                })
        );
    } else {
        // Cache First, then Network (for other assets like images that are less critical to be fresh)
        event.respondWith(
            caches.match(event.request).then((cachedResponse) => {
                if (cachedResponse) {
                    // console.log(`[Service Worker] Cache First successful for ${event.request.url}, serving from cache.`);
                    return cachedResponse;
                }
                // If not in cache, try to fetch from network and cache it
                return fetch(event.request).then((networkResponse) => {
                    if (!networkResponse || networkResponse.status !== 200 || networkResponse.type !== 'basic') {
                        return networkResponse;
                    }
                    const responseToCache = networkResponse.clone();
                    caches.open(CACHE_NAME).then((cache) => {
                        cache.put(event.request, responseToCache);
                    });
                    // console.log(`[Service Worker] Cache First missed for ${event.request.url}, fetched and cached.`);
                    return networkResponse;
                }).catch((error) => {
                    console.log(`[Service Worker] Cache First missed and network failed for ${event.request.url}.`, error);
                    // No fallback for non-navigation requests, let them fail silently or return a placeholder
                    return new Response(null, { status: 503, statusText: 'Service Unavailable' });
                });
            })
        );
    }
});