"use strict";

const http = require("http");
const fs = require("fs");
const fsp = fs.promises;
const path = require("path");
const crypto = require("crypto");
const { spawn } = require("child_process");

const APP_VERSION = require("./package.json").version;
const PORT = Number(process.env.APP_PORT || 80);
const APP_LANG = process.env.APP_LANG === "en" ? "en" : "zh";
const DATA_DIR = path.resolve(process.env.DATA_DIR || "/var/lib/shufflebox");
const MEDIA_ROOT = path.resolve(process.env.MEDIA_ROOT || "/mnt/shufflebox-media");
const MEDIA_PREMOUNTED = process.env.MEDIA_PREMOUNTED === "true";
// Administrative SMB controls are opt-in and enforced server-side as well as
// in the UI, so browser-console requests cannot bypass the hidden controls.
const ADMIN_SETTINGS_ENABLED = process.env.SHUFFLEBOX_ADMIN_SETTINGS === "true";
const STATIC_ROOT = path.join(__dirname, APP_LANG);
const CONFIG_FILE = path.join(DATA_DIR, "smb-config.json");
const MEDIA_PREFERENCES_FILE = path.join(DATA_DIR, "media-preferences.json");
const FAVORITES_FILE = path.join(DATA_DIR, "favorites.json");
const TAGS_FILE = path.join(DATA_DIR, "tags.json");
const VIDEO_TAGS_FILE = path.join(DATA_DIR, "video-tags.txt");
const THUMB_DIR = path.join(DATA_DIR, "thumbs");
const THUMB_CACHE_DIR = path.join(DATA_DIR, "cache");
const THUMB_CACHE_CONFIG_FILE = path.join(THUMB_CACHE_DIR, "config.json");
const HLS_DIR = path.join(DATA_DIR, "hls");
const CREDENTIALS_FILE = path.join(DATA_DIR, ".smb-credentials");
const VIDEO_EXTENSIONS = new Set([
  ".mp4",
  ".mkv",
  ".m4v",
  ".mov",
  ".avi",
  ".webm",
  ".wmv",
  ".flv",
  ".ts",
  ".m2ts",
  ".mts",
  ".mpg",
  ".mpeg",
  ".vob",
  ".3gp",
  ".ogv",
]);
const MIME_TYPES = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".json": "application/json; charset=utf-8",
  ".png": "image/png",
  ".webp": "image/webp",
  ".ico": "image/x-icon",
  ".svg": "image/svg+xml",
  ".mp4": "video/mp4",
  ".m4v": "video/mp4",
  ".mkv": "video/x-matroska",
  ".webm": "video/webm",
  ".mov": "video/quicktime",
  ".avi": "video/x-msvideo",
  ".ts": "video/mp2t",
  ".m2ts": "video/mp2t",
};

let config = {
  share: "",
  username: "",
  password: "",
  vers: "3.0",
  guest: false,
  deleteMode: false,
};
let favorites = new Set();
let tags = [];
let videoTags = new Map();
let mediaPreferences = { libraryId: "", libraryType: "library", collapsedGroupPaths: [] };
let items = [];
let itemsById = new Map();
let libraries = [];
let scanState = { scanning: false, error: "", lastScan: null };
const THUMBNAIL_CACHE_LIMIT_BYTES = 5 * 1024 ** 3;
const THUMBNAIL_MAX_BYTES = 150 * 1024;
const THUMBNAIL_MAX_CONCURRENCY = 2;
const THUMBNAIL_ENTRY_RESERVATION_BYTES = THUMBNAIL_MAX_BYTES + 1024;
const THUMBNAIL_JOB_TIMEOUT_MS = 60 * 1000;
const THUMBNAIL_PREWARM_DELAY_MS = 1000;
const THUMBNAIL_PREWARM_IDLE_DELAY_MS = 500;
const THUMBNAIL_PREWARM_STEP_DELAY_MS = 50;
const THUMBNAIL_TEMP_PREFIX = ".shufflebox-thumb-tmp-";
let thumbnailCacheConfig = { version: 1, sources: {} };
let currentThumbnailSource = null;
let thumbnailCacheBytes = 0;
let thumbnailCacheReservedBytes = 0;
let thumbnailCacheLimitExceeded = false;
let thumbnailCacheRefreshPromise = null;
let thumbnailCacheConfigWritePromise = Promise.resolve();
let thumbnailCacheLock = Promise.resolve();
const thumbnailJobs = new Map();
const thumbnailJobQueue = [];
let activeThumbnailJobs = 0;
let thumbnailPrewarmGeneration = 0;
let thumbnailPrewarmItems = [];
let thumbnailPrewarmCursor = 0;
let thumbnailPrewarmTimer = null;
let thumbnailPrewarmPausedByLimit = false;
const HLS_IDLE_TIMEOUT_MS = 5 * 1000;
const hlsJobs = new Map();
const PLAYBACK_SESSION_TTL_MS = 10 * 60 * 1000;
const PLAYBACK_BURST_SECONDS = 3;
const PLAYBACK_MIN_BYTES_PER_SECOND = 512 * 1024;
const playbackSessions = new Map();

function stopHlsJob(itemId, reason = "idle") {
  const job = hlsJobs.get(itemId);
  if (!job) return;
  clearTimeout(job.idleTimer);
  hlsJobs.delete(itemId);
  job.cleanupOnClose = true;
  if (!job.child.killed) job.child.kill("SIGTERM");
  console.log(`Stopped HLS transcode for ${itemId} (${reason})`);
}

function touchHlsJob(itemId) {
  const job = hlsJobs.get(itemId);
  if (!job) return;
  job.lastAccess = Date.now();
  clearTimeout(job.idleTimer);
  job.idleTimer = setTimeout(() => {
    const current = hlsJobs.get(itemId);
    if (!current) return;
    if (Date.now() - current.lastAccess >= HLS_IDLE_TIMEOUT_MS)
      stopHlsJob(itemId, "no requests");
    else touchHlsJob(itemId);
  }, HLS_IDLE_TIMEOUT_MS);
  job.idleTimer.unref();
}

function playbackControlId(url) {
  const value = String(url.searchParams.get("PlaybackControlId") || "");
  return /^[A-Za-z0-9_.:-]{1,128}$/.test(value) ? value : "";
}

function playbackGeneration(url) {
  if (!url.searchParams.has("PlaybackGeneration")) return -1;
  const value = Number(url.searchParams.get("PlaybackGeneration"));
  return Number.isSafeInteger(value) && value >= 0 ? value : -1;
}

function managedPlayback(url, itemId) {
  const sessionId = playbackControlId(url);
  if (!sessionId) return { managed: false, session: null };
  const session = playbackSessions.get(sessionId);
  if (
    !session ||
    playbackGeneration(url) !== session.generation ||
    itemId !== session.currentId
  ) {
    return { managed: true, session: null };
  }
  session.lastAccess = Date.now();
  return { managed: true, session };
}

function registerPlaybackResponse(session, itemId, res) {
  if (!session) return;
  if (!session.responses.has(itemId)) session.responses.set(itemId, new Set());
  const responses = session.responses.get(itemId);
  responses.add(res);
  res.once("close", () => {
    responses.delete(res);
    if (!responses.size) session.responses.delete(itemId);
  });
}

function closePlaybackResponses(session, allowedIds = new Set()) {
  for (const [itemId, responses] of session.responses) {
    if (allowedIds.has(itemId)) continue;
    for (const response of responses) response.destroy();
    session.responses.delete(itemId);
  }
}

function itemNeededByPlaybackSession(itemId) {
  for (const session of playbackSessions.values()) {
    if (session.currentId === itemId) return true;
  }
  return false;
}

function stopUnusedHlsJobs(previousIds, allowedIds) {
  for (const itemId of previousIds) {
    if (
      itemId &&
      !allowedIds.has(itemId) &&
      !itemNeededByPlaybackSession(itemId)
    )
      stopHlsJob(itemId, "playback switched");
  }
}

function updatePlaybackSession(sessionId, generation, currentId) {
  let session = playbackSessions.get(sessionId);
  if (session && generation < session.generation) return null;
  if (!session) {
    session = {
      id: sessionId,
      generation: -1,
      currentId: "",
      lastAccess: Date.now(),
      responses: new Map(),
    };
    playbackSessions.set(sessionId, session);
  }
  const previousIds = new Set([session.currentId].filter(Boolean));
  const allowedIds = new Set([currentId].filter(Boolean));
  // Every generation owns fresh media URLs. Close all older-generation
  // responses before allowing the newly current item to stream.
  closePlaybackResponses(session);
  session.generation = generation;
  session.currentId = currentId;
  session.lastAccess = Date.now();
  stopUnusedHlsJobs(previousIds, allowedIds);
  return session;
}

const playbackSessionCleanup = setInterval(() => {
  const expiredBefore = Date.now() - PLAYBACK_SESSION_TTL_MS;
  for (const [sessionId, session] of playbackSessions) {
    if (session.lastAccess >= expiredBefore) continue;
    const previousIds = new Set([session.currentId].filter(Boolean));
    closePlaybackResponses(session);
    playbackSessions.delete(sessionId);
    stopUnusedHlsJobs(previousIds, new Set());
  }
}, 60 * 1000);
playbackSessionCleanup.unref();

function idFor(value) {
  return crypto.createHash("sha256").update(value).digest("hex").slice(0, 24);
}

function safeJsonParse(text, fallback) {
  try {
    return JSON.parse(text);
  } catch {
    return fallback;
  }
}

function normalizeSmbShare(value) {
  const normalized = String(value || "")
    .trim()
    .replace(/\\/g, "/")
    .replace(/^\/+/, "//")
    .replace(/\/+$/, "");
  const match = /^\/\/([^/]+)\/(.+)$/.exec(normalized);
  if (!match) return "";
  const sharePath = match[2].replace(/\/{2,}/g, "/").replace(/^\/+|\/+$/g, "");
  if (!sharePath) return "";
  return `//${match[1].toLowerCase()}/${sharePath}`;
}

function safeCacheSegment(value, fallback = "source") {
  const safe = String(value || "")
    .replace(/[^A-Za-z0-9._-]+/g, "_")
    .replace(/^\.+/, "")
    .replace(/_+/g, "_")
    .slice(0, 80)
    .replace(/^[_-]+|[_-]+$/g, "");
  return safe || fallback;
}

function thumbnailSourceIdentity() {
  const share = normalizeSmbShare(config.share);
  const canonicalSource = share || (MEDIA_PREMOUNTED ? `premounted://${MEDIA_ROOT}` : "");
  if (!canonicalSource) return null;
  const sourceId = idFor(`thumbnail-source:${canonicalSource}`);
  const shareParts = /^\/\/([^/]+)\/(.+)$/.exec(canonicalSource);
  const label = shareParts
    ? `${safeCacheSegment(shareParts[1])}_${safeCacheSegment(shareParts[2])}`
    : "premounted";
  return {
    id: sourceId,
    share: canonicalSource,
    directory: `${label}_${sourceId}`,
  };
}

function normalizeMediaRelativePath(value) {
  const normalized = String(value || "").replace(/\\/g, "/");
  const segments = normalized.split("/");
  if (
    !normalized ||
    segments.some(
      (segment) => !segment || segment === "." || segment === ".." || segment.includes("\0"),
    )
  )
    throw new Error("媒体路径无效");
  return segments.join("/");
}

function cachePathWithin(root, relativePath) {
  const resolvedRoot = path.resolve(root);
  const resolvedPath = path.resolve(root, relativePath);
  if (resolvedPath !== resolvedRoot && !resolvedPath.startsWith(`${resolvedRoot}${path.sep}`))
    throw new Error("缩略图缓存路径无效");
  return resolvedPath;
}

async function writeJsonAtomically(file, value, mode = 0o600) {
  const directory = path.dirname(file);
  await fsp.mkdir(directory, { recursive: true, mode: 0o750 });
  const temporary = path.join(
    directory,
    `${THUMBNAIL_TEMP_PREFIX}${process.pid}-${crypto.randomUUID()}.tmp`,
  );
  try {
    await fsp.writeFile(temporary, JSON.stringify(value, null, 2), { mode });
    await fsp.chmod(temporary, mode);
    await fsp.rename(temporary, file);
    await fsp.chmod(file, mode);
  } catch (error) {
    await fsp.rm(temporary, { force: true }).catch(() => {});
    throw error;
  }
}

async function loadThumbnailCacheConfig() {
  try {
    const parsed = safeJsonParse(await fsp.readFile(THUMB_CACHE_CONFIG_FILE, "utf8"), {});
    if (parsed && typeof parsed === "object" && parsed.sources && typeof parsed.sources === "object") {
      thumbnailCacheConfig = { version: 1, sources: parsed.sources };
    }
  } catch {}
}

async function saveThumbnailCacheConfig() {
  const nextWrite = thumbnailCacheConfigWritePromise.then(() =>
    writeJsonAtomically(THUMB_CACHE_CONFIG_FILE, thumbnailCacheConfig, 0o600),
  );
  thumbnailCacheConfigWritePromise = nextWrite.catch(() => {});
  return nextWrite;
}

async function ensureThumbnailSource() {
  const source = thumbnailSourceIdentity();
  currentThumbnailSource = source;
  if (!source) {
    cancelThumbnailPrewarm();
    return null;
  }
  const sourceDirectory = cachePathWithin(THUMB_CACHE_DIR, source.directory);
  await fsp.mkdir(sourceDirectory, { recursive: true, mode: 0o750 });
  const previous = thumbnailCacheConfig.sources[source.id];
  const next = {
    share: source.share,
    directory: source.directory,
    createdAt: previous?.createdAt || new Date().toISOString(),
    lastSeenAt: new Date().toISOString(),
  };
  thumbnailCacheConfig.sources[source.id] = next;
  await saveThumbnailCacheConfig();
  return source;
}

async function removeThumbnailTemporaryFiles(directory = THUMB_CACHE_DIR) {
  let entries;
  try {
    entries = await fsp.readdir(directory, { withFileTypes: true });
  } catch {
    return;
  }
  for (const entry of entries) {
    const target = path.join(directory, entry.name);
    if (entry.isDirectory()) {
      await removeThumbnailTemporaryFiles(target);
    } else if (entry.isFile() && entry.name.startsWith(THUMBNAIL_TEMP_PREFIX)) {
      await fsp.rm(target, { force: true }).catch(() => {});
    }
  }
}

async function sumThumbnailCacheBytes(directory = THUMB_CACHE_DIR) {
  let entries;
  try {
    entries = await fsp.readdir(directory, { withFileTypes: true });
  } catch {
    return 0;
  }
  let total = 0;
  for (const entry of entries) {
    if (entry.name.startsWith(THUMBNAIL_TEMP_PREFIX)) continue;
    const target = path.join(directory, entry.name);
    if (entry.isDirectory()) {
      total += await sumThumbnailCacheBytes(target);
    } else if (entry.isFile()) {
      try {
        total += (await fsp.stat(target)).size;
      } catch {}
    }
  }
  return total;
}

function refreshThumbnailCacheUsage() {
  if (thumbnailCacheRefreshPromise) return thumbnailCacheRefreshPromise;
  thumbnailCacheRefreshPromise = sumThumbnailCacheBytes()
    .then((bytes) => {
      thumbnailCacheBytes = bytes;
      if (bytes < THUMBNAIL_CACHE_LIMIT_BYTES) thumbnailCacheLimitExceeded = false;
      else thumbnailCacheLimitExceeded = true;
      if (!thumbnailCacheLimitExceeded && thumbnailPrewarmPausedByLimit) {
        thumbnailPrewarmPausedByLimit = false;
        scheduleThumbnailPrewarm();
      }
      return bytes;
    })
    .finally(() => {
      thumbnailCacheRefreshPromise = null;
    });
  return thumbnailCacheRefreshPromise;
}

function withThumbnailCacheLock(task) {
  const next = thumbnailCacheLock.then(task, task);
  thumbnailCacheLock = next.catch(() => {});
  return next;
}

async function entryBytes(paths) {
  let total = 0;
  for (const file of [paths.target, paths.metadata]) {
    try {
      const stat = await fsp.stat(file);
      if (stat.isFile()) total += stat.size;
    } catch {}
  }
  return total;
}

async function reserveThumbnailSpace(paths) {
  return withThumbnailCacheLock(async () => {
    await refreshThumbnailCacheUsage();
    const existingBytes = await entryBytes(paths);
    const reservedBytes = Math.max(
      0,
      THUMBNAIL_ENTRY_RESERVATION_BYTES - existingBytes,
    );
    if (
      thumbnailCacheBytes + thumbnailCacheReservedBytes + reservedBytes >
      THUMBNAIL_CACHE_LIMIT_BYTES
    ) {
      thumbnailCacheLimitExceeded = true;
      return null;
    }
    thumbnailCacheReservedBytes += reservedBytes;
    return { existingBytes, reservedBytes };
  });
}

async function releaseThumbnailSpace(paths, reservation) {
  if (!reservation) return;
  await withThumbnailCacheLock(async () => {
    thumbnailCacheReservedBytes = Math.max(
      0,
      thumbnailCacheReservedBytes - reservation.reservedBytes,
    );
    const currentBytes = await entryBytes(paths);
    thumbnailCacheBytes = Math.max(
      0,
      thumbnailCacheBytes + currentBytes - reservation.existingBytes,
    );
    thumbnailCacheLimitExceeded =
      thumbnailCacheBytes >= THUMBNAIL_CACHE_LIMIT_BYTES;
  });
}

function thumbnailEntryPaths(source, relativePath) {
  const sourceDirectory = cachePathWithin(THUMB_CACHE_DIR, source.directory);
  const target = cachePathWithin(sourceDirectory, `${relativePath}.webp`);
  return { target, metadata: `${target}.meta.json` };
}

async function currentThumbnailContext(item) {
  if (!currentThumbnailSource) return null;
  const relativePath = normalizeMediaRelativePath(item.Path);
  const stat = await fsp.stat(item._absolutePath);
  const paths = thumbnailEntryPaths(currentThumbnailSource, relativePath);
  const source = {
    id: currentThumbnailSource.id,
    share: currentThumbnailSource.share,
    relativePath,
    size: stat.size,
    mtimeMs: Math.trunc(stat.mtimeMs),
  };
  return { item, source, paths };
}

async function validThumbnail(context) {
  try {
    const cacheRoot = await fsp.realpath(THUMB_CACHE_DIR);
    const cacheParent = await fsp.realpath(path.dirname(context.paths.target));
    if (
      cacheParent !== cacheRoot &&
      !cacheParent.startsWith(`${cacheRoot}${path.sep}`)
    )
      return null;
    const [metadataText, stat, targetLink, metadataLink] = await Promise.all([
      fsp.readFile(context.paths.metadata, "utf8"),
      fsp.stat(context.paths.target),
      fsp.lstat(context.paths.target),
      fsp.lstat(context.paths.metadata),
    ]);
    const metadata = safeJsonParse(metadataText, null);
    if (
      !stat.isFile() ||
      !targetLink.isFile() ||
      !metadataLink.isFile() ||
      stat.size <= 0 ||
      stat.size > THUMBNAIL_MAX_BYTES ||
      !metadata ||
      metadata.version !== 1 ||
      metadata.sourceId !== context.source.id ||
      metadata.relativePath !== context.source.relativePath ||
      metadata.size !== context.source.size ||
      metadata.mtimeMs !== context.source.mtimeMs
    )
      return null;
    return stat;
  } catch {
    return null;
  }
}

function thumbnailJobKey(context) {
  return `${context.source.id}\0${context.source.relativePath}`;
}

function hasForegroundThumbnailWork() {
  return [...thumbnailJobs.values()].some(
    (job) => job.priority === "foreground",
  );
}

function takeNextThumbnailJob() {
  const queued = thumbnailJobQueue.filter((job) => job.state === "queued");
  if (!queued.length) return null;
  const foregroundIndex = thumbnailJobQueue.findIndex(
    (job) => job.state === "queued" && job.priority === "foreground",
  );
  // Keep one worker available for a foreground request. If older state has
  // already filled both workers with background jobs, enqueueing foreground
  // work below will cancel enough background jobs to free that slot.
  if (foregroundIndex < 0 && activeThumbnailJobs >= THUMBNAIL_MAX_CONCURRENCY - 1)
    return null;
  const index = foregroundIndex >= 0
    ? foregroundIndex
    : thumbnailJobQueue.findIndex((job) => job.state === "queued");
  return thumbnailJobQueue.splice(index, 1)[0] || null;
}

function stopThumbnailJob(job) {
  if (!job) return;
  job.cancelled = true;
  if (!job.child || job.child.exitCode !== null) return;
  job.child.kill("SIGTERM");
  if (job.cancelTimer) clearTimeout(job.cancelTimer);
  job.cancelTimer = setTimeout(() => {
    if (job.child && job.child.exitCode === null) job.child.kill("SIGKILL");
  }, 1000);
  job.cancelTimer.unref();
}

function preemptBackgroundThumbnailJobs() {
  const foregroundRunning = [...thumbnailJobs.values()].filter(
    (job) => job.state === "running" && job.priority === "foreground",
  ).length;
  const allowedBackground = Math.max(
    0,
    THUMBNAIL_MAX_CONCURRENCY - foregroundRunning - 1,
  );
  const runningBackground = [...thumbnailJobs.values()].filter(
    (job) => job.state === "running" && job.priority === "background",
  );
  for (const job of runningBackground.slice(allowedBackground))
    stopThumbnailJob(job);
}

function pumpThumbnailJobs() {
  while (activeThumbnailJobs < THUMBNAIL_MAX_CONCURRENCY) {
    const job = takeNextThumbnailJob();
    if (!job) return;
    activeThumbnailJobs += 1;
    job.state = "running";
    runThumbnailJob(job)
      .then((result) => job.resolve(result))
      .catch((error) => {
        if (error.code === "THUMBNAIL_CANCELLED") {
          job.resolve({ status: "cancelled" });
        } else {
          console.warn(`缩略图生成失败：${error.message}`);
          job.resolve({ status: "failed" });
        }
      })
      .finally(() => {
        activeThumbnailJobs -= 1;
        thumbnailJobs.delete(job.key);
        pumpThumbnailJobs();
      });
  }
}

function enqueueThumbnailJob(context, priority = "foreground") {
  const key = thumbnailJobKey(context);
  const existing = thumbnailJobs.get(key);
  if (existing) {
    if (priority === "foreground") {
      existing.priority = "foreground";
      preemptBackgroundThumbnailJobs();
    }
    return existing.promise;
  }
  let resolve;
  const promise = new Promise((complete) => {
    resolve = complete;
  });
  const job = {
    key,
    context,
    priority,
    state: "queued",
    child: null,
    cancelled: false,
    resolve,
    promise,
  };
  thumbnailJobs.set(key, job);
  thumbnailJobQueue.push(job);
  if (priority === "foreground") preemptBackgroundThumbnailJobs();
  pumpThumbnailJobs();
  return promise;
}

function runFfmpeg(commandArgs, job) {
  return new Promise((resolve, reject) => {
    if (job.cancelled) {
      const error = new Error("缩略图任务已取消");
      error.code = "THUMBNAIL_CANCELLED";
      reject(error);
      return;
    }
    const child = spawn("ffmpeg", commandArgs, {
      stdio: ["ignore", "ignore", "pipe"],
    });
    job.child = child;
    let errorText = "";
    let finished = false;
    let timedOut = false;
    const timeout = setTimeout(() => {
      if (finished) return;
      timedOut = true;
      child.kill("SIGTERM");
    }, THUMBNAIL_JOB_TIMEOUT_MS);
    timeout.unref();
    child.stderr.on("data", (chunk) => {
      errorText = (errorText + chunk).slice(-2000);
    });
    child.once("error", (error) => {
      if (finished) return;
      finished = true;
      clearTimeout(timeout);
      if (job.cancelTimer) {
        clearTimeout(job.cancelTimer);
        job.cancelTimer = null;
      }
      job.child = null;
      reject(error);
    });
    child.once("close", (code) => {
      if (finished) return;
      finished = true;
      clearTimeout(timeout);
      if (job.cancelTimer) {
        clearTimeout(job.cancelTimer);
        job.cancelTimer = null;
      }
      job.child = null;
      if (job.cancelled) {
        const error = new Error("缩略图任务已取消");
        error.code = "THUMBNAIL_CANCELLED";
        reject(error);
      } else if (timedOut) {
        const error = new Error("缩略图生成超时");
        error.code = "THUMBNAIL_TIMEOUT";
        reject(error);
      } else if (code === 0) {
        resolve();
      } else {
        reject(new Error(errorText.trim() || `ffmpeg exited with ${code}`));
      }
    });
  });
}

async function encodeThumbnail(context, job, temporary) {
  const attempts = [
    { width: 480, quality: 65 },
    { width: 360, quality: 50 },
    { width: 320, quality: 35 },
  ];
  for (const attempt of attempts) {
    await fsp.rm(temporary, { force: true });
    await runFfmpeg(
      [
        "-hide_banner",
        "-loglevel",
        "error",
        "-nostdin",
        "-ss",
        "3",
        "-i",
        context.item._absolutePath,
        "-frames:v",
        "1",
        "-vf",
        `scale=${attempt.width}:-2`,
        "-c:v",
        "libwebp",
        "-q:v",
        String(attempt.quality),
        "-compression_level",
        "6",
        "-preset",
        "picture",
        "-an",
        "-f",
        "webp",
        "-y",
        temporary,
      ],
      job,
    );
    const stat = await fsp.stat(temporary);
    if (stat.isFile() && stat.size > 0 && stat.size <= THUMBNAIL_MAX_BYTES)
      return stat.size;
  }
  throw new Error("缩略图超过大小限制");
}

async function runThumbnailJob(job) {
  const context = await currentThumbnailContext(job.context.item);
  if (!context || context.source.id !== job.context.source.id)
    return { status: "unavailable" };
  if (await validThumbnail(context)) return { status: "cached" };
  if (!(await isMounted())) return { status: "unavailable" };

  const reservation = await reserveThumbnailSpace(context.paths);
  if (!reservation) return { status: "limit" };
  const temporary = path.join(
    path.dirname(context.paths.target),
    `${THUMBNAIL_TEMP_PREFIX}${process.pid}-${crypto.randomUUID()}.webp`,
  );
  let committed = false;
  let targetRenamed = false;
  try {
    if (job.cancelled) return { status: "cancelled" };
    await fsp.mkdir(path.dirname(context.paths.target), {
      recursive: true,
      mode: 0o750,
    });
    const cacheRoot = await fsp.realpath(THUMB_CACHE_DIR);
    const cacheParent = await fsp.realpath(path.dirname(context.paths.target));
    if (
      cacheParent !== cacheRoot &&
      !cacheParent.startsWith(`${cacheRoot}${path.sep}`)
    )
      throw new Error("缩略图缓存路径无效");
    await encodeThumbnail(context, job, temporary);
    if (job.cancelled) return { status: "cancelled" };
    const latestStat = await fsp.stat(context.item._absolutePath);
    if (
      latestStat.size !== context.source.size ||
      Math.trunc(latestStat.mtimeMs) !== context.source.mtimeMs
    )
      return { status: "changed" };
    await fsp.chmod(temporary, 0o640);
    await fsp.rename(temporary, context.paths.target);
    targetRenamed = true;
    await writeJsonAtomically(
      context.paths.metadata,
      {
        version: 1,
        sourceId: context.source.id,
        relativePath: context.source.relativePath,
        size: context.source.size,
        mtimeMs: context.source.mtimeMs,
      },
      0o640,
    );
    committed = true;
    return { status: "generated" };
  } finally {
    await fsp.rm(temporary, { force: true }).catch(() => {});
    if (!committed && targetRenamed) {
      // The target is only renamed immediately before its metadata is written;
      // remove that incomplete pair so it can never be served as a cache hit.
      await fsp.rm(context.paths.target, { force: true }).catch(() => {});
    }
    await releaseThumbnailSpace(context.paths, reservation);
  }
}

function cancelThumbnailPrewarm() {
  thumbnailPrewarmGeneration += 1;
  thumbnailPrewarmItems = [];
  thumbnailPrewarmCursor = 0;
  thumbnailPrewarmPausedByLimit = false;
  if (thumbnailPrewarmTimer) {
    clearTimeout(thumbnailPrewarmTimer);
    thumbnailPrewarmTimer = null;
  }
  for (const job of [...thumbnailJobs.values()]) {
    if (job.priority === "background") stopThumbnailJob(job);
  }
  for (let index = thumbnailJobQueue.length - 1; index >= 0; index -= 1) {
    const job = thumbnailJobQueue[index];
    if (job.priority !== "background") continue;
    thumbnailJobQueue.splice(index, 1);
    thumbnailJobs.delete(job.key);
    job.state = "cancelled";
    job.resolve({ status: "cancelled" });
  }
}

function scheduleThumbnailPrewarm() {
  if (!currentThumbnailSource || !items.length) {
    cancelThumbnailPrewarm();
    return;
  }
  thumbnailPrewarmGeneration += 1;
  const generation = thumbnailPrewarmGeneration;
  thumbnailPrewarmItems = [...items];
  thumbnailPrewarmCursor = 0;
  thumbnailPrewarmPausedByLimit = false;
  if (thumbnailPrewarmTimer) clearTimeout(thumbnailPrewarmTimer);
  thumbnailPrewarmTimer = setTimeout(
    () => runThumbnailPrewarm(generation),
    THUMBNAIL_PREWARM_DELAY_MS,
  );
  thumbnailPrewarmTimer.unref();
}

async function runThumbnailPrewarm(generation) {
  thumbnailPrewarmTimer = null;
  if (
    generation !== thumbnailPrewarmGeneration ||
    !currentThumbnailSource ||
    thumbnailPrewarmCursor >= thumbnailPrewarmItems.length
  )
    return;
  if (!(await isMounted())) return;
  await refreshThumbnailCacheUsage();
  if (thumbnailCacheLimitExceeded) {
    thumbnailPrewarmPausedByLimit = true;
    return;
  }
  if (hasForegroundThumbnailWork()) {
    thumbnailPrewarmTimer = setTimeout(
      () => runThumbnailPrewarm(generation),
      THUMBNAIL_PREWARM_IDLE_DELAY_MS,
    );
    thumbnailPrewarmTimer.unref();
    return;
  }
  const item = thumbnailPrewarmItems[thumbnailPrewarmCursor];
  let context;
  try {
    context = await currentThumbnailContext(item);
  } catch {
    return;
  }
  if (generation !== thumbnailPrewarmGeneration) return;
  if (await validThumbnail(context)) {
    thumbnailPrewarmCursor += 1;
  } else {
    const result = await enqueueThumbnailJob(context, "background");
    if (generation !== thumbnailPrewarmGeneration) return;
    if (result.status === "limit") {
      thumbnailPrewarmPausedByLimit = true;
      return;
    }
    if (["unavailable", "failed", "changed"].includes(result.status)) return;
    thumbnailPrewarmCursor += 1;
  }
  if (thumbnailPrewarmCursor < thumbnailPrewarmItems.length) {
    thumbnailPrewarmTimer = setTimeout(
      () => runThumbnailPrewarm(generation),
      THUMBNAIL_PREWARM_STEP_DELAY_MS,
    );
    thumbnailPrewarmTimer.unref();
  }
}

const thumbnailCacheRefreshTimer = setInterval(() => {
  refreshThumbnailCacheUsage().catch((error) =>
    console.warn(`缩略图缓存检查失败：${error.message}`),
  );
}, 30 * 1000);
thumbnailCacheRefreshTimer.unref();

// Build a deterministic random stream for one shuffle session.  The client
// reuses the same seed while paging, so every page is a slice of one stable
// permutation instead of a fresh shuffle with duplicates and omissions.
function seededRandomInt(seed) {
  let counter = 0;
  return (max) => {
    if (!Number.isSafeInteger(max) || max <= 0) return 0;
    const digest = crypto
      .createHmac("sha256", seed)
      .update(String(counter++))
      .digest();
    return Number(digest.readBigUInt64BE(0) % BigInt(max));
  };
}

function shuffleInPlace(values, randomInt) {
  for (let index = values.length - 1; index > 0; index -= 1) {
    const other = randomInt(index + 1);
    [values[index], values[other]] = [values[other], values[index]];
  }
  return values;
}

function balancedRandomize(source, groupKey, randomInt) {
  const buckets = new Map();
  for (const item of source) {
    const key = groupKey(item);
    if (!buckets.has(key)) buckets.set(key, []);
    buckets.get(key).push(item);
  }
  for (const bucket of buckets.values()) shuffleInPlace(bucket, randomInt);

  const randomized = [];
  let previousKey = null;
  while (buckets.size) {
    const keys = shuffleInPlace([...buckets.keys()], randomInt);
    // Do not let the boundary between two rounds repeat the same directory.
    if (keys.length > 1 && keys[0] === previousKey) {
      const swapAt = 1 + randomInt(keys.length - 1);
      [keys[0], keys[swapAt]] = [keys[swapAt], keys[0]];
    }
    for (const key of keys) {
      const bucket = buckets.get(key);
      randomized.push(bucket.pop());
      previousKey = key;
      if (!bucket.length) buckets.delete(key);
    }
  }
  return randomized;
}

async function ensureDataDirs() {
  await fsp.mkdir(DATA_DIR, { recursive: true });
  await fsp.mkdir(MEDIA_ROOT, { recursive: true });
  await fsp.mkdir(THUMB_DIR, { recursive: true });
  await fsp.mkdir(THUMB_CACHE_DIR, { recursive: true, mode: 0o750 });
  await fsp.mkdir(HLS_DIR, { recursive: true });
}

async function loadState() {
  await ensureDataDirs();
  await removeThumbnailTemporaryFiles();
  await loadThumbnailCacheConfig();
  await refreshThumbnailCacheUsage();
  try {
    config = {
      ...config,
      ...safeJsonParse(await fsp.readFile(CONFIG_FILE, "utf8"), {}),
    };
  } catch {}
  if (!ADMIN_SETTINGS_ENABLED) config.deleteMode = false;
  try {
    favorites = new Set(
      safeJsonParse(await fsp.readFile(FAVORITES_FILE, "utf8"), []),
    );
  } catch {}
  try {
    mediaPreferences = normalizeMediaPreferences(
      safeJsonParse(await fsp.readFile(MEDIA_PREFERENCES_FILE, "utf8"), {}),
    );
  } catch {}
  try {
    tags = normalizeTags(safeJsonParse(await fsp.readFile(TAGS_FILE, "utf8"), []));
  } catch {}
  try {
    videoTags = parseVideoTags(await fsp.readFile(VIDEO_TAGS_FILE, "utf8"));
  } catch {}
}

async function saveFavorites() {
  await fsp.writeFile(FAVORITES_FILE, JSON.stringify([...favorites], null, 2));
}

function normalizeTag(value) {
  return Array.from(String(value || "").trim()).slice(0, 8).join("").replace(/[\r\n,]/g, "");
}

function normalizeTags(value) {
  if (!Array.isArray(value)) return [];
  return [...new Set(value.map(normalizeTag).filter(Boolean))].slice(0, 200);
}

function parseVideoTags(text) {
  const result = new Map();
  for (const line of text.split(/\r?\n/)) {
    const marker = " tags:";
    const markerAt = line.lastIndexOf(marker);
    if (markerAt <= 0) continue;
    const filePath = line.slice(0, markerAt);
    const assigned = normalizeTags(line.slice(markerAt + marker.length).split(","));
    if (assigned.length) result.set(filePath, assigned);
  }
  return result;
}

async function saveTags() {
  await fsp.writeFile(TAGS_FILE, JSON.stringify(tags, null, 2), { mode: 0o600 });
}

async function saveVideoTags() {
  const content = [...videoTags.entries()]
    .map(([filePath, assigned]) => `${filePath} tags:${assigned.join(",")}`)
    .join("\n");
  await fsp.writeFile(VIDEO_TAGS_FILE, content ? `${content}\n` : "", { mode: 0o600 });
}

function normalizeMediaPreferences(value) {
  const libraryId = String(value?.libraryId || "").trim().slice(0, 4096);
  const libraryType = ["library", "playlist", "favorites"].includes(value?.libraryType)
    ? value.libraryType
    : "library";
  const collapsedGroupPaths = Array.isArray(value?.collapsedGroupPaths)
    ? [...new Set(value.collapsedGroupPaths
        .filter((item) => typeof item === "string")
        .map((item) => item.replaceAll("\\\\", "/").replace(/^\/+|\/+$/g, "").slice(0, 1024))
        .filter(Boolean))].slice(0, 1000)
    : [];
  return { libraryId, libraryType, collapsedGroupPaths };
}

async function saveMediaPreferences(next) {
  mediaPreferences = normalizeMediaPreferences(next);
  await fsp.writeFile(MEDIA_PREFERENCES_FILE, JSON.stringify(mediaPreferences, null, 2), {
    mode: 0o600,
  });
  return mediaPreferences;
}

function run(command, args, options = {}) {
  return new Promise((resolve, reject) => {
    const child = spawn(command, args, {
      stdio: ["ignore", "pipe", "pipe"],
      ...options,
    });
    let stdout = "";
    let stderr = "";
    child.stdout?.on("data", (chunk) => {
      stdout += chunk;
    });
    child.stderr?.on("data", (chunk) => {
      stderr += chunk;
    });
    child.on("error", reject);
    child.on("close", (code) =>
      code === 0
        ? resolve(stdout)
        : reject(new Error(stderr.trim() || `${command} exited with ${code}`)),
    );
  });
}

async function isMounted() {
  if (MEDIA_PREMOUNTED) return true;
  if (process.platform !== "linux") return true;
  try {
    const mounts = await fsp.readFile("/proc/mounts", "utf8");
    return mounts
      .split("\n")
      .some(
        (line) => line.split(" ")[1] === MEDIA_ROOT.replaceAll(" ", "\\040"),
      );
  } catch {
    return false;
  }
}

async function unmountShare() {
  cancelThumbnailPrewarm();
  currentThumbnailSource = null;
  if (MEDIA_PREMOUNTED || !(await isMounted())) return;
  try {
    await run("umount", [MEDIA_ROOT]);
  } catch (error) {
    // A player, scanner, or container may still have an open file. A lazy
    // unmount detaches the mount immediately and lets existing handles close
    // naturally, so the next SMB mount can use the same mount point.
    if (!/busy|target is busy/i.test(error.message || "")) throw error;
    await run("umount", ["-l", MEDIA_ROOT]);
  }
}

async function mountShare(nextConfig = config) {
  if (MEDIA_PREMOUNTED) return;
  if (process.platform !== "linux")
    throw new Error("SMB 自动挂载仅支持 Linux；开发环境请设置 MEDIA_ROOT");
  if (!/^\/\/[^/]+\/[^/]+/.test(nextConfig.share || ""))
    throw new Error("SMB 地址格式应为 //服务器/共享名");

  await unmountShare();
  const options = [
    nextConfig.deleteMode ? "rw" : "ro",
    "iocharset=utf8",
    `vers=${nextConfig.vers || "3.0"}`,
    "noserverino",
  ];
  if (nextConfig.guest) {
    options.push("guest");
  } else {
    if (!nextConfig.username)
      throw new Error("请填写 SMB 用户名，或启用访客访问");
    const credentialText = `username=${nextConfig.username}\npassword=${nextConfig.password || ""}\n`;
    await fsp.writeFile(CREDENTIALS_FILE, credentialText, { mode: 0o600 });
    await fsp.chmod(CREDENTIALS_FILE, 0o600);
    options.push(`credentials=${CREDENTIALS_FILE}`);
  }
  await run("mount", [
    "-t",
    "cifs",
    nextConfig.share,
    MEDIA_ROOT,
    "-o",
    options.join(","),
  ]);
}

function mountConfigChanged(current, next) {
  return (
    current.share !== next.share ||
    current.username !== next.username ||
    current.password !== next.password ||
    current.vers !== next.vers ||
    current.guest !== next.guest ||
    current.deleteMode !== next.deleteMode
  );
}

async function walkVideos(directory, root = MEDIA_ROOT, output = []) {
  const entries = await fsp.readdir(directory, { withFileTypes: true });
  for (const entry of entries) {
    if (entry.name.startsWith(".")) continue;
    const absolute = path.join(directory, entry.name);
    if (entry.isDirectory()) {
      await walkVideos(absolute, root, output);
    } else if (
      entry.isFile() &&
      VIDEO_EXTENSIONS.has(path.extname(entry.name).toLowerCase())
    ) {
      const stat = await fsp.stat(absolute);
      const relative = path.relative(root, absolute);
      const segments = relative.split(path.sep);
      const libraryName = segments.length > 1 ? segments[0] : "全部视频";
      const ext = path.extname(entry.name).toLowerCase().slice(1);
      const id = idFor(relative.replaceAll(path.sep, "/"));
      output.push({
        Id: id,
        Name: path.basename(entry.name, path.extname(entry.name)),
        Overview: relative,
        Path: relative,
        DateCreated: stat.mtime.toISOString(),
        RunTimeTicks: 0,
        Size: stat.size,
        LibraryId: idFor(`library:${libraryName}`),
        LibraryName: libraryName,
        ImageTags: { Primary: id },
        UserData: { IsFavorite: favorites.has(id) },
        MediaSources: [
          {
            Id: id,
            Path: relative,
            Container: ext,
            Size: stat.size,
            VideoCodec: "",
            MediaStreams: [],
          },
        ],
        _absolutePath: absolute,
      });
    }
  }
  return output;
}

async function scanLibrary() {
  if (scanState.scanning) return;
  scanState = { ...scanState, scanning: true, error: "" };
  try {
    const nextItems = await walkVideos(MEDIA_ROOT);
    nextItems.sort((a, b) => b.DateCreated.localeCompare(a.DateCreated));
    items = nextItems;
    itemsById = new Map(items.map((item) => [item.Id, item]));
    const map = new Map();
    for (const item of items)
      map.set(item.LibraryId, {
        Id: item.LibraryId,
        Name: item.LibraryName,
        CollectionType: "homevideos",
      });
    libraries = [...map.values()].sort((a, b) =>
      a.Name.localeCompare(b.Name, "zh-CN"),
    );
    scanState.lastScan = new Date().toISOString();
    try {
      await ensureThumbnailSource();
      scheduleThumbnailPrewarm();
    } catch (error) {
      console.warn(`缩略图缓存初始化失败：${error.message}`);
    }
  } catch (error) {
    scanState.error = error.message;
    throw error;
  } finally {
    scanState.scanning = false;
  }
}

function json(res, status, body) {
  const data = Buffer.from(JSON.stringify(body));
  res.writeHead(status, {
    "Content-Type": "application/json; charset=utf-8",
    "Content-Length": data.length,
    "Cache-Control": "no-store",
  });
  res.end(data);
}

async function readBody(req) {
  const chunks = [];
  let size = 0;
  for await (const chunk of req) {
    size += chunk.length;
    if (size > 1024 * 1024) throw new Error("请求体过大");
    chunks.push(chunk);
  }
  return safeJsonParse(Buffer.concat(chunks).toString("utf8"), {});
}

function publicConfig() {
  return {
    version: APP_VERSION,
    configured: Boolean(config.share || MEDIA_PREMOUNTED),
    adminSettingsEnabled: ADMIN_SETTINGS_ENABLED,
    share: ADMIN_SETTINGS_ENABLED ? config.share || "" : "",
    username: ADMIN_SETTINGS_ENABLED ? config.username || "" : "",
    hasPassword: ADMIN_SETTINGS_ENABLED && Boolean(config.password),
    vers: config.vers || "3.0",
    guest: Boolean(config.guest),
    deleteMode: Boolean(config.deleteMode),
    mounted: MEDIA_PREMOUNTED ? true : undefined,
    itemCount: items.length,
    cacheLimitExceeded: thumbnailCacheLimitExceeded,
    ...scanState,
  };
}

function waitForDrain(stream) {
  return new Promise((resolve, reject) => {
    const cleanup = () => {
      stream.removeListener("drain", onDrain);
      stream.removeListener("error", onError);
      stream.removeListener("close", onClose);
    };
    const onDrain = () => {
      cleanup();
      resolve();
    };
    const onError = (error) => {
      cleanup();
      reject(error);
    };
    const onClose = () => {
      const error = new Error("response closed");
      error.code = "ERR_STREAM_PREMATURE_CLOSE";
      onError(error);
    };
    stream.once("drain", onDrain);
    stream.once("error", onError);
    stream.once("close", onClose);
  });
}

async function pipeVideoRange(
  req,
  res,
  item,
  start,
  end,
  session,
  expectedGeneration,
) {
  let position = start;

  const durationSeconds = Number(item.RunTimeTicks || 0) / 10000000;
  const averageBytesPerSecond = durationSeconds
    ? Number(item.Size || 0) / durationSeconds
    : Number(item.MediaSources?.[0]?.Bitrate || 0) / 8;
  const bytesPerSecond = session
    ? Math.max(
        PLAYBACK_MIN_BYTES_PER_SECOND,
        Math.ceil(averageBytesPerSecond * 1.35),
      )
    : 0;
  const source = fs.createReadStream(item._absolutePath, { start: position, end });
  const stop = () => source.destroy();
  req.once("aborted", stop);
  res.once("close", stop);
  let pacedBytes = 0;
  const burstBytes = averageBytesPerSecond * PLAYBACK_BURST_SECONDS;
  const pacingStarted = Date.now();
  try {
    for await (const chunk of source) {
      if (res.destroyed) break;
      if (session && session.generation !== expectedGeneration) {
        res.destroy();
        break;
      }
      if (bytesPerSecond) {
        pacedBytes += chunk.length;
        const targetElapsed =
          (Math.max(0, pacedBytes - burstBytes) / bytesPerSecond) * 1000;
        const delay = targetElapsed - (Date.now() - pacingStarted);
        if (delay > 1)
          await new Promise((resolve) => setTimeout(resolve, delay));
      }
      if (!res.write(chunk)) await waitForDrain(res);
    }
    if (!res.destroyed) res.end();
  } catch (error) {
    if (!res.destroyed && error.code !== "ERR_STREAM_PREMATURE_CLOSE") throw error;
  } finally {
    req.removeListener("aborted", stop);
  }
}

async function serveVideo(req, res, item, url) {
  const playback = managedPlayback(url, item.Id);
  if (playback.managed && !playback.session)
    return json(res, 409, { error: "播放会话已过期" });
  const session = playback.session;
  const expectedGeneration = session ? playbackGeneration(url) : -1;
  if (session) await probeItem(item);
  if (
    session &&
    (session.generation !== expectedGeneration || item.Id !== session.currentId)
  )
    return json(res, 409, { error: "播放会话已切换" });
  const stat = await fsp.stat(item._absolutePath);
  const size = stat.size;
  const range = req.headers.range;
  const type =
    MIME_TYPES[path.extname(item._absolutePath).toLowerCase()] ||
    "application/octet-stream";
  let start = 0;
  let end = size - 1;
  if (range) {
    const match = /^bytes=(\d*)-(\d*)$/.exec(range);
    if (!match) {
      res.writeHead(416, { "Content-Range": `bytes */${size}` });
      res.end();
      return;
    }
    start = match[1] ? Number(match[1]) : 0;
    end = match[2] ? Math.min(Number(match[2]), size - 1) : size - 1;
  }

  if (start > end || start >= size) {
    res.writeHead(416, { "Content-Range": `bytes */${size}` });
    res.end();
    return;
  }
  registerPlaybackResponse(session, item.Id, res);
  if (!range) {
    res.writeHead(200, {
      "Content-Type": type,
      "Content-Length": end - start + 1,
      "Accept-Ranges": "bytes",
    });
    await pipeVideoRange(
      req,
      res,
      item,
      start,
      end,
      session,
      expectedGeneration,
    );
    return;
  }
  res.writeHead(206, {
    "Content-Type": type,
    "Content-Length": end - start + 1,
    "Content-Range": `bytes ${start}-${end}/${size}`,
    "Accept-Ranges": "bytes",
  });
  await pipeVideoRange(
    req,
    res,
    item,
    start,
    end,
    session,
    expectedGeneration,
  );
}

function redirectToThumbnailPlaceholder(res) {
  if (thumbnailCacheLimitExceeded)
    res.setHeader("X-ShuffleBox-Cache-Limit", "exceeded");
  res.writeHead(302, { Location: "/poster.webp" });
  res.end();
}

async function serveCachedThumbnail(res, context, stat) {
  if (thumbnailCacheLimitExceeded)
    res.setHeader("X-ShuffleBox-Cache-Limit", "exceeded");
  res.writeHead(200, {
    "Content-Type": "image/webp",
    "Content-Length": stat.size,
    "Cache-Control": "public, max-age=2592000",
  });
  const stream = fs.createReadStream(context.paths.target);
  stream.on("error", (error) => {
    if (!res.headersSent) res.destroy(error);
    else res.destroy();
  });
  stream.pipe(res);
}

async function serveThumbnail(res, item) {
  let context;
  try {
    context = await currentThumbnailContext(item);
  } catch {
    redirectToThumbnailPlaceholder(res);
    return;
  }
  if (!context) {
    redirectToThumbnailPlaceholder(res);
    return;
  }
  let stat = await validThumbnail(context);
  if (!stat) {
    const result = await enqueueThumbnailJob(context, "foreground");
    if (result.status !== "generated" && result.status !== "cached") {
      redirectToThumbnailPlaceholder(res);
      return;
    }
    stat = await validThumbnail(context);
  }
  if (!stat) {
    redirectToThumbnailPlaceholder(res);
    return;
  }
  await serveCachedThumbnail(res, context, stat);
}

async function probeItem(item) {
  if (item._probed) return item;
  try {
    const output = await run("ffprobe", [
      "-v",
      "error",
      "-show_entries",
      "format=duration,bit_rate:stream=index,codec_type,codec_name,width,height,avg_frame_rate,bit_rate",
      "-of",
      "json",
      item._absolutePath,
    ]);
    const info = safeJsonParse(output, {});
    const streams = (info.streams || []).map((stream) => ({
      Index: stream.index,
      Type:
        stream.codec_type === "video"
          ? "Video"
          : stream.codec_type === "audio"
            ? "Audio"
            : stream.codec_type,
      Codec: stream.codec_name || "",
      Width: stream.width,
      Height: stream.height,
      AverageFrameRate: stream.avg_frame_rate,
      BitRate: Number(stream.bit_rate || 0),
    }));
    const video = streams.find((stream) => stream.Type === "Video");
    item.RunTimeTicks = Math.round(
      Number(info.format?.duration || 0) * 10000000,
    );
    item.MediaSources[0].MediaStreams = streams;
    item.MediaSources[0].VideoCodec = video?.Codec || "";
    item.MediaSources[0].Bitrate = Number(info.format?.bit_rate || 0);
    item._probed = true;
  } catch (error) {
    console.warn(`ffprobe failed for ${item.Path}: ${error.message}`);
  }
  return item;
}

async function waitForFile(file, timeoutMs = 20000) {
  const started = Date.now();
  while (Date.now() - started < timeoutMs) {
    try {
      await fsp.access(file);
      return;
    } catch {}
    await new Promise((resolve) => setTimeout(resolve, 250));
  }
  throw new Error("转码启动超时");
}

async function ensureHls(item) {
  const directory = path.join(HLS_DIR, item.Id);
  const playlist = path.join(directory, "index.m3u8");
  if (hlsJobs.has(item.Id)) touchHlsJob(item.Id);
  try {
    await fsp.access(playlist);
    return playlist;
  } catch {}
  if (!hlsJobs.has(item.Id)) {
    await fsp.mkdir(directory, { recursive: true });
    const child = spawn(
      "ffmpeg",
      [
        "-hide_banner",
        "-loglevel",
        "warning",
        "-i",
        item._absolutePath,
        "-map",
        "0:v:0",
        "-map",
        "0:a:0?",
        "-c:v",
        "libx264",
        "-preset",
        "veryfast",
        "-crf",
        "23",
        "-c:a",
        "aac",
        "-ac",
        "2",
        "-b:a",
        "192k",
        "-f",
        "hls",
        "-hls_time",
        "4",
        "-hls_list_size",
        "0",
        "-hls_playlist_type",
        "event",
        "-hls_segment_filename",
        "seg%05d.ts",
        "index.m3u8",
      ],
      { cwd: directory, stdio: ["ignore", "ignore", "pipe"] },
    );
    let errorText = "";
    child.stderr.on("data", (chunk) => {
      errorText = (errorText + chunk).slice(-4000);
    });
    const job = {
      child,
      lastAccess: Date.now(),
      idleTimer: null,
      cleanupOnClose: false,
    };
    child.on("close", (code) => {
      const current = hlsJobs.get(item.Id);
      if (current?.child === child) hlsJobs.delete(item.Id);
      clearTimeout(job.idleTimer);
      if (code !== 0)
        console.error(`HLS transcode failed for ${item.Path}:`, errorText);
      const cleanup = setTimeout(
        () => fsp.rm(directory, { recursive: true, force: true }).catch(() => {}),
        job.cleanupOnClose ? 0 : 60 * 60 * 1000,
      );
      cleanup.unref();
    });
    child.on("error", (error) => {
      const current = hlsJobs.get(item.Id);
      if (current?.child === child) hlsJobs.delete(item.Id);
      clearTimeout(job.idleTimer);
      console.error(error);
    });
    hlsJobs.set(item.Id, job);
    touchHlsJob(item.Id);
  }
  await waitForFile(playlist);
  return playlist;
}

// Do not orphan CPU-heavy ffmpeg children when the service is restarted.
for (const signal of ["SIGTERM", "SIGINT"]) {
  process.on(signal, () => {
    for (const itemId of [...hlsJobs.keys()]) stopHlsJob(itemId, signal);
    for (const job of thumbnailJobs.values()) stopThumbnailJob(job);
    process.exit(0);
  });
}

async function serveFile(res, file, contentType, cache = "no-cache") {
  const stat = await fsp.stat(file);
  res.writeHead(200, {
    "Content-Type": contentType,
    "Content-Length": stat.size,
    "Cache-Control": cache,
  });
  fs.createReadStream(file).pipe(res);
}

function filteredItems(url) {
  let result = [...items];
  const ids = url.searchParams.get("Ids");
  const parentId = url.searchParams.get("ParentId");
  if (ids) {
    const wanted = new Set(ids.split(","));
    result = result.filter((item) => wanted.has(item.Id));
  }
  if (parentId) {
    // ParentId accepts a comma-separated list so clients can combine media sources.
    const parentIds = new Set(parentId.split(",").filter(Boolean));
    result = result.filter((item) => parentIds.has(item.LibraryId));
  }
  if (url.searchParams.get("Filters") === "IsFavorite")
    result = result.filter((item) => favorites.has(item.Id));
  if ((url.searchParams.get("SortBy") || "").toLowerCase() === "random") {
    // Emit at most one item from each active directory per round. This keeps
    // every prefix (especially the first page) balanced and avoids streaks.
    let collapsedRoots = [];
    try {
      collapsedRoots = JSON.parse(url.searchParams.get("RandomGroups") || "[]")
        .filter((value) => typeof value === "string")
        .map((value) => value.replaceAll("\\\\", "/").replace(/^\/+|\/+$/g, ""));
    } catch {}
    const groupKey = (item) => {
      const directory = path.posix.dirname(item.Path.replaceAll("\\\\", "/"));
      const matchingRoot = collapsedRoots
        .filter((root) => directory === root || directory.startsWith(`${root}/`))
        .sort((a, b) => b.length - a.length)[0];
      return matchingRoot || (directory === "." ? "" : directory);
    };
    const requestedSeed = String(url.searchParams.get("RandomSeed") || "").slice(0, 256);
    const seed = requestedSeed || crypto.randomUUID();
    result = balancedRandomize(result, groupKey, seededRandomInt(seed));
  } else if ((url.searchParams.get("SortBy") || "").toLowerCase() === "path") {
    result.sort((a, b) =>
      a.Path.localeCompare(b.Path, "zh-CN", { numeric: true }),
    );
  }
  return result;
}

function mediaTree() {
  const roots = new Map();
  for (const item of items) {
    const segments = item.Path.replaceAll("\\\\", "/").split("/");
    const library = segments.shift() || "全部视频";
    if (!roots.has(item.LibraryId))
      roots.set(item.LibraryId, {
        id: item.LibraryId,
        name: library,
        path: library === "全部视频" ? "" : library,
        children: new Map(),
        count: 0,
      });
    let node = roots.get(item.LibraryId);
    node.count += 1;
    let currentPath = node.path;
    for (const segment of segments.slice(0, -1)) {
      currentPath = currentPath ? `${currentPath}/${segment}` : segment;
      if (!node.children.has(segment))
        node.children.set(segment, { name: segment, path: currentPath, children: new Map(), count: 0 });
      node = node.children.get(segment);
      node.count += 1;
    }
  }
  const serialize = (node) => ({
    id: node.id,
    name: node.name,
    path: node.path,
    count: node.count,
    children: [...node.children.values()].sort((a, b) => a.name.localeCompare(b.name, "zh-CN")).map(serialize),
  });
  return [...roots.values()].sort((a, b) => a.name.localeCompare(b.name, "zh-CN")).map(serialize);
}

async function handleApi(req, res, url) {
  if (url.pathname === "/api/playback/session" && req.method === "PUT") {
    const body = await readBody(req);
    const sessionId = String(body.sessionId || "");
    const generation = Number(body.generation);
    const currentId = String(body.currentId || "");
    if (!/^[A-Za-z0-9_.:-]{1,128}$/.test(sessionId))
      return json(res, 400, { error: "无效的播放会话" });
    if (!Number.isSafeInteger(generation) || generation < 0)
      return json(res, 400, { error: "无效的播放代次" });
    if (!itemsById.has(currentId))
      return json(res, 404, { error: "当前视频不存在" });
    const session = updatePlaybackSession(
      sessionId,
      generation,
      currentId,
    );
    if (!session) return json(res, 409, { error: "播放会话代次已过期" });
    return json(res, 200, {
      sessionId,
      generation,
      currentId: session.currentId,
    });
  }
  if (url.pathname === "/api/tags" && req.method === "GET") {
    const itemId = String(url.searchParams.get("itemId") || "");
    const item = itemsById.get(itemId);
    return json(res, 200, {
      tags,
      selected: item ? (videoTags.get(item.Path) || []) : [],
    });
  }
  if (url.pathname === "/api/tags" && req.method === "POST") {
    const body = await readBody(req);
    const name = normalizeTag(body.name);
    if (!name) return json(res, 400, { error: "标签名称不能为空，且不能包含逗号或换行" });
    if (!tags.includes(name)) {
      tags.push(name);
      await saveTags();
    }
    return json(res, 201, { name, tags });
  }
  if (url.pathname === "/api/tags/video" && req.method === "PUT") {
    const body = await readBody(req);
    const item = itemsById.get(String(body.itemId || ""));
    if (!item) return json(res, 404, { error: "视频不存在" });
    const assigned = normalizeTags(body.tags).filter((name) => tags.includes(name));
    if (assigned.length) videoTags.set(item.Path, assigned);
    else videoTags.delete(item.Path);
    await saveVideoTags();
    return json(res, 200, { selected: assigned });
  }
  if (url.pathname === "/api/status" && req.method === "GET") {
    return json(res, 200, { ...publicConfig(), mounted: await isMounted() });
  }
  if (url.pathname === "/api/media/tree" && req.method === "GET")
    return json(res, 200, { Items: mediaTree() });
  if (url.pathname === "/api/media/preferences" && req.method === "GET")
    return json(res, 200, mediaPreferences);
  if (url.pathname === "/api/media/preferences" && req.method === "PUT") {
    const body = await readBody(req);
    return json(res, 200, await saveMediaPreferences(body));
  }
  if (url.pathname === "/api/smb/config" && req.method === "GET")
    return json(res, 200, publicConfig());
  if (url.pathname === "/api/smb/config" && req.method === "POST") {
    if (!ADMIN_SETTINGS_ENABLED)
      return json(res, 403, { error: "SMB 管理设置已被管理员隐藏" });
    const body = await readBody(req);
    const next = {
      share: String(body.share || "")
        .trim()
        .replace(/\\/g, "/"),
      username: String(body.username || "").trim(),
      password:
        body.password === "********"
          ? config.password
          : String(body.password || ""),
      vers: String(body.vers || "3.0"),
      guest: Boolean(body.guest),
      deleteMode: Boolean(body.deleteMode),
    };
    // UI-only preferences are submitted with this request too. Reusing an
    // unchanged mount avoids unmounting a share while a video is being read.
    const remountRequired = mountConfigChanged(config, next);
    const needsMount = remountRequired || !(await isMounted());
    if (needsMount) await mountShare(next);
    config = next;
    await fsp.writeFile(CONFIG_FILE, JSON.stringify(config, null, 2), {
      mode: 0o600,
    });
    if (needsMount || items.length === 0) await scanLibrary();
    // A new SMB share has different library identifiers; do not carry a stale
    // selection into it.
    if (remountRequired) await saveMediaPreferences({});
    return json(res, 200, publicConfig());
  }
  if (url.pathname === "/api/smb/config" && req.method === "DELETE") {
    if (!ADMIN_SETTINGS_ENABLED)
      return json(res, 403, { error: "清除挂载状态已被管理员禁用" });
    await unmountShare();
    config = {
      share: "",
      username: "",
      password: "",
      vers: "3.0",
      guest: false,
      deleteMode: false,
    };
    items = [];
    itemsById = new Map();
    libraries = [];
    await fsp.rm(CONFIG_FILE, { force: true });
    await fsp.rm(CREDENTIALS_FILE, { force: true });
    await fsp.rm(MEDIA_PREFERENCES_FILE, { force: true });
    mediaPreferences = { libraryId: "", libraryType: "library", collapsedGroupPaths: [] };
    return json(res, 200, publicConfig());
  }
  if (url.pathname === "/api/rescan" && req.method === "POST") {
    await scanLibrary();
    return json(res, 200, publicConfig());
  }
  return false;
}

async function handleCompatibleApi(req, res, url) {
  const pathname = url.pathname;
  if (
    /\/emby\/Users\/[^/]+\/Items$/.test(pathname) &&
    url.searchParams.get("IncludeItemTypes") === "Playlist"
  )
    return json(res, 200, { Items: [] });
  if (/\/emby\/Users\/[^/]+\/Items$/.test(pathname) && req.method === "GET") {
    const result = filteredItems(url);
    const total = result.length;
    const start = Math.max(0, Number(url.searchParams.get("StartIndex") || 0));
    const limit = url.searchParams.has("Limit")
      ? Math.max(1, Number(url.searchParams.get("Limit")))
      : Math.max(1, result.length);
    const page = result.slice(start, start + limit).map((item) => ({
      ...item,
      _absolutePath: undefined,
      UserData: { IsFavorite: favorites.has(item.Id) },
    }));
    return json(res, 200, {
      Items: page,
      TotalRecordCount: total,
      StartIndex: start,
    });
  }
  const detail = pathname.match(/\/emby\/Users\/[^/]+\/Items\/([^/]+)$/);
  if (detail && req.method === "GET") {
    const item = itemsById.get(detail[1]);
    if (!item) return json(res, 404, { error: "视频不存在" });
    await probeItem(item);
    return json(res, 200, {
      ...item,
      _absolutePath: undefined,
      _probed: undefined,
      UserData: { IsFavorite: favorites.has(item.Id) },
    });
  }
  if (/\/emby\/Users\/[^/]+\/Views$/.test(pathname) && req.method === "GET")
    return json(res, 200, {
      Items: libraries,
      TotalRecordCount: libraries.length,
    });
  const favorite = pathname.match(
    /\/emby\/Users\/[^/]+\/FavoriteItems\/([^/]+)$/,
  );
  if (favorite && (req.method === "POST" || req.method === "DELETE")) {
    if (req.method === "POST") favorites.add(favorite[1]);
    else favorites.delete(favorite[1]);
    const item = itemsById.get(favorite[1]);
    if (item) item.UserData.IsFavorite = req.method === "POST";
    await saveFavorites();
    res.writeHead(204);
    res.end();
    return true;
  }
  const hlsMaster = pathname.match(/\/emby\/Videos\/([^/]+)\/master\.m3u8$/);
  if (hlsMaster && req.method === "GET") {
    const item = itemsById.get(hlsMaster[1]);
    if (!item) return json(res, 404, { error: "视频不存在" });
    const playback = managedPlayback(url, item.Id);
    if (playback.managed && !playback.session)
      return json(res, 409, { error: "播放会话已过期" });
    const playlist = await ensureHls(item);
    const raw = await fsp.readFile(playlist, "utf8");
    const playbackQuery = playback.session
      ? `?PlaybackControlId=${encodeURIComponent(playback.session.id)}&PlaybackGeneration=${playback.session.generation}`
      : "";
    const rewritten = raw.replace(
      /^(seg\d+\.ts)$/gm,
      `/emby/Videos/${item.Id}/hls/$1${playbackQuery}`,
    );
    const data = Buffer.from(rewritten);
    res.writeHead(200, {
      "Content-Type": "application/vnd.apple.mpegurl",
      "Content-Length": data.length,
      "Cache-Control": "no-cache",
    });
    res.end(data);
    return true;
  }
  const hlsSegment = pathname.match(
    /\/emby\/Videos\/([^/]+)\/hls\/(seg\d+\.ts)$/,
  );
  if (hlsSegment && req.method === "GET") {
    if (!itemsById.has(hlsSegment[1]))
      return json(res, 404, { error: "视频不存在" });
    const playback = managedPlayback(url, hlsSegment[1]);
    if (playback.managed && !playback.session)
      return json(res, 409, { error: "播放会话已过期" });
    const file = path.join(HLS_DIR, hlsSegment[1], hlsSegment[2]);
    touchHlsJob(hlsSegment[1]);
    await serveFile(res, file, "video/mp2t", "public, max-age=3600");
    return true;
  }
  const stream = pathname.match(/\/emby\/Videos\/([^/]+)\/stream(?:\.[^/]+)?$/);
  if (stream && req.method === "GET") {
    const item = itemsById.get(stream[1]);
    if (!item) return json(res, 404, { error: "视频不存在" });
    await serveVideo(req, res, item, url);
    return true;
  }
  const image = pathname.match(/\/emby\/Items\/([^/]+)\/Images\/Primary$/);
  if (image && req.method === "GET") {
    const item = itemsById.get(image[1]);
    if (!item) return json(res, 404, { error: "视频不存在" });
    await serveThumbnail(res, item);
    return true;
  }
  const remove = pathname.match(/\/emby\/Items\/([^/]+)$/);
  if (remove && req.method === "DELETE") {
    if (!ADMIN_SETTINGS_ENABLED || !config.deleteMode)
      return json(res, 403, { error: "媒体删除功能未启用" });
    const item = itemsById.get(remove[1]);
    if (!item) return json(res, 404, { error: "视频不存在" });
    await fsp.unlink(item._absolutePath);
    favorites.delete(item.Id);
    await saveFavorites();
    if (videoTags.delete(item.Path)) await saveVideoTags();
    await scanLibrary();
    res.writeHead(204);
    res.end();
    return true;
  }
  if (pathname.startsWith("/emby/Sessions/") && req.method === "POST") {
    res.writeHead(204);
    res.end();
    return true;
  }
  return false;
}

async function serveStatic(res, url) {
  const requested = decodeURIComponent(
    url.pathname === "/" ? "/index.html" : url.pathname,
  );
  const target = path.resolve(STATIC_ROOT, `.${requested}`);
  if (!target.startsWith(STATIC_ROOT + path.sep) && target !== STATIC_ROOT)
    return json(res, 403, { error: "Forbidden" });
  let file = target;
  try {
    if ((await fsp.stat(file)).isDirectory())
      file = path.join(file, "index.html");
  } catch {
    file = path.join(STATIC_ROOT, "index.html");
  }
  const stat = await fsp.stat(file);
  res.writeHead(200, {
    "Content-Type":
      MIME_TYPES[path.extname(file).toLowerCase()] ||
      "application/octet-stream",
    "Content-Length": stat.size,
    "Cache-Control":
      ["index.html", "sw.js"].includes(path.basename(file))
        ? "no-cache, no-store, must-revalidate"
        : "public, max-age=3600",
  });
  fs.createReadStream(file).pipe(res);
}

async function requestHandler(req, res) {
  const url = new URL(req.url, `http://${req.headers.host || "localhost"}`);
  try {
    if (url.pathname.startsWith("/api/")) {
      const handled = await handleApi(req, res, url);
      if (handled !== false) return;
    }
    if (url.pathname.startsWith("/emby/")) {
      const handled = await handleCompatibleApi(req, res, url);
      if (handled !== false) return;
    }
    await serveStatic(res, url);
  } catch (error) {
    console.error(req.method, url.pathname, error);
    if (!res.headersSent)
      json(res, 500, { error: error.message || "服务器内部错误" });
    else res.destroy(error);
  }
}

loadState()
  .then(async () => {
    try {
      if (config.share && !(await isMounted())) await mountShare(config);
      if (config.share || MEDIA_PREMOUNTED) await scanLibrary();
    } catch (error) {
      scanState.error = error.message;
      console.error("Startup mount/scan failed:", error.message);
    }
    http.createServer(requestHandler).listen(PORT, "0.0.0.0", () => {
      console.log(
        `ShuffleBox SMB listening on http://0.0.0.0:${PORT} (${items.length} videos)`,
      );
    });
  })
  .catch((error) => {
    console.error(error);
    process.exit(1);
  });
