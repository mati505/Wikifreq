const API = "https://en.wikipedia.org/w/api.php";
const MAX_GUESSES = 5;
const MAX_HINTS = 2;
const HINT_COST = 50;
const HINT_REVEAL_RATIO = 0.6;  // share of letters shown in a hint
const ROUND_END_DELAY = 1400;   // ms to let the last point animation play
const PAGEVIEW_DAYS = 30;
const MAX_CANDIDATES = 150;     // article candidates checked per round
const MAX_CATEGORIES = 40;      // category pages scanned per title refill
const MAX_DEPTH = 2;            // how far down subcategories to walk
const MAX_TITLES = 400;         // stop scanning once this many titles are found
const CHECK_BATCH = 3;          // candidates checked at the same time

// Difficulty presets. Each one sets how popular and how long an article must be.
const DIFFICULTY = {
  easy:   { minViews: 300, minWords: 500 },
  normal: { minViews: 50,  minWords: 300 },
  hard:   { minViews: 20,  minWords: 200 }
};

// Categories that skip the popularity check.
const BYPASS_POPULARITY = ["science", "history", "trending"];

// Each category's source pages. Film merges two category trees.
// "good" is used by the random option in Classic mode.
const CATEGORY_PAGES = {
  good: "Category:Good articles",
  music: "Category:Music",
  film: ["Category:Films", "Category:Television series"],
  videogames: "Category:Video games",
  science: "Category:Science",
  history: "Category:History",
  geography: "Category:Geography",
  sports: "Category:Sports",
  transport: "Category:Transport",
  food: "Category:Food and drink",
  trending: "top"   // placeholder; titles come from the daily top-views list
};

// How often each option appears in Classic mode. "random" picks from Good articles.
// Set a weight to 0 to remove that option.
const ALL_WEIGHTS = {
  music: 3,
  film: 2,
  videogames: 2,
  science: 3,
  history: 3,
  geography: 3,
  sports: 3,
  random: 2,
  transport: 2,
  food: 3
};

// Descriptions shown on the category buttons. Keys must match the select's values.
const CATEGORY_INFO = {
  all:        { label: "Classic",      desc: "The original way to play. A mix of every category, weighted by taste." },
  music:      { label: "Music",        desc: "Bands, albums, songs, and some musicians." },
  film:       { label: "Film & TV",    desc: "Movies and TV series." },
  videogames: { label: "Video games",  desc: "Games, consoles, and studios." },
  science:    { label: "Science",      desc: "Concepts, theories, research and discoveries that transformed the world." },
  history:    { label: "History",      desc: "Empires, eras, and historical events." },
  geography:  { label: "Geography",    desc: "Places, regions, and landscapes." },
  sports:     { label: "Sports",       desc: "Teams, leagues, competitions and terms." },
  food:       { label: "Food & drink", desc: "Dishes, ingredients, and drinks." },
  trending:   { label: "Trending",     desc: "Most read Wikipedia articles this week. Short, but beginner friendly." }
};

// Descriptions shown on the difficulty buttons.
const DIFFICULTY_INFO = {
  easy:   { label: "Easy",   desc: "Well-known, longer articles." },
  normal: { label: "Normal", desc: "A balanced mix." },
  hard:   { label: "Hard",   desc: "Obscure, shorter articles." }
};

// Common words, excluded from counting and never scored.
const STOP = new Set(`a an and are as at be been but by can for from had has have he her
his i if in into is it its of on or our she so than that the their them then there these
they this to was we were what when which who will with you your not no do does did
about also after all any been being both each few more most other over same some such
only own just now would could should may might while where why how up down out off`.split(/\s+/));

// Generic words that apply to every round.
const GENERIC_ALL = `first new time year years later made used called known including
also one two three many several part parts people world became begun`.split(/\s+/);

// Generic words for each category, on top of STOP and GENERIC_ALL.
const CATEGORY_GENERIC = {
  music: `song songs album albums band bands singer singers music track tracks single
singles record records release released musician musicians group groups live lyrics
chart charts tour`.split(/\s+/),
  film: `film films movie movies actor actors actress scene scenes director role roles
cast release released story character characters screen plot episode episodes season
seasons series show shows television tv`.split(/\s+/),
  videogames: `game games player players level levels release released developer developed
version mode console consoles gameplay character characters`.split(/\s+/),
  science: `study studies research theory data process system method methods results
scientist scientists field experiment experiments`.split(/\s+/),
  history: `war wars king kings century centuries empire period state states government
era history`.split(/\s+/),
  geography: `region regions area areas located population town towns north south east west
km miles`.split(/\s+/),
  transport: `vehicle vehicles transport transports transportation service services route routes
network networks system systems operated operate operates operating built build builds
construction travel travels traveled traveling passenger passengers
carry carried carries design designed manufacturer manufactured model models speed capacity
km miles`.split(/\s+/),
  sports: `team teams season seasons player players match matches league club
coach win won played playing championship`.split(/\s+/),
  food: `dish dishes food foods cook cooked cooking recipe recipes serve served serving
eat eaten made make common popular traditional style flavor flavour ingredient ingredients`.split(/\s+/)
};

// Headings for sections that hold citations and links rather than article prose.
const SOURCE_HEADINGS = /^(references|sources|notes|footnotes|citations|works cited|bibliography|further reading|external links)$/i;

// Saved walk state per category, so each refill continues where the last one stopped.
const walks = {};
const pools = {};
const popularityCache = new Map();
const personCache = new Map();

// Every article used this session, across all categories, so nothing repeats.
const usedTitles = new Set();

let categoryBag = [];
let roundId = 0;             // increments on each new round or menu press, so stale loads are discarded
let pointsBank = 0;
let savedDifficulty = null;  // remembered for the session once picked in Classic

const board = [];
let lastEntry = null;
let state = null;

const $ = id => document.getElementById(id);
const words = text => text.toLowerCase().match(/\p{L}+/gu) || [];

// Fisher-Yates shuffle, returns a new shuffled array.
function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

// Points by how often the word family appears in the article. Rarer = more points.
function pointsFor(n) {
  if (n <= 1) return 100;
  if (n === 2) return 50;
  if (n === 3) return 30;
  if (n <= 5) return 20;
  return 10;
}

function updatePointsBank() {
  $("bank").textContent = `Points bank: ${pointsBank}`;
}

// ---------- Small UI helpers ----------

// Restarts a CSS animation on an element, even if it was already played.
function animate(el, cls) {
  el.classList.remove(cls);
  void el.offsetWidth;  // forces a reflow so the animation restarts
  el.classList.add(cls);
}

function setMsg(text) {
  $("msg").textContent = text;
  animate($("msg"), "fade-in");
}

function setTitle(text) {
  $("title").textContent = text;
  animate($("title"), "fade-in");
}

function setScore(value) {
  $("score").textContent = value;
  animate($("score"), "bump");
}

// Shows a message and shakes the input, for guesses that can't be used.
function reject(text) {
  setMsg(text);
  animate($("guess"), "shake");
}

// Switches between the start, game, and results screens.
function showScreen(name) {
  ["start", "game", "results"].forEach(s => { $(s).hidden = s !== name; });
}

// Shows the loading panel with a message and progress (0 to 1).
function showLoading(text, fraction = 0) {
  $("loading").hidden = false;
  $("loading-text").textContent = text;
  $("bar-fill").style.width = `${Math.min(100, Math.round(fraction * 100))}%`;
}

function hideLoading() {
  $("loading").hidden = true;
}

// Five placeholder rows, so the table shows the open slots from the start.
function resetTable() {
  $("guesses").innerHTML = Array.from({ length: MAX_GUESSES }, (_, i) =>
    `<tr class="empty"><td class="muted">Guess ${i + 1}</td><td>—</td><td>—</td></tr>`
  ).join("");
}

// Fills one of the placeholder rows with a guess result.
function fillRow(slot, word, occurrences, pts, note) {
  const tr = $("guesses").children[slot];
  tr.className = "pop-in";
  tr.innerHTML = `<td></td><td>${occurrences}</td><td class="pts">${pts}${note ? ` <span class="muted">(${note})</span>` : ""}</td>`;
  tr.firstChild.textContent = word;
  if (pts > 0) tr.querySelector(".pts").classList.add("pts-good");
}

// Swaps the Start button for the difficulty buttons, and back.
function showDifficulty(show) {
  $("difficulty-section").hidden = !show;
  $("start-btn").hidden = show;
}

// ---------- Text processing ----------

// Porter stemmer (Martin Porter's 1980 algorithm). Groups related words into
// one stem: "educate", "educator", "education", "educating" -> "educ";
// "ship" and "shipping" -> "ship"; "shipment" stays "shipment".
function stem(word) {
  let s = word.toLowerCase();
  if (s.length <= 2) return s;

  const isCons = (str, i) => {
    const c = str[i];
    if ("aeiou".includes(c)) return false;
    if (c === "y") return i === 0 ? true : !isCons(str, i - 1);
    return true;
  };
  // m = number of vowel-consonant sequences in the stem
  const measure = str => {
    let m = 0, i = 0;
    const n = str.length;
    while (i < n && isCons(str, i)) i++;
    while (i < n) {
      while (i < n && !isCons(str, i)) i++;
      if (i >= n) break;
      while (i < n && isCons(str, i)) i++;
      m++;
    }
    return m;
  };
  const hasVowel = str => { for (let i = 0; i < str.length; i++) if (!isCons(str, i)) return true; return false; };
  const endsDoubleCons = str => str.length >= 2 && str[str.length - 1] === str[str.length - 2] && isCons(str, str.length - 1);
  const endsCvc = str => {
    const n = str.length;
    return n >= 3 && isCons(str, n - 3) && !isCons(str, n - 2) && isCons(str, n - 1) && !"wxy".includes(str[n - 1]);
  };
  // Applies the longest matching suffix rule, but only if the stem's measure exceeds minM.
  const applyRules = (str, rules, minM) => {
    const match = [...rules].sort((a, b) => b[0].length - a[0].length).find(([suf]) => str.endsWith(suf));
    if (!match) return str;
    const base = str.slice(0, -match[0].length);
    return measure(base) > minM ? base + match[1] : str;
  };

  // Step 1a
  if (s.endsWith("sses")) s = s.slice(0, -2);
  else if (s.endsWith("ies")) s = s.slice(0, -2);
  else if (s.endsWith("ss")) { /* keep */ }
  else if (s.endsWith("s")) s = s.slice(0, -1);

  // Step 1b
  let extra = false;
  if (s.endsWith("eed")) {
    if (measure(s.slice(0, -3)) > 0) s = s.slice(0, -1);
  } else if (s.endsWith("ed") && hasVowel(s.slice(0, -2))) {
    s = s.slice(0, -2); extra = true;
  } else if (s.endsWith("ing") && hasVowel(s.slice(0, -3))) {
    s = s.slice(0, -3); extra = true;
  }
  if (extra) {
    if (s.endsWith("at") || s.endsWith("bl") || s.endsWith("iz")) s += "e";
    else if (endsDoubleCons(s) && !"lsz".includes(s[s.length - 1])) s = s.slice(0, -1);
    else if (measure(s) === 1 && endsCvc(s)) s += "e";
  }

  // Step 1c
  if (s.endsWith("y") && hasVowel(s.slice(0, -1))) s = s.slice(0, -1) + "i";

  // Step 2
  s = applyRules(s, [
    ["ational", "ate"], ["tional", "tion"], ["enci", "ence"], ["anci", "ance"],
    ["izer", "ize"], ["abli", "able"], ["alli", "al"], ["entli", "ent"], ["eli", "e"],
    ["ousli", "ous"], ["ization", "ize"], ["ation", "ate"], ["ator", "ate"],
    ["alism", "al"], ["iveness", "ive"], ["fulness", "ful"], ["ousness", "ous"],
    ["aliti", "al"], ["iviti", "ive"], ["biliti", "ble"], ["logi", "log"]
  ], 0);

  // Step 3
  s = applyRules(s, [
    ["icate", "ic"], ["ative", ""], ["alize", "al"], ["iciti", "ic"],
    ["ical", "ic"], ["ful", ""], ["ness", ""]
  ], 0);

  // Step 4
  s = applyRules(s, [
    ["al", ""], ["ance", ""], ["ence", ""], ["er", ""], ["ic", ""], ["able", ""],
    ["ible", ""], ["ant", ""], ["ement", ""], ["ment", ""], ["ent", ""], ["ou", ""],
    ["ism", ""], ["ate", ""], ["iti", ""], ["ous", ""], ["ive", ""], ["ize", ""]
  ], 1);
  if (s.endsWith("ion")) {
    const base = s.slice(0, -3);
    if (measure(base) > 1 && (base.endsWith("s") || base.endsWith("t"))) s = base;
  }

  // Step 5a
  if (s.endsWith("e")) {
    const base = s.slice(0, -1);
    if (measure(base) > 1 || (measure(base) === 1 && !endsCvc(base))) s = base;
  }

  // Step 5b
  if (measure(s) > 1 && endsDoubleCons(s) && s.endsWith("l")) s = s.slice(0, -1);

  return s;
}

// Removes section headings like "== References ==" from the plain text.
const cleanText = text => text.replace(/^=+.*?=+\s*$/gm, "");

// Removes source sections (references, bibliography, etc.), including nested subsections.
function cutSourceSections(text) {
  const out = [];
  let skipLevel = null;

  for (const line of text.split("\n")) {
    const m = line.match(/^(=+)\s*(.*?)\s*=+\s*$/);
    if (m) {
      const level = m[1].length;
      // A heading at the same or a higher level ends the skipped section.
      if (skipLevel !== null && level <= skipLevel) skipLevel = null;
      if (skipLevel === null && SOURCE_HEADINGS.test(m[2])) {
        skipLevel = level;
        continue;
      }
    }
    if (skipLevel === null) out.push(line);
  }
  return out.join("\n");
}

// ---------- Loading articles ----------

// JSONP: loads the API through a <script> tag, which avoids the fetch/CORS
// restrictions that block requests from local files and preview panes.
function jsonp(params) {
  return new Promise((resolve, reject) => {
    const cb = "wg_" + Math.random().toString(36).slice(2);
    const script = document.createElement("script");
    const cleanup = () => { delete window[cb]; script.remove(); };
    const timer = setTimeout(() => { cleanup(); reject(new Error("Wikipedia took too long to respond.")); }, 15000);
    window[cb] = data => { clearTimeout(timer); cleanup(); resolve(data); };
    script.onerror = () => { clearTimeout(timer); cleanup(); reject(new Error("Couldn't reach Wikipedia.")); };
    const query = new URLSearchParams({ ...params, format: "json", callback: cb });
    script.src = `${API}?${query}`;
    document.head.appendChild(script);
  });
}

// Retries on 429 and 5xx with exponential backoff. Returns null for 404.
async function fetchJSONWithRetry(url, retries = 3) {
  for (let i = 0; i < retries; i++) {
    const res = await fetch(url);
    if (res.status === 404) return null;
    if (res.ok) return res.json();
    if (res.status === 429 || res.status >= 500) {
      await new Promise(r => setTimeout(r, 1000 * 2 ** i));
      continue;
    }
    throw new Error(`HTTP ${res.status}`);
  }
  throw new Error("Wikimedia is rate-limiting requests.");
}

// Returns the most-viewed English Wikipedia articles from a recent day.
// Looks back a few days, since the daily list isn't available for the last day or two.
async function fetchTopTitles() {
  for (let back = 3; back <= 6; back++) {
    const d = new Date();
    d.setUTCDate(d.getUTCDate() - back);
    const path = [
      d.getUTCFullYear(),
      String(d.getUTCMonth() + 1).padStart(2, "0"),
      String(d.getUTCDate()).padStart(2, "0")
    ].join("/");

    const data = await fetchJSONWithRetry(
      `https://wikimedia.org/api/rest_v1/metrics/pageviews/top/en.wikipedia.org/all-access/${path}`
    );
    const articles = data?.items?.[0]?.articles || [];
    const titles = articles
      .map(a => a.article.replace(/_/g, " "))
      .filter(t => !/^(Main Page|Special:|Wikipedia:|Portal:|List of |Deaths in |Category:)/.test(t))
      .slice(0, 200);

    if (titles.length > 0) return titles;
  }
  return [];
}

// Returns the saved walk for a category, creating it with shuffled starting points if needed.
function getWalk(key) {
  if (!walks[key]) {
    const roots = shuffle([CATEGORY_PAGES[key]].flat());
    walks[key] = { queue: roots.map(cat => ({ cat, depth: 0 })), seen: new Set() };
  }
  return walks[key];
}

// Walks each category's subcategories (breadth-first, up to MAX_DEPTH, in shuffled
// order) and collects article titles. Each call continues the saved walk.
async function loadTitles(key, onProgress = () => {}) {
  if (key === "trending") {
    onProgress("Loading today's most-read articles…", 0.5);
    return fetchTopTitles();
  }
  if (!CATEGORY_PAGES[key]) throw new Error(`No category set up for "${key}"`);

  let walk = getWalk(key);
  if (walk.queue.length === 0) {
    delete walks[key];
    walk = getWalk(key);
  }

  const titles = new Set();
  let requests = 0;

  while (walk.queue.length && requests < MAX_CATEGORIES && titles.size < MAX_TITLES) {
    const { cat, depth } = walk.queue.shift();
    if (walk.seen.has(cat)) continue;
    walk.seen.add(cat);
    requests++;

    onProgress(
      `Scanning categories… ${walk.seen.size} done, ${titles.size} articles found`,
      0.5 * requests / MAX_CATEGORIES
    );

    const data = await jsonp({
      action: "query",
      list: "categorymembers",
      cmtitle: cat,
      cmtype: "page|subcat",
      cmlimit: "500"
    });
    if (data.error) {
      console.warn(`Wikipedia API error for ${cat}:`, data.error.info);
      continue;
    }

    for (const m of shuffle(data.query?.categorymembers || [])) {
      if (m.ns === 14) {
        if (depth < MAX_DEPTH) walk.queue.push({ cat: m.title, depth: depth + 1 });
      } else {
        titles.add(m.title);
      }
    }
  }

  return [...titles];
}

// Returns the average daily views over the window. Cached per title.
async function averageViews(title) {
  if (popularityCache.has(title)) return popularityCache.get(title);

  const end = new Date();
  end.setUTCDate(end.getUTCDate() - 2);
  const start = new Date(end);
  start.setUTCDate(start.getUTCDate() - (PAGEVIEW_DAYS - 1));
  const fmt = d => d.toISOString().slice(0, 10).replace(/-/g, "");

  const url =
    `https://wikimedia.org/api/rest_v1/metrics/pageviews/per-article/` +
    `en.wikipedia.org/all-access/user/` +
    `${encodeURIComponent(title.replace(/ /g, "_"))}/daily/` +
    `${fmt(start)}/${fmt(end)}`;

  const data = await fetchJSONWithRetry(url);
  const items = data?.items || [];
  const avg = items.length > 0
    ? items.reduce((sum, d) => sum + d.views, 0) / items.length
    : 0;

  popularityCache.set(title, avg);
  return avg;
}

// True if the article's Wikidata item is an instance of human (Q5). Cached per title.
async function isIndividualPerson(title) {
  if (personCache.has(title)) return personCache.get(title);

  const data = await jsonp({
    action: "query",
    prop: "pageprops",
    ppprop: "wikibase_item",
    titles: title
  });
  const page = Object.values(data.query?.pages || {})[0];
  const id = page?.pageprops?.wikibase_item;

  let result = false;
  if (id) {
    const res = await fetchJSONWithRetry(
      `https://www.wikidata.org/w/api.php?` +
      new URLSearchParams({
        action: "wbgetentities", ids: id, props: "claims", format: "json", origin: "*"
      })
    );
    const entity = res?.entities?.[id];
    result = (entity?.claims?.P31 || []).some(c =>
      c.mainsnak?.datavalue?.value?.id === "Q5"
    );
  }

  personCache.set(title, result);
  return result;
}

// Runs every check for one candidate. Returns { ok: true, ... } or { ok: false, reason }.
async function checkCandidate(key, title, level) {
  const data = await jsonp({
    action: "query", prop: "extracts", explaintext: "1", titles: title
  });
  const page = Object.values(data.query?.pages || {})[0];
  const body = cutSourceSections(page?.extract || "");

  if (words(body).length < level.minWords) return { ok: false, reason: "short" };

  if (!BYPASS_POPULARITY.includes(key)) {
    const views = await averageViews(page.title);
    if (views < level.minViews) return { ok: false, reason: "unpopular" };
  }
  if (await isIndividualPerson(page.title)) return { ok: false, reason: "person" };

  return { ok: true, requested: title, title: page.title, text: cleanText(body) };
}

// Finds an article that passes the difficulty settings. Checks a few candidates
// at once, and returns the first that passes. The rest go back into the pool.
async function fetchArticle(key, onProgress = () => {}, level = DIFFICULTY.normal) {
  const pool = (pools[key] ||= []);
  const rejected = { short: 0, unpopular: 0, person: 0, error: 0 };
  const maxCandidates = level.minViews >= 300 ? 400 : MAX_CANDIDATES;
  let attempts = 0;
  let emptyLoads = 0;

  while (attempts < maxCandidates) {
    if (pool.length === 0) {
      const titles = await loadTitles(key, onProgress);
      const fresh = titles.filter(t => !usedTitles.has(t));
      pool.push(...fresh);
      if (fresh.length < 10 && ++emptyLoads >= 3) break;
      if (pool.length === 0) continue;
    }

    // Take up to CHECK_BATCH unused titles out of the pool.
    const batch = [];
    while (batch.length < CHECK_BATCH && pool.length > 0) {
      const i = Math.floor(Math.random() * pool.length);
      const [title] = pool.splice(i, 1);
      if (!usedTitles.has(title)) batch.push(title);
    }
    if (batch.length === 0) continue;

    attempts += batch.length;
    onProgress("Checking articles…", 0.5 + 0.5 * attempts / maxCandidates);

    // allSettled means one failed request doesn't cancel the others.
    const results = await Promise.allSettled(
      batch.map(title => checkCandidate(key, title, level))
    );

    let winner = null;
    results.forEach((r, idx) => {
      if (r.status === "rejected") {
        rejected.error++;
        console.warn("Candidate check failed:", batch[idx], r.reason);
      } else if (!r.value.ok) {
        rejected[r.value.reason]++;
      } else if (!winner) {
        winner = r.value;
      }
    });

    if (winner) {
      usedTitles.add(winner.title);
      usedTitles.add(winner.requested);
      // Other candidates in this batch go back into the pool for later rounds.
      pool.push(...batch.filter(t => t !== winner.requested));
      return { title: winner.title, text: winner.text };
    }

    // Nothing passed, so return the whole batch to the pool.
    pool.push(...batch);

    if (rejected.error >= 8) {
      throw new Error("Wikipedia is rate-limiting requests. Wait a minute and try again.");
    }
  }

  console.log(`No article found in "${key}" after ${attempts} candidates (budget ${maxCandidates}):`, rejected);
  throw new Error("Couldn't find a popular article. Try another category.");
}

// ---------- Category selection ----------

// Returns the next category for Classic mode from a weighted, shuffled bag. Every
// option appears in proportion to its weight before any repeats, and the same
// option never comes up twice in a row. "random" resolves to Good articles.
function nextCategory() {
  if (categoryBag.length === 0) {
    categoryBag = Object.entries(ALL_WEIGHTS)
      .filter(([, w]) => w > 0)
      .flatMap(([cat, w]) => Array(w).fill(cat));

    // Reshuffle until no option appears twice in a row. Gives up after 100 tries.
    for (let attempt = 0; attempt < 100; attempt++) {
      categoryBag = shuffle(categoryBag);
      const clean = categoryBag.every((c, i) => i === 0 || c !== categoryBag[i - 1]);
      if (clean) break;
    }
  }

  const pick = categoryBag.pop();
  return pick === "random" ? "good" : pick;
}

// Builds one full-width button per option. Clicking a button sets the hidden
// select's value, then calls onPick with the chosen value.
function buildPickList(selectId, listId, info, onPick = () => {}) {
  const select = $(selectId);
  const box = $(listId);
  box.innerHTML = "";

  for (const opt of select.options) {
    const meta = info[opt.value] || { label: opt.textContent, desc: "" };

    const btn = document.createElement("button");
    btn.type = "button";
    btn.className = "pick";
    btn.dataset.value = opt.value;

    const strong = document.createElement("strong");
    strong.textContent = meta.label;
    const small = document.createElement("small");
    small.textContent = meta.desc;
    btn.append(strong, small);

    btn.addEventListener("click", () => {
      select.value = opt.value;
      box.querySelectorAll(".pick").forEach(b => b.classList.toggle("selected", b === btn));
      onPick(opt.value);
    });
    box.appendChild(btn);
  }

  box.querySelectorAll(".pick").forEach(b =>
    b.classList.toggle("selected", b.dataset.value === select.value)
  );
}

// ---------- Building the round ----------

// Counts each exact word in the article. Stopwords are skipped.
function buildCounts(text) {
  const counts = new Map();
  for (const w of words(text)) {
    if (w.length < 2 || STOP.has(w)) continue;
    counts.set(w, (counts.get(w) || 0) + 1);
  }
  return counts;
}

// Groups the article's own words by stem. A guess only links to words that
// actually appear in this article.
function buildStemIndex(counts) {
  const index = new Map();
  for (const w of counts.keys()) {
    const s = stem(w);
    if (!index.has(s)) index.set(s, []);
    index.get(s).push(w);
  }
  return index;
}

function refreshButtons() {
  const active = !!state && !state.done && state.left > 0;
  $("guess").disabled = !active;
  $("submit").disabled = !active;
  $("end").disabled = !active;
  $("hint").textContent =
    `Buy hint (${HINT_COST} bank points, ${MAX_HINTS - (state?.hintsUsed || 0)} left)`;
  $("hint").disabled =
    !active ||
    state.hintsUsed >= MAX_HINTS ||
    pointsBank < HINT_COST;
  if (active) $("guess").focus();
}

// Starts a round: shows the game screen, loads an article, and resets the table.
async function startRound() {
  const myRound = ++roundId;
  state = null;
  refreshButtons();
  showScreen("game");
  showLoading("Finding an article…", 0);
  setTitle("Loading...");
  setMsg("");
  resetTable();
  $("left").textContent = MAX_GUESSES;
  setScore(0);

  let key = $("category").value;
  const isAll = key === "all";

  // Classic uses the saved difficulty. Specific categories always use Normal.
  const level = isAll
    ? (DIFFICULTY[savedDifficulty] || DIFFICULTY.normal)
    : DIFFICULTY.normal;

  if (isAll) key = nextCategory();
  delete walks[key];   // each round starts from a new, shuffled point in the tree

  try {
    const article = await fetchArticle(key, showLoading, level);
    if (myRound !== roundId) return;   // the player left or restarted during the load

    hideLoading();

    const counts = buildCounts(article.text);
    // Same rule whether the category was picked directly or through Classic:
    // basic stopwords, shared generic words, and the list for the article's category.
    const genericWords = [...STOP, ...GENERIC_ALL, ...(CATEGORY_GENERIC[key] || [])];

    state = {
      title: article.title,
      counts,
      stemIndex: buildStemIndex(counts),
      titleSet: new Set(words(article.title)),
      generic: new Set(genericWords.map(stem)),
      scored: new Set(),
      tried: new Set(),
      hinted: new Set(),
      hintsUsed: 0,
      used: 0,
      left: MAX_GUESSES,
      score: 0,
      done: false
    };

    setTitle(article.title);
    refreshButtons();
  } catch (err) {
    if (myRound !== roundId) return;
    hideLoading();
    showResults({ heading: "Couldn't load an article", message: err.message, retryable: true });
  }
}

// Start button: Classic asks for a difficulty first (unless one is saved),
// and any other category starts right away.
function onStartPressed() {
  if ($("category").value === "all" && !savedDifficulty) {
    showDifficulty(true);
    return;
  }
  startRound();
}

// ---------- Leaderboard and results ----------

function pushBoard(entry) {
  board.push(entry);
  board.sort((a, b) => b.score - a.score);
  lastEntry = entry;
}

function renderBoard() {
  $("board").innerHTML = "";
  board.forEach((entry, i) => {
    const tr = document.createElement("tr");
    if (entry === lastEntry) tr.className = "pop-in";
    tr.innerHTML = `<td>${i + 1}</td><td></td><td>${entry.score}</td>`;
    tr.children[1].textContent = entry.title + (entry.skipped ? " (ended early)" : "");
    $("board").appendChild(tr);
  });
  lastEntry = null;
}

// Shows the results screen with the full leaderboard and a link to the article.
// Safe to call with no article loaded.
function showResults({ heading, message, retryable = false }) {
  const link = $("article-link");
  if (state?.title) {
    link.href = `https://en.wikipedia.org/wiki/${encodeURIComponent(state.title.replace(/ /g, "_"))}`;
    link.hidden = false;
  } else {
    link.hidden = true;
  }
  $("results-heading").textContent = heading;
  $("results-msg").textContent = message;
  animate($("results-msg"), "fade-in");
  $("continue").textContent = retryable ? "Try again" : "Continue";
  renderBoard();
  showScreen("results");
}

// Ends the round, records the score, and shows the results screen.
// skipped = true when the player ended the article before using all guesses.
function endRound(skipped = false) {
  if (!state || state.done) return;

  state.done = true;
  state.left = 0;
  pointsBank += state.score;
  updatePointsBank();

  pushBoard({ title: state.title, score: state.score, skipped });

  showResults({
    heading: skipped ? "Article ended" : "Round over",
    message: skipped
      ? `You earned ${state.score} points.`
      : `You scored ${state.score} points.`
  });
}

// ---------- Scoring ----------

// Works out how a guess scores. Only article words are considered.
// Returns { repeat: true } if the guess matches an already-scored word.
function scoreGuess(raw) {
  const s = stem(raw);

  // Words in the title never score.
  if (state.titleSet.has(raw) ||
      state.titleSet.has(s) ||
      [...state.titleSet].some(w => stem(w) === s)) {
    return { pts: 0, occ: "–", note: "in title", msg: `"${raw}" is in the title, so it doesn't score.` };
  }

  const matches = state.stemIndex.get(s) || [];
  const scorable = matches.filter(w => !state.titleSet.has(w));

  if (matches.length === 0) {
    return { pts: 0, occ: 0, note: "not in article", msg: `"${raw}" isn't in the article.` };
  }
  if (scorable.length === 0) {
    return { pts: 0, occ: "–", note: "in title", msg: `"${raw}" is in the title, so it doesn't score.` };
  }
  if (state.generic.has(s)) {
    return { pts: 0, occ: "–", note: "too generic", msg: `"${raw}": too generic` };
  }
  if (scorable.some(w => state.scored.has(w))) {
    return { repeat: true };
  }

  const n = scorable.reduce((sum, w) => sum + state.counts.get(w), 0);
  const pts = pointsFor(n);
  return { pts, occ: n, note: "", msg: `"${raw}" scores ${pts}!`, mark: scorable };
}

function useGuess(raw, result) {
  if (result.mark) result.mark.forEach(w => state.scored.add(w));

  const slot = state.used++;
  state.left--;
  state.score += result.pts;
  $("left").textContent = state.left;
  fillRow(slot, raw, result.occ, result.pts, result.note);
  setScore(state.score);
  setMsg(result.msg);
  $("guess").value = "";

  if (state.left === 0) {
    // Lock input now, then move to the results once the last point has shown.
    refreshButtons();
    setTimeout(() => endRound(), ROUND_END_DELAY);
  } else {
    refreshButtons();
  }
}

// ---------- Hints ----------

// Reveals a share of the word's letters, rounded up, so longer words show more.
// Short words still show at least one letter.
function maskWord(word) {
  const shown = Math.max(1, Math.ceil(word.length * HINT_REVEAL_RATIO));
  const hidden = word.length - shown;
  const blanks = Array(hidden).fill("_").join(" ");
  return `${word.slice(0, shown).toUpperCase()} ${blanks}`;
}

// Finds a word that would score the maximum (it appears exactly once) and hasn't
// been scored, hinted, or excluded by the title or generic rules.
function pickHintWord() {
  const options = [];

  for (const [s, forms] of state.stemIndex) {
    if (state.generic.has(s)) continue;

    const scorable = forms.filter(w => !state.titleSet.has(w));
    if (scorable.length === 0) continue;
    if (scorable.some(w => state.scored.has(w))) continue;

    const total = scorable.reduce((sum, w) => sum + state.counts.get(w), 0);
    if (total !== 1) continue;

    const word = scorable[0];
    if (state.hinted.has(word)) continue;

    options.push(word);
  }

  return options.length > 0
    ? options[Math.floor(Math.random() * options.length)]
    : null;
}

// ---------- Setup and events ----------

// Picking a category hides any open difficulty buttons.
buildPickList("category", "category-list", CATEGORY_INFO, () => showDifficulty(false));

// Picking a difficulty remembers it and starts the game.
buildPickList("difficulty", "difficulty-list", DIFFICULTY_INFO, value => {
  savedDifficulty = value;
  showDifficulty(false);
  startRound();
});

$("start-btn").addEventListener("click", onStartPressed);

$("continue").addEventListener("click", () => {
  showScreen("start");
  onStartPressed();
});

$("menu").addEventListener("click", () => {
  roundId++;               // cancels any in-flight load
  hideLoading();
  state = null;
  refreshButtons();
  setMsg("");
  showScreen("start");
});

$("guessForm").addEventListener("submit", e => {
  e.preventDefault();
  if (!state || state.done || state.left === 0) return;

  // Case doesn't matter.
  const raw = $("guess").value.trim().toLowerCase();

  if (!/^\p{L}+$/u.test(raw)) {
    reject("Enter one word, letters only.");
    return;
  }
  if (state.tried.has(raw)) {
    reject(`You already guessed "${raw}".`);
    $("guess").value = "";
    return;
  }
  state.tried.add(raw);

  const result = scoreGuess(raw);
  if (result.repeat) {
    reject(`"${raw}" is the same word as one you already guessed.`);
    $("guess").value = "";
    return;
  }
  useGuess(raw, result);
});

$("hint").addEventListener("click", () => {
  if (!state || state.done || state.left === 0 || state.hintsUsed >= MAX_HINTS) return;

  if (pointsBank < HINT_COST) {
    setMsg("Not enough banked points to buy a hint!");
    return;
  }

  const word = pickHintWord();
  if (!word) {
    setMsg(`No ${pointsFor(1)}-point words left to hint at!`);
    return;
  }

  // Charge the points bank, NOT the current round score.
  pointsBank -= HINT_COST;
  updatePointsBank();

  state.hinted.add(word);
  state.hintsUsed++;

  setMsg(`Hint (worth ${pointsFor(1)} points): ${maskWord(word)}`);
  refreshButtons();
});

$("end").addEventListener("click", () => {
  if (!state || state.done || state.left === 0) return;
  endRound(true);
});

// Start on the rules screen.
showScreen("start");
refreshButtons();
