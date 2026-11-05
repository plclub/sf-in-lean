// Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
// Mostly AI-generated prototype code; see CONTRIBUTING.md, "AI policy".
//
// Find the line of a chapter file that a click in the HTML book refers to.
// No VS Code dependency, so that test/check-locate.js can run it under Node.
//
// The page (SFLMeta/editor-links.js) sends the titles of the sections
// enclosing the clicked element, outermost first, and the first dozen words
// of its text.  Both kinds of chapter file contain the same words:
//
//   * an extracted copy (what readers have) carries headings as `--  ## Title`
//     and prose as `--` comments re-wrapped at 75 columns;
//   * a Verso source carries headings as `## Title` and prose as Markdown,
//     with extra words from roles such as {name}`foo`.
//
// So the search compares only words (letters, digits, `_`; case-folded),
// ignoring line breaks, punctuation, and comment markers, and tolerates a few
// extra words in the file between the ones it is looking for.  Searching by
// content rather than by line number keeps it right after the reader has
// edited the file (filled-in exercises, say).
'use strict';

const WORD = /[\p{L}\p{N}_]+/gu;
const HEADING = /^\s*(?:--\s*)?(#{1,6})\s+(\S.*?)\s*$/;
const DOC_TITLE = /^#doc\s*\([^)]*\)\s*"(.*)"/;  // a Verso source's chapter title
const GAP = 4;           // extra file words allowed between two snippet words
const ANCHOR_WORDS = 3;  // a match must start at one of the first few words
const PREFIX_WORDS = 5;

function words(s) {
  return (s.match(WORD) || []).map((w) => w.toLowerCase());
}

function index(text) {
  const lines = text.split(/\r?\n/);
  const toks = [];
  const tokLine = [];
  const headings = [];
  lines.forEach((line, i) => {
    const h = HEADING.exec(line);
    const t = h ? null : DOC_TITLE.exec(line);
    if (h) headings.push({ line: i, level: h[1].length, words: titleWords(h[2]), tok: toks.length });
    else if (t) headings.push({ line: i, level: 1, words: titleWords(t[1]), tok: toks.length });
    for (const w of words(line)) {
      toks.push(w);
      tokLine.push(i);
    }
  });
  return { toks, tokLine, headings };
}

// A heading's words, without Verso role markup: `{tactic}` in
// "Using {tactic}`cases` on Expressions" is not part of the title the page shows.
function titleWords(title) {
  return words(title.replace(/\{[^}]*\}/g, ' '));
}

// Is `have` (a heading in the file) the title `want` (from the page)?  An
// exact match, or -- when `fuzzy` -- one sharing two-thirds of the longer
// title's words, for a heading reworded since the page was built
// ("Behavior" -> "Behavioral").
function sameTitle(have, want, fuzzy) {
  if (want.length === 0) return false;
  if (have.length === want.length && have.every((w, i) => w === want[i])) return true;
  if (!fuzzy) return false;
  const pool = new Set(have);
  const common = want.filter((w) => pool.has(w)).length;
  return want.length >= 2 && common / Math.max(have.length, want.length) >= 0.66;
}

// The first heading at or after line `from` titled `title`: exact if any,
// else fuzzy.
function findHeading(ix, title, from) {
  const want = words(title);
  return ix.headings.find((x) => x.line >= from && sameTitle(x.words, want, false))
    || ix.headings.find((x) => x.line >= from && sameTitle(x.words, want, true));
}

// The best in-order match of `snip` starting in toks[start, end): for each
// start position whose word is one of the first ANCHOR_WORDS snippet words,
// greedily match the remaining snippet words, each within GAP words of the
// previous match, skipping snippet words that do not occur.  A match scores
// the number of words matched, less the number of leading snippet words it
// skipped.  Returns the earliest best-scoring match, if it matched enough:
// most of the snippet, or its first PREFIX_WORDS words without a skip (in a
// Verso source, an exercise's solution replaces the `sorry` the page shows,
// so only the start of the code agrees).
function bestMatch(ix, snip, start, end) {
  if (snip.length === 0) return null;
  const need = Math.max(Math.min(snip.length, 2), Math.ceil(snip.length * 0.6));
  const anchors = snip.slice(0, ANCHOR_WORDS);
  let best = null;
  for (let s = Math.max(0, start); s < end; s++) {
    const j0 = anchors.indexOf(ix.toks[s]);
    if (j0 < 0) continue;
    let k = s + 1;
    let matched = 1;
    let prefix = j0 === 0 ? 1 : 0;
    for (let j = j0 + 1; j < snip.length; j++) {
      const lim = Math.min(ix.toks.length, k + GAP + 1);
      let found = false;
      for (let m = k; m < lim; m++) {
        if (ix.toks[m] === snip[j]) {
          matched++;
          k = m + 1;
          found = true;
          break;
        }
      }
      if (found && prefix === j) prefix++;
    }
    const score = matched - j0;
    const enough = matched >= need || prefix >= Math.min(PREFIX_WORDS, snip.length);
    if (enough && (!best || score > best.score)) {
      best = { score, tok: s, end: k, line: ix.tokLine[s] };
      if (score === snip.length) break;
    }
  }
  return best;
}

// `d` = { headings: [title, ...], kind: 'heading' | 'text', text: 'first words' }.
// Returns { line (0-based), how }, where `how` says what was found:
//   'text'    -- the element's own words;
//   'near'    -- not its words, but the elements before it;
//   'heading' -- only its innermost enclosing heading that the file has;
//   'none'    -- nothing; line 0.
function locate(fileText, d) {
  const ix = index(fileText);

  // Walk down the chain of section titles.  A title the file lacks (e.g. the
  // chapter title, which a Verso source gives in `#doc` rather than as a
  // `#` heading) is skipped rather than ending the walk.
  let from = 0;
  let section = null;
  for (const title of d.headings || []) {
    const h = findHeading(ix, title, from);
    if (h) {
      from = h.line + 1;
      section = h;
    }
  }
  const fallback = section ? { line: section.line, how: 'heading' } : { line: 0, how: 'none' };
  if (d.kind === 'heading' || !d.text) return fallback;

  // The element's own words, searched for in the region between its
  // section's heading and the heading the page shows next (d.next; the file
  // may have more headings in between, such as exercise titles).  Within the
  // region, first step past the elements that precede the clicked one
  // (d.prev, oldest first), each found after the last; one that cannot be
  // found is skipped.  Then search from there to the end of the region.
  //
  // Some page text is in no chapter file (quiz answers, say), and a partial
  // match is then easy to find somewhere else.  So the search widens -- to
  // anywhere after the heading, then anywhere at all -- only when nothing
  // pins the element down: no preceding element found and the file lacks one
  // of the region's two headings.  Otherwise, if the words are not found,
  // land just after the last preceding element found, or else on the heading.
  const snip = words(d.text);
  const start = section ? section.tok : 0;
  const next = d.next ? findHeading(ix, d.next, section ? section.line + 1 : 0) : null;
  const end = next ? next.tok : ix.toks.length;
  let after = start;
  for (const p of d.prev || []) {
    const m = bestMatch(ix, words(p), after, end);
    if (m) after = m.end;
  }
  const pinned = after > start || (section && next);
  const hit = bestMatch(ix, snip, after, end)
    || (!pinned && bestMatch(ix, snip, start, ix.toks.length))
    || (!pinned && bestMatch(ix, snip, 0, start));
  if (hit) return { line: hit.line, how: 'text' };
  if (after > start && after < ix.toks.length) return { line: ix.tokLine[after], how: 'near' };
  return fallback;
}

module.exports = { locate, words };
