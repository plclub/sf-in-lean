// Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
// Mostly AI-generated test code; see CONTRIBUTING.md, "AI policy".
//
// Check locate.js against a chapter file, using the descriptors printed by
// page-descriptors.js:
//
//   node vscode-extension/test/check-locate.js d.json _out/lf/student/lean/LF/Basics.lean [-v]
//
// Reports how each element was found (its own words, only its heading, or
// nothing) and how many found lines go backwards relative to the previous
// element in page order -- a sign of a wrong match, since the HTML and the
// file present the chapter in the same order.  -v lists the problem cases.
'use strict';

const fs = require('fs');
const { locate } = require('../locate');

function main() {
  const [descFile, leanFile, flag] = process.argv.slice(2);
  if (!descFile || !leanFile) {
    console.error('usage: node check-locate.js <descriptors.json> <chapter.lean> [-v]');
    process.exit(2);
  }
  const verbose = flag === '-v';
  const descs = JSON.parse(fs.readFileSync(descFile, 'utf8'));
  const text = fs.readFileSync(leanFile, 'utf8');
  const lines = text.split(/\r?\n/);
  const counts = { text: 0, near: 0, heading: 0, none: 0 };
  let headingMissed = 0;
  let backwards = 0;
  let prev = 0;
  const problems = [];
  let badUris = 0;
  for (const d of descs) {
    // The link must carry the description intact (the page's base64url of
    // UTF-8 JSON, decoded as extension.js does).
    if (d.uri) {
      const m = /[?&]d=([A-Za-z0-9_-]+)$/.exec(d.uri);
      const back = m && JSON.parse(Buffer.from(m[1], 'base64url').toString('utf8'));
      if (!back || ['headings', 'kind', 'text', 'prev', 'next']
        .some((k) => JSON.stringify(back[k]) !== JSON.stringify(d[k]))) badUris++;
    }
    const r = locate(text, d);
    const wantedText = d.kind !== 'heading' && d.text;
    const how = wantedText ? r.how : (r.how === 'none' ? 'none' : 'heading');
    counts[how]++;
    let problem = null;
    if (wantedText && r.how !== 'text') problem = `only ${r.how}`;
    if (!wantedText && r.how === 'none') { headingMissed++; problem = 'heading not found'; }
    if (r.line < prev - 1) { backwards++; problem = problem || `backwards from ${prev + 1}`; }
    prev = Math.max(prev, r.line);
    if (problem) problems.push({ problem, line: r.line + 1, d, at: (lines[r.line] || '').trim() });
  }
  const total = descs.length;
  const textWanted = descs.filter((d) => d.kind !== 'heading' && d.text).length;
  console.log(`${leanFile}: ${total} elements; ` +
    `${counts.text}/${textWanted} found by their words, ${counts.near} near; ` +
    `${headingMissed} headings not found; ${backwards} backwards` +
    (badUris ? `; ${badUris} LINKS DO NOT DECODE` : ''));
  if (verbose) {
    for (const p of problems) {
      console.log(`  [${p.problem}] line ${p.line}: ${p.d.tag} ${JSON.stringify(p.d.headings.slice(-1))} ` +
        `"${p.d.text}"\n      -> ${p.at.slice(0, 100)}`);
    }
  }
}

main();
