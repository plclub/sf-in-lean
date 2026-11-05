// Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
// Mostly AI-generated test code; see CONTRIBUTING.md, "AI policy".
//
// Exercise the buttons on a built chapter page in headless Chrome:
//
//   node vscode-extension/test/page-ui.js _out/lf/student/html/Logic/index.html
//
// The page must come from a build that includes the script.  A copy of it,
// with a test script added, is written next to it (so that the chapter and
// <base> resolve exactly as for the real page) and removed afterwards.  The
// test replaces sflEditorLinks.navigate, so no vscode: link is launched.
'use strict';

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

const CHROME = process.env.CHROME
  || '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';

const TEST = `
window.addEventListener('load', function () { setTimeout(function () {
  var L = window.sflEditorLinks, res = {}, launched = [];
  L.navigate = function (u) { launched.push(u); };
  var btn = document.querySelector('.sfl-editor-link');
  res.oneButton = document.querySelectorAll('.sfl-editor-link').length === 1;
  res.context = L.pageContext();
  function hover(el) { el.dispatchEvent(new MouseEvent('mouseover', { bubbles: true })); }
  var p = document.querySelectorAll('main section > p')[4];
  hover(p);
  res.shownOnParagraph = btn.style.display === 'block';
  var r = p.getBoundingClientRect();
  res.besideParagraph = Math.abs(parseFloat(btn.style.top) - (r.top + window.scrollY)) < 1;
  btn.click();
  res.paragraphLink = launched[0] === L.uriFor(L.pageContext(), L.describe(p));
  var code = document.querySelector('main code.hl.lean.block');
  hover(code.querySelector('span') || code);
  btn.click();
  res.codeLink = launched[1] === L.uriFor(L.pageContext(), L.describe(code));
  var h = document.querySelectorAll('main section > h2')[1];
  hover(h.firstChild && h.firstChild.nodeType === 1 ? h.firstChild : h);
  btn.click();
  res.headingLink = launched[2] === L.uriFor(L.pageContext(), L.describe(h));
  res.preferSource = JSON.parse(atob(launched[0].split('d=')[1].replace(/-/g, '+').replace(/_/g, '/'))).prefer === 'source';
  res.noNoteYet = !document.querySelector('.sfl-editor-note');
  setTimeout(function () {
    var note = document.querySelector('.sfl-editor-note');
    res.noteAfterDelay = !!note;
    if (note) note.querySelectorAll('button')[0].click();  // "hide these buttons"
    res.hiddenAfterHide = !document.querySelector('.sfl-editor-link')
      && localStorage.getItem('sfl-editor-links') === 'off';
    var pre = document.createElement('pre');
    pre.id = 'sfl-test-out';
    pre.textContent = JSON.stringify(res);
    document.body.appendChild(pre);
  }, 3500);
}, 0); });`;

function main() {
  const page = path.resolve(process.argv[2] || '');
  if (!fs.existsSync(page)) {
    console.error('usage: node page-ui.js <built chapter index.html>');
    process.exit(2);
  }
  const html = fs.readFileSync(page, 'utf8');
  if (!html.includes('sfl-editor-links.js')) {
    console.error('this page was built without the editor-links script');
    process.exit(2);
  }
  // Without the navigate hook, a simulated click would launch a real link.
  const shipped = path.join(path.dirname(path.dirname(page)), '-verso-data', 'sfl-editor-links.js');
  if (!fs.readFileSync(shipped, 'utf8').includes('api.navigate(uri)')) {
    console.error(`${shipped} predates the navigate hook; rebuild the book first`);
    process.exit(2);
  }
  const tmp = path.join(path.dirname(page), 'sfl-ui-test.html');
  fs.writeFileSync(tmp, html.replace('</body>', `<script>${TEST}</script></body>`));
  try {
    const dom = execFileSync(CHROME, [
      '--headless', '--disable-gpu', '--allow-file-access-from-files',
      '--virtual-time-budget=30000', '--dump-dom', 'file://' + tmp,
    ], { maxBuffer: 1 << 30, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
    const m = /<pre id="sfl-test-out">([\s\S]*?)<\/pre>/.exec(dom);
    if (!m) throw new Error('test output not found in the dumped DOM');
    const res = JSON.parse(m[1].replace(/&quot;/g, '"').replace(/&amp;/g, '&'));
    let failed = 0;
    for (const [k, v] of Object.entries(res)) {
      const ok = k === 'context' ? !!v : v === true;
      if (!ok) failed++;
      console.log(`${ok ? 'ok  ' : 'FAIL'} ${k}${k === 'context' ? ' ' + JSON.stringify(v) : ''}`);
    }
    console.log(failed ? `${failed} FAILED` : 'PASS');
    process.exitCode = failed ? 1 : 0;
  } finally {
    fs.rmSync(tmp, { force: true });
  }
}

main();
