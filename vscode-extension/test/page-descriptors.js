// Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
// Mostly AI-generated test code; see CONTRIBUTING.md, "AI policy".
//
// Run the page script (SFLMeta/editor-links.js) over a built chapter page in
// headless Chrome and print, as JSON, what clicking each element would send
// (the description, plus in `uri` the link the page would open for it):
//
//   node vscode-extension/test/page-descriptors.js _out/lf/student/html/Basics/index.html > d.json
//
// The page is copied to a temporary file with the script and a collector
// injected (so the copy works whether or not the build already includes the
// script), and with <base> pointed back at the real book root.
'use strict';

const fs = require('fs');
const os = require('os');
const path = require('path');
const { execFileSync } = require('child_process');

const CHROME = process.env.CHROME
  || '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';

function main() {
  const page = path.resolve(process.argv[2] || '');
  if (!fs.existsSync(page)) {
    console.error('usage: node page-descriptors.js <built chapter index.html>');
    process.exit(2);
  }
  const script = fs.readFileSync(path.join(__dirname, '..', '..', 'SFLMeta', 'editor-links.js'), 'utf8');
  const root = path.dirname(path.dirname(page)) + '/';
  let html = fs.readFileSync(page, 'utf8');
  html = html.replace(/<base href="[^"]*">/, `<base href="file://${encodeURI(root)}">`);
  const collector = `
    window.addEventListener('load', function () {
      var L = window.sflEditorLinks, out = [];
      document.querySelectorAll('main').forEach(function (main) {
        main.querySelectorAll(L.TARGETS).forEach(function (el) {
          if (el.closest(L.EXCLUDE)) return;
          var d = L.describe(el);
          d.uri = L.uriFor({ vol: 'lf', chapter: 'Test' }, d);
          d.tag = el.tagName.toLowerCase();
          out.push(d);
        });
      });
      var pre = document.createElement('pre');
      pre.id = 'sfl-test-out';
      pre.textContent = JSON.stringify(out);
      document.body.appendChild(pre);
    });`;
  html = html.replace('</head>', `<script>${script}</script><script>${collector}</script></head>`);
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'sfl-page-'));
  const tmp = path.join(dir, 'page.html');
  fs.writeFileSync(tmp, html);
  try {
    const dom = execFileSync(CHROME, [
      '--headless', '--disable-gpu', '--allow-file-access-from-files',
      '--virtual-time-budget=20000', '--dump-dom', 'file://' + tmp,
    ], { maxBuffer: 1 << 30, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
    const m = /<pre id="sfl-test-out">([\s\S]*?)<\/pre>/.exec(dom);
    if (!m) throw new Error('collector output not found in the dumped DOM');
    const json = m[1].replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"')
      .replace(/&#39;/g, "'").replace(/&nbsp;/g, ' ').replace(/&amp;/g, '&');
    process.stdout.write(json + '\n');
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

main();
