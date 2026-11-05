// Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
// Mostly AI-generated test code; see CONTRIBUTING.md, "AI policy".
//
// Runs inside a throwaway VS Code instance started by vscode-smoke.sh (as its
// --extensionTestsPath).  Drives the extension through the same entry point a
// vscode: link reaches, with payloads taken from a real chapter page
// (page-descriptors.js output), and writes a report to $SFL_TEST_OUT.
'use strict';

const vscode = require('vscode');
const fs = require('fs');
const path = require('path');
const { locate, words } = require('../locate');

function payloadQuery(obj) {
  return 'd=' + Buffer.from(JSON.stringify(obj), 'utf8').toString('base64url');
}

async function run() {
  const out = [];
  const log = (s) => out.push(s);
  let failures = 0;
  const check = (ok, what) => {
    log(`${ok ? 'ok  ' : 'FAIL'} ${what}`);
    if (!ok) failures++;
  };
  try {
    const ext = vscode.extensions.getExtension('plclub.sf-in-lean');
    check(!!ext, 'extension is present');
    const api = await ext.activate();
    const root = vscode.workspace.workspaceFolders[0].uri.fsPath;
    const vol = process.env.SFL_TEST_VOL;
    const chapter = process.env.SFL_TEST_CHAPTER;
    const file = path.join(root, vol.toUpperCase(), `${chapter}.lean`);
    const text = fs.readFileSync(file, 'utf8');
    const descs = JSON.parse(fs.readFileSync(process.env.SFL_TEST_DESCRIPTORS, 'utf8'));

    // A spread of elements: the first of each tag, then every 37th.
    const picks = [];
    const seen = new Set();
    descs.forEach((d, i) => {
      if (!seen.has(d.tag) || i % 37 === 0) picks.push(d);
      seen.add(d.tag);
    });
    for (const d of picks) {
      const payload = Object.assign({ v: 1, vol, chapter }, d);
      const r = await api.handleQuery(payloadQuery(payload));
      const editor = vscode.window.activeTextEditor;
      const expected = locate(text, d).line;
      // Visible ranges catch up with revealRange asynchronously.
      const shown = () => editor.visibleRanges.some((v) => v.contains(editor.selection.active));
      for (let i = 0; editor && i < 40 && !shown(); i++) await new Promise((res) => setTimeout(res, 25));
      const ok = r && editor && editor.document.uri.fsPath === file
        && editor.selection.active.line === expected && shown();
      const lineText = editor ? editor.document.lineAt(editor.selection.active.line).text : '';
      const first = words(d.text || d.headings[d.headings.length - 1] || '')[0] || '';
      check(ok && lineText.toLowerCase().includes(first),
        `${d.tag} -> line ${expected + 1} (${r && r.how}): "${lineText.trim().slice(0, 70)}"`);
    }

    // The file already open in another editor group is revealed there.
    await vscode.commands.executeCommand('workbench.action.splitEditorRight');
    await vscode.commands.executeCommand('workbench.action.focusFirstEditorGroup');
    await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    const second = Object.assign({ v: 1, vol, chapter }, picks[picks.length - 1]);
    await api.handleQuery(payloadQuery(second));
    const tabs = vscode.window.tabGroups.all.flatMap((g) => g.tabs)
      .filter((t) => t.input instanceof vscode.TabInputText && t.input.uri.fsPath === file);
    check(tabs.length === 1, `file open in exactly one tab (found ${tabs.length})`);

    // Malformed or hostile payloads open nothing.
    await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    const bad = [
      'd=not*base64',
      payloadQuery({ v: 1, vol: 'lf', chapter: '../../etc/passwd' }),
      payloadQuery({ v: 1, vol: '../x', chapter: 'Basics' }),
      payloadQuery({ v: 2, vol: 'lf', chapter: 'Basics' }),
    ];
    for (const q of bad) {
      const r = await api.handleQuery(q);
      check(r === null && !vscode.window.activeTextEditor, `rejected ${q.slice(0, 40)}`);
    }
  } catch (e) {
    check(false, `exception: ${e && e.stack ? e.stack : e}`);
  }
  log(failures === 0 ? 'PASS' : `${failures} FAILED`);
  fs.writeFileSync(process.env.SFL_TEST_OUT, out.join('\n') + '\n');
}

module.exports = { run };
