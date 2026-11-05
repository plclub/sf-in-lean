// Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
// Mostly AI-generated prototype code; see CONTRIBUTING.md, "AI policy".
//
// The SF-in-Lean VS Code extension.  Its one job: handle the links that the
// HTML book's "open in editor" buttons send (SFLMeta/editor-links.js),
//
//   vscode://plclub.sf-in-lean/open?d=<base64url JSON>
//
// where the JSON is { v: 1, vol, chapter, headings, kind, text, prev, next,
// prefer? }.  It opens the chapter's file, `<VOL>/<chapter>.lean`, and puts
// the cursor at the clicked spot, which locate.js finds by content.
//
// Which copy of the chapter:
//   * a workspace folder of this window holding an extracted volume (its
//     lakefile.toml says `name = "<vol>-extracted"`; that is what the release
//     zip unpacks to) -- a reader's copy;
//   * a workspace folder holding the SFL development repository (it has
//     SFLMeta/) -- the Verso source; preferred when the link says
//     `prefer: "source"`, which pages of a local build do;
//   * failing both, a folder the reader picked earlier for this volume, or
//     else one they pick now (remembered per volume, in globalState).
//
// Any web page can send such a link, so the handler validates the payload,
// only ever opens `<VOL>/<chapter>.lean` inside one of those folders, and
// never runs anything or edits anything.
'use strict';

const vscode = require('vscode');
const fs = require('fs');
const path = require('path');
const { locate } = require('./locate');

// Reader-facing wording.  PLACEHOLDERS: CONTRIBUTING.md's AI policy requires
// these strings to be written by a human before the extension is published.
const TEXT = {
  badLink: '[placeholder] SF in Lean: this link is not one the extension understands.',
  whereIsCopy: (vol) => `[placeholder] Where is your copy of ${vol.toUpperCase()}? ` +
    'Choose the folder you unpacked from the release zip (it contains lakefile.toml).',
  locate: '[placeholder] Locate…',
  openLabel: '[placeholder] Use this folder',
  notACopy: (folder, rel) => `[placeholder] ${folder} does not look like a copy of the ` +
    `volume: there is no ${rel} in it.`,
  approximate: '[placeholder] SF in Lean: could not find that exact spot; showing the nearest place found.',
  forgotten: '[placeholder] SF in Lean: forgot the remembered folders.',
};

const FLASH_MS = 1500;
const GLOBAL_KEY = (vol) => `folder.${vol}`;

function decodePayload(query) {
  const m = /(?:^|&)d=([A-Za-z0-9_-]+)/.exec(query);
  if (!m) return null;
  try {
    return JSON.parse(Buffer.from(m[1], 'base64url').toString('utf8'));
  } catch (e) {
    return null;
  }
}

function strings(xs, max, len) {
  return Array.isArray(xs)
    ? xs.filter((x) => typeof x === 'string').slice(0, max).map((x) => x.slice(0, len))
    : [];
}

// The payload, checked and trimmed, or null.
function validate(d) {
  if (!d || typeof d !== 'object' || d.v !== 1) return null;
  if (typeof d.vol !== 'string' || !/^[a-z]{1,8}$/.test(d.vol)) return null;
  if (typeof d.chapter !== 'string' || !/^[A-Za-z][A-Za-z0-9_]{0,63}$/.test(d.chapter)) return null;
  return {
    vol: d.vol,
    chapter: d.chapter,
    headings: strings(d.headings, 8, 200),
    kind: d.kind === 'heading' ? 'heading' : 'text',
    text: typeof d.text === 'string' ? d.text.slice(0, 400) : '',
    prev: strings(d.prev, 12, 200),
    next: typeof d.next === 'string' ? d.next.slice(0, 200) : '',
    prefer: d.prefer === 'source' ? 'source' : 'copy',
  };
}

function relFile(d) {
  return path.join(d.vol.toUpperCase(), `${d.chapter}.lean`);
}

function isFile(p) {
  try { return fs.statSync(p).isFile(); } catch (e) { return false; }
}

function isDir(p) {
  try { return fs.statSync(p).isDirectory(); } catch (e) { return false; }
}

function lakePackageName(root) {
  try {
    const m = /^name\s*=\s*"([^"]*)"/m.exec(fs.readFileSync(path.join(root, 'lakefile.toml'), 'utf8'));
    return m ? m[1] : null;
  } catch (e) {
    return null;
  }
}

// What `root` is, as a place to find chapter `d`: { kind, rank, file } or null.
// Lower rank is better: the preferred kind first, an exact volume match
// before another volume's copy that happens to include the chapter.
function classify(root, d) {
  const file = path.join(root, relFile(d));
  if (!isFile(file)) return null;
  if (isDir(path.join(root, 'SFLMeta'))) {
    return { kind: 'source', rank: d.prefer === 'source' ? 0 : 2, file };
  }
  const name = lakePackageName(root);
  if (!name || !name.endsWith('-extracted')) return null;
  const exact = name === `${d.vol}-extracted`;
  return { kind: 'copy', rank: (d.prefer === 'copy' ? 0 : 2) + (exact ? 0 : 1), file };
}

async function findFile(d, context) {
  const found = (vscode.workspace.workspaceFolders || [])
    .map((f) => classify(f.uri.fsPath, d))
    .filter(Boolean)
    .sort((a, b) => a.rank - b.rank);
  if (found.length) return found[0].file;

  const remembered = context.globalState.get(GLOBAL_KEY(d.vol));
  if (remembered) {
    const c = classify(remembered, d);
    if (c) return c.file;
  }

  const choice = await vscode.window.showInformationMessage(
    TEXT.whereIsCopy(d.vol), { modal: true }, TEXT.locate);
  if (choice !== TEXT.locate) return null;
  const picked = await vscode.window.showOpenDialog({
    canSelectFolders: true, canSelectFiles: false, canSelectMany: false, openLabel: TEXT.openLabel,
  });
  if (!picked || picked.length === 0) return null;
  const root = picked[0].fsPath;
  const c = classify(root, d);
  if (!c) {
    vscode.window.showErrorMessage(TEXT.notACopy(root, relFile(d)));
    return null;
  }
  await context.globalState.update(GLOBAL_KEY(d.vol), root);
  return c.file;
}

// The editor group already showing `uri`, if any, so that the file is
// revealed there rather than opened a second time in the active group.
function columnShowing(uri) {
  for (const group of vscode.window.tabGroups.all) {
    for (const tab of group.tabs) {
      if (tab.input instanceof vscode.TabInputText && tab.input.uri.fsPath === uri.fsPath) {
        return group.viewColumn;
      }
    }
  }
  return undefined;
}

let flashType = null;

function flash(editor, line) {
  if (!flashType) {
    flashType = vscode.window.createTextEditorDecorationType({
      isWholeLine: true,
      backgroundColor: new vscode.ThemeColor('editor.findMatchHighlightBackground'),
    });
  }
  const range = new vscode.Range(line, 0, line, 0);
  editor.setDecorations(flashType, [range]);
  setTimeout(() => editor.setDecorations(flashType, []), FLASH_MS);
}

async function openAt(file, d) {
  const uri = vscode.Uri.file(file);
  const doc = await vscode.workspace.openTextDocument(uri);
  const editor = await vscode.window.showTextDocument(doc, {
    viewColumn: columnShowing(uri), preview: false,
  });
  const where = locate(doc.getText(), d);
  const pos = new vscode.Position(where.line, 0);
  editor.selection = new vscode.Selection(pos, pos);
  editor.revealRange(new vscode.Range(pos, pos), vscode.TextEditorRevealType.AtTop);
  flash(editor, where.line);
  const wanted = d.kind === 'heading' ? 'heading' : 'text';
  if (where.how !== wanted) vscode.window.setStatusBarMessage(TEXT.approximate, 6000);
  return { file, line: where.line, how: where.how };
}

// Open the spot `payload` describes.  Returns { file, line, how } or null.
async function open(payload, context) {
  const d = validate(payload);
  if (!d) {
    vscode.window.showErrorMessage(TEXT.badLink);
    return null;
  }
  const file = await findFile(d, context);
  return file ? openAt(file, d) : null;
}

function activate(context) {
  context.subscriptions.push(vscode.window.registerUriHandler({
    handleUri(uri) {
      if (uri.path === '/open') return open(decodePayload(uri.query), context);
      return undefined;
    },
  }));
  context.subscriptions.push(vscode.commands.registerCommand('sfInLean.forgetFolders', async () => {
    for (const key of context.globalState.keys()) {
      if (key.startsWith('folder.')) await context.globalState.update(key, undefined);
    }
    vscode.window.showInformationMessage(TEXT.forgotten);
  }));
  // For test/vscode-test.js, which cannot send a real vscode: link without
  // the OS routing it to some other VS Code instance.
  return {
    open: (payload) => open(payload, context),
    handleQuery: (query) => open(decodePayload(query), context),
  };
}

function deactivate() {
  if (flashType) flashType.dispose();
}

module.exports = { activate, deactivate };
