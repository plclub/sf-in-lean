// Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
// Mostly AI-generated prototype code; see CONTRIBUTING.md, "AI policy".
//
// "Open in editor" buttons for the HTML book.  Hovering over a heading,
// paragraph, list item, or Lean code block shows a small button in the left
// margin.  Clicking it hands VS Code a `vscode://plclub.sf-in-lean/open?d=...`
// link, which the SF-in-Lean extension (vscode-extension/ in this repository)
// handles by opening the reader's own copy of the chapter at that spot.
//
// The page does not know where the reader's files are, and line numbers from
// the build would drift as soon as the reader edits the file.  So the link
// carries a description of the clicked element instead: volume, chapter, the
// titles of the enclosing sections (outermost first), and the first words of
// the element's text.  The extension finds the reader's copy and searches it
// for those headings and words (vscode-extension/locate.js).
//
// On a local build (a file:// page under /_out/, or localhost) the link also
// says `prefer: "source"`, so that a VS Code window with the SFL development
// repository open shows the Verso source rather than an extracted copy.
//
// Installed into every page by `mkConfig` in SFLMeta/Run.lean, which also
// writes the `<meta name="sfl-volume">` tag read below.
(function () {
  'use strict';

  // Reader-facing wording.  PLACEHOLDERS: CONTRIBUTING.md's AI policy requires
  // these strings to be written by a human before the feature reaches readers.
  const TEXT = {
    buttonTitle: '[placeholder] Open this spot in VS Code (shift-click for options)',
    notOpened: '[placeholder] Did nothing happen? This button opens your copy ' +
      'of the chapter in VS Code, using the SF-in-Lean extension.',
    setupLink: '[placeholder] Setup instructions',
    hideButtons: '[placeholder] Hide these buttons',
    dismiss: '[placeholder] Dismiss',
  };
  const SETUP_URL = null; // Placeholder: where the setup instructions will live.

  const EXTENSION_ID = 'plclub.sf-in-lean';
  const SNIPPET_WORDS = 12;
  const HIDE_DELAY_MS = 700;
  const NOTE_DELAY_MS = 3000;
  const PREF_KEY = 'sfl-editor-links';           // 'off' hides the buttons
  const WORKED_KEY = 'sfl-editor-links-worked';  // a click has reached an app
  const TARGETS = 'h1, h2, h3, h4, h5, h6, p, li, dt, dd, ' +
    'code.hl.lean.block, pre, blockquote';
  // Never targets themselves, nothing inside them is a target, and their text
  // is left out of a description.  The hover, message, and tactic-state
  // classes are Verso's pop-up material inside Lean code, which the chapter
  // file does not contain.
  const EXCLUDE = 'nav, header, summary, .permalink-widget, .sf-dev-note-label, ' +
    '.hover-container, .hover-info, .tactic-state, .tactic-toggle, ' +
    '.sfl-editor-link, .sfl-editor-note';
  const PREV_ELEMENTS = 8;
  const PREV_WORDS = 6;
  const HEADING = /^H[1-6]$/;
  const WORD = /[\p{L}\p{N}_]+/gu;

  // Browser storage is a per-reader convenience only; it may be unavailable.
  function load(key) {
    try { return window.localStorage.getItem(key); } catch (e) { return null; }
  }
  function store(key, value) {
    try {
      if (value === null) window.localStorage.removeItem(key);
      else window.localStorage.setItem(key, value);
    } catch (e) { /* ignore */ }
  }

  // The volume (from the meta tag) and chapter (the first path segment below
  // the book root, which Verso's `<base href>` points at), or null on pages
  // that are not chapters (the title page, search, ...).
  function pageContext() {
    const meta = document.querySelector('meta[name="sfl-volume"]');
    if (!meta || !/^[a-z]+$/.test(meta.content)) return null;
    if (!document.querySelector('main section > h1')) return null;
    const base = new URL(document.baseURI).pathname;
    const here = window.location.pathname;
    if (!here.startsWith(base)) return null;
    const chapter = decodeURIComponent(here.slice(base.length).split('/')[0]);
    if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(chapter)) return null;
    return { vol: meta.content, chapter: chapter };
  }

  function preferSource() {
    const loc = window.location;
    if (loc.protocol === 'file:') return loc.pathname.includes('/_out/');
    return loc.hostname === 'localhost' || loc.hostname === '127.0.0.1';
  }

  function cleanText(el) {
    const copy = el.cloneNode(true);
    copy.querySelectorAll(EXCLUDE).forEach(function (e) { e.remove(); });
    return copy.textContent.replace(/\s+/g, ' ').trim();
  }

  // A heading's title without Verso's section number ("2.1. ").
  function headingTitle(h) {
    return cleanText(h).replace(/^(\d+\.)+\s*/, '');
  }

  // Titles of the sections enclosing `el`, outermost first.  A heading is the
  // first child of its own <section>, so for a heading the list ends with it.
  function sectionTitles(el) {
    const titles = [];
    let s = el.closest('section');
    while (s) {
      const h = s.querySelector(
        ':scope > h1, :scope > h2, :scope > h3, :scope > h4, :scope > h5, :scope > h6');
      if (h) titles.unshift(headingTitle(h));
      s = s.parentElement && s.parentElement.closest('section');
    }
    return titles;
  }

  function firstWords(s, n) {
    return (s.match(WORD) || []).slice(0, n).join(' ');
  }

  // The first words of up to PREV_ELEMENTS elements before `el` in its
  // section, oldest first: at each level from `el` up to the section, the
  // preceding siblings, nearest first.  The same short text ("true : Bool")
  // can occur several times in a section; finding these first, in order,
  // lets the extension skip the earlier occurrences.
  function prevTexts(el) {
    const found = [];
    for (let node = el; node && node.tagName !== 'SECTION'; node = node.parentElement) {
      for (let sib = node.previousElementSibling; sib; sib = sib.previousElementSibling) {
        if (HEADING.test(sib.tagName) || sib.tagName === 'SECTION') return found.reverse();
        if (sib.matches(EXCLUDE)) continue;
        const t = firstWords(cleanText(sib), PREV_WORDS);
        if (t) found.push(t);
        if (found.length === PREV_ELEMENTS) return found.reverse();
      }
    }
    return found.reverse();
  }

  // The title of the first heading after `el`, if any.  The extension stops
  // its search there.  It cannot just stop at the file's next heading: the
  // chapter file has headings the page does not (exercise titles, say).
  function nextTitle(el) {
    const main = el.closest('main');
    if (!main) return '';
    for (const h of main.querySelectorAll('h1, h2, h3, h4, h5, h6')) {
      if (el.compareDocumentPosition(h) & Node.DOCUMENT_POSITION_FOLLOWING && !el.contains(h)) {
        return headingTitle(h);
      }
    }
    return '';
  }

  function describe(el) {
    const isHeading = HEADING.test(el.tagName);
    if (isHeading) return { headings: sectionTitles(el), kind: 'heading', text: '' };
    return {
      headings: sectionTitles(el),
      kind: 'text',
      text: firstWords(cleanText(el), SNIPPET_WORDS),
      prev: prevTexts(el),
      next: nextTitle(el),
    };
  }

  // The payload travels as base64url JSON: those characters survive any
  // amount of percent-encoding and -decoding between browser, OS, and VS Code.
  function encode(obj) {
    const bytes = new TextEncoder().encode(JSON.stringify(obj));
    let bin = '';
    bytes.forEach(function (b) { bin += String.fromCharCode(b); });
    return btoa(bin).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  }

  function uriFor(ctx, d) {
    const payload = Object.assign({ v: 1, vol: ctx.vol, chapter: ctx.chapter }, d);
    if (preferSource()) payload.prefer = 'source';
    return 'vscode://' + EXTENSION_ID + '/open?d=' + encode(payload);
  }

  const CSS = `
.sfl-editor-link {
  position: absolute; z-index: 50; display: none;
  width: 1.5rem; height: 1.5rem; padding: 0;
  border: 1px solid var(--sf-rule, #ccc); border-radius: 4px;
  background: var(--verso-surface-color, #fff); color: inherit;
  font-size: 0.9rem; line-height: 1; cursor: pointer; opacity: 0.55;
}
.sfl-editor-link:hover, .sfl-editor-link:focus-visible { opacity: 1; }
.sfl-editor-note {
  position: fixed; right: 1rem; bottom: 1rem; z-index: 60; max-width: 24rem;
  padding: 0.8em 1em; border: 1px solid var(--sf-rule, #ccc); border-radius: 6px;
  background: var(--verso-surface-color, #fff); color: inherit;
  box-shadow: 0 2px 10px rgba(0, 0, 0, 0.15); font-size: 0.9rem;
}
.sfl-editor-note p { margin: 0 0 0.6em 0; }
.sfl-editor-note button, .sfl-editor-note a { margin-right: 0.8em; font-size: 0.85rem; }
@media (max-width: 700px) { .sfl-editor-link { display: none !important; } }
`;

  function init() {
    if (window.location.hash === '#editor-links') store(PREF_KEY, null);
    if (load(PREF_KEY) === 'off') return;
    const ctx = pageContext();
    const main = document.querySelector('main');
    if (!ctx || !main) return;

    const style = document.createElement('style');
    style.textContent = CSS;
    document.head.appendChild(style);

    const button = document.createElement('button');
    button.type = 'button';
    button.className = 'sfl-editor-link';
    button.textContent = '✎'; // pencil
    button.title = TEXT.buttonTitle;
    button.setAttribute('aria-label', TEXT.buttonTitle);
    document.body.appendChild(button);

    let current = null;
    let hideTimer = null;
    let note = null;

    function hideButton() {
      button.style.display = 'none';
      current = null;
    }
    function scheduleHide() {
      clearTimeout(hideTimer);
      hideTimer = setTimeout(hideButton, HIDE_DELAY_MS);
    }
    function showButton(el) {
      current = el;
      const r = el.getBoundingClientRect();
      let left = r.left + window.scrollX - 32;
      if (left < window.scrollX + 4) left = r.right + window.scrollX - 28;
      button.style.top = (r.top + window.scrollY) + 'px';
      button.style.left = left + 'px';
      button.style.display = 'block';
    }

    main.addEventListener('mouseover', function (e) {
      const t = e.target.closest && e.target.closest(TARGETS);
      if (!t || !main.contains(t) || t.closest(EXCLUDE)) return;
      clearTimeout(hideTimer);
      if (t !== current) showButton(t);
    });
    main.addEventListener('mouseleave', scheduleHide);
    button.addEventListener('mouseenter', function () { clearTimeout(hideTimer); });
    button.addEventListener('mouseleave', scheduleHide);

    function closeNote() {
      if (note) note.remove();
      note = null;
    }
    function showNote(message) {
      closeNote();
      note = document.createElement('div');
      note.className = 'sfl-editor-note';
      note.setAttribute('role', 'status');
      const p = document.createElement('p');
      p.textContent = message;
      note.appendChild(p);
      if (SETUP_URL) {
        const a = document.createElement('a');
        a.href = SETUP_URL;
        a.textContent = TEXT.setupLink;
        note.appendChild(a);
      }
      const hide = document.createElement('button');
      hide.type = 'button';
      hide.textContent = TEXT.hideButtons;
      hide.addEventListener('click', function () {
        store(PREF_KEY, 'off');
        closeNote();
        button.remove();
      });
      note.appendChild(hide);
      const dismiss = document.createElement('button');
      dismiss.type = 'button';
      dismiss.textContent = TEXT.dismiss;
      dismiss.addEventListener('click', closeNote);
      note.appendChild(dismiss);
      document.body.appendChild(note);
    }

    // There is no way to ask whether anything handled the vscode: link.  If
    // the page keeps focus for a few seconds, assume nothing did and say how
    // to set things up -- unless a click has worked before.  Losing focus
    // later (the reader confirming the browser's prompt) takes the note away.
    function launch(uri) {
      let left = false;
      function onLeave() {
        left = true;
        store(WORKED_KEY, '1');
        closeNote();
        window.removeEventListener('blur', onLeave);
      }
      window.addEventListener('blur', onLeave);
      setTimeout(function () { window.removeEventListener('blur', onLeave); }, 30000);
      setTimeout(function () {
        if (!left && !load(WORKED_KEY)) showNote(TEXT.notOpened);
      }, NOTE_DELAY_MS);
      api.navigate(uri);
    }

    button.addEventListener('click', function (e) {
      e.preventDefault();
      if (e.shiftKey) { showNote(TEXT.notOpened); return; }
      if (current) launch(uriFor(ctx, describe(current)));
    });
  }

  // Exposed for the tests in vscode-extension/test/, which replace `navigate`
  // so that a simulated click does not launch anything.
  const api = window.sflEditorLinks = {
    TARGETS: TARGETS, EXCLUDE: EXCLUDE, describe: describe, encode: encode,
    uriFor: uriFor, pageContext: pageContext,
    navigate: function (uri) { window.location.href = uri; },
  };

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
  else init();
})();
