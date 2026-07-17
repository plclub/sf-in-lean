import VersoManual

open Verso.Genre Manual

namespace SFLMeta

/-- Inline CSS that paints the rendered HTML in *Software Foundations*-style
colors: warm cream background, deep maroon section headings, dark red accents,
off-white code background. Wired into the build via `Config.extraCss` in
`Main.lean`. The original Verso layout, typography, and code highlighting are
otherwise untouched — only colors and a small amount of border styling are
overridden. -/
def sfTheme : CSS where
  css := r###"
:root {
  --sf-bg: #fffdf6;
  --sf-text: #1a1208;
  --sf-heading: #6b0d0d;
  --sf-accent: #a00;
  --sf-link: #7a1a1a;
  --sf-link-hover: #a00;
  --sf-code-bg: #f6efe0;
  --sf-rule: #e6dcc4;
  --sf-toc-bg: #fbf6e8;

  /* Override Verso's syntax highlighting palette */
  --verso-code-keyword-color: #697f2f;
  --verso-code-const-color: #416DFF;
}

body {
  /* Software Foundations LF background — same image and layout as the
     original site (no-repeat, full width, scrolls with the page so it
     fades off the top as you read down). The body color is plain white,
     matching the original SF site, so the area below the image (once it
     has scrolled off) shows the same neutral backdrop the SF book uses. */
  background-color: white;
  background-image: url('assets/prog_lang_bg.jpg');
  background-repeat: no-repeat;
  background-size: 100% auto;
  background-position: top left;
  background-attachment: scroll;
  color: var(--sf-text);
}

/* Solid card behind the actual prose so the background image never bleeds
   through the text itself. */
main .content-wrapper {
  background: var(--sf-bg);
  padding: 1.5rem var(--verso--content-padding-x);
  box-shadow: 0 2px 12px rgba(0, 0, 0, 0.18);
  border-radius: 2px;
}

main h1, main h2, main h3, main h4, main h5, main h6,
.header-title, .toc-title h1 {
  color: var(--sf-heading);
}

/* A section whose heading is full-only (see
   SFLMeta.Block.suppressPreviousHeaderWhenTerse): the marker div is present
   only in the terse build, where the heading hides. */
section:has(> .suppress-previous-header-when-terse)
    > :is(h1, h2, h3, h4, h5, h6):first-child {
  display: none;
}

a, a:visited { color: var(--sf-link); }
a:hover, a:active { color: var(--sf-link-hover); }

header {
  background: var(--sf-bg);
  border-bottom: 1px solid var(--sf-rule);
  box-shadow: none;
}

#toc {
  background: var(--sf-toc-bg) !important;
  border-right: 1px solid var(--sf-rule);
}

code:not(.hl), pre:not(.hl) {
  background: var(--sf-code-bg);
  padding: 0.1em 0.3em;
  border-radius: 2px;
}

pre:not(.hl) {
  padding: 0.6em 0.9em;
  border-left: 3px solid var(--sf-accent);
  background: var(--sf-code-bg);
}

.hl.lean.block {
  background: var(--sf-code-bg);
  border-left: 3px solid var(--sf-accent);
  padding: 0.6em 0.9em;
  border-radius: 2px;
}

blockquote {
  border-left: 3px solid var(--sf-accent);
  background: #fbf5e2;
  margin-left: 0;
  padding: 0.4em 1em;
  color: #3a2a10;
}

/* Tighten the exercise box to share the same palette */
.exercise {
  background: #fbf5e2;
  border-left: 3px solid var(--sf-accent);
}
"###

end SFLMeta
