/-
Written by Claude (Opus 5.5) on 2026-11-05 at Benjamin Pierce's request.
Mostly AI-generated prototype code; see CONTRIBUTING.md, "AI policy".
-/
import VersoManual

/-!
# "Open in editor" buttons

The page script `editor-links.js` (beside this file; its header comment explains
the design) gives every chapter page buttons that open the clicked spot in the
reader's copy of the chapter, through the SF-in-Lean VS Code extension in
`vscode-extension/`.  `mkConfig` (`SFLMeta/Run.lean`) installs the script on every
page, together with a `<meta name="sfl-volume">` tag naming the volume, which the
script needs in order to name the chapter's file.

The script is read when the book is rendered, not embedded with `include_str`:
Lake does not track a file that `include_str` reads, so an edited script would
silently fail to reach the pages until something else forced a rebuild.
-/

open Verso.Genre.Manual

namespace SFLMeta

/-- The page script, written to the Verso data directory and loaded by every page.
Read from `SFLMeta/editor-links.js`, relative to the repository root, where the
book executables run (as `SFLMeta/Save/Project.lean` reads `lean-toolchain`). -/
def editorLinksJs : IO JsFile := do
  let js ← IO.FS.readFile ("SFLMeta" / "editor-links.js")
  return { filename := "sfl-editor-links.js", defer := true, contents := ⟨js⟩, sourceMap? := none }

/-- The tag telling the page script which volume it is in (`lf`, `hl`, `ts`). -/
def volumeMetaHtml (vol : String) : Verso.Output.Html :=
  open Verso.Output.Html in
  {{<meta name="sfl-volume" content={{vol}}/>}}

end SFLMeta
