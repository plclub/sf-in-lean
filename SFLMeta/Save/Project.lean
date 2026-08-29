import VersoManual

import Lake.Load.Manifest
import Lake.Toml
import Lean.Elab.Import

import SFLMeta.Variant
import SFLMeta.Save.Extract

open Verso Doc Genre Manual

namespace SFLMeta.Save

structure ExtractConfig where
  destSlug : String
  modPrefix : String
  variant : Variant
  verify : Bool

def ExtractConfig.fromVolume (vol : String) (variant : Variant) (verify : Bool) : ExtractConfig :=
  { destSlug := vol.toLower, modPrefix := vol, variant, verify}

/-! ## Generated Lake project -/

/-- Build a `[[require]]` table of package with `name`, using the revision from `manifest`. -/
private def manifestRequire (manifest : Lake.Manifest) (name : String) : IO Lake.Toml.Table := do
  for pkg in manifest.packages do
    if pkg.prettyName == name then
      match pkg.src with
      | .git url rev _ subDir? =>
          return Lake.Toml.Table.empty
            |>.insert `name name
            |>.insert `git url
            |>.insert `rev rev
            |>.insertSome `subDir subDir?
      | .path _ =>
          throw <| IO.userError s!"package '{name}' is not a Git dependency"
  throw <| IO.userError s!"package '{name}' is missing from lake-manifest.json"

/-- Packages to be included in extracted projects. -/
private def projectRequires
    (v : Variant) : IO (Array Lake.Toml.Table) := do
  -- This is our parent project
  let manifest ← Lake.Manifest.load "lake-manifest.json"

  let batteries ← manifestRequire manifest "batteries"

  if v.isGrading then
    let autograder ← manifestRequire manifest "comparator-autograder-lib"
    return #[autograder, batteries]
  else
    return #[batteries]

private def lakefileToml (vol : String) (extraLibs : Array String)
    (reqs : Array Lake.Toml.Table) : Lake.Toml.Table :=
  let libs := (#[vol] ++ extraLibs.filter (· != vol)).map fun name =>
    Lake.Toml.Table.empty.insert `name name
  Lake.Toml.Table.empty
    |>.insert `name (vol.toLower ++ "-extracted")
    |>.insert `version "0.1.0"
    |>.insert `defaultTargets #[vol]
    |>.insert `require reqs
    |>.insert `lean_lib libs

/--
The `.vscode/settings.json` shipped inside every extracted project.

Students open the generated `lean/` directory directly (`code .`), so the
repository's own `.vscode/settings.json` is not in scope for them. This is the
student-facing subset of it, plus settings that only make sense for the
*generated* files: the editor settings that make the chapters readable and
typable, without the authoring-only entries (rulers, rewrap width, icon theme)
or any setting that would demand an extension they have no reason to install.

In an extracted chapter the book's prose arrives as `--` comments wrapping the
code, so comments are recoloured to a blue-grey that reads as narration rather
than as code.  These files are read as a book, so the prose is tuned to be
comfortably legible rather than de-emphasised: both tones sit above the stock
comment colour of the theme they replace (5.1:1 for Light+'s green, 5.0:1 for
Dark+'s).

A theme-scoped key selects on the theme's *name* — VS Code matches the
`settingsId` with `*` allowed at either end, and appends theme-scoped rules
after the unscoped ones, so the last match wins.  Name matching is not the same
as knowing a theme is light or dark: `Monokai`, `Abyss` and `Red` say neither.
So the unscoped rule carries a mid-tone that works on either background and the
two scoped rules sharpen it wherever the name does tell us:

* unscoped `#6B7C8C` — 4.3:1 on Light+, 3.9:1 on Dark+
* `[*Light*]` `#4A5A6A` — 7.1:1 on white
* `[*Dark*]`  `#89A0B3` — 6.2:1 on `#1E1E1E`

`[*Light*]` also captures `Default High Contrast Light`, where a reader may
prefer the theme's own maximum-contrast comment colour; there is no way to opt
a scope back out of a customisation, so that is a known rough edge.

The rules name the three `lean4` comment scopes rather than the bare `comment`
scope, which would also recolour the Markdown, JSON and TOML files sitting
beside the chapters.

Keep the `lean4.input.customTranslations` entries in step with the repository's
`.vscode/settings.json`.
-/
private def vscodeSettingsJson : String :=
  r##"{
    // Chapter prose is set in wide comment blocks; wrap it rather than
    // scrolling sideways.
    "[lean4]": {
        "editor.wordWrap": "on"
    },
    // Lean input abbreviation for the type-colon glyph ⦂ (U+2982) used in the
    // typing judgment `⊢ t ⦂ T`: type `\tc` then space.
    "lean4.input.customTranslations": {
        "tc": "⦂"
    },
    // The book's prose reaches these files as `--` comments; tint them so the
    // narration reads as distinct from the code it surrounds.  The unscoped
    // rule is a mid-tone that works on either background, for themes whose
    // name says neither "Light" nor "Dark"; the scoped rules sharpen it where
    // the name does tell us.  Theme-scoped rules are applied last and win.
    "editor.tokenColorCustomizations": {
        "textMateRules": [
            {
                "scope": [
                    "comment.line.double-dash.lean4",
                    "comment.block.lean4",
                    "comment.block.documentation.lean4"
                ],
                "settings": {
                    "foreground": "#6B7C8C"
                }
            }
        ],
        "[*Light*]": {
            "textMateRules": [
                {
                    "scope": [
                        "comment.line.double-dash.lean4",
                        "comment.block.lean4",
                        "comment.block.documentation.lean4"
                    ],
                    "settings": {
                        "foreground": "#4A5A6A"
                    }
                }
            ]
        },
        "[*Dark*]": {
            "textMateRules": [
                {
                    "scope": [
                        "comment.line.double-dash.lean4",
                        "comment.block.lean4",
                        "comment.block.documentation.lean4"
                    ],
                    "settings": {
                        "foreground": "#89A0B3"
                    }
                }
            ]
        }
    }
}
"##

private def writeProject (dest : System.FilePath) (toolchain : String)
    (vol : String) (v : Variant) (files : Array (String × String))
    (extraLibs : Array String) (reqs : Array Lake.Toml.Table) : IO Unit := do
  IO.FS.createDirAll dest

  -- Remove existing generated files
  for lib in vol :: extraLibs.toList do
    let libRoot := dest / lib
    if ← libRoot.pathExists then
      IO.FS.removeDirAll libRoot

  -- Remove the old lakefile
  let manifest := dest / "lake-manifest.json"
  if ← manifest.pathExists then
    IO.FS.removeFile manifest

  IO.FS.writeFile (dest / "lakefile.toml")
    <| Lake.Toml.ppTable
    <| lakefileToml vol extraLibs reqs
  IO.FS.writeFile (dest / "lean-toolchain") toolchain
  IO.FS.writeFile (dest / "README.md")
    s!"# {vol} — {v} version\n\nGenerated from the Verso source.\n"

  IO.FS.createDirAll (dest / ".vscode")
  IO.FS.writeFile (dest / ".vscode" / "settings.json") vscodeSettingsJson

  for (relPath, body) in files do
    let target := dest / relPath
    target.parent.forM IO.FS.createDirAll
    IO.FS.writeFile target body

private def buildProject (dest : System.FilePath) (v : Variant) : BuildLogT IO Unit := do
  IO.println s!"Building generated {v} project at {dest}"
  let res ← IO.Process.output {
    cmd := "lake"
    args := #["build"]
    cwd := dest
  }
  if res.exitCode != 0 then
    reportError <|
      s!"Generated {v} project at {dest} failed to build " ++
      s!"(exit {res.exitCode}):\n--- stdout ---\n{res.stdout}\n" ++
      s!"--- stderr ---\n{res.stderr}"
  else
    IO.println s!"Generated {v} project built successfully."

/-! ## Imports -/

/-- Modules we don't want to bring into extracted projects -/
private def frameworkPrefixes : List String :=
  ["VersoManual", "Verso", "Illuminate", "SFLMeta", "SubVerso", "Credits"]

private def modTop (m : String) : String :=
  (m.splitOn ".").headD m

private def keepImport (m : String) : Bool :=
  !frameworkPrefixes.contains (modTop m)

private def modToPath (m : String) : String :=
  m.replace "." "/" ++ ".lean"

/-- Run Lean parser to get the imports. -/
private def headerImports (file src : String) : IO (Array String) := do
  let inputCtx := Lean.Parser.mkInputContext src file
  let (header, _, messages) ← Lean.Parser.parseHeader inputCtx
  if messages.hasErrors then
    throw <| IO.userError s!"failed to parse Lean header in '{file}'"
  return (Lean.Elab.HeaderSyntax.imports header (includeInit := false)).map fun imp =>
    imp.module.toString (escape := false)

/--
Starting from the imports used by generated chapters,
recursively copy any imported `.lean` files that live in this repo
into the extracted project.

`generatedModules`: modules that are already being generated
`files`: local source files we've decided to copy
-/
private partial def bundleLoop
    (generatedModules : List String)
    (queue seen : List String)
    (files : Array (String × String)) :
    IO (Array (String × String)) := do
  match queue with
  | [] => return files
  | m :: rest =>
    if seen.contains m then
      bundleLoop generatedModules rest seen files
    else if generatedModules.contains m then
      bundleLoop generatedModules rest (m :: seen) files
    else
      let path := modToPath m
      let sourcePath := System.FilePath.mk path
      if !(← sourcePath.pathExists) then
        -- files from toolcahin
        bundleLoop generatedModules rest (m :: seen) files
      else
        let content ← IO.FS.readFile sourcePath
        let deps := (← headerImports path content).toList.filter keepImport
        bundleLoop generatedModules
          (deps ++ rest)
          (m :: seen)
          (files.push (path, content))

private def mergeAdjacentModuleDocs (s : String) : String :=
  s.replace "\n-/\n\n/-!\n" "\n\n"

/-! ## Extraction -/

/--
Write one extracted project to `_out/<destSlug>/<variant>/lean/`.

`crossVol`: earlier-volume Verso chapters needed by this volume
-/
private def emitSavedImpl (config : ExtractConfig)
    (crossVol : List (String × Part Manual) := []) :
    Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit :=
  fun _mode _cfg _state text => do
    let width := Text.fillWidthFor config.variant
    let isTerse := config.variant.isTerse
    let mut buf : SaveBuffers := walkOuter width isTerse config.modPrefix text {}

    for (vol, part) in crossVol do
      let file := chapterPath vol part
      buf := buf.appendOnly file .grading "import ComparatorAutograderLib\n"
      buf := buf.appendAll file s!"import SFLCompat\n\n"
      buf := walkSection width isTerse 1 file part buf

    let toolchain ← IO.FS.readFile "lean-toolchain"
    let requires ← projectRequires config.variant
    let rootFile := config.modPrefix ++ ".lean"

    let entries := buf.fold (init := []) fun acc file variants =>
      (file, variants) :: acc

    -- Modules that are generated from Verso
    -- Get the module name from the file name
    let generatedModules := entries.map fun (file, _) =>
      ((file.dropEnd 5).toString).replace "/" "."

    let mut files : Array (String × String) := #[]

    let mut seeds : List String := ["SFLCompat"]

    for (file, variants) in entries do
      let chosen := mergeAdjacentModuleDocs <| variants.get config.variant
      if file == rootFile then
        files := files.push (file, chosen)
      else
        let source ← IO.FS.readFile file
        let imports :=
          (← headerImports file source).toList.filter keepImport
        -- Order does not matter for dependency discovery.
        seeds := imports ++ seeds
        let preamble :=
          String.join <| imports.map fun imp =>
            s!"import {imp}\n"
        files := files.push
          (file, if preamble.isEmpty then chosen else preamble ++ "\n" ++ chosen)

    let bundleFiles ← bundleLoop generatedModules seeds [] #[]

    -- Using a chapter in another volume makes that volume an additional library
    let extraLibs :=
      bundleFiles.foldl (init := crossVol.map (·.1) |>.toArray) fun libs (path, _) =>
        let lib :=
          if path == "SFLCompat.lean" then "SFLCompat"
          else (path.splitOn "/").headD ""
        if lib == config.modPrefix || libs.contains lib then
          libs
        else
          libs.push lib

    let dest :=
      System.FilePath.mk "_out" /
        config.destSlug /
        config.variant.toString /
        "lean"

    writeProject dest toolchain config.modPrefix config.variant
      (files ++ bundleFiles) extraLibs requires

    if config.verify then
      buildProject dest config.variant


def emitSavedStudent (vol : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .student true) crossVol

def emitSavedSolutions (vol : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .solutions true) crossVol

def emitSavedTerse (vol : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .terse true) crossVol

def emitSavedGrading (vol : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .grading true) crossVol

end SFLMeta.Save
