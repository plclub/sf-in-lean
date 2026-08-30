import VersoManual

import Lake.Load.Manifest
import Lake.Toml
import Lean.Elab.Import

import SFLMeta.BuildStamp
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

/-- Settings from the repository's own `.vscode/settings.json` that are also
wanted by a reader of the *generated* chapters.

Everything else there is authoring-only (rulers, rewrap width, the icon theme
and its folder clones, `explorer.excludeGitIgnore`) or would demand an
extension a reader has no cause to install.  Naming what to keep, rather than
what to drop, means a new authoring setting stays out of the student projects
until someone deliberately adds it here. -/
private def studentSettingKeys : List String :=
  ["[lean4]", "lean4.input.customTranslations", "editor.tokenColorCustomizations"]

/-- Drop a `//` line comment from one line of JSONC, leaving any `//` that
falls inside a string literal alone.  A JSON string cannot contain a raw
newline, so string state never carries across lines and each line can be
scanned on its own. -/
private def stripLineComment (line : String) : String := Id.run do
  let mut out := ""
  let mut inString := false
  let mut escaped := false
  -- A '/' outside a string is withheld until the next character says whether
  -- it opened a comment or was just a slash.
  let mut pendingSlash := false
  for c in line.toList do
    if inString then
      out := out.push c
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then inString := false
    else if pendingSlash then
      if c == '/' then
        return out
      pendingSlash := false
      out := out.push '/'
      if c == '"' then inString := true
      out := out.push c
    else if c == '/' then
      pendingSlash := true
    else
      if c == '"' then inString := true
      out := out.push c
  if pendingSlash then
    out := out.push '/'
  return out

/-- The `.vscode/settings.json` to ship inside an extracted project.

The repository's own `.vscode/settings.json` is the single source of truth:
this reads it, keeps `studentSettingKeys`, and re-emits them.  Nothing is
duplicated, so a colour or abbreviation retuned while authoring reaches the
next generated project for free.

Read relative to the working directory, which is the repository root when the
volume executable runs (as it is for `lean-toolchain` and
`lake-manifest.json`).  A missing or malformed file, or a missing key, is an
error rather than a silent omission: each would mean students quietly lose a
setting the authors thought they had. -/
private def vscodeSettingsJson : IO String := do
  let path : System.FilePath := ".vscode" / "settings.json"
  unless ← path.pathExists do
    throw <| IO.userError
      s!"{path} is missing; it is the source of the settings shipped to readers"
  let raw ← IO.FS.readFile path
  let stripped := String.intercalate "\n" <| (raw.splitOn "\n").map stripLineComment
  let json ←
    match Lean.Json.parse stripped with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"could not parse {path}: {e}"
  match json.getObj? with
  | .ok _ => pure ()
  | .error e => throw <| IO.userError s!"{path} is not a JSON object: {e}"
  let mut kept : List (String × Lean.Json) := []
  for key in studentSettingKeys.reverse do
    match json.getObjVal? key with
    | .ok v => kept := (key, v) :: kept
    | .error _ =>
      let msg := s!"{path} has no '{key}'; it is shipped to readers, so "
        ++ "removing it should be deliberate (update studentSettingKeys)"
      throw <| IO.userError msg
  let banner :=
    "// Generated from the repository's own .vscode/settings.json -- edit it there,\n"
      ++ "// not here (see `studentSettingKeys` in SFLMeta/Save/Project.lean).\n"
  return banner ++ (Lean.Json.mkObj kept).pretty ++ "\n"

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
  IO.FS.writeFile (dest / ".vscode" / "settings.json") (← vscodeSettingsJson)

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

/-- Every quiz is emitted between two `quizSeparator` rules, so a run of
consecutive quizzes ends up with a doubled rule at each interior boundary.
Collapse each doubled rule to one: a run of quizzes is then introduced,
separated, and terminated by a single rule. -/
private def dedupQuizSeparators (s : String) : String :=
  s.replace (quizSeparator ++ quizSeparator) quizSeparator

/-! ## Extraction -/

/--
Write one extracted project to `_out/<destSlug>/<variant>/lean/`.

`stamp`: this build's stamp (`SFLMeta.buildStamp`), appended as a trailing
comment to every file generated from Verso -- the same sentence the HTML page of
that chapter ends with

`crossVol`: earlier-volume Verso chapters needed by this volume
-/
private def emitSavedImpl (config : ExtractConfig) (stamp : String)
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
      let chosen := dedupQuizSeparators <| mergeAdjacentModuleDocs <| variants.get config.variant
      if file == rootFile then
        files := files.push (file, withBuildStamp stamp chosen)
      else
        let source ← IO.FS.readFile file
        let imports :=
          (← headerImports file source).toList.filter keepImport
        -- Order does not matter for dependency discovery.
        seeds := imports ++ seeds
        let preamble :=
          String.join <| imports.map fun imp =>
            s!"import {imp}\n"
        let body := if preamble.isEmpty then chosen else preamble ++ "\n" ++ chosen
        files := files.push (file, withBuildStamp stamp body)

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


def emitSavedStudent (vol stamp : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .student true) stamp crossVol

def emitSavedSolutions (vol stamp : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .solutions true) stamp crossVol

def emitSavedTerse (vol stamp : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .terse true) stamp crossVol

def emitSavedGrading (vol stamp : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .grading true) stamp crossVol

end SFLMeta.Save
