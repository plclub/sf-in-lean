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
    (requires : Array Lake.Toml.Table) : Lake.Toml.Table :=
  let libs := (#[vol] ++ extraLibs.filter (· != vol)).map fun name =>
    Lake.Toml.Table.empty.insert `name name
  Lake.Toml.Table.empty
    |>.insert `name (vol.toLower ++ "-extracted")
    |>.insert `version "0.1.0"
    |>.insert `defaultTargets #[vol]
    |>.insert `require requires
    |>.insert `lean_lib libs

private def writeProject (dest : System.FilePath) (toolchain : String)
    (vol : String) (v : Variant) (files : Array (String × String))
    (extraLibs : Array String) (requires : Array Lake.Toml.Table) : IO Unit := do
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
    <| lakefileToml vol extraLibs requires
  IO.FS.writeFile (dest / "lean-toolchain") toolchain
  IO.FS.writeFile (dest / "README.md")
    s!"# {vol} — {v} version\n\nGenerated from the Verso source.\n"

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
    let mut buf : SaveBuffers := walkOuter width config.modPrefix text {}

    for (vol, part) in crossVol do
      let file := chapterPath vol part
      buf := buf.appendOnly file .grading "import ComparatorAutograderLib\n"
      buf := buf.appendAll file s!"import {supportModuleName config.modPrefix}\n\n"
      buf := walkSection width 1 file part buf

    let toolchain ← IO.FS.readFile "lean-toolchain"
    let supportModule ← readSFLCompat
    let requires ← projectRequires config.variant
    let rootFile := config.modPrefix ++ ".lean"

    let entries := buf.fold (init := []) fun acc file variants =>
      (file, variants) :: acc

    -- Modules that are generated from Verso
    -- Get the module name from the file name
    let generatedModules := entries.map fun (file, _) =>
      ((file.dropEnd 5).toString).replace "/" "."

    let mut files : Array (String × String) :=
      #[(supportModulePath config.modPrefix, supportModule)]

    let mut seeds : List String := []

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
        let lib := (path.splitOn "/").headD ""
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
