
import VersoManual

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

/-! ## Lake project scaffold templates -/

/-- Contents of the generated project's `lakefile.toml`. `extraLibs` names the
additional `lean_lib`s holding bundled prerequisite sources (e.g. `LF` for the
bare `LF/Maps.lean` that Imp depends on).  `pkgRequires` lists external package
dependencies `(name, git url, rev)` needed by some emitted chapter's imports
(e.g. batteries for `import Batteries.CodeAction`), each pinned to the same
revision the book itself builds with. -/
private def lakefileTemplate (vol : String) (v : Variant) (extraLibs : Array String)
    (pkgRequires : Array (String × String × String)) : String :=
  -- A bundled prerequisite may live in the volume's own namespace (e.g. the
  -- bare `LF/CustomTactics.lean` bundled into the LF project): the volume's
  -- `lean_lib` already covers it, and Lake rejects a duplicate target.
  let extra := (extraLibs.filter (· != vol)).foldl (init := "") fun acc l =>
    acc ++ "\n[[lean_lib]]\nname = \"" ++ l ++ "\"\n"
  let pkgRequires := if v.isGrading
    then pkgRequires.push ("autograder", "https://github.com/plclub/lean4-autograder-main", "bump-4-32-0")
    else pkgRequires
  let reqs := pkgRequires.foldl (init := "") fun acc (name, url, rev) =>
    acc ++ "\n[[require]]\nname = \"" ++ name ++ "\"\ngit = \"" ++ url ++
      "\"\nrev = \"" ++ rev ++ "\"\n"
  "name = \"" ++ vol.toLower ++ "-extracted\"\n" ++
  "version = \"0.1.0\"\n" ++
  "defaultTargets = [\"" ++ vol ++ "\"]\n" ++
  reqs ++
  "\n[[lean_lib]]\n" ++
  "name = \"" ++ vol ++ "\"\n" ++
  extra

/--
Write a complete generated Lake project at `dest`: the per-file buffer contents
under `dest/`, plus `lakefile.toml`, `lean-toolchain`, and a README. The root
module file is one of the saved buffers produced by `walkOuter`. -/
private def writeProject (dest : System.FilePath) (toolchain : String)
    (vol : String) (v : Variant) (files : Array (String × String))
    (extraLibs : Array String)
    (pkgRequires : Array (String × String × String)) : IO Unit := do
  IO.FS.createDirAll dest
  -- Clear the volume source tree (and any bundled-prerequisite lib trees) so
  -- files that have since been renamed or removed don't linger as stale
  -- orphans. Other artifacts (`.lake`, `lakefile.toml`, `lean-toolchain`,
  -- `README.md`) are left alone.
  for lib in vol :: extraLibs.toList do
    let libRoot := dest / lib
    if ← libRoot.pathExists then
      IO.FS.removeDirAll libRoot
  -- Also drop any manifest left by a previous emit: `lake build` auto-resolves
  -- dependencies when there is no manifest, but refuses ("missing manifest")
  -- when an existing manifest lacks a package the lakefile now `require`s.
  let manifest := dest / "lake-manifest.json"
  if ← manifest.pathExists then
    IO.FS.removeFile manifest
  IO.FS.writeFile (dest / "lakefile.toml") (lakefileTemplate vol v extraLibs pkgRequires)
  IO.FS.writeFile (dest / "lean-toolchain") toolchain
  IO.FS.writeFile (dest / "README.md")
    s!"# {vol} — {v} version\n\nGenerated from the Verso source.\n"
  for (relPath, body) in files do
    let target := dest / relPath
    target.parent.forM IO.FS.createDirAll
    IO.FS.writeFile target body

/--
Run `lake build` inside `dest` and report any failure via `logError`. Used to
verify each generated project compiles. Student and terse builds may contain
intentional `sorry` warnings; expected-error doc examples have already been
wrapped in `sf_expect_failure` during extraction. -/
private def buildProject (dest : System.FilePath) (v : Variant) :
    BuildLogT IO Unit := do
  IO.println s!"Building generated {v} project at {dest}…"
  let res ← IO.Process.output {
    cmd := "lake", args := #["build"], cwd := dest
  }
  if res.exitCode != 0 then
    reportError <|
      s!"Generated {v} project at {dest} failed to build " ++
      s!"(exit {res.exitCode}):\n--- stdout ---\n{res.stdout}\n" ++
      s!"--- stderr ---\n{res.stderr}"
  else
    IO.println s!"Generated {v} project built successfully."

/-! ## Extracted-project imports & bundled prerequisites

Extracted `.lean` projects are standalone Lake packages, so each chapter's
outside dependencies must be reconstructed from its own header `import`s: drop
the framework imports (they build the book, not student code), re-emit the rest,
and bundle the source of any that is a content prerequisite (not toolchain, not
an emitted book chapter — e.g. the bare `LF.CustomTactics`) under its own
`lean_lib`. A bundled module is copied verbatim, so it must be plain (non-Verso) Lean; a
content prerequisite that is itself a Verso chapter of an earlier volume (e.g.
`LF.Typeclasses` imported by `HL.Imp`) cannot be bundled this way and is instead
walked and emitted like a native chapter via `emitSavedImpl`'s `crossVol`
parameter (which also excludes it from this bundle).
An import from an external package (e.g. `Batteries.CodeAction`) is re-emitted
too, and the generated `lakefile.toml` gains a matching `[[require]]` pinned to
the revision in the book's `lake-manifest.json`. -/

/-- Module top-namespaces belonging to the authoring framework: their imports
build the book but must never appear in an extracted `.lean` file.

`Credits` is a shared, include-only prose module (a Verso `#doc` whose
text is spliced into each volume's Preface via `{include 2 Credits}`).
Its prose is inlined by the walker at include time, so the extracted chapter
already contains it; the module itself is a build-only artifact that would drag
in `import SFLMeta`, so it is dropped and never bundled — exactly like the
framework modules. -/
private def frameworkPrefixes : List String :=
  ["VersoManual", "Verso", "Illuminate", "SFLMeta", "SubVerso", "Credits"]

/-- Toolchain-provided top-namespaces: always available in any Lake project, so
they stay as `import` lines but are never bundled as source. -/
private def corePrefixes : List String :=
  ["Lean", "Std", "Init"]

/-- Top-namespaces provided by external packages: their imports stay as
`import` lines and are never bundled as source, but the extracted project's
`lakefile.toml` must `require` the package (pinned via `manifestPin`) for them
to resolve. The package's Lake name is the prefix lowercased. -/
private def pkgPrefixes : List String :=
  ["Batteries"]

/-- Top namespace of a module name (`LF.Maps` ⇒ `LF`). -/
private def modTop (m : String) : String := (m.splitOn ".").headD m

/-- Look up package `name` in the book's own `lake-manifest.json`, returning
its `(git url, pinned rev)` so an extracted project can `require` the package
at exactly the revision the book builds with. -/
private def manifestPin (name : String) : IO (Option (String × String)) := do
  let .ok raw ← (IO.FS.readFile "lake-manifest.json").toBaseIO | return none
  let .ok json := Lean.Json.parse raw | return none
  let .ok pkgs := json.getObjVal? "packages" | return none
  let .ok arr := pkgs.getArr? | return none
  for p in arr do
    if (p.getObjValAs? String "name").toOption == some name then
      let .ok url := p.getObjValAs? String "url" | return none
      let .ok rev := p.getObjValAs? String "rev" | return none
      return some (url, rev)
  return none

/-- Should module `m` appear as an `import` in an extracted file? (Framework
imports are dropped; everything else — toolchain and content — is kept.) -/
private def keepImport (m : String) : Bool := ! frameworkPrefixes.contains (modTop m)

/-- The relative source path of a module
(`LF.Typeclasses` ⇒ `LF/Typeclasses.lean`). -/
private def modToPath (m : String) : String := m.replace "." "/" ++ ".lean"

/-- Header `import` module names in Lean source text, scanning only the file
header (up to the first `#doc`). -/
private def headerImports (src : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for raw in src.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "#doc" then break
    if line.startsWith "import " then
      out := out.push ((line.drop 7).trimAscii.toString)
  return out

/-- Transitively gather the bundled prerequisite files (path, verbatim source)
and the extra `lean_lib` names they need. `needsBundle` decides which modules
are content prerequisites (not framework, not toolchain, not an emitted
chapter). -/
private partial def bundleLoop (needsBundle : String → Bool)
    (queue seen : List String)
    (files : Array (String × String)) (libs : Array String) :
    IO (Array (String × String) × Array String) := do
  match queue with
  | [] => return (files, libs)
  | m :: rest =>
    if seen.contains m then
      bundleLoop needsBundle rest seen files libs
    else
      let path := modToPath m
      if ! (← (System.FilePath.mk path).pathExists) then
        -- Not a bundleable source file (e.g. a spurious match); skip it.
        bundleLoop needsBundle rest (m :: seen) files libs
      else
        let content ← IO.FS.readFile path
        let top := modTop m
        let libs := if libs.contains top then libs else libs.push top
        let deps := (headerImports content).toList.filter needsBundle
        bundleLoop needsBundle (rest ++ deps) (m :: seen)
          (files.push (path, content)) libs

/-- Merge adjacent `/-! … -/` blocks into one, separating their contents with a blank line. -/
private def mergeAdjacentModuleDocs (s : String) : String :=
  s.replace "\n-/\n\n/-!\n" "\n\n"


/--
Shared implementation. Writes the extracted Lean project to
`_out/<destSlug>/<variant>/lean/`, next to that variant's `html/`
(which `manualMain` writes via `cfg.destination := "_out/<destSlug>/<variant>"`,
as `html-multi/`, renamed to `html/` by `SFLMeta.renameHtmlDir`).
`modPrefix` is the uppercase module prefix used for the generated chapters'
module names and paths (e.g. `"LF"`, `"HL"`, `"TS"`); it is normally the same
as `destSlug` uppercased, but the draft executable passes `modPrefix := "LF"`
with `destSlug := "lf-draft"` so its output lands under `LF/…` in a separate
tree that never clobbers the real `lf` build.
`variant` selects which typed source variant is written: `.solutions` the
solution-filled form, `.terse` the lecture form (`workinclass!` proofs and
solutions stubbed), and `.student` the student form.
`verify` runs `lake build` on the extracted project to confirm it compiles;
the draft emitter passes `verify := false`, since its not-yet-graduated
chapters are not expected to build standalone. -/
private def emitSavedImpl (config : ExtractConfig)
    (crossVol : List (String × Part Manual) := []) :
    Mode → Config → TraverseState → Part Manual → BuildLogT IO Unit :=
  fun _mode _cfg _state text => do
    let width := Text.fillWidthFor <| config.variant
    let mut buf : SaveBuffers := walkOuter width config.modPrefix text {}
    -- Cross-volume Verso prerequisites (e.g. `LF.Typeclasses`, imported by
    -- `HL.Imp`) are chapters of an *earlier* volume that a chapter here depends
    -- on.  They are authored in Verso just like this volume's own chapters, so
    -- they must go through the same transformation rather than be copied
    -- verbatim (a Verso `#doc` file is not plain Lean and won't compile as a
    -- bundled prerequisite).  Walk each into the buffer under its own volume
    -- prefix, producing e.g. `LF/Typeclasses.lean` with the same import
    -- preamble reconstruction and variant selection as a native chapter.  This
    -- also adds the module to `chapterModules` below, which keeps it out of the
    -- verbatim bundle; its prefix becomes an extra `lean_lib` (see `extraLibs`).
    for (pre, part) in crossVol do
      let chFile := chapterPath pre part
      buf := buf.appendOnly chFile .grading "import AutograderLib\n"
      buf := buf.appendAll chFile s!"import {supportModuleName config.modPrefix}\n\n"
      buf := walkSection width 1 chFile part buf
    let toolchain ← (IO.FS.readFile "lean-toolchain").toBaseIO >>= fun
      | .ok s => pure s
      | .error _ => pure "leanprover/lean4:v4.30.0-rc2\n"
    let supportModuleTemplate ← readSFLCompat
    let rootFile := config.modPrefix ++ ".lean"
    -- Snapshot the buffer as a list so we can read source files (IO) per entry.
    let entries := buf.fold (init := [])
      fun acc k v => (k, v) :: acc
    -- Emitted book chapters: buffer keys with a path separator (the root
    -- `<Vol>.lean` has none). `HL/Imp.lean` ⇒ module `HL.Imp`.
    let chapterModules := entries.map (·.1) |>.filter (·.any (· == '/'))
      |>.map fun k => ((k.dropEnd 5).toString).replace "/" "."
    let needsBundle (m : String) : Bool :=
      keepImport m && ! corePrefixes.contains (modTop m)
        && ! pkgPrefixes.contains (modTop m) && ! chapterModules.contains m
    -- Pick the variant per file; prepend each chapter's (framework-stripped)
    -- import preamble; collect bundle seeds from the chapters' source imports.
    let mut files : Array (String × String) := #[(supportModulePath config.modPrefix, supportModuleTemplate)]
    let mut seeds : List String := []
    let mut usedPkgs : Array String := #[]
    for (file, vs) in entries do
      let chosen := mergeAdjacentModuleDocs <| vs.get config.variant
      if file == rootFile then
        files := files.push (file, chosen)
      else
        -- The buffer key is the chapter's repo-relative source path, so read its
        -- real header imports and re-emit the non-framework ones.
        let src ← (IO.FS.readFile file).toBaseIO >>= fun
          | .ok s => pure s
          | .error _ => pure ""
        let imps := (headerImports src).toList.filter keepImport
        seeds := seeds ++ imps.filter needsBundle
        for i in imps do
          if pkgPrefixes.contains (modTop i) && ! usedPkgs.contains (modTop i) then
            usedPkgs := usedPkgs.push (modTop i)
        let preamble := imps.foldl (init := "") fun acc i => acc ++ "import " ++ i ++ "\n"
        let preamble := if preamble.isEmpty then "" else preamble ++ "\n"
        files := files.push (file, preamble ++ chosen)
    let (bundleFiles, bundleLibs) ← bundleLoop needsBundle seeds [] #[] #[]
    -- The cross-volume prerequisite chapters emitted above (under their own
    -- volume prefix, e.g. `LF/Typeclasses.lean`) each need their prefix declared
    -- as a `lean_lib` in the generated `lakefile.toml`, just like a verbatim
    -- bundle does.
    let extraLibs := crossVol.foldl (init := bundleLibs) fun acc (pre, _) =>
      if acc.contains pre then acc else acc.push pre
    let allFiles := files ++ bundleFiles
    -- Chapters importing an external package (e.g. Batteries) need the
    -- extracted lakefile to `require` it, pinned to the book's own revision.
    let mut pkgRequires : Array (String × String × String) := #[]
    for pre in usedPkgs do
      let name := pre.toLower
      match ← manifestPin name with
      | .some (url, rev) => pkgRequires := pkgRequires.push (name, url, rev)
      | .none => reportError <|
          s!"package '{name}' (needed for `import {pre}.…` in an extracted " ++
          s!"chapter) is not in lake-manifest.json, so the extracted project " ++
          s!"cannot pin it"
    let dest := System.FilePath.mk "_out" / config.destSlug / config.variant.toString / "lean"
    writeProject dest toolchain config.modPrefix config.variant allFiles extraLibs pkgRequires
    if config.verify then buildProject dest config.variant

/-- `ExtraStep` for the student build: solutions elided.  `crossVol` lists any
Verso chapters from earlier volumes that a chapter here imports (see
`emitSavedImpl`), as `(volume-prefix, chapter-part)` pairs. -/
def emitSavedStudent (vol : String) (crossVol : List (String × Part Manual) := []) :=
    emitSavedImpl (ExtractConfig.fromVolume vol .student true) crossVol

/-- `ExtraStep` for the solutions build: solutions shown. -/
def emitSavedSolutions (vol : String) (crossVol : List (String × Part Manual) := []) :=
    emitSavedImpl (ExtractConfig.fromVolume vol .solutions true) crossVol

/-- `ExtraStep` for the terse build: solutions elided and `workinclass!`
proofs stubbed to `sorry`. -/
def emitSavedTerse (vol : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .terse true) crossVol

def emitSavedGrading (vol : String) (crossVol : List (String × Part Manual) := []) :=
  emitSavedImpl (ExtractConfig.fromVolume vol .grading true) crossVol


end SFLMeta.Save
