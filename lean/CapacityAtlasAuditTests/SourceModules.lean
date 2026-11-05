/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasAuditCore.SourceModules
import Lean.Elab.Command

open CapacityAtlas.Audit

run_cmd do
  Lean.Elab.Command.liftIO <| IO.FS.withTempDir fun directory => do
    let emptyRejected ← try
      let _ ← discoverSourceModules directory
      pure false
    catch error =>
      pure ((error.toString.splitOn "Lean package directory").length > 1)
    unless emptyRejected do
      throw <| IO.userError "source discovery accepted a directory outside the Lean package"
    IO.FS.writeFile (directory / "lakefile.toml") ""
    for root in #["CapacityAtlas", "CapacityAtlasForMathlib", "CapacityAtlasUtil"] do
      IO.FS.writeFile (directory / s!"{root}.lean") ""
      IO.FS.createDirAll (directory / root)
    let nested := directory / "CapacityAtlasForMathlib" / "Unimported"
    IO.FS.createDirAll nested
    IO.FS.writeFile (nested / "NewTheorem.lean") ""
    IO.FS.writeFile (nested / "DeletedTheorem.olean") ""
    IO.FS.writeFile (directory / "Unrelated.lean") ""
    let modules ← discoverSourceModules directory
    let expected := #[`CapacityAtlas, `CapacityAtlasForMathlib,
      `CapacityAtlasForMathlib.Unimported.NewTheorem, `CapacityAtlasUtil]
    unless modules == expected.qsort Lean.Name.quickLt do
      throw <| IO.userError s!"source discovery omitted a current module or included stale artifacts: {modules}"
