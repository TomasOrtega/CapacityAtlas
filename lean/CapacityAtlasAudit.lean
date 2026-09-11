/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlas
import CapacityAtlasAuditCore

open Lean

namespace CapacityAtlas.Audit

private def runAudit : IO Report := do
  unsafe Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `CapacityAtlas }] {} (loadExts := true)
  let context : Core.Context := { fileName := "", fileMap := default }
  let state : Core.State := { env }
  Prod.fst <$> (audit env).toIO context state

def run (_args : List String) : IO UInt32 := do
  let report ← runAudit
  IO.println (toJson report).compress
  for error in report.errors do
    IO.eprintln s!"error: {error}"
  return if report.errors.isEmpty then 0 else 1

end CapacityAtlas.Audit

def main (args : List String) : IO UInt32 :=
  CapacityAtlas.Audit.run args
