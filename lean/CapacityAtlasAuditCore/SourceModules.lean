/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Lean.Data.Name
import Lean.Util.Path

namespace CapacityAtlas.Audit

/-- Discover every current library source module under the Lean package directory. -/
def discoverSourceModules (packageDir : System.FilePath) : IO (Array Lean.Name) := do
  let roots := #[`CapacityAtlas, `CapacityAtlasForMathlib, `CapacityAtlasUtil]
  let invalidPackage := IO.userError
    s!"capacity_audit requires the Lean package directory: {packageDir}; expected lakefile.toml and all three library source roots"
  unless ← (packageDir / "lakefile.toml").pathExists do
    throw invalidPackage
  let mut modules := #[]
  for root in roots do
    let source := packageDir / s!"{root}.lean"
    let directory := packageDir / root.toString
    unless (← source.pathExists) && (← directory.isDir) do
      throw invalidPackage
    modules := modules.push root
    let found ← IO.mkRef #[]
    Lean.forEachModuleInDir directory fun name => do
      found.modify (·.push (root ++ name))
    modules := modules ++ (← found.get)
  return modules.qsort Lean.Name.quickLt

end CapacityAtlas.Audit
