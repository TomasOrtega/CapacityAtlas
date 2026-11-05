/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasAuditCore
import CapacityAtlas.Claims.GaussianWiretap

open Lean CapacityAtlas.Audit CapacityAtlas.Metadata

namespace CapacityAtlasAuditTests.TrustBoundary

@[capacity_problem "audit-fixture", capacity_claim "shared-research" 1,
  capacity_statement, capacity_solved, capacity_shared_api]
theorem sharedResearch : True := True.intro

run_meta do
  let env ← getEnv
  let declaration := `CapacityAtlas.Claims.gaussianWiretap
  unless (← Lean.collectAxioms declaration).contains ``sorryAx do
    throwError "trust fixture no longer refers to an admitted research claim"
  let some moduleIndex := env.getModuleIdxFor? declaration
    | throwError "trust fixture is missing its imported module"
  let problemModule := env.header.moduleNames[moduleIndex]!
  unless ← allowsResearchAdmission env problemModule declaration do
    throwError "audit policy rejected a registered problem-layer research admission"
  for moduleName in #[`CapacityAtlasForMathlib.InformationTheory, `CapacityAtlasUtil.Metadata] do
    if ← allowsResearchAdmission env moduleName declaration then
      throwError "audit policy permitted a research admission in the trusted library {moduleName}"
  if ← allowsResearchAdmission env `CapacityAtlas.Claims ``sharedResearch then
    throwError "audit policy permitted a reusable API research admission"

end CapacityAtlasAuditTests.TrustBoundary
