/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasAuditCore
import CapacityAtlasAuditTests.Assumptions.Fixtures

open Lean CapacityAtlas.Audit

run_meta do
  let report ← audit (← getEnv)
  let fixtures := "CapacityAtlasAuditTests.Assumptions.Fixtures."
  for (declaration, type) in #[
      ("namedUnused", "True"), ("underscoreUnused", "True"),
      ("instanceUnused", "Nonempty"), ("dataUnused", "Nat"),
      ("suppressedUnused", "True")] do
    unless report.errors.any (fun error =>
        error.startsWith (fixtures ++ declaration ++ ":") &&
          (error.splitOn "unused argument 1:").length > 1 &&
          (error.splitOn type).length > 1) do
      throwError "audit failed to reject unused theorem argument in {declaration}"
  for declaration in #["necessaryProof", "finalResult", "laterBinderType", "propositionOnly"] do
    if report.errors.any (·.startsWith (fixtures ++ declaration ++ ":")) then
      throwError "audit rejected necessary theorem argument in {declaration}"
  let dependentErrors := report.errors.filter
    (·.startsWith (fixtures ++ "laterUnusedBinderType:"))
  unless dependentErrors.size == 1 &&
      (dependentErrors[0]!.splitOn "unused argument 2:").length > 1 do
    throwError "audit ignored a dependency in a later binder's type"
  if report.errors.any (fun error =>
      (error.splitOn "privateHelper").length > 1 &&
        (error.splitOn "unused argument").length > 1) then
    throwError "audit rejected a private helper"
