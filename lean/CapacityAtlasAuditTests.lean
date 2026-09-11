/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasAuditCore
import CapacityAtlasAuditTests.Fixtures

open Lean CapacityAtlas.Audit

run_meta do
  let report ← audit (← getEnv)
  let fixtures := "CapacityAtlasAuditTests.Fixtures."
  let expected := #[
    ("wrongType", "must be a definition returning Prop"),
    ("proofTerm", "must be a definition returning Prop"),
    ("localProof", "cannot be marked [capacity_formal_proof]"),
    ("api", "requires an open or solved category"),
    ("test", "requires an open or solved category"),
    ("missingIdentity", "requires [capacity_claim]"),
    ("taggedTheorem", "must be a definition returning Prop")
  ]
  for (declaration, message) in expected do
    unless report.errors.any (fun error =>
        error.startsWith (fixtures ++ declaration ++ ":") && (error.splitOn message).length > 1) do
      throwError "audit failed to reject {declaration}: {message}"
  for declaration in #["parameterized", "reducedResult", "provedTheorem"] do
    if report.errors.any (·.startsWith (fixtures ++ declaration ++ ":")) then
      throwError "audit rejected valid declaration {declaration}"
  let some proposition := report.declarations.find? (·.declaration == fixtures ++ "parameterized")
    | throwError "audit omitted parameterized proposition"
  unless proposition.proposition && !proposition.formalProof && proposition.axioms.isEmpty do
    throwError "audit misclassified parameterized proposition"
  let some theoremRecord := report.declarations.find? (·.declaration == fixtures ++ "provedTheorem")
    | throwError "audit omitted proved theorem"
  unless !theoremRecord.proposition && theoremRecord.formalProof do
    throwError "audit misclassified proved theorem"
