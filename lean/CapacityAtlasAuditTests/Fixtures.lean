/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata

namespace CapacityAtlasAuditTests.Fixtures

/-- A parameterized proposition with valid canonical-claim metadata. -/
@[capacity_problem "audit-fixture", capacity_claim "parameterized" 1,
  capacity_statement, capacity_proposition, capacity_solved]
def parameterized (α : Type) (x : α) : Prop := x = x

/-- An alias used to test reduction of a canonical proposition's result sort. -/
abbrev PropositionSort := Prop

/-- A valid canonical proposition whose result sort reduces through an alias. -/
@[capacity_problem "audit-fixture", capacity_claim "reduced-result" 1,
  capacity_statement, capacity_proposition, capacity_open]
def reducedResult (n : Nat) : PropositionSort := n = n

/-- A non-propositional value that the canonical-proposition audit must reject. -/
@[capacity_problem "audit-fixture", capacity_claim "wrong-type" 1,
  capacity_statement, capacity_proposition, capacity_solved]
def wrongType (n : Nat) : Nat := n

set_option linter.defProp false in
/-- A proof term that must not be accepted as a definition returning `Prop`. -/
@[capacity_problem "audit-fixture", capacity_claim "proof-term" 1,
  capacity_statement, capacity_proposition, capacity_solved]
def proofTerm : True := trivial

/-- A canonical proposition incorrectly tagged as a local proof. -/
@[capacity_problem "audit-fixture", capacity_claim "local-proof" 1,
  capacity_statement, capacity_proposition, capacity_solved, capacity_formal_proof]
def localProof : Prop := True

/-- A canonical proposition incorrectly classified as reusable API. -/
@[capacity_problem "audit-fixture", capacity_claim "api" 1,
  capacity_statement, capacity_proposition, capacity_api]
def api : Prop := True

/-- A canonical proposition incorrectly classified as a structural test. -/
@[capacity_problem "audit-fixture", capacity_claim "test" 1,
  capacity_statement, capacity_proposition, capacity_test]
def test : Prop := True

/-- A canonical proposition lacking its required claim identity and version. -/
@[capacity_proposition]
def missingIdentity : Prop := True

@[capacity_problem "audit-fixture", capacity_claim "theorem" 1,
  capacity_statement, capacity_proposition, capacity_solved]
theorem taggedTheorem : True := trivial

@[capacity_problem "audit-fixture", capacity_claim "proved-theorem" 1,
  capacity_statement, capacity_solved, capacity_formal_proof]
theorem provedTheorem : True := trivial

end CapacityAtlasAuditTests.Fixtures
