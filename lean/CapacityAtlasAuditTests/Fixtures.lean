/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata

namespace CapacityAtlasAuditTests.Fixtures

@[capacity_problem "audit-fixture", capacity_claim "parameterized" 1,
  capacity_statement, capacity_proposition, capacity_solved]
def parameterized (α : Type) (x : α) : Prop := x = x

abbrev PropositionSort := Prop

@[capacity_problem "audit-fixture", capacity_claim "reduced-result" 1,
  capacity_statement, capacity_proposition, capacity_open]
def reducedResult (n : Nat) : PropositionSort := n = n

@[capacity_problem "audit-fixture", capacity_claim "wrong-type" 1,
  capacity_statement, capacity_proposition, capacity_solved]
def wrongType (n : Nat) : Nat := n

set_option linter.defProp false in
@[capacity_problem "audit-fixture", capacity_claim "proof-term" 1,
  capacity_statement, capacity_proposition, capacity_solved]
def proofTerm : True := trivial

@[capacity_problem "audit-fixture", capacity_claim "local-proof" 1,
  capacity_statement, capacity_proposition, capacity_solved, capacity_formal_proof]
def localProof : Prop := True

@[capacity_problem "audit-fixture", capacity_claim "api" 1,
  capacity_statement, capacity_proposition, capacity_api]
def api : Prop := True

@[capacity_problem "audit-fixture", capacity_claim "test" 1,
  capacity_statement, capacity_proposition, capacity_test]
def test : Prop := True

@[capacity_proposition]
def missingIdentity : Prop := True

@[capacity_problem "audit-fixture", capacity_claim "theorem" 1,
  capacity_statement, capacity_proposition, capacity_solved]
theorem taggedTheorem : True := trivial

@[capacity_problem "audit-fixture", capacity_claim "proved-theorem" 1,
  capacity_statement, capacity_solved, capacity_formal_proof]
theorem provedTheorem : True := trivial

end CapacityAtlasAuditTests.Fixtures
