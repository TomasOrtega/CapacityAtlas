/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import Batteries.Tactic.Lint.Misc

set_option linter.unusedVariables false

namespace CapacityAtlasAuditTests.Assumptions.Fixtures

@[capacity_test]
theorem namedUnused (h : True) : True := True.intro

@[capacity_test]
theorem underscoreUnused (_h : True) : True := True.intro

@[capacity_test]
theorem instanceUnused [Nonempty Nat] : True := True.intro

@[capacity_test]
theorem dataUnused (n : Nat) : True := True.intro

@[capacity_test, nolint unusedArguments]
theorem suppressedUnused (_h : True) : True := True.intro

@[capacity_test]
theorem necessaryProof {p : Prop} (h : p) : p := h

@[capacity_test]
theorem finalResult (n : Nat) : n = n := rfl

@[capacity_test]
theorem laterBinderType (h : True) (proof : h = h) : proof = proof := rfl

@[capacity_test]
theorem laterUnusedBinderType (h : True) (_proof : h = h) : True := True.intro

@[capacity_test]
private theorem privateHelper (_h : True) : True := True.intro

/-- A proposition definition has no proof from which to infer redundant premises. -/
@[capacity_test]
def propositionOnly (_h : True) : Prop := True

end CapacityAtlasAuditTests.Assumptions.Fixtures
