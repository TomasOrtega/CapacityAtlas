/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.Fin.Tuple.Basic

namespace CapacityAtlas.CausalHistories

/-- Only the strictly past part of the physical transcript is revealed. -/
def past {A : Type*} {n : ℕ} (word : Fin n → A) (t : Fin n) : Fin t.val → A :=
  fun j ↦ word ⟨j.val, Nat.lt_trans j.isLt t.isLt⟩

/-- Evaluate a causal deterministic recursion in chronological order. -/
def run {Y Z : Type*} {n : ℕ} (initial : Y)
    (step : (t : Fin n) → (Fin t.val → Y) → Z → Y) (noise : Fin n → Z) : Fin n → Y :=
  (List.finRange n).foldl
    (fun history t ↦ Function.update history t (step t (past history t) (noise t)))
    (fun _ ↦ initial)

end CapacityAtlas.CausalHistories
