/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.RateRegion

namespace CapacityAtlas.Operational

/-- Rate of a positive finite message set, in bits per physical channel use.
The zero-blocklength value is immaterial: achievability only uses positive lengths. -/
noncomputable def messageRate (messages blocklength : ℕ) : ℝ :=
  Real.logb 2 messages / blocklength

/-- Rate-closed, nonnegative vanishing-average-error achievability.
Unlike `FiniteChannel.AchievableRate`, this includes an epsilon rate tolerance.
Their rates need not agree at the boundary. The named obligations in
`CapacityAtlas.Obligations.Interfaces` state the intended closure and supremum bridges.
These bridges are proof tasks, not hypotheses used to define capacity. -/
def Achievable (Code : ℕ → Type*)
    (admissible : ∀ n, Code n → Prop) (error rate : ∀ n, Code n → ℝ)
    (target : ℝ) : Prop :=
  0 ≤ target ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ n, N ≤ n → ∃ code : Code n,
      admissible n code ∧ error n code ≤ ε ∧ target - ε ≤ rate n code

/-- Scalar operational capacity for a specified family of physical codes. -/
noncomputable def capacity (Code : ℕ → Type*)
    (admissible : ∀ n, Code n → Prop) (error rate : ∀ n, Code n → ℝ) : ℝ :=
  sSup {target | Achievable Code admissible error rate target}

/-- Closed two-message achievable region, with one shared error and rate tolerance. -/
def achievableRegion (Code : ℕ → Type*)
    (admissible : ∀ n, Code n → Prop) (error : ∀ n, Code n → ℝ)
    (rates : ∀ n, Code n → RatePair) : Set RatePair :=
  {target | 0 ≤ target.1 ∧ 0 ≤ target.2 ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      ∃ code : Code n, admissible n code ∧ error n code ≤ ε ∧
        target.1 - ε ≤ (rates n code).1 ∧ target.2 - ε ≤ (rates n code).2}

end CapacityAtlas.Operational
