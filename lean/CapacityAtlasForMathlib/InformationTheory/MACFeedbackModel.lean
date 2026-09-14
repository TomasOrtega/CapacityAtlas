/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.CausalHistories
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion
import Mathlib.Analysis.Convex.Hull

open scoped BigOperators

namespace CapacityAtlas.MACFeedback

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-- Both encoders receive the same strictly causal output feedback. -/
structure Code (W : FiniteChannel (X₁ × X₂) Y) (n : ℕ) where
  messages₁ : ℕ
  messages₂ : ℕ
  messages₁_pos : 0 < messages₁
  messages₂_pos : 0 < messages₂
  encode₁ : Fin messages₁ → (t : Fin n) → (Fin t.val → Y) → X₁
  encode₂ : Fin messages₂ → (t : Fin n) → (Fin t.val → Y) → X₂
  decode : (Fin n → Y) → Fin messages₁ × Fin messages₂

noncomputable def error {W : FiniteChannel (X₁ × X₂) Y} {n : ℕ}
    (c : Code W n) : ℝ := by
  classical
  exact (c.messages₁ * c.messages₂ : ℝ)⁻¹ * ∑ m₁, ∑ m₂, ∑ y : Fin n → Y,
    if c.decode y = (m₁, m₂) then 0 else
      ∏ t, W.transition
        (c.encode₁ m₁ t (CausalHistories.past y t),
          c.encode₂ m₂ t (CausalHistories.past y t)) (y t)

noncomputable def rates {W : FiniteChannel (X₁ × X₂) Y} {n : ℕ}
    (c : Code W n) : RatePair :=
  (Operational.messageRate c.messages₁ n, Operational.messageRate c.messages₂ n)

noncomputable def capacityRegion (W : FiniteChannel (X₁ × X₂) Y) : Set RatePair :=
  Operational.achievableRegion (Code W) (fun _ _ ↦ True)
    (fun _ c ↦ error c) (fun _ c ↦ rates c)

/-- Cover--Leung: conditional input independence, but an unconditional sum bound. -/
noncomputable def coverLeung (W : FiniteChannel (X₁ × X₂) Y) : Set RatePair :=
  closure (convexHull ℝ {r : RatePair | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ u : ℕ, ∃ p : FiniteDistribution (Fin u),
    ∃ a : FiniteChannel (Fin u) X₁, ∃ b : FiniteChannel (Fin u) X₂,
      let inputs := FiniteInformation.joint p
        (FiniteChannel.ofRows fun v ↦ FiniteInformation.independent
          (a.rowDistribution v) (b.rowDistribution v))
      let q := FiniteInformation.joint inputs (W.encoded Prod.snd)
      r.1 ≤ FiniteInformation.conditional q (fun z ↦ z.1.2.1) Prod.snd
        (fun z ↦ (z.1.1, z.1.2.2)) ∧
      r.2 ≤ FiniteInformation.conditional q (fun z ↦ z.1.2.2) Prod.snd
        (fun z ↦ (z.1.1, z.1.2.1)) ∧
      r.1 + r.2 ≤ FiniteInformation.information q (fun z ↦ z.1.2) Prod.snd})

/-- All inequalities and the dependence constraint use one joint law. -/
noncomputable def dependenceBalance (W : FiniteChannel (X₁ × X₂) Y) : Set RatePair :=
  closure {r : RatePair | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ t : ℕ, ∃ p : FiniteDistribution (Fin t × X₁ × X₂),
      let q := FiniteInformation.joint p (W.encoded Prod.snd)
      FiniteInformation.conditional q (fun z ↦ z.1.2.1) (fun z ↦ z.1.2.2)
          (fun z ↦ z.1.1) ≤
        FiniteInformation.conditional q (fun z ↦ z.1.2.1) (fun z ↦ z.1.2.2)
          (fun z ↦ (z.1.1, z.2)) ∧
      r.1 ≤ FiniteInformation.conditional q (fun z ↦ z.1.2.1) Prod.snd
        (fun z ↦ (z.1.1, z.1.2.2)) ∧
      r.2 ≤ FiniteInformation.conditional q (fun z ↦ z.1.2.2) Prod.snd
        (fun z ↦ (z.1.1, z.1.2.1)) ∧
      r.1 + r.2 ≤ FiniteInformation.conditional q (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1)}

end CapacityAtlas.MACFeedback
