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

namespace CapacityAtlas.TwoWay

variable {A B Y Z : Type*} [Fintype A] [Fintype B] [Fintype Y] [Fintype Z]

/-- Message 1 travels to output Z. Each terminal knows its own message and past outputs. -/
structure Code (W : FiniteChannel (A × B) (Y × Z)) (n : ℕ) where
  messages₁ : ℕ
  messages₂ : ℕ
  messages₁_pos : 0 < messages₁
  messages₂_pos : 0 < messages₂
  encode₁ : Fin messages₁ → (t : Fin n) → (Fin t.val → Y) → A
  encode₂ : Fin messages₂ → (t : Fin n) → (Fin t.val → Z) → B
  decode₁ : Fin messages₁ → (Fin n → Y) → Fin messages₂
  decode₂ : Fin messages₂ → (Fin n → Z) → Fin messages₁

noncomputable def error {W : FiniteChannel (A × B) (Y × Z)} {n : ℕ}
    (c : Code W n) : ℝ := by
  classical
  exact (c.messages₁ * c.messages₂ : ℝ)⁻¹ *
    ∑ m₁, ∑ m₂, ∑ y : Fin n → Y, ∑ z : Fin n → Z,
      if c.decode₁ m₁ y = m₂ ∧ c.decode₂ m₂ z = m₁ then 0 else
        ∏ t, W.transition
          (c.encode₁ m₁ t (CausalHistories.past y t),
            c.encode₂ m₂ t (CausalHistories.past z t)) (y t, z t)

noncomputable def rates {W : FiniteChannel (A × B) (Y × Z)} {n : ℕ}
    (c : Code W n) : RatePair :=
  (Operational.messageRate c.messages₁ n, Operational.messageRate c.messages₂ n)

noncomputable def capacityRegion (W : FiniteChannel (A × B) (Y × Z)) : Set RatePair :=
  Operational.achievableRegion (Code W) (fun _ _ ↦ True)
    (fun _ c ↦ error c) (fun _ c ↦ rates c)

noncomputable def rectangle (W : FiniteChannel (A × B) (Y × Z))
    (p : FiniteDistribution (A × B)) : Set RatePair :=
  let q := FiniteInformation.joint p W
  {r : RatePair | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    r.1 ≤ FiniteInformation.conditional q (fun a ↦ a.1.1) (fun a ↦ a.2.2)
      (fun a ↦ a.1.2) ∧
    r.2 ≤ FiniteInformation.conditional q (fun a ↦ a.1.2) (fun a ↦ a.2.1)
      (fun a ↦ a.1.1)}

noncomputable def shannonInner (W : FiniteChannel (A × B) (Y × Z)) : Set RatePair :=
  closure (convexHull ℝ {r | ∃ p : FiniteDistribution A, ∃ q : FiniteDistribution B,
    r ∈ rectangle W (FiniteInformation.independent p q)})

noncomputable def shannonOuter (W : FiniteChannel (A × B) (Y × Z)) : Set RatePair :=
  closure {r | ∃ p : FiniteDistribution (A × B), r ∈ rectangle W p}

/-- Independent noises, with the self-input included in the physical law. -/
noncomputable def additiveChannel {G : Type*} [Fintype G] [AddCommGroup G]
    (noise₁ noise₂ : FiniteDistribution G) : FiniteChannel (G × G) (G × G) := by
  classical
  exact FiniteChannel.ofRows fun input ↦
    (FiniteInformation.independent noise₁ noise₂).map
      (fun z ↦ (input.1 + input.2 + z.1, input.1 + input.2 + z.2))

end CapacityAtlas.TwoWay
