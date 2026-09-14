/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.FiniteMixture
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion

open scoped BigOperators

namespace CapacityAtlas.ArbitrarilyVarying

variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

/-- The jammer knows the code but not the message. Neither terminal sees the state. -/
structure Code (W : S → FiniteChannel X Y) (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → Fin n → X
  decode : (Fin n → Y) → Fin messages

noncomputable def errorAt {W : S → FiniteChannel X Y} {n : ℕ}
    (c : Code W n) (state : Fin n → S) : ℝ := by
  classical
  exact (c.messages : ℝ)⁻¹ * ∑ m, ∑ y : Fin n → Y,
    if c.decode y = m then 0 else
      ∏ t, (W (state t)).transition (c.encode m t) (y t)

/-- Supremum over states AFTER averaging over messages. -/
noncomputable def error {W : S → FiniteChannel X Y} {n : ℕ} (c : Code W n) : ℝ :=
  sSup (Set.range (errorAt c))

noncomputable def rate {W : S → FiniteChannel X Y} {n : ℕ} (c : Code W n) : ℝ :=
  Operational.messageRate c.messages n

noncomputable def capacity (W : S → FiniteChannel X Y) : ℝ :=
  Operational.capacity (Code W) (fun _ _ ↦ True) (fun _ c ↦ error c) (fun _ c ↦ rate c)

/-- The actual input-dependent symmetrizing jammer kernel. -/
def Symmetrizable (W : S → FiniteChannel X Y) : Prop :=
  ∃ U : FiniteChannel X S, ∀ x x' y,
    (∑ s, U.transition x' s * (W s).transition x y) =
      ∑ s, U.transition x s * (W s).transition x' y

noncomputable def averaged (W : S → FiniteChannel X Y) (q : FiniteDistribution S) :
    FiniteChannel X Y :=
  FiniteChannel.ofRows fun x ↦ q.mixture (fun s ↦ (W s).rowDistribution x)

noncomputable def randomCodeValue (W : S → FiniteChannel X Y) : ℝ :=
  sSup (Set.range fun p : FiniteDistribution X ↦
    sInf (Set.range fun q : FiniteDistribution S ↦ (averaged W q).mutualInformationBits p))

end CapacityAtlas.ArbitrarilyVarying
