/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Basic

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteChannel

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

@[capacity_shared_api]
theorem comp_assoc (V : FiniteChannel C D) (W : FiniteChannel B C)
    (T : FiniteChannel A B) : (V.comp W).comp T = V.comp (W.comp T) := by
  ext a d
  simp only [comp, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ (mul_assoc _ _ _).symm

@[capacity_shared_api]
theorem block_comp (W : FiniteChannel B C) (T : FiniteChannel A B) (n : ℕ) :
    (W.comp T).block n = (W.block n).comp (T.block n) := by
  ext a c
  change (∏ i, ∑ b, T.transition (a i) b * W.transition b (c i)) =
    ∑ b : Fin n → B, (∏ i, T.transition (a i) (b i)) * ∏ i, W.transition (b i) (c i)
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.prod_mul_distrib

end FiniteChannel

namespace ConfidentialBroadcast

variable {X V Y Z : Type*} [Fintype X] [Fintype V] [Fintype Y] [Fintype Z]

def prefixed (W : FiniteBroadcastChannel X Y Z) (P : FiniteChannel V X) :
    FiniteBroadcastChannel V Y Z := ⟨W.receiver₁.comp P, W.receiver₂.comp P⟩

namespace Code

variable {W : FiniteBroadcastChannel X Y Z} {P : FiniteChannel V X} {n : ℕ}

def liftPrefix (c : Code (prefixed W P) n) : Code W n where
  commonCount := c.commonCount
  secretCount := c.secretCount
  commonCount_pos := c.commonCount_pos
  secretCount_pos := c.secretCount_pos
  encode := (P.block n).comp c.encode
  decodeLegitimate := c.decodeLegitimate
  decodeCommon := c.decodeCommon

@[simp]
theorem prefix_messages (c : Code (prefixed W P) n) : c.liftPrefix.messages = c.messages := rfl

@[simp]
theorem prefix_induced {O : Type*} [Fintype O] (c : Code (prefixed W P) n)
    (T : FiniteChannel X O) : c.liftPrefix.induced T = c.induced (T.comp P) := by
  simp only [induced, liftPrefix, FiniteChannel.block_comp, FiniteChannel.comp_assoc]
  rfl

@[simp]
theorem prefix_joint {O : Type*} [Fintype O] (c : Code (prefixed W P) n)
    (T : FiniteChannel X O) : c.liftPrefix.joint T = c.joint (T.comp P) := by
  simp only [joint, prefix_messages, prefix_induced]
  rfl

@[simp]
theorem prefix_legitimateError (c : Code (prefixed W P) n) :
    c.liftPrefix.legitimateError = c.legitimateError := by
  classical
  change (∑ a, ∑ y, if c.decodeLegitimate y = a then 0 else
    c.messages a * (c.liftPrefix.induced W.receiver₁).transition a y) = _
  rw [prefix_induced]
  rfl

@[simp]
theorem prefix_commonError (c : Code (prefixed W P) n) :
    c.liftPrefix.commonError = c.commonError := by
  classical
  change (∑ a, ∑ z, if c.decodeCommon z = a.1 then 0 else
    c.messages a * (c.liftPrefix.induced W.receiver₂).transition a z) = _
  rw [prefix_induced]
  rfl

@[simp]
theorem prefix_error (c : Code (prefixed W P) n) : c.liftPrefix.error = c.error := by
  simp only [error, prefix_legitimateError, prefix_commonError]

@[simp]
theorem prefix_leakage (c : Code (prefixed W P) n) : c.liftPrefix.leakage = c.leakage := by
  simp only [leakage, prefix_joint, prefixed]
  rfl

@[simp]
theorem prefix_defect (c : Code (prefixed W P) n) : c.liftPrefix.defect = c.defect := by
  simp only [defect, prefix_error, prefix_leakage]

@[simp]
theorem prefix_rates (c : Code (prefixed W P) n) : c.liftPrefix.rates = c.rates := rfl

end Code

theorem capacityRegion_prefixed_subset (W : FiniteBroadcastChannel X Y Z)
    (P : FiniteChannel V X) : capacityRegion (prefixed W P) ⊆ capacityRegion W := by
  intro r hr
  refine ⟨hr.1, hr.2.1, fun ε hε ↦ ?_⟩
  obtain ⟨N, hN, hcodes⟩ := hr.2.2 ε hε
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  obtain ⟨c, _, hdefect, hcommon, hsecret⟩ := hcodes n hn
  exact ⟨c.liftPrefix, trivial, by simpa only [Code.prefix_defect] using hdefect, hcommon, hsecret⟩

end ConfidentialBroadcast

end CapacityAtlas
