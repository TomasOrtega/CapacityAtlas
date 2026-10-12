/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Capacity

namespace CapacityAtlas.Tests

open ConfidentialBroadcast FiniteInformation

@[capacity_test]
theorem confidentialBroadcast_identical_receivers {X Y : Type*} [Fintype X] [Fintype Y]
    (W : FiniteBroadcastChannel X Y Y) (hW : W.receiver₁ = W.receiver₂)
    {r : RatePair} (hr : r ∈ capacityRegion W) : r.2 = 0 := by
  have haux : auxiliaryRegion W ⊆ {r : RatePair | r.2 = 0} := by
    rintro s ⟨_, hs, u, v, p, P, _, _, hsecret⟩
    rw [hW, sub_self] at hsecret
    exact le_antisymm hsecret hs
  have hclosed : IsClosed {r : RatePair | r.2 = 0} :=
    isClosed_eq continuous_snd continuous_const
  exact closure_minimal haux hclosed (capacityRegion_subset_informationRegion W hr)

private def secretBitChannel : FiniteBroadcastChannel (Fin 2) (Fin 2) Unit where
  receiver₁ := FiniteChannel.deterministic id
  receiver₂ := FiniteChannel.deterministic (fun _ ↦ ())

private noncomputable abbrev secretBitCode : Code secretBitChannel 1 where
  commonCount := 1
  secretCount := 2
  commonCount_pos := by decide
  secretCount_pos := by decide
  encode := FiniteChannel.deterministic (fun m _ ↦ m.2)
  decodeLegitimate y := (0, y 0)
  decodeCommon _ := 0

@[capacity_test]
theorem confidentialBroadcast_secret_bit_rates : secretBitCode.rates = (0, 1) := by
  norm_num [Code.rates, Operational.messageRate, Real.logb]

@[capacity_test]
theorem confidentialBroadcast_secret_bit_error : secretBitCode.error = 0 := by
  have hleg : secretBitCode.legitimateError = 0 := by
    classical
    unfold Code.legitimateError
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro y _
    by_cases h : y 0 = m.2
    · have hm : secretBitCode.decodeLegitimate y = m := by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact h
      change (0, y 0) = m at hm
      simp only [hm, ite_true]
    · have ht : (secretBitCode.induced secretBitChannel.receiver₁).transition m y = 0 := by
        simp only [Code.induced, FiniteChannel.comp, FiniteChannel.deterministic,
          FiniteChannel.block_transition]
        apply Finset.sum_eq_zero
        intro x _
        by_cases hx : x = fun _ ↦ m.2
        · subst x
          simp [secretBitChannel, FiniteChannel.deterministic, h]
        · simp [hx]
      simp only [ht, mul_zero, ite_self]
  have hcommon : secretBitCode.commonError = 0 := by
    classical
    unfold Code.commonError
    apply Finset.sum_eq_zero
    intro m _
    apply Finset.sum_eq_zero
    intro z _
    have hm : (0 : Fin 1) = m.1 := Subsingleton.elim _ _
    simp only [hm, ite_true]
  simp only [Code.error, hleg, hcommon, max_self]

@[capacity_test]
theorem confidentialBroadcast_secret_bit_leakage : secretBitCode.leakage = 0 := by
  let p := secretBitCode.joint secretBitChannel.receiver₂
  let f : (Fin 1 × Fin 2) × (Fin 1 → Unit) → Fin 2 := fun a ↦ a.1.2
  let z : Fin 1 → Unit := fun _ ↦ ()
  have hg : (Prod.snd : (Fin 1 × Fin 2) × (Fin 1 → Unit) → (Fin 1 → Unit)) =
      fun _ ↦ z := by funext a; exact Subsingleton.elim _ _
  have he := entropy_comp_injective p f (fun s ↦ (s, z))
    (fun _ _ h ↦ (Prod.mk.inj h).1)
  simp only [Function.comp_def] at he
  unfold Code.leakage
  norm_num only [Nat.cast_one, div_one]
  change information p f Prod.snd = 0
  rw [hg, information, entropy_const, he]
  ring

end CapacityAtlas.Tests
