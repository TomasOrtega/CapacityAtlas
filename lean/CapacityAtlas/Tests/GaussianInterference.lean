/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.BasicFacts

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.Tests

private def interferenceMessageCounts : Fin 2 → ℕ := ![2, 3]

private def firstInterferenceMessage (i : Fin 2) : Fin (interferenceMessageCounts i) :=
  ⟨0, by fin_cases i <;> decide⟩

private def interferenceTestCode : Gaussian.Interference.Code 2 1 where
  messages := interferenceMessageCounts
  messages_pos i := by fin_cases i <;> decide
  encode := fun i _ _ _ => if i = 0 then 1 else Complex.I
  encode_measurable _ _ _ := measurable_const
  encode_causal _ _ _ _ _ _ := rfl
  decode i :=
    { apply := fun _ => firstInterferenceMessage i
      measurable_fiber m := by
        change MeasurableSet {_x | firstInterferenceMessage i = m}
        by_cases h : firstInterferenceMessage i = m <;> simp [h] }

@[capacity_test]
theorem interference_power_shared_across_users (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Gaussian.Interference.PowerAdmissible μ 2 interferenceTestCode ∧
      ¬Gaussian.Interference.PowerAdmissible μ 1 interferenceTestCode := by
  have he (m : interferenceTestCode.Message) (H : Gaussian.Interference.StateBlock 2 1) :
      Gaussian.Interference.energy interferenceTestCode m H = 2 := by
    simp only [Gaussian.Interference.energy, Fin.sum_univ_one, Fin.sum_univ_two]
    change ‖(1 : ℂ)‖ ^ 2 + ‖Complex.I‖ ^ 2 = 2
    norm_num
  have hint (m : interferenceTestCode.Message) :
      Integrable (Gaussian.Interference.energy interferenceTestCode m)
        (Gaussian.Interference.stateLaw μ 2 1) := by
    simp_rw [show Gaussian.Interference.energy interferenceTestCode m = fun _ => 2 from funext (he m)]
    exact integrable_const _
  have hc : Fintype.card interferenceTestCode.Message = 6 := by
    change Fintype.card ((i : Fin 2) → Fin (interferenceMessageCounts i)) = 6
    rw [Fintype.card_pi]
    norm_num [interferenceMessageCounts, Fin.prod_univ_succ]
  have hv : (∏ i, (interferenceTestCode.messages i : ℝ))⁻¹ *
      (∑ m, ∫ H, Gaussian.Interference.energy interferenceTestCode m H
        ∂Gaussian.Interference.stateLaw μ 2 1) = 2 := by
    simp_rw [he]
    norm_num [hc, interferenceTestCode, interferenceMessageCounts, Fin.prod_univ_succ]
  simp only [Gaussian.Interference.PowerAdmissible, hint, hv]
  norm_num

@[capacity_test]
theorem interference_joint_error (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    Gaussian.Interference.error μ interferenceTestCode = (5 / 6 : ℝ) := by
  classical
  have he (m : interferenceTestCode.Message) :
      Gaussian.Interference.errorEvent interferenceTestCode m =
        if m = firstInterferenceMessage then ∅ else Set.univ := by
    ext hz
    change (∃ i, firstInterferenceMessage i ≠ m i) ↔
      hz ∈ if m = firstInterferenceMessage then ∅ else Set.univ
    by_cases h : m = firstInterferenceMessage
    · subst m
      simp
    · have hi : ∃ i, firstInterferenceMessage i ≠ m i := by
        by_contra hn
        push Not at hn
        exact h (funext hn).symm
      simp [h, hi]
  have hc : Fintype.card interferenceTestCode.Message = 6 := by
    change Fintype.card ((i : Fin 2) → Fin (interferenceMessageCounts i)) = 6
    rw [Fintype.card_pi]
    norm_num [interferenceMessageCounts, Fin.prod_univ_succ]
  unfold Gaussian.Interference.error
  simp_rw [he]
  simp only [apply_ite, measure_empty, measure_univ, ENNReal.toReal_zero, ENNReal.toReal_one]
  have hs : (∑ m : interferenceTestCode.Message,
      if m = firstInterferenceMessage then (0 : ℝ) else 1) = 5 := by
    calc
      _ = ∑ m : interferenceTestCode.Message,
          (1 - if m = firstInterferenceMessage then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro m _
        split_ifs <;> norm_num
      _ = 5 := by norm_num [Finset.sum_sub_distrib, hc]
  rw [hs]
  norm_num [interferenceTestCode, interferenceMessageCounts, Fin.prod_univ_succ]

end CapacityAtlas.Tests
