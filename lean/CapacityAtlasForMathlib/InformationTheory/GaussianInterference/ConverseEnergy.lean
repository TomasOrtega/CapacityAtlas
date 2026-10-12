/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.CodePair

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

namespace CapacityAtlas.Gaussian.Interference

variable {K n : ℕ}

theorem measurable_userSignal (c : Code K n) (r i : Fin K) (a : Fin (c.messages i)) :
    Measurable fun H ↦ userSignal c H r i a := by
  apply measurable_realBlock.comp
  apply measurable_pi_lambda
  intro t
  exact (by fun_prop : Measurable fun H : StateBlock K n ↦ H t r i).mul
    (c.encode_measurable i a t)

theorem measurable_pairEnergy (c : Code K n) (i j : Fin K) (m : c.Message) :
    Measurable fun H ↦ pairEnergy c H i j m :=
  ((measurable_userSignal c i i (m i)).add
    (measurable_userSignal c i j (m j))).norm.pow_const 2

theorem pairEnergy_nonneg (c : Code K n) (H : StateBlock K n) (i j : Fin K)
    (m : c.Message) : 0 ≤ pairEnergy c H i j m := sq_nonneg _

theorem pairEnergy_le_energy (c : Code K n) (H : StateBlock K n) (i j : Fin K)
    (hij : i ≠ j) (m : c.Message) {U : ℝ} (_hU : 0 ≤ U)
    (hHi : ∀ s, ‖H s i i‖ ≤ U) (hHj : ∀ s, ‖H s i j‖ ≤ U) :
    pairEnergy c H i j m ≤ 2 * U ^ 2 * energy c m H := by
  unfold pairEnergy userSignal
  rw [← realBlock_add, norm_realBlock_sq]
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  simp only [Pi.add_apply]
  have hnorm (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have h := norm_add_le x y
    nlinarith [norm_nonneg (x + y), norm_nonneg x, norm_nonneg y,
      sq_nonneg (‖x‖ - ‖y‖)]
  have hi : ‖H s i i * c.encode i (m i) H s‖ ^ 2 ≤
      U ^ 2 * ‖c.encode i (m i) H s‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    gcongr
    exact hHi s
  have hj : ‖H s i j * c.encode j (m j) H s‖ ^ 2 ≤
      U ^ 2 * ‖c.encode j (m j) H s‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    gcongr
    exact hHj s
  have hs : ‖c.encode i (m i) H s‖ ^ 2 + ‖c.encode j (m j) H s‖ ^ 2 ≤
      ∑ k, ‖c.encode k (m k) H s‖ ^ 2 := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg
      (s := {i, j}) (t := Finset.univ) (f := fun k ↦ ‖c.encode k (m k) H s‖ ^ 2)
      (Finset.subset_univ _) (fun k _ _ ↦ sq_nonneg _)
    simpa [hij] using hsub
  have hscale := mul_le_mul_of_nonneg_left hs (sq_nonneg U)
  have h := hnorm (H s i i * c.encode i (m i) H s) (H s i j * c.encode j (m j) H s)
  nlinarith

theorem integrable_pairEnergy (μ : Measure ℂ) (c : Code K n) {P U : ℝ}
    (hc : PowerAdmissible μ P c) (hU : 0 ≤ U) (i j : Fin K) (hij : i ≠ j)
    (hH : ∀ᵐ H ∂stateLaw μ K n, (∀ s, ‖H s i i‖ ≤ U) ∧ (∀ s, ‖H s i j‖ ≤ U))
    (m : c.Message) : Integrable (fun H ↦ pairEnergy c H i j m) (stateLaw μ K n) := by
  apply Integrable.mono' ((hc.1 m).const_mul (2 * U ^ 2))
    (measurable_pairEnergy c i j m).aestronglyMeasurable
  filter_upwards [hH] with H hh
  rw [Real.norm_eq_abs, abs_of_nonneg (pairEnergy_nonneg c H i j m)]
  exact pairEnergy_le_energy c H i j hij m hU hh.1 hh.2

theorem integrable_messageAverage (μ : Measure ℂ) (c : Code K n)
    (f : c.Message → StateBlock K n → ℝ)
    (hf : ∀ m, Integrable (f m) (stateLaw μ K n)) :
    Integrable (fun H ↦ ∫ m, f m H ∂messageLaw c) (stateLaw μ K n) := by
  simp_rw [integral_messageLaw]
  exact (integrable_finsetSum Finset.univ (fun m _ ↦ hf m)).const_mul _

theorem integral_state_messageAverage (μ : Measure ℂ) (c : Code K n)
    (f : c.Message → StateBlock K n → ℝ)
    (hf : ∀ m, Integrable (f m) (stateLaw μ K n)) :
    (∫ H, ∫ m, f m H ∂messageLaw c ∂stateLaw μ K n) =
      ∫ m, ∫ H, f m H ∂stateLaw μ K n ∂messageLaw c := by
  simp_rw [integral_messageLaw]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun m _ ↦ hf m)]

theorem integral_pairEnergy_le (μ : Measure ℂ) (c : Code K n) {P U : ℝ}
    (hc : PowerAdmissible μ P c) (hU : 0 ≤ U) (i j : Fin K) (hij : i ≠ j)
    (hH : ∀ᵐ H ∂stateLaw μ K n, (∀ s, ‖H s i i‖ ≤ U) ∧ (∀ s, ‖H s i j‖ ≤ U)) :
    (∫ H, ∫ m, pairEnergy c H i j m ∂messageLaw c ∂stateLaw μ K n) ≤
      2 * U ^ 2 * ((n : ℝ) * P) := by
  have hp (m : c.Message) := integrable_pairEnergy μ c hc hU i j hij hH m
  rw [integral_state_messageAverage μ c _ hp, integral_messageLaw]
  have hi (m : c.Message) : (∫ H, pairEnergy c H i j m ∂stateLaw μ K n) ≤
      2 * U ^ 2 * (∫ H, energy c m H ∂stateLaw μ K n) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hp m) ((hc.1 m).const_mul _)
    filter_upwards [hH] with H hh
    exact pairEnergy_le_energy c H i j hij m hU hh.1 hh.2
  calc
    _ ≤ (∏ i, (c.messages i : ℝ))⁻¹ *
        ∑ m, 2 * U ^ 2 * (∫ H, energy c m H ∂stateLaw μ K n) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ ↦ hi m) (by positivity)
    _ = 2 * U ^ 2 * ((∏ i, (c.messages i : ℝ))⁻¹ *
        ∑ m, ∫ H, energy c m H ∂stateLaw μ K n) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc.2 (by positivity)

end CapacityAtlas.Gaussian.Interference
