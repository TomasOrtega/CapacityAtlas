/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.PairMessages
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Genie

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

namespace CapacityAtlas.Gaussian.Interference

variable {K n : ℕ}

noncomputable def pairEnergy (c : Code K n) (H : StateBlock K n) (i j : Fin K)
    (m : c.Message) : ℝ :=
  ‖userSignal c H i i (m i) + userSignal c H i j (m j)‖ ^ 2

theorem code_pair_fano_given_other_messages (c : Code K n) (H : StateBlock K n)
    (m : c.Message) (i j : Fin K) (hij : i ≠ j)
    (hcross : ∀ s, H s i j ≠ 0) {e t : ℝ} (he : 0 < e) (ht : 0 < t)
    (hehalf : e ≤ 1 / 2)
    (hres : ∀ s, e * ‖H s j j / H s i j‖ ^ 2 ≤ 1 / 2) :
    Real.log (c.messages i) + Real.log (c.messages j) ≤
      (n : ℝ) * Real.log (t / e) +
      ((2 * n : ℝ) * e + (∫ a, ∫ b,
        pairEnergy c H i j (pairMessage c m i j a b)
        ∂uniformFinLaw (c.messages j) (c.messages_pos j)
        ∂uniformFinLaw (c.messages i) (c.messages_pos i))) / (2 * t) - n + 2 * Real.log 2 +
      (∫ a, ∫ b, receiverErrorAt c (pairMessage c m i j a b) H i
        ∂uniformFinLaw (c.messages j) (c.messages_pos j)
        ∂uniformFinLaw (c.messages i) (c.messages_pos i)) * Real.log (c.messages i) +
      (∫ a, ∫ b, receiverErrorAt c (pairMessage c m i j a b) H j
        ∂uniformFinLaw (c.messages j) (c.messages_pos j)
        ∂uniformFinLaw (c.messages i) (c.messages_pos i)) * Real.log (c.messages j) := by
  letI : Nonempty (Fin (c.messages i)) := ⟨⟨0, c.messages_pos i⟩⟩
  letI : Nonempty (Fin (c.messages j)) := ⟨⟨0, c.messages_pos j⟩⟩
  have hd (k : Fin K) : Measurable fun y : EuclideanSpace ℝ (Fin 2 × Fin n) ↦
      (c.decode k).apply (H, complexBlock y) :=
    (measurable_to_countable' (c.decode k).measurable_fiber).comp
      (measurable_const.prodMk measurable_complexBlock)
  have hf := twoUser_linear_gaussian_fano
    (uniformFinLaw (c.messages i) (c.messages_pos i))
    (uniformFinLaw (c.messages j) (c.messages_pos j))
    (userSignal c H i i) (userSignal c H j i) (userSignal c H i j)
    (pairBackground c m H i i j) (pairBackground c m H j i j)
    (complexBlockMatrix fun s ↦ H s j j / H s i j) he ht hehalf
    (complexBlockMatrix_residual_posSemidef _ e (1 / 2) hres)
    (fun y ↦ (c.decode i).apply (H, complexBlock y)) (hd i)
    (fun y ↦ (c.decode j).apply (H, complexBlock y)) (hd j)
    (fun a ↦ by simpa using uniformFinLaw_singleton _ _ a)
    (fun b ↦ by simpa using uniformFinLaw_singleton _ _ b)
  simp_rw [userSignal_transfer c H i j j hcross,
    ← receiverMean_pairMessage c m H i i j hij,
    ← receiverMean_pairMessage c m H j i j hij] at hf
  have hri (a : Fin (c.messages i)) (b : Fin (c.messages j)) :=
    receiverErrorAt_eq_gaussian c (pairMessage c m i j a b) H i
  have hrj (a : Fin (c.messages i)) (b : Fin (c.messages j)) :=
    receiverErrorAt_eq_gaussian c (pairMessage c m i j a b) H j
  simp only [pairMessage_left c m i j hij] at hri
  simp only [pairMessage_right] at hrj
  simp_rw [← hri, ← hrj] at hf
  rw [integral_prod _ Integrable.of_finite] at hf
  simpa only [Fintype.card_fin, Fintype.card_prod, Nat.cast_mul, Nat.cast_ofNat,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), pairEnergy,
    pairMessage_left c m i j hij, pairMessage_right] using hf

theorem code_pair_fano_at_state (c : Code K n) (H : StateBlock K n)
    (i j : Fin K) (hij : i ≠ j)
    (hcross : ∀ s, H s i j ≠ 0) {e t : ℝ} (he : 0 < e) (ht : 0 < t)
    (hehalf : e ≤ 1 / 2)
    (hres : ∀ s, e * ‖H s j j / H s i j‖ ^ 2 ≤ 1 / 2) :
    Real.log (c.messages i) + Real.log (c.messages j) ≤
      (n : ℝ) * Real.log (t / e) +
      ((2 * n : ℝ) * e + (∫ m, pairEnergy c H i j m ∂messageLaw c)) / (2 * t) -
        n + 2 * Real.log 2 +
      (∫ m, receiverErrorAt c m H i ∂messageLaw c) * Real.log (c.messages i) +
      (∫ m, receiverErrorAt c m H j ∂messageLaw c) * Real.log (c.messages j) := by
  have hf := integral_mono (μ := messageLaw c)
    (integrable_const (Real.log (c.messages i) + Real.log (c.messages j)))
    Integrable.of_finite
    (fun m ↦ code_pair_fano_given_other_messages c H m i j hij hcross he ht hehalf hres)
  simp only [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_div, integral_mul_const, integral_const, probReal_univ, one_smul,
    integral_pairMessage] at hf
  rw [integral_pairMessage c i j (fun m ↦ receiverErrorAt c m H i),
    integral_pairMessage c i j (fun m ↦ receiverErrorAt c m H j)] at hf
  exact hf

end CapacityAtlas.Gaussian.Interference
