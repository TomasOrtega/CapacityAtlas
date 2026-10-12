/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.QAMInformation
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.BlockAchievability
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.BasicFacts

open MeasureTheory Filter
open scoped BigOperators Topology

namespace CapacityAtlas.Gaussian.Interference

theorem qam_sum_lower (μ : Measure ℂ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {K n q : ℕ} (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ) (M : ℝ)
    (hM : ∀ᵐ h ∂μ, ‖h‖ ≤ M) {ε : ℝ}
    (hε : (environmentLaw μ K n).real (noiseBad δ) ≤ ε)
    (hB : BddAbove {s | ∃ R ∈ capacityRegion μ K
      (qamPowerFactor K n M δ * (q : ℝ) ^ 2), s = ∑ i, R i}) :
    K * ((((1 - ε) * (2 * Fintype.card (Box (Fin K) n) * Real.log q) - Real.log 2) /
      Real.log 2) / extensionLength K n - 1) ≤
      sumCapacity μ K (qamPowerFactor K n M δ * (q : ℝ) ^ 2) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let r := (((1 - ε) * (2 * Fintype.card (Box (Fin K) n) * Real.log q) - Real.log 2) /
    Real.log 2) / extensionLength K n - 1
  change (K : ℝ) * r ≤ _
  by_cases hr : r ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg K) hr).trans
      (sumCapacity_nonneg hB)
  · have hL : (0 : ℝ) < extensionLength K n := by
      exact_mod_cast extensionLength_pos K n
    have hP : 0 ≤ qamPowerFactor K n M δ * (q : ℝ) ^ 2 := by
      unfold qamPowerFactor
      positivity
    have hR := (qamScheme μ hq δ hδ M hM).capacityRegion_of_lt
      (extensionLength_pos K n) hP (fun _ => r) (fun _ => (lt_of_not_ge hr).le) (by
        intro i
        have hi := div_le_div_of_nonneg_right (qam_information_lower μ hq δ hδ hε i) hL.le
        change r < (qamChannel μ (n := n) hq δ i).informationCapacityBits / extensionLength K n
        dsimp [r]
        linarith)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using sum_le_sumCapacity hB hR

/-- Fixed spacing gives a quadratic power grid with arbitrarily small Fano loss. -/
theorem exists_quadratic_grid_lower (μ : Measure ℂ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {K : ℕ} (hK : 0 < K) (M : ℝ)
    (hM : ∀ᵐ h ∂μ, ‖h‖ ≤ M)
    (hB : ∀ P, BddAbove {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i})
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ b : ℝ, ∀ᶠ q : ℕ in atTop,
      (K * (1 - ε) * 2 * Fintype.card (Box (Fin K) n) / extensionLength K n) * Real.log q - b ≤
        sumCapacity μ K (C * (q : ℝ) ^ 2) * Real.log 2 := by
  obtain ⟨δ, hδ, he⟩ := exists_qam_spacing μ K n hε
  refine ⟨qamPowerFactor K n M δ, qamPowerFactor_pos hK hn M δ hδ,
    K * (Real.log 2 / extensionLength K n + Real.log 2), ?_⟩
  filter_upwards [eventually_gt_atTop 0] with q hq
  have h := mul_le_mul_of_nonneg_right
    (qam_sum_lower μ hq δ hδ M hM he.le (hB _)) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have hL : (extensionLength K n : ℝ) ≠ 0 := by
    exact_mod_cast (extensionLength_pos K n).ne'
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  calc
    _ = K * ((((1 - ε) * (2 * Fintype.card (Box (Fin K) n) * Real.log q) - Real.log 2) /
        Real.log 2) / extensionLength K n - 1) * Real.log 2 := by
      field_simp
      ring
    _ ≤ _ := h

end CapacityAtlas.Gaussian.Interference
