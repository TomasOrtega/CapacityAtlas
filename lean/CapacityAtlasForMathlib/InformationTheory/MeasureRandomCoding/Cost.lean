/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.MeasureChannel

variable {X Y M : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace M] [Fintype M]

/-- Replace disallowed words with one allowed input while retaining the original decoder. -/
noncomputable def repairCode (allowed : Set X) (fallback : X) (code : OneShotCode X Y M) :
    OneShotCode X Y M where
  encode m := if code.encode m ∈ allowed then code.encode m else fallback
  decode := code.decode
  measurable_decode := code.measurable_decode

omit [MeasurableSpace X] [Fintype M] in
theorem repairCode_encode_mem (allowed : Set X) {fallback : X} (hf : fallback ∈ allowed)
    (code : OneShotCode X Y M) (m : M) : (repairCode allowed fallback code).encode m ∈ allowed := by
  change (if code.encode m ∈ allowed then code.encode m else fallback) ∈ allowed
  split_ifs with hm
  · exact hm
  · exact hf

noncomputable def badFraction (allowed : Set X) (codebook : M → X) : ℝ≥0∞ :=
  (Fintype.card M : ℝ≥0∞)⁻¹ * ∑ m, if codebook m ∈ allowed then 0 else 1

theorem repairCode_averageError_le (κ : Kernel X Y) [IsMarkovKernel κ]
    (allowed : Set X) (fallback : X) (code : OneShotCode X Y M) :
    averageError κ (repairCode allowed fallback code) ≤
      averageError κ code + badFraction allowed code.encode := by
  have hpoint (m : M) : errorProbability κ (repairCode allowed fallback code) m ≤
      errorProbability κ code m + if code.encode m ∈ allowed then 0 else 1 := by
    by_cases hm : code.encode m ∈ allowed
    · simp [errorProbability, repairCode, hm]
    · simp only [if_neg hm]
      exact prob_le_one.trans (le_add_self)
  unfold averageError badFraction
  rw [← mul_add, ← Finset.sum_add_distrib]
  exact mul_le_mul_right (Finset.sum_le_sum fun m _ ↦ hpoint m) _

omit [MeasurableSpace Y] [MeasurableSpace M] in
theorem measurable_badFraction (allowed : Set X) (hallowed : MeasurableSet allowed) :
    Measurable (badFraction (M := M) allowed) := by
  unfold badFraction
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun m _ ↦
    Measurable.ite (hallowed.preimage (measurable_pi_apply m)) measurable_const measurable_const

omit [MeasurableSpace Y] [MeasurableSpace M] in
theorem lintegral_badFraction [Nonempty M] (allowed : Set X) (hallowed : MeasurableSet allowed)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    (∫⁻ c : M → X, badFraction allowed c ∂Measure.pi (fun _ : M ↦ μ)) = μ allowedᶜ := by
  have hbad : Measurable (fun x : X ↦ if x ∈ allowed then (0 : ℝ≥0∞) else 1) :=
    Measurable.ite hallowed measurable_const measurable_const
  have hbadCode (m : M) : Measurable (fun c : M → X ↦
      if c m ∈ allowed then (0 : ℝ≥0∞) else 1) := hbad.comp (measurable_pi_apply m)
  have hterm (m : M) : (∫⁻ c : M → X, (if c m ∈ allowed then (0 : ℝ≥0∞) else 1)
      ∂Measure.pi (fun _ : M ↦ μ)) = μ allowedᶜ := by
    rw [(measurePreserving_eval (fun _ : M ↦ μ) m).lintegral_comp hbad]
    have hindicator : (fun x : X ↦ if x ∈ allowed then (0 : ℝ≥0∞) else 1) =
        allowedᶜ.indicator (fun _ ↦ 1) := by
      ext x
      by_cases hx : x ∈ allowed <;> simp [hx]
    rw [hindicator, lintegral_indicator_const hallowed.compl, one_mul]
  unfold badFraction
  rw [lintegral_const_mul _ (Finset.measurable_sum Finset.univ (fun m _ ↦ hbadCode m)),
    lintegral_finsetSum _ (fun m _ ↦ hbadCode m)]
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.inv_mul_cancel_left (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)

/-- Cost-admissible codewords and reliability come from one selected random codebook. -/
theorem exists_oneShotCode_averageError_le_of_allowed [Nonempty M]
    (κ : Kernel X Y) [IsMarkovKernel κ] (A : Set (X × Y)) (hA : MeasurableSet A)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (allowed : Set X) (hallowed : MeasurableSet allowed) (hne : allowed.Nonempty) :
    ∃ code : OneShotCode X Y M, (∀ m, code.encode m ∈ allowed) ∧
      averageError κ code ≤ (∫⁻ x, missedDetection κ A x ∂μ) +
        (Fintype.card M - 1 : ℕ) * (∫⁻ x, ∫⁻ x', falseAcceptance κ A x x' ∂μ ∂μ) +
          μ allowedᶜ := by
  obtain ⟨fallback, hfallback⟩ := hne
  have hmeas : Measurable (fun c : M → X ↦ packingBound κ A c + badFraction allowed c) :=
    (measurable_packingBound κ A hA).add (measurable_badFraction allowed hallowed)
  obtain ⟨c, hc⟩ := exists_le_lintegral (μ := Measure.pi (fun _ : M ↦ μ)) hmeas.aemeasurable
  refine ⟨repairCode allowed fallback (thresholdCode A hA c),
    repairCode_encode_mem allowed hfallback _, ?_⟩
  calc
    _ ≤ averageError κ (thresholdCode A hA c) + badFraction allowed c :=
      repairCode_averageError_le κ allowed fallback _
    _ ≤ packingBound κ A c + badFraction allowed c :=
      add_le_add (thresholdCode_averageError_le κ A hA c) le_rfl
    _ ≤ _ := hc.trans_eq (by
      rw [lintegral_add_left (measurable_packingBound κ A hA),
        lintegral_packingBound κ A hA μ, lintegral_badFraction allowed hallowed μ])

end CapacityAtlas.MeasureChannel
