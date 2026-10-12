/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding.Cost
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CapacityAtlas.MeasureChannel

variable {X Y M : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem lintegral_falseAcceptance_eq_output (κ : Kernel X Y) [IsSFiniteKernel κ]
    (A : Set (X × Y)) (hA : MeasurableSet A) (μ : Measure X) [SFinite μ] :
    (∫⁻ x, ∫⁻ x', falseAcceptance κ A x x' ∂μ ∂μ) =
      ∫⁻ x', (κ ∘ₘ μ) {y | (x', y) ∈ A} ∂μ := by
  rw [lintegral_lintegral_swap (measurable_falseAcceptance κ A hA).aemeasurable]
  apply lintegral_congr
  intro x'
  exact (Measure.bind_apply (hA.preimage (measurable_const.prodMk measurable_id))
    κ.aemeasurable).symm

/-- A likelihood ratio is a row density with respect to the actual output law. -/
theorem falseAcceptance_likelihoodRatio_le
    (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X × Y → ℝ≥0∞) (hf : Measurable f)
    (hκ : ∀ x, κ x = (κ ∘ₘ μ).withDensity (fun y ↦ f (x, y)))
    {threshold : ℝ≥0∞} (ht0 : threshold ≠ 0) (httop : threshold ≠ ∞) :
    (∫⁻ x, ∫⁻ x', falseAcceptance κ {p | threshold < f p} x x' ∂μ ∂μ) ≤
      threshold⁻¹ := by
  have hA : MeasurableSet {p | threshold < f p} := measurableSet_lt measurable_const hf
  rw [lintegral_falseAcceptance_eq_output κ _ hA μ]
  calc
    _ ≤ ∫⁻ _x : X, threshold⁻¹ ∂μ := by
      apply lintegral_mono
      intro x
      have hnorm : (∫⁻ y, f (x, y) ∂(κ ∘ₘ μ)) = 1 := by
        have h := congrArg (fun ν : Measure Y ↦ ν Set.univ) (hκ x)
        simpa [withDensity_apply] using h.symm
      have hmarkov := meas_ge_le_lintegral_div
        (μ := κ ∘ₘ μ) (f := fun y ↦ f (x, y))
        (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable ht0 httop
      have hmono : (κ ∘ₘ μ) {y | threshold < f (x, y)} ≤
          (κ ∘ₘ μ) {y | threshold ≤ f (x, y)} := by
        apply measure_mono
        intro y hy
        change threshold < f (x, y) at hy
        change threshold ≤ f (x, y)
        exact hy.le
      exact hmono.trans (hmarkov.trans_eq (by rw [hnorm, one_div]))
    _ = threshold⁻¹ := by simp

/-- The threshold random-coding bound for a measurable likelihood ratio. -/
theorem exists_oneShotCode_averageError_le_likelihoodRatio
    [MeasurableSpace M] [Fintype M] [Nonempty M]
    (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X × Y → ℝ≥0∞) (hf : Measurable f)
    (hκ : ∀ x, κ x = (κ ∘ₘ μ).withDensity (fun y ↦ f (x, y)))
    {threshold : ℝ≥0∞} (ht0 : threshold ≠ 0) (httop : threshold ≠ ∞) :
    ∃ code : OneShotCode X Y M,
      averageError κ code ≤ (∫⁻ x, κ x {y | f (x, y) ≤ threshold} ∂μ) +
        (Fintype.card M - 1 : ℕ) * threshold⁻¹ := by
  have hA : MeasurableSet {p | threshold < f p} := measurableSet_lt measurable_const hf
  obtain ⟨code, hcode⟩ := exists_oneShotCode_averageError_le (M := M) κ _ hA μ
  refine ⟨code, hcode.trans ?_⟩
  simp only [missedDetection, Set.mem_setOf_eq, not_lt]
  exact add_le_add le_rfl (mul_le_mul_right
    (falseAcceptance_likelihoodRatio_le κ μ f hf hκ ht0 httop) _)

theorem exists_oneShotCode_averageError_le_likelihoodRatio_of_allowed
    [MeasurableSpace M] [Fintype M] [Nonempty M]
    (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X × Y → ℝ≥0∞) (hf : Measurable f)
    (hκ : ∀ x, κ x = (κ ∘ₘ μ).withDensity (fun y ↦ f (x, y)))
    {threshold : ℝ≥0∞} (ht0 : threshold ≠ 0) (httop : threshold ≠ ∞)
    (allowed : Set X) (hallowed : MeasurableSet allowed) (hne : allowed.Nonempty) :
    ∃ code : OneShotCode X Y M, (∀ m, code.encode m ∈ allowed) ∧
      averageError κ code ≤ (∫⁻ x, κ x {y | f (x, y) ≤ threshold} ∂μ) +
        (Fintype.card M - 1 : ℕ) * threshold⁻¹ + μ allowedᶜ := by
  have hA : MeasurableSet {p | threshold < f p} := measurableSet_lt measurable_const hf
  obtain ⟨code, hallowedCode, hcode⟩ := exists_oneShotCode_averageError_le_of_allowed
    (M := M) κ _ hA μ allowed hallowed hne
  refine ⟨code, hallowedCode, hcode.trans ?_⟩
  simp only [missedDetection, Set.mem_setOf_eq, not_lt]
  exact add_le_add (add_le_add le_rfl (mul_le_mul_right
    (falseAcceptance_likelihoodRatio_le κ μ f hf hκ ht0 httop) _)) le_rfl

end CapacityAtlas.MeasureChannel
