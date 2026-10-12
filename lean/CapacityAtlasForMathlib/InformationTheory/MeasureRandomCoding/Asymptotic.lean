/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding.Density
import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace CapacityAtlas.MeasureChannel

theorem roundedMessage_threshold_le (R a : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    (FiniteChannel.messageCountAtRate R n - 1 : ℕ) *
        (ENNReal.ofReal (Real.exp ((n : ℝ) * a)))⁻¹ ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * (a - R * Real.log 2)))) := by
  calc
    _ ≤ (FiniteChannel.messageCountAtRate R n : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp ((n : ℝ) * a)))⁻¹ := by
      gcongr
      exact Nat.sub_le (FiniteChannel.messageCountAtRate R n) 1
    _ = ENNReal.ofReal ((FiniteChannel.messageCountAtRate R n : ℝ) *
        Real.exp (-((n : ℝ) * a))) := by
      rw [Real.exp_neg, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (FiniteChannel.messageCountAtRate_mul_exp_neg_le R (a - R * Real.log 2) hR n
        (by ring_nf; rfl))

theorem exponential_gap_tendsto_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * δ))))
      atTop (𝓝 0) := by
  have hreal : Tendsto (fun n : ℕ ↦ 2 * Real.exp (-((n : ℝ) * δ))) atTop (𝓝 0) := by
    simpa using FiniteChannel.weightedRandomCodingBound_tendsto_zero 0 δ 2 hδ
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

/-- Distributional likelihood and cost concentration yield actual codes at every large length. -/
theorem exists_codes_of_likelihood_tail_tendsto_zero
    {X Y : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    (κ : (n : ℕ) → Kernel (X n) (Y n)) [∀ n, IsMarkovKernel (κ n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (f : (n : ℕ) → X n × Y n → ℝ≥0∞) (hf : ∀ n, Measurable (f n))
    (hκ : ∀ n x, κ n x = (κ n ∘ₘ μ n).withDensity (fun y ↦ f n (x, y)))
    (allowed : (n : ℕ) → Set (X n)) (hallowed : ∀ n, MeasurableSet (allowed n))
    (hne : ∀ n, (allowed n).Nonempty)
    {R a : ℝ} (hR : 0 ≤ R) (hgap : R * Real.log 2 < a)
    (htail : Tendsto (fun n ↦ ∫⁻ x, κ n x
      {y | f n (x, y) ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * a))} ∂μ n) atTop (𝓝 0))
    (hcost : Tendsto (fun n ↦ μ n (allowed n)ᶜ) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      ∃ code : OneShotCode (X n) (Y n) (Fin (FiniteChannel.messageCountAtRate R n)),
        (∀ m, code.encode m ∈ allowed n) ∧ (averageError (κ n) code).toReal ≤ ε ∧
          R ≤ Real.logb 2 (FiniteChannel.messageCountAtRate R n : ℝ) / n := by
  intro ε hε
  have hdecay := exponential_gap_tendsto_zero (sub_pos.mpr hgap)
  have htotal : Tendsto (fun n ↦
      (∫⁻ x, κ n x {y | f n (x, y) ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * a))} ∂μ n) +
        ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * (a - R * Real.log 2)))) +
          μ n (allowed n)ᶜ) atTop (𝓝 0) := by
    simpa using (htail.add hdecay).add hcost
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (htotal.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε)))
  refine ⟨max N 1, by omega, fun n hn ↦ ?_⟩
  have hnpos : 0 < n := by omega
  letI : Nonempty (Fin (FiniteChannel.messageCountAtRate R n)) :=
    Fin.pos_iff_nonempty.mp (FiniteChannel.messageCountAtRate_pos R n)
  obtain ⟨code, hcodeAllowed, herror⟩ :=
    exists_oneShotCode_averageError_le_likelihoodRatio_of_allowed
      (M := Fin (FiniteChannel.messageCountAtRate R n)) (κ n) (μ n) (f n) (hf n) (hκ n)
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top
      (allowed n) (hallowed n) (hne n)
  refine ⟨code, hcodeAllowed, ?_, FiniteChannel.targetRate_le_rateOfMessageCountAtRate R hnpos⟩
  have hbound : averageError (κ n) code ≤ ENNReal.ofReal ε := by
    apply herror.trans
    apply le_trans (add_le_add (add_le_add le_rfl ?_) le_rfl) (hN n (by omega)).le
    simpa only [Fintype.card_fin] using roundedMessage_threshold_le R a hR n
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
    ENNReal.ofReal_ne_top).mpr hbound |>.trans_eq (ENNReal.toReal_ofReal hε.le)

end CapacityAtlas.MeasureChannel
