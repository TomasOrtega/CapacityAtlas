/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.GoodSet

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.MeasureBinning

noncomputable def binCount (b : ℝ) (n : ℕ) : ℕ := Nat.ceil (Real.exp ((n : ℝ) * b))

theorem binCount_pos (b : ℝ) (n : ℕ) : 0 < binCount b n := Nat.ceil_pos.mpr (Real.exp_pos _)

theorem coveringTerm_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      (Real.exp (-((binCount b n : ℝ) * ((1 / 2) / Real.exp ((n : ℝ) * a))))))
      atTop (𝓝 0) := by
  have hscale : Tendsto (fun n : ℕ ↦ (n : ℝ) * (b - a)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.mpr hab)
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) * (b - a)) / 2) atTop atTop :=
    (Real.tendsto_exp_atTop.comp hscale).atTop_div_const (by norm_num)
  have hreal : Tendsto (fun n : ℕ ↦ Real.exp (-(Real.exp ((n : ℝ) * (b - a)) / 2)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hexp)
  have hbound : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal (Real.exp (-(Real.exp ((n : ℝ) * (b - a)) / 2)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun _ ↦ zero_le)
  intro n
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  calc
    Real.exp ((n : ℝ) * (b - a)) / 2 =
        Real.exp ((n : ℝ) * b) * ((1 / 2) / Real.exp ((n : ℝ) * a)) := by
      rw [show (n : ℝ) * (b - a) = (n : ℝ) * b - (n : ℝ) * a by ring, Real.exp_sub]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)

theorem binningPackingTerm_le {R b d : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b) (n : ℕ) :
    (FiniteChannel.messageCountAtRate R n - 1 : ℕ) * binCount b n *
        (ENNReal.ofReal (Real.exp ((n : ℝ) * d)))⁻¹ ≤
      ENNReal.ofReal (4 * Real.exp (-((n : ℝ) * (d - b - R * Real.log 2)))) := by
  calc
    _ ≤ (FiniteChannel.messageCountAtRate R n : ℝ≥0∞) * binCount b n *
        (ENNReal.ofReal (Real.exp ((n : ℝ) * d)))⁻¹ := by
      gcongr
      exact Nat.sub_le _ _
    _ = ENNReal.ofReal ((FiniteChannel.messageCountAtRate R n : ℝ) * binCount b n *
        Real.exp (-((n : ℝ) * d))) := by
      rw [Real.exp_neg, ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
        ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (2 * Real.exp ((n : ℝ) * R * Real.log 2)) *
            (2 * Real.exp ((n : ℝ) * b)) * Real.exp (-((n : ℝ) * d)) := by
          gcongr
          · exact FiniteChannel.natCeil_exp_le_two_mul_exp (by positivity)
          · exact FiniteChannel.natCeil_exp_le_two_mul_exp (by positivity)
        _ = _ := by
          calc
            _ = 4 * (Real.exp ((n : ℝ) * R * Real.log 2) *
                Real.exp ((n : ℝ) * b) * Real.exp (-((n : ℝ) * d))) := by ring
            _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

theorem binningPackingTerm_tendsto_zero {R b d : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hgap : R * Real.log 2 + b < d) :
    Tendsto (fun n : ℕ ↦ (FiniteChannel.messageCountAtRate R n - 1 : ℕ) * binCount b n *
      (ENNReal.ofReal (Real.exp ((n : ℝ) * d)))⁻¹) atTop (𝓝 0) := by
  have hδ : 0 < d - b - R * Real.log 2 := by linarith
  have hreal : Tendsto (fun n : ℕ ↦
      4 * Real.exp (-((n : ℝ) * (d - b - R * Real.log 2)))) atTop (𝓝 0) := by
    simpa using FiniteChannel.weightedRandomCodingBound_tendsto_zero 0 _ 4 hδ
  have hbound : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal (4 * Real.exp (-((n : ℝ) * (d - b - R * Real.log 2))))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ zero_le) (binningPackingTerm_le hR hb)

/-- Primitive block likelihood and cost tails yield actual noncausal-state codes. -/
theorem exists_stateCodes_of_tails_tendsto_zero
    {S U X Y : ℕ → Type*} [∀ n, MeasurableSpace (S n)] [∀ n, MeasurableSpace (U n)]
    [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    (κ : (n : ℕ) → Kernel (S n × X n) (Y n)) [∀ n, IsMarkovKernel (κ n)]
    (σ : (n : ℕ) → Measure (S n)) [∀ n, IsProbabilityMeasure (σ n)]
    (η : (n : ℕ) → Kernel (S n) (U n)) [∀ n, IsMarkovKernel (η n)]
    (μ : (n : ℕ) → Measure (U n)) [∀ n, IsProbabilityMeasure (μ n)]
    (g : (n : ℕ) → S n × U n → ℝ≥0∞) (hg : ∀ n, Measurable (g n))
    (hη : ∀ n s, η n s = (μ n).withDensity (fun u ↦ g n (s, u)))
    (reverse : (n : ℕ) → Kernel (Y n) (U n)) [∀ n, IsMarkovKernel (reverse n)]
    (f : (n : ℕ) → U n × Y n → ℝ≥0∞) (hf : ∀ n, Measurable (f n))
    (hreverse : ∀ n y, reverse n y = (μ n).withDensity (fun u ↦ f n (u, y)))
    (input : (n : ℕ) → S n × U n → X n) (hinput : ∀ n, Measurable (input n))
    (fallback : (n : ℕ) → S n → X n) (hfallback : ∀ n, Measurable (fallback n))
    (allowed : (n : ℕ) → Set (S n × X n)) (hallowed : ∀ n, MeasurableSet (allowed n))
    (hfallback_mem : ∀ n s, (s, fallback n s) ∈ allowed n)
    {R a b d : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b) (hab : a < b)
    (hgap : R * Real.log 2 + b < d)
    (hstateTail : Tendsto (fun n ↦ (σ n ⊗ₘ η n)
      {z | ENNReal.ofReal (Real.exp ((n : ℝ) * a)) < g n z}) atTop (𝓝 0))
    (hcostTail : Tendsto (fun n ↦ (σ n ⊗ₘ η n)
      {z | (z.1, input n z) ∉ allowed n}) atTop (𝓝 0))
    (hdecodeTail : Tendsto (fun n ↦ ∫⁻ z, conditionalMiss (κ n) (input n)
      {p | ENNReal.ofReal (Real.exp ((n : ℝ) * d)) < f n p} z ∂(σ n ⊗ₘ η n))
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      ∃ code : StateCode (S n) (X n) (Y n) (Fin (FiniteChannel.messageCountAtRate R n)),
        (∀ m s, (s, code.encode m s) ∈ allowed n) ∧
          (stateAverageError (κ n) (σ n) code).toReal ≤ ε ∧
          R ≤ Real.logb 2 (FiniteChannel.messageCountAtRate R n : ℝ) / n := by
  intro ε hε
  let δ := ENNReal.ofReal (ε / 2)
  have hδ₀ : δ ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hδtop : δ ≠ ∞ := ENNReal.ofReal_ne_top
  let total (n : ℕ) : ℝ≥0∞ :=
    2 * ((σ n ⊗ₘ η n) {z | ENNReal.ofReal (Real.exp ((n : ℝ) * a)) < g n z} +
      (σ n ⊗ₘ η n) {z | (z.1, input n z) ∉ allowed n} +
      (∫⁻ z, conditionalMiss (κ n) (input n)
        {p | ENNReal.ofReal (Real.exp ((n : ℝ) * d)) < f n p} z ∂(σ n ⊗ₘ η n)) / δ) +
      ENNReal.ofReal (Real.exp (-((binCount b n : ℝ) * ((1 / 2) / Real.exp ((n : ℝ) * a))))) +
      δ + (FiniteChannel.messageCountAtRate R n - 1 : ℕ) * binCount b n *
        (ENNReal.ofReal (Real.exp ((n : ℝ) * d)))⁻¹
  have hdiv := ENNReal.Tendsto.div_const hdecodeTail (Or.inr hδ₀)
  have hsmall := ENNReal.Tendsto.const_mul ((hstateTail.add hcostTail).add hdiv)
    (a := (2 : ℝ≥0∞)) (Or.inr (by finiteness))
  have htotal : Tendsto total atTop (𝓝 δ) := by
    simpa only [total, add_zero, zero_add, ENNReal.zero_div, mul_zero] using
      (((hsmall.add (coveringTerm_tendsto_zero hab)).add
        (tendsto_const_nhds (x := δ) (f := atTop))).add
        (binningPackingTerm_tendsto_zero hR hb hgap))
  have hδε : δ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htotal.eventually (gt_mem_nhds hδε))
  refine ⟨max N 1, by omega, fun n hn ↦ ?_⟩
  have hnpos : 0 < n := by omega
  letI : Nonempty (Fin (FiniteChannel.messageCountAtRate R n)) :=
    Fin.pos_iff_nonempty.mp (FiniteChannel.messageCountAtRate_pos R n)
  letI : Nonempty (Fin (binCount b n)) := Fin.pos_iff_nonempty.mp (binCount_pos b n)
  obtain ⟨code, hcode, herror⟩ := exists_stateCode_error_le_likelihood_tails
    (M := Fin (FiniteChannel.messageCountAtRate R n)) (L := Fin (binCount b n))
    (κ n) (σ n) (η n) (μ n) (g n) (hg n) (hη n)
    (reverse n) (f n) (hf n) (hreverse n) (Real.exp_pos ((n : ℝ) * a))
    (F := ENNReal.ofReal (Real.exp ((n : ℝ) * d)))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top hδ₀ hδtop
    (input n) (hinput n) (fallback n) (hfallback n) (allowed n) (hallowed n) (hfallback_mem n)
  refine ⟨code, hcode, ?_, FiniteChannel.targetRate_le_rateOfMessageCountAtRate R hnpos⟩
  have hbound : stateAverageError (κ n) (σ n) code ≤ ENNReal.ofReal ε := by
    apply le_trans _ (hN n (by omega)).le
    simpa only [total, Fintype.card_fin] using herror
  exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
    ENNReal.ofReal_ne_top).mpr hbound |>.trans_eq (ENNReal.toReal_ofReal hε.le)

end CapacityAtlas.MeasureBinning
