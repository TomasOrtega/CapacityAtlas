/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.MeasureChannel

variable {Ω : Type*} [MeasurableSpace Ω]

def iidSum (Z : Ω → ℝ) (n : ℕ) (x : Fin n → Ω) : ℝ := ∑ i, Z (x i)

noncomputable def iidMean (Z : Ω → ℝ) (n : ℕ) (x : Fin n → Ω) : ℝ := iidSum Z n x / n

theorem memLp_iidSum (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) (n : ℕ) :
    MemLp (iidSum Z n) 2 (Measure.pi (fun _ : Fin n ↦ μ)) :=
  memLp_finsetSum _ (fun i _ ↦ hZ.comp_measurePreserving (measurePreserving_eval _ i))

theorem integral_iidSum (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) (n : ℕ) :
    (∫ x, iidSum Z n x ∂Measure.pi (fun _ : Fin n ↦ μ)) = (n : ℝ) * ∫ x, Z x ∂μ := by
  have hcoord (i : Fin n) :
      Integrable (fun x : Fin n → Ω ↦ Z (x i)) (Measure.pi (fun _ : Fin n ↦ μ)) :=
    (hZ.comp_measurePreserving (measurePreserving_eval _ i)).integrable (by norm_num)
  unfold iidSum
  rw [integral_finsetSum _ (fun i _ ↦ hcoord i)]
  have heval (i : Fin n) :
      (∫ x : Fin n → Ω, Z (x i) ∂Measure.pi (fun _ : Fin n ↦ μ)) = ∫ x, Z x ∂μ := by
    have hmap := (measurePreserving_eval (fun _ : Fin n ↦ μ) i).map_eq
    calc
      _ = ∫ y, Z y ∂(Measure.pi (fun _ : Fin n ↦ μ)).map (fun x ↦ x i) :=
        (integral_map (measurable_pi_apply i).aemeasurable (by
          rw [hmap]
          exact hZ.aestronglyMeasurable)).symm
      _ = _ := by rw [hmap]
  simp_rw [heval]
  simp

theorem variance_iidSum (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) (n : ℕ) :
    Var[iidSum Z n; Measure.pi (fun _ : Fin n ↦ μ)] = (n : ℝ) * Var[Z; μ] := by
  have hsum : iidSum Z n = ∑ i : Fin n, fun x : Fin n → Ω ↦ Z (x i) := by
    ext x
    simp [iidSum]
  rw [hsum]
  simpa only [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using
    (variance_sum_pi (μ := fun _ : Fin n ↦ μ) (X := fun _ ↦ Z) (fun _ ↦ hZ))

theorem iidSum_deviation_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi (fun _ : Fin n ↦ μ))
      {x | (n : ℝ) * δ ≤ |iidSum Z n x - (n : ℝ) * ∫ y, Z y ∂μ|} ≤
      ENNReal.ofReal (((n : ℝ) * Var[Z; μ]) / (((n : ℝ) * δ) ^ 2)) := by
  simpa only [integral_iidSum μ hZ n, variance_iidSum μ hZ n] using
    meas_ge_le_variance_div_sq (memLp_iidSum μ hZ n) (mul_pos (Nat.cast_pos.mpr hn) hδ)

theorem iidMean_deviation_tendsto_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ (Measure.pi (fun _ : Fin n ↦ μ))
      {x | δ ≤ |iidMean Z n x - ∫ y, Z y ∂μ|}) atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun n : ℕ ↦ ((n : ℝ) * Var[Z; μ]) / (((n : ℝ) * δ) ^ 2)) atTop (𝓝 0) := by
    simpa using FiniteChannel.weightedRandomCodingBound_tendsto_zero (Var[Z; μ]) δ 0 hδ
  have hbound : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal (((n : ℝ) * Var[Z; μ]) / (((n : ℝ) * δ) ^ 2)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall (fun _ ↦ zero_le))
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply le_trans (measure_mono ?_) (iidSum_deviation_le μ hZ hn hδ)
  intro x hx
  change δ ≤ |iidSum Z n x / (n : ℝ) - ∫ y, Z y ∂μ| at hx
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hidentity : |iidSum Z n x / (n : ℝ) - ∫ y, Z y ∂μ| =
      |iidSum Z n x - (n : ℝ) * ∫ y, Z y ∂μ| / (n : ℝ) := by
    calc
      _ = |(iidSum Z n x - (n : ℝ) * ∫ y, Z y ∂μ) / (n : ℝ)| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_div, abs_of_pos hnreal]
  rw [hidentity] at hx
  change (n : ℝ) * δ ≤ |iidSum Z n x - (n : ℝ) * ∫ y, Z y ∂μ|
  nlinarith [(le_div_iff₀ hnreal).mp hx]

theorem iidMean_lowerTail_tendsto_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) {a : ℝ} (ha : a < ∫ y, Z y ∂μ) :
    Tendsto (fun n : ℕ ↦ (Measure.pi (fun _ : Fin n ↦ μ))
      {x | iidMean Z n x ≤ a}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (iidMean_deviation_tendsto_zero μ hZ (sub_pos.mpr ha)) (fun _ ↦ zero_le)
  intro n
  apply measure_mono
  intro x hx
  change iidMean Z n x ≤ a at hx
  change (∫ y, Z y ∂μ) - a ≤ |iidMean Z n x - ∫ y, Z y ∂μ|
  exact le_trans (by linarith) (neg_le_abs _)

theorem iidMean_upperTail_tendsto_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) {a : ℝ} (ha : (∫ y, Z y ∂μ) < a) :
    Tendsto (fun n : ℕ ↦ (Measure.pi (fun _ : Fin n ↦ μ))
      {x | a ≤ iidMean Z n x}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (iidMean_deviation_tendsto_zero μ hZ (sub_pos.mpr ha)) (fun _ ↦ zero_le)
  intro n
  apply measure_mono
  intro x hx
  change a ≤ iidMean Z n x at hx
  change a - (∫ y, Z y ∂μ) ≤ |iidMean Z n x - ∫ y, Z y ∂μ|
  exact le_trans (by linarith) (le_abs_self _)

theorem iidSum_lowerTail_tendsto_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) {a : ℝ} (ha : a < ∫ y, Z y ∂μ) :
    Tendsto (fun n : ℕ ↦ (Measure.pi (fun _ : Fin n ↦ μ))
      {x | iidSum Z n x ≤ (n : ℝ) * a}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (iidMean_lowerTail_tendsto_zero μ hZ ha) (Eventually.of_forall (fun _ ↦ zero_le))
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply measure_mono
  intro x hx
  change iidSum Z n x ≤ (n : ℝ) * a at hx
  change iidSum Z n x / (n : ℝ) ≤ a
  exact (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using hx)

theorem iidSum_upperTail_tendsto_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) {a : ℝ} (ha : (∫ y, Z y ∂μ) < a) :
    Tendsto (fun n : ℕ ↦ (Measure.pi (fun _ : Fin n ↦ μ))
      {x | (n : ℝ) * a ≤ iidSum Z n x}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (iidMean_upperTail_tendsto_zero μ hZ ha) (Eventually.of_forall (fun _ ↦ zero_le))
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply measure_mono
  intro x hx
  change (n : ℝ) * a ≤ iidSum Z n x at hx
  change a ≤ iidSum Z n x / (n : ℝ)
  exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using hx)

theorem iidLikelihood_lowerTail_tendsto_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ) {a : ℝ} (ha : a < ∫ y, Z y ∂μ) :
    Tendsto (fun n : ℕ ↦ (Measure.pi (fun _ : Fin n ↦ μ))
      {x | ENNReal.ofReal (Real.exp (iidSum Z n x)) ≤
        ENNReal.ofReal (Real.exp ((n : ℝ) * a))}) atTop (𝓝 0) := by
  have hevent (n : ℕ) :
      {x | ENNReal.ofReal (Real.exp (iidSum Z n x)) ≤
        ENNReal.ofReal (Real.exp ((n : ℝ) * a))} =
      {x | iidSum Z n x ≤ (n : ℝ) * a} := by
    ext x
    simp only [Set.mem_setOf_eq, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
      Real.exp_le_exp]
  simp_rw [hevent]
  exact iidSum_lowerTail_tendsto_zero μ hZ ha

theorem iidCost_rejection_tendsto_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {cost : Ω → ℝ} (hcost : MemLp cost 2 μ) {P : ℝ} (hP : (∫ y, cost y ∂μ) < P) :
    Tendsto (fun n : ℕ ↦ (Measure.pi (fun _ : Fin n ↦ μ))
      {x | iidSum cost n x ≤ (n : ℝ) * P}ᶜ) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (iidSum_upperTail_tendsto_zero μ hcost hP) (fun _ ↦ zero_le)
  intro n
  apply measure_mono
  intro x hx
  change ¬iidSum cost n x ≤ (n : ℝ) * P at hx
  change (n : ℝ) * P ≤ iidSum cost n x
  exact (not_le.mp hx).le

end CapacityAtlas.MeasureChannel
