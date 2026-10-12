/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianHeatFlow

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators

namespace CapacityAtlas.MeasureInformation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def gaussianHeatLogNormalizer (N : Matrix ι ι ℝ) (t : ℝ) : ℝ :=
  -((Fintype.card ι : ℝ) * log (2 * π) + Fintype.card ι * log t + log N.det) / 2

lemma gaussianHeat_quadratic_nonneg (m x : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) : 0 ≤ (x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m) := by
  simpa only [star_trivial, WithLp.ofLp_sub] using
    hN.inv.posSemidef.dotProduct_mulVec_nonneg (x - m)

lemma gaussianHeatLogNormalizer_antitone (N : Matrix ι ι ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    gaussianHeatLogNormalizer N b ≤ gaussianHeatLogNormalizer N a := by
  have hlog := mul_le_mul_of_nonneg_left (log_le_log ha hab) (Nat.cast_nonneg (Fintype.card ι))
  unfold gaussianHeatLogNormalizer
  linarith

/-- On a compact positive-time interval, a wider Gaussian dominates every kernel. -/
theorem multivariateGaussianPDFReal_smul_le (m x : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) {a t b : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) :
    multivariateGaussianPDFReal m (t • N) x ≤
      exp ((Fintype.card ι : ℝ) * (log b - log a) / 2) *
        multivariateGaussianPDFReal m (b • N) x := by
  have ht := ha.trans_le hat
  have hb := ht.trans_le htb
  have hq := gaussianHeat_quadratic_nonneg m x N hN
  have hlog := mul_le_mul_of_nonneg_left (log_le_log ha hat)
    (Nat.cast_nonneg (Fintype.card ι))
  have hdiv := div_le_div_of_nonneg_left hq (mul_pos (by norm_num : (0 : ℝ) < 2) ht)
    (mul_le_mul_of_nonneg_left htb (by norm_num : (0 : ℝ) ≤ 2))
  have hcomp : log (multivariateGaussianPDFReal m (t • N) x) ≤
      (Fintype.card ι : ℝ) * (log b - log a) / 2 +
        log (multivariateGaussianPDFReal m (b • N) x) := by
    rw [log_multivariateGaussianPDFReal_smul m x N hN ht,
      log_multivariateGaussianPDFReal_smul m x N hN hb]
    linarith
  calc
    _ = exp (log (multivariateGaussianPDFReal m (t • N) x)) :=
      (exp_log (multivariateGaussianPDFReal_pos m (t • N) (hN.smul ht) x)).symm
    _ ≤ exp ((Fintype.card ι : ℝ) * (log b - log a) / 2 +
        log (multivariateGaussianPDFReal m (b • N) x)) := exp_le_exp.mpr hcomp
    _ = _ := by
      rw [exp_add, exp_log (multivariateGaussianPDFReal_pos m (b • N) (hN.smul hb) x)]

lemma log_multivariateGaussianPDFReal_smul_le_normalizer (m x : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    log (multivariateGaussianPDFReal m (t • N) x) ≤ gaussianHeatLogNormalizer N a := by
  have ht := ha.trans_le hat
  rw [log_multivariateGaussianPDFReal_smul m x N hN ht]
  change gaussianHeatLogNormalizer N t - _ ≤ _
  exact (sub_le_self _ (div_nonneg (gaussianHeat_quadratic_nonneg m x N hN)
    (mul_pos (by norm_num) ht).le)).trans (gaussianHeatLogNormalizer_antitone N ha hat)

lemma normalizer_sub_quadratic_le_log_multivariateGaussianPDFReal_smul
    (m x : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef) {a t b : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) :
    gaussianHeatLogNormalizer N b - ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * a) ≤
      log (multivariateGaussianPDFReal m (t • N) x) := by
  have ht := ha.trans_le hat
  rw [log_multivariateGaussianPDFReal_smul m x N hN ht]
  change _ ≤ gaussianHeatLogNormalizer N t - _
  apply sub_le_sub (gaussianHeatLogNormalizer_antitone N ht htb)
  exact div_le_div_of_nonneg_left (gaussianHeat_quadratic_nonneg m x N hN)
    (mul_pos (by norm_num) ha) (mul_le_mul_of_nonneg_left hat (by norm_num))

section FiniteMixture

variable {α : Type*} [Fintype α]

noncomputable def gaussianMixturePDFReal (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ a, w a * multivariateGaussianPDFReal (m a) N x

lemma gaussianMixturePDFReal_pos_of_pos_weight (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (j : α) (hj : 0 < w j) (x : EuclideanSpace ℝ ι) :
    0 < gaussianMixturePDFReal w m N x := by
  apply Finset.sum_pos' (fun a _ ↦ mul_nonneg (hw a)
    (multivariateGaussianPDFReal_pos (m a) N hN x).le)
  exact ⟨j, Finset.mem_univ j, mul_pos hj (multivariateGaussianPDFReal_pos (m j) N hN x)⟩

lemma gaussianMixturePDFReal_pos (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (x : EuclideanSpace ℝ ι) : 0 < gaussianMixturePDFReal w m N x := by
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) ↦ hw a)).mp
    (show 0 < ∑ a, w a by rw [hw1]; norm_num)
  exact gaussianMixturePDFReal_pos_of_pos_weight w hw m N hN j hj x

@[fun_prop]
lemma measurable_gaussianMixturePDFReal (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) : Measurable (gaussianMixturePDFReal w m N) := by
  unfold gaussianMixturePDFReal
  fun_prop

theorem log_gaussianMixturePDFReal_smul_le (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (x : EuclideanSpace ℝ ι)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    log (gaussianMixturePDFReal w m (t • N) x) ≤ gaussianHeatLogNormalizer N a := by
  have ht := ha.trans_le hat
  have hupper : gaussianMixturePDFReal w m (t • N) x ≤ exp (gaussianHeatLogNormalizer N a) := by
    calc
      _ ≤ ∑ j, w j * exp (gaussianHeatLogNormalizer N a) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (hw j)
        rw [← log_le_iff_le_exp (multivariateGaussianPDFReal_pos (m j) (t • N) (hN.smul ht) x)]
        exact log_multivariateGaussianPDFReal_smul_le_normalizer (m j) x N hN ha hat
      _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]
  exact (log_le_log (gaussianMixturePDFReal_pos w hw hw1 m (t • N) (hN.smul ht) x)
    hupper).trans_eq (log_exp _)

/-- One positive component gives a uniform quadratic bound for the mixture log density. -/
theorem abs_log_gaussianMixturePDFReal_smul_le (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (j : α) (hj : 0 < w j)
    (x : EuclideanSpace ℝ ι) {a t b : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) :
    |log (gaussianMixturePDFReal w m (t • N) x)| ≤
      |gaussianHeatLogNormalizer N a| + |gaussianHeatLogNormalizer N b| + |log (w j)| +
        ((x - m j) ⬝ᵥ N⁻¹ *ᵥ (x - m j)) / (2 * a) := by
  have ht := ha.trans_le hat
  have hrow : w j * multivariateGaussianPDFReal (m j) (t • N) x ≤
      gaussianMixturePDFReal w m (t • N) x := by
    exact Finset.single_le_sum (fun k _ ↦ mul_nonneg (hw k)
      (multivariateGaussianPDFReal_pos (m k) (t • N) (hN.smul ht) x).le) (Finset.mem_univ j)
  have hlower := log_le_log
    (mul_pos hj (multivariateGaussianPDFReal_pos (m j) (t • N) (hN.smul ht) x)) hrow
  rw [log_mul hj.ne' (multivariateGaussianPDFReal_pos (m j) (t • N) (hN.smul ht) x).ne'] at hlower
  have hquad := normalizer_sub_quadratic_le_log_multivariateGaussianPDFReal_smul
    (m j) x N hN ha hat htb
  have hupper := log_gaussianMixturePDFReal_smul_le w hw hw1 m N hN x ha hat
  have hq := div_nonneg (gaussianHeat_quadratic_nonneg (m j) x N hN)
    (mul_pos (by norm_num : (0 : ℝ) < 2) ha).le
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (gaussianHeatLogNormalizer N b), neg_abs_le (log (w j)),
      abs_nonneg (gaussianHeatLogNormalizer N a)]
  · linarith [le_abs_self (gaussianHeatLogNormalizer N a),
      abs_nonneg (gaussianHeatLogNormalizer N b), abs_nonneg (log (w j))]

end FiniteMixture

end CapacityAtlas.MeasureInformation
