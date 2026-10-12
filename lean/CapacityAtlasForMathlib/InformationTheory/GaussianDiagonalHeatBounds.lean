/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianDiagonalHeatFlow

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

lemma identity_covarianceQuadratic (m x : EuclideanSpace ℝ ι) :
    (x - m) ⬝ᵥ (1 : Matrix ι ι ℝ)⁻¹ *ᵥ (x - m) = ∑ i, (x i - m i) ^ 2 := by
  simp [dotProduct, pow_two]

omit [DecidableEq ι] in
lemma diagonal_log_sum_bounds (d : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (had : ∀ i, a ≤ d i) (hdb : ∀ i, d i ≤ b) :
    (Fintype.card ι : ℝ) * log a ≤ ∑ i, log (d i) ∧
      (∑ i, log (d i)) ≤ (Fintype.card ι : ℝ) * log b := by
  constructor
  · simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ log_le_log ha (had i))
  · simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ log_le_log (ha.trans_le (had i)) (hdb i))

omit [DecidableEq ι] in
lemma diagonal_quadratic_bounds (m x : EuclideanSpace ℝ ι) (d : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (had : ∀ i, a ≤ d i) (hdb : ∀ i, d i ≤ b) :
    (∑ i, (x i - m i) ^ 2) / b ≤ ∑ i, (x i - m i) ^ 2 / d i ∧
      (∑ i, (x i - m i) ^ 2 / d i) ≤ (∑ i, (x i - m i) ^ 2) / a := by
  simp only [Finset.sum_div]
  constructor
  · exact Finset.sum_le_sum fun i _ ↦
      div_le_div_of_nonneg_left (sq_nonneg _) (ha.trans_le (had i)) (hdb i)
  · exact Finset.sum_le_sum fun i _ ↦
      div_le_div_of_nonneg_left (sq_nonneg _) ha (had i)

lemma log_multivariateGaussianPDFReal_diagonal_le_normalizer
    (m x : EuclideanSpace ℝ ι) (d : ι → ℝ) {a : ℝ}
    (ha : 0 < a) (had : ∀ i, a ≤ d i) :
    log (multivariateGaussianPDFReal m (diagonal d) x) ≤ gaussianHeatLogNormalizer (1 : Matrix ι ι ℝ) a := by
  have hl : (Fintype.card ι : ℝ) * log a ≤ ∑ i, log (d i) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ log_le_log ha (had i))
  have hq : 0 ≤ ∑ i, (x i - m i) ^ 2 / d i :=
    Finset.sum_nonneg fun i _ ↦ div_nonneg (sq_nonneg _) (ha.trans_le (had i)).le
  rw [log_multivariateGaussianPDFReal_diagonal m x d (fun i ↦ ha.trans_le (had i))]
  unfold gaussianHeatLogNormalizer
  simp only [Matrix.det_one, log_one, add_zero]
  linarith

lemma normalizer_sub_quadratic_le_log_multivariateGaussianPDFReal_diagonal
    (m x : EuclideanSpace ℝ ι) (d : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (had : ∀ i, a ≤ d i) (hdb : ∀ i, d i ≤ b) :
    gaussianHeatLogNormalizer (1 : Matrix ι ι ℝ) b -
      ((x - m) ⬝ᵥ (1 : Matrix ι ι ℝ)⁻¹ *ᵥ (x - m)) / (2 * a) ≤
        log (multivariateGaussianPDFReal m (diagonal d) x) := by
  have hl := (diagonal_log_sum_bounds d ha had hdb).2
  have hq := (diagonal_quadratic_bounds m x d ha had hdb).2
  rw [log_multivariateGaussianPDFReal_diagonal m x d (fun i ↦ ha.trans_le (had i)),
    identity_covarianceQuadratic]
  unfold gaussianHeatLogNormalizer
  simp only [Matrix.det_one, log_one, add_zero]
  rw [show (∑ i, (x i - m i) ^ 2) / (2 * a) = (∑ i, (x i - m i) ^ 2) / a / 2 by ring]
  linarith

theorem multivariateGaussianPDFReal_diagonal_le_isotropic
    (m x : EuclideanSpace ℝ ι) (d : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (had : ∀ i, a ≤ d i) (hdb : ∀ i, d i ≤ b) :
    multivariateGaussianPDFReal m (diagonal d) x ≤
      exp ((Fintype.card ι : ℝ) * (log b - log a) / 2) *
        multivariateGaussianPDFReal m (b • (1 : Matrix ι ι ℝ)) x := by
  have hd := Matrix.PosDef.diagonal (fun i ↦ ha.trans_le (had i))
  have hl := (diagonal_log_sum_bounds d ha had hdb).1
  have hq := (diagonal_quadratic_bounds m x d ha had hdb).1
  have hcomp : log (multivariateGaussianPDFReal m (diagonal d) x) ≤
      (Fintype.card ι : ℝ) * (log b - log a) / 2 +
        log (multivariateGaussianPDFReal m (b • (1 : Matrix ι ι ℝ)) x) := by
    rw [log_multivariateGaussianPDFReal_diagonal m x d (fun i ↦ ha.trans_le (had i)),
      log_multivariateGaussianPDFReal_smul m x 1 PosDef.one hb, identity_covarianceQuadratic]
    simp only [Matrix.det_one, log_one, add_zero]
    rw [show (∑ i, (x i - m i) ^ 2) / (2 * b) = (∑ i, (x i - m i) ^ 2) / b / 2 by ring]
    nlinarith
  calc
    _ = exp (log (multivariateGaussianPDFReal m (diagonal d) x)) :=
      (exp_log (multivariateGaussianPDFReal_pos m _ hd x)).symm
    _ ≤ exp ((Fintype.card ι : ℝ) * (log b - log a) / 2 +
        log (multivariateGaussianPDFReal m (b • (1 : Matrix ι ι ℝ)) x)) := exp_le_exp.mpr hcomp
    _ = _ := by rw [exp_add, exp_log (multivariateGaussianPDFReal_pos m _ (PosDef.one.smul hb) x)]

theorem log_gaussianMixturePDFReal_diagonal_le (w : α → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (m : α → EuclideanSpace ℝ ι) (d : ι → ℝ)
    (x : EuclideanSpace ℝ ι) {a : ℝ} (ha : 0 < a) (had : ∀ i, a ≤ d i) :
    log (gaussianMixturePDFReal w m (diagonal d) x) ≤ gaussianHeatLogNormalizer (1 : Matrix ι ι ℝ) a := by
  have hd := Matrix.PosDef.diagonal (fun i ↦ ha.trans_le (had i))
  have hupper : gaussianMixturePDFReal w m (diagonal d) x ≤ exp (gaussianHeatLogNormalizer (1 : Matrix ι ι ℝ) a) := by
    calc
      _ ≤ ∑ j, w j * exp (gaussianHeatLogNormalizer (1 : Matrix ι ι ℝ) a) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (hw j)
        rw [← log_le_iff_le_exp (multivariateGaussianPDFReal_pos (m j) _ hd x)]
        exact log_multivariateGaussianPDFReal_diagonal_le_normalizer (m j) x d ha had
      _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]
  exact (log_le_log (gaussianMixturePDFReal_pos w hw hw1 m _ hd x) hupper).trans_eq (log_exp _)

theorem abs_log_gaussianMixturePDFReal_diagonal_le (w : α → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (m : α → EuclideanSpace ℝ ι) (d : ι → ℝ) (j : α) (hj : 0 < w j)
    (x : EuclideanSpace ℝ ι) {a b : ℝ}
    (ha : 0 < a) (had : ∀ i, a ≤ d i) (hdb : ∀ i, d i ≤ b) :
    |log (gaussianMixturePDFReal w m (diagonal d) x)| ≤ gaussianMixtureLogBound w m 1 j a b x := by
  have hd := Matrix.PosDef.diagonal (fun i ↦ ha.trans_le (had i))
  have hrow : w j * multivariateGaussianPDFReal (m j) (diagonal d) x ≤
      gaussianMixturePDFReal w m (diagonal d) x :=
    Finset.single_le_sum (fun k _ ↦ mul_nonneg (hw k)
      (multivariateGaussianPDFReal_pos (m k) _ hd x).le) (Finset.mem_univ j)
  have hlower := log_le_log (mul_pos hj (multivariateGaussianPDFReal_pos (m j) _ hd x)) hrow
  rw [log_mul hj.ne' (multivariateGaussianPDFReal_pos (m j) _ hd x).ne'] at hlower
  have hquad := normalizer_sub_quadratic_le_log_multivariateGaussianPDFReal_diagonal
    (m j) x d ha had hdb
  have hupper := log_gaussianMixturePDFReal_diagonal_le w hw hw1 m d x ha had
  have hq : 0 ≤ ((x - m j) ⬝ᵥ (1 : Matrix ι ι ℝ)⁻¹ *ᵥ (x - m j)) / (2 * a) :=
    div_nonneg (gaussianHeat_quadratic_nonneg (m j) x 1 PosDef.one) (by positivity)
  unfold gaussianMixtureLogBound
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (gaussianHeatLogNormalizer (1 : Matrix ι ι ℝ) b),
      neg_abs_le (log (w j)), abs_nonneg (gaussianHeatLogNormalizer (1 : Matrix ι ι ℝ) a)]
  · linarith [le_abs_self (gaussianHeatLogNormalizer (1 : Matrix ι ι ℝ) a),
      abs_nonneg (gaussianHeatLogNormalizer (1 : Matrix ι ι ℝ) b), abs_nonneg (log (w j))]

theorem abs_gaussianDiagonalMixtureHeatDeriv_mul_log_le (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (j : α) (hj : 0 < w j)
    (x : EuclideanSpace ℝ ι) {a t b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hat : a ≤ t) (hcb : ∀ i, c i + t ≤ b) :
    |gaussianDiagonalMixtureHeatDeriv w m c t x *
      (1 + log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t)) x))| ≤
        gaussianMixtureEntropyDerivBound w m 1 j a b x := by
  let C := exp ((Fintype.card ι : ℝ) * (log b - log a) / 2)
  have had (i : ι) : a ≤ c i + t := hat.trans (le_add_of_nonneg_left (hc i))
  have hdpos := Matrix.PosDef.diagonal (fun i ↦ ha.trans_le (had i))
  have hd : |gaussianDiagonalMixtureHeatDeriv w m c t x| ≤
      C * ∑ k, w k * (multivariateGaussianPDFReal (m k) (b • (1 : Matrix ι ι ℝ)) x *
        gaussianHeatScoreBound (m k) 1 a x) := by
    calc
      _ ≤ ∑ k, |w k * (gaussianDiagonalHeatScore (m k) c t x *
          multivariateGaussianPDFReal (m k) (diagonal (fun i ↦ c i + t)) x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, w k * (gaussianHeatScoreBound (m k) 1 a x *
          (C * multivariateGaussianPDFReal (m k) (b • (1 : Matrix ι ι ℝ)) x)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_of_nonneg (hw k), abs_mul,
          abs_of_pos (multivariateGaussianPDFReal_pos (m k) (diagonal (fun i ↦ c i + t)) hdpos x)]
        apply mul_le_mul_of_nonneg_left _ (hw k)
        exact mul_le_mul (abs_gaussianDiagonalHeatScore_le (m k) x c hc ha hat)
          (multivariateGaussianPDFReal_diagonal_le_isotropic (m k) x _ ha hb had hcb)
          (multivariateGaussianPDFReal_pos (m k) (diagonal (fun i ↦ c i + t)) hdpos x).le
          (gaussianHeatScoreBound_nonneg (m k) x 1 PosDef.one ha)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hl : |1 + log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t)) x)| ≤
      1 + gaussianMixtureLogBound w m 1 j a b x := by
    calc
      _ ≤ |(1 : ℝ)| + |log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t)) x)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_one]
        exact add_le_add le_rfl (abs_log_gaussianMixturePDFReal_diagonal_le
          w hw hw1 m _ j hj x ha had hcb)
  rw [abs_mul]
  calc
    _ ≤ (C * ∑ k, w k * (multivariateGaussianPDFReal (m k) (b • (1 : Matrix ι ι ℝ)) x *
        gaussianHeatScoreBound (m k) 1 a x)) *
          (1 + gaussianMixtureLogBound w m 1 j a b x) :=
      mul_le_mul hd hl (abs_nonneg _) ((abs_nonneg _).trans hd)
    _ = _ := by
      unfold gaussianMixtureEntropyDerivBound
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring

end CapacityAtlas.MeasureInformation
