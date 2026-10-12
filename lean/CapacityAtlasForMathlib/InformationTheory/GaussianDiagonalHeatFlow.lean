/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianDeBruijn

open MeasureTheory ProbabilityTheory Real Matrix Filter
open scoped BigOperators Topology

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

lemma inverse_diagonal_pos (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i ↦ (d i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  have heq : (fun i ↦ (d i)⁻¹ * d i) = fun _ ↦ (1 : ℝ) := by
    funext i
    exact inv_mul_cancel₀ (hd i).ne'
  rw [heq, Matrix.diagonal_one]

lemma log_multivariateGaussianPDFReal_diagonal (m x : EuclideanSpace ℝ ι)
    (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    log (multivariateGaussianPDFReal m (Matrix.diagonal d) x) =
      -((Fintype.card ι : ℝ) * log (2 * π) + ∑ i, log (d i)) / 2 -
        (∑ i, (x i - m i) ^ 2 / d i) / 2 := by
  rw [log_multivariateGaussianPDFReal m (Matrix.diagonal d) (Matrix.PosDef.diagonal hd),
    Matrix.det_diagonal, log_prod (fun i _ ↦ (hd i).ne'), inverse_diagonal_pos d hd]
  congr 2
  simp only [dotProduct, Matrix.mulVec_diagonal, WithLp.ofLp_sub, Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma hasDerivAt_log_multivariateGaussianPDFReal_diagonal_add
    (m x : EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ log (multivariateGaussianPDFReal m (Matrix.diagonal (fun i ↦ c i + s)) x))
      ((1 / 2 : ℝ) * ∑ i, (((x i - m i) / (c i + t)) ^ 2 - 1 / (c i + t))) t := by
  have hct (i : ι) : 0 < c i + t := add_pos_of_nonneg_of_pos (hc i) ht
  have heq : (fun s ↦ log (multivariateGaussianPDFReal m (Matrix.diagonal (fun i ↦ c i + s)) x))
      =ᶠ[𝓝 t] (fun s ↦ -((Fintype.card ι : ℝ) * log (2 * π) + ∑ i, log (c i + s)) / 2 -
        (∑ i, (x i - m i) ^ 2 / (c i + s)) / 2) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact log_multivariateGaussianPDFReal_diagonal m x (fun i ↦ c i + s)
      (fun i ↦ add_pos_of_nonneg_of_pos (hc i) hs)
  have hlog := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) ↦
    ((hasDerivAt_id t).const_add (c i)).log (hct i).ne')
  have hquad := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) ↦
    (hasDerivAt_const t ((x i - m i) ^ 2)).div
      ((hasDerivAt_id t).const_add (c i)) (hct i).ne')
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert! ((hlog.const_add ((Fintype.card ι : ℝ) * log (2 * π))).neg.div_const 2).sub
    (hquad.div_const 2) using 1
  simp only [id_eq, one_div, zero_mul, zero_sub, mul_one, neg_div]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  simp only [div_pow, neg_div]
  ring

lemma hasDerivAt_multivariateGaussianPDFReal_diagonal_add
    (m x : EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ multivariateGaussianPDFReal m (Matrix.diagonal (fun i ↦ c i + s)) x)
      (((1 / 2 : ℝ) * ∑ i, (((x i - m i) / (c i + t)) ^ 2 - 1 / (c i + t))) *
        multivariateGaussianPDFReal m (Matrix.diagonal (fun i ↦ c i + t)) x) t := by
  have hpos {s : ℝ} (hs : 0 < s) : 0 <
      multivariateGaussianPDFReal m (Matrix.diagonal (fun i ↦ c i + s)) x :=
    multivariateGaussianPDFReal_pos m _
      (Matrix.PosDef.diagonal (fun i ↦ add_pos_of_nonneg_of_pos (hc i) hs)) x
  have heq : (fun s ↦ multivariateGaussianPDFReal m (Matrix.diagonal (fun i ↦ c i + s)) x)
      =ᶠ[𝓝 t] (fun s ↦ exp (log (multivariateGaussianPDFReal m
        (Matrix.diagonal (fun i ↦ c i + s)) x))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (exp_log (hpos hs)).symm
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  simpa only [exp_log (hpos ht), mul_comm] using
    (hasDerivAt_log_multivariateGaussianPDFReal_diagonal_add m x c hc ht).exp

lemma lineDeriv_lineDeriv_multivariateGaussianPDFReal_diagonal
    (m x : EuclideanSpace ℝ ι) (d : ι → ℝ) (hd : ∀ i, 0 < d i) (i : ι) :
    lineDeriv ℝ (fun y ↦ lineDeriv ℝ (multivariateGaussianPDFReal m (Matrix.diagonal d)) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
      (((x i - m i) / d i) ^ 2 - 1 / d i) *
        multivariateGaussianPDFReal m (Matrix.diagonal d) x := by
  rw [(hasLineDerivAt_lineDeriv_multivariateGaussianPDFReal m x (EuclideanSpace.single i 1)
    (Matrix.diagonal d) (Matrix.PosDef.diagonal hd)).lineDeriv, inverse_diagonal_pos d hd]
  simp only [PiLp.ofLp_single, single_one_dotProduct, Matrix.mulVec_diagonal,
    Pi.sub_apply, Pi.single_eq_same, mul_one, div_eq_mul_inv, mul_comm]

/-- The native heat equation allows arbitrary diagonal initial covariance. -/
theorem hasDerivAt_multivariateGaussianPDFReal_diagonal_heat
    (m x : EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ multivariateGaussianPDFReal m (Matrix.diagonal (fun i ↦ c i + s)) x)
      ((1 / 2 : ℝ) * ∑ i, lineDeriv ℝ (fun y ↦ lineDeriv ℝ
        (multivariateGaussianPDFReal m (Matrix.diagonal (fun i ↦ c i + t))) y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) t := by
  apply (hasDerivAt_multivariateGaussianPDFReal_diagonal_add m x c hc ht).congr_deriv
  simp_rw [lineDeriv_lineDeriv_multivariateGaussianPDFReal_diagonal m x
    (fun i ↦ c i + t) (fun i ↦ add_pos_of_nonneg_of_pos (hc i) ht)]
  rw [← Finset.sum_mul, mul_assoc]

noncomputable def gaussianDiagonalHeatScore (m : EuclideanSpace ℝ ι) (c : ι → ℝ)
    (t : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (((x i - m i) / (c i + t)) ^ 2 - 1 / (c i + t))

noncomputable def gaussianDiagonalMixtureHeatDeriv (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) (t : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ a, w a * (gaussianDiagonalHeatScore (m a) c t x *
    multivariateGaussianPDFReal (m a) (Matrix.diagonal (fun i ↦ c i + t)) x)

lemma hasDerivAt_gaussianMixturePDFReal_diagonal_add (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (x : EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ gaussianMixturePDFReal w m (Matrix.diagonal (fun i ↦ c i + s)) x)
      (gaussianDiagonalMixtureHeatDeriv w m c t x) t := by
  exact HasDerivAt.fun_sum (fun a _ ↦
    (hasDerivAt_multivariateGaussianPDFReal_diagonal_add (m a) x c hc ht).const_mul (w a))

theorem hasDerivAt_gaussianMixturePDFReal_diagonal_heat (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (x : EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ gaussianMixturePDFReal w m (Matrix.diagonal (fun i ↦ c i + s)) x)
      ((1 / 2 : ℝ) * ∑ i, lineDeriv ℝ (fun y ↦ lineDeriv ℝ
        (gaussianMixturePDFReal w m (Matrix.diagonal (fun i ↦ c i + t))) y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) t := by
  have hdiag := Matrix.PosDef.diagonal (fun i ↦ add_pos_of_nonneg_of_pos (hc i) ht)
  convert! HasDerivAt.fun_sum (fun a (_ : a ∈ Finset.univ) ↦
    (hasDerivAt_multivariateGaussianPDFReal_diagonal_heat (m a) x c hc ht).const_mul (w a)) using 1
  unfold gaussianMixturePDFReal
  simp_rw [lineDeriv_lineDeriv_gaussian_mixture w m _ hdiag]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma abs_gaussianDiagonalHeatScore_le (m x : EuclideanSpace ℝ ι)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    |gaussianDiagonalHeatScore m c t x| ≤ gaussianHeatScoreBound m 1 a x := by
  have hct (i : ι) : a ≤ c i + t := le_add_of_nonneg_left (hc i) |>.trans' hat
  have hp (i : ι) : 0 < c i + t := ha.trans_le (hct i)
  have hterm (i : ι) : |((x i - m i) / (c i + t)) ^ 2 - 1 / (c i + t)| ≤
      (x i - m i) ^ 2 / a ^ 2 + 1 / a := by
    calc
      _ ≤ |((x i - m i) / (c i + t)) ^ 2| + |1 / (c i + t)| := abs_sub _ _
      _ = (x i - m i) ^ 2 / (c i + t) ^ 2 + 1 / (c i + t) := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_pos (one_div_pos.mpr (hp i)), div_pow]
      _ ≤ _ := add_le_add
        (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos ha)
          (sq_le_sq₀ ha.le (hp i).le |>.mpr (hct i)))
        (div_le_div_of_nonneg_left zero_le_one ha (hct i))
  have hq : (x - m) ⬝ᵥ (1 : Matrix ι ι ℝ)⁻¹ *ᵥ (x - m) =
      ∑ i, (x i - m i) ^ 2 := by simp [dotProduct, pow_two]
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ i, |((x i - m i) / (c i + t)) ^ 2 - 1 / (c i + t)| := by
      rw [gaussianDiagonalHeatScore, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∑ i, ((x i - m i) ^ 2 / a ^ 2 + 1 / a) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hterm i)) (by norm_num)
    _ = _ := by
      rw [gaussianHeatScoreBound, hq, Finset.sum_add_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end CapacityAtlas.MeasureInformation
