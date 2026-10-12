/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianDiagonalHeatBounds

open MeasureTheory ProbabilityTheory Real Matrix Filter
open scoped BigOperators Topology

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

omit [DecidableEq ι] in
@[fun_prop]
lemma measurable_gaussianDiagonalHeatScore (m : EuclideanSpace ℝ ι) (c : ι → ℝ) (t : ℝ) :
    Measurable (gaussianDiagonalHeatScore m c t) := by
  unfold gaussianDiagonalHeatScore
  fun_prop

@[fun_prop]
lemma measurable_gaussianDiagonalMixtureHeatDeriv (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) (t : ℝ) :
    Measurable (gaussianDiagonalMixtureHeatDeriv w m c t) := by
  unfold gaussianDiagonalMixtureHeatDeriv
  fun_prop

lemma hasDerivAt_gaussianMixturePDFReal_diagonal_mul_log
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (x : EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x *
      log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x))
      (gaussianDiagonalMixtureHeatDeriv w m c t x *
        (1 + log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t)) x))) t := by
  have hp := gaussianMixturePDFReal_pos w hw hw1 m _
    (PosDef.diagonal (fun i ↦ add_pos_of_nonneg_of_pos (hc i) ht)) x
  have hd := hasDerivAt_gaussianMixturePDFReal_diagonal_add w m c hc x ht
  convert! hd.mul (hd.log hp.ne') using 1
  field_simp
  ring

/-- Differentiation under the entropy integral for arbitrary diagonal initial covariance. -/
theorem hasDerivAt_integral_gaussianMixturePDFReal_diagonal_mul_log
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ ∫ x, gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x *
      log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x))
      (∫ x, gaussianDiagonalMixtureHeatDeriv w m c t x *
        (1 + log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t)) x))) t := by
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) ↦ hw a)).mp
    (show 0 < ∑ a, w a by rw [hw1]; norm_num)
  have ha : 0 < t / 2 := by positivity
  have hsum : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ hc i)
  have hb : 0 < 2 * t + ∑ i, c i := by positivity
  have hnb : Set.Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hi : Integrable (fun x ↦ gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t)) x *
      log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t)) x)) volume := by
    simpa only [one_smul] using integrable_gaussianMixturePDFReal_mul_log w hw hw1 m
      (diagonal (fun i ↦ c i + t))
      (PosDef.diagonal (fun i ↦ add_pos_of_nonneg_of_pos (hc i) ht)) j hj zero_lt_one
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s x ↦ gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x *
      log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x))
    (F' := fun s x ↦ gaussianDiagonalMixtureHeatDeriv w m c s x *
      (1 + log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x)))
    (bound := gaussianMixtureEntropyDerivBound w m 1 j (t / 2) (2 * t + ∑ i, c i)) hnb
    (Eventually.of_forall (fun _ ↦ by fun_prop)) hi (by fun_prop) _
    (integrable_gaussianMixtureEntropyDerivBound w m 1 PosDef.one j (t / 2) hb) _).2
  · filter_upwards with x
    intro s hs
    exact (Real.norm_eq_abs _).trans_le
      (abs_gaussianDiagonalMixtureHeatDeriv_mul_log_le w hw hw1 m c hc j hj x ha hb hs.1.le
        (fun i ↦ by
          have hi := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hc i) (Finset.mem_univ i)
          linarith [hs.2]))
  · filter_upwards with x
    intro s hs
    exact hasDerivAt_gaussianMixturePDFReal_diagonal_mul_log w hw hw1 m c hc x (ha.trans hs.1)

/-- The native de Bruijn identity along a diagonal covariance plus isotropic noise. -/
theorem hasDerivAt_entropyWith_gaussianMixture_diagonal_add
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ entropyWith (volume.withDensity
      (fun x ↦ ENNReal.ofReal (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x))) volume)
      ((1 / 2 : ℝ) * ∑ i, directionalFisherWith volume
        (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + t))) (EuclideanSpace.single i 1)) t := by
  let N := diagonal (fun i ↦ c i + t)
  have hN : N.PosDef := PosDef.diagonal (fun i ↦ add_pos_of_nonneg_of_pos (hc i) ht)
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) ↦ hw a)).mp
    (show 0 < ∑ a, w a by rw [hw1]; norm_num)
  have hlog (k : α) : MemLp (fun x ↦ 1 + log (gaussianMixturePDFReal w m N x)) 2
      (multivariateGaussian (m k) N) := by
    have hcst : MemLp (fun _ : EuclideanSpace ℝ ι ↦ (1 : ℝ)) 2
        (multivariateGaussian (m k) N) := memLp_const 1
    apply hcst.add
    simpa only [one_smul] using
      memLp_two_log_gaussianMixturePDFReal_smul w hw hw1 m N hN j hj zero_lt_one (m k) N
  have hheat (x : EuclideanSpace ℝ ι) : gaussianDiagonalMixtureHeatDeriv w m c t x =
      (1 / 2 : ℝ) * ∑ i, lineDeriv ℝ (fun y ↦ lineDeriv ℝ
        (gaussianMixturePDFReal w m N) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) :=
    (hasDerivAt_gaussianMixturePDFReal_diagonal_add w m c hc x ht).unique
      (hasDerivAt_gaussianMixturePDFReal_diagonal_heat w m c hc x ht)
  have hderiv := (hasDerivAt_integral_gaussianMixturePDFReal_diagonal_mul_log w hw hw1 m c hc ht).neg
  have heq : (fun s ↦ entropyWith (volume.withDensity
      (fun x ↦ ENNReal.ofReal (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x))) volume)
      =ᶠ[𝓝 t] (fun s ↦ -(∫ x, gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x *
        log (gaussianMixturePDFReal w m (diagonal (fun i ↦ c i + s)) x))) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact entropyWith_gaussianMixtureDensity w hw hw1 m _
      (PosDef.diagonal (fun i ↦ add_pos_of_nonneg_of_pos (hc i) hs))
  apply (hderiv.congr_of_eventuallyEq heq).congr_deriv
  change -(∫ x, gaussianDiagonalMixtureHeatDeriv w m c t x *
    (1 + log (gaussianMixturePDFReal w m N x))) = _
  simp_rw [hheat, mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum]
  · have hibp (v : EuclideanSpace ℝ ι) :=
      integral_one_add_log_mul_secondDeriv_gaussianMixture w hw hw1 m N hN zero_lt_one v
    simp only [one_smul] at hibp
    simp_rw [mul_comm (lineDeriv ℝ _ _ _), hibp, Finset.sum_neg_distrib]
    ring
  · intro i _
    exact integrable_gaussianMixture_lineDeriv_lineDeriv_mul w m N hN
      (EuclideanSpace.single i 1) _ hlog

end CapacityAtlas.MeasureInformation
