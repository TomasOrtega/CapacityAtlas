/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianHeatBounds
import CapacityAtlasForMathlib.InformationTheory.GaussianInformationDensity
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory ProbabilityTheory Real Matrix Filter
open scoped BigOperators Topology

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

noncomputable def gaussianHeatTimeScore (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ)
    (t : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  -Fintype.card ι / (2 * t) + ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * t ^ 2)

noncomputable def gaussianMixtureHeatDeriv (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (t : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ a, w a * (gaussianHeatTimeScore (m a) N t x *
    multivariateGaussianPDFReal (m a) (t • N) x)

lemma hasDerivAt_gaussianMixturePDFReal_smul (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (x : EuclideanSpace ℝ ι)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ gaussianMixturePDFReal w m (s • N) x)
      (gaussianMixtureHeatDeriv w m N t x) t := by
  exact HasDerivAt.fun_sum (fun a _ ↦
    (hasDerivAt_multivariateGaussianPDFReal_smul (m a) x N hN ht).const_mul (w a))

lemma hasDerivAt_gaussianMixturePDFReal_mul_log (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (x : EuclideanSpace ℝ ι)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ gaussianMixturePDFReal w m (s • N) x *
      log (gaussianMixturePDFReal w m (s • N) x))
      (gaussianMixtureHeatDeriv w m N t x *
        (1 + log (gaussianMixturePDFReal w m (t • N) x))) t := by
  have hp := gaussianMixturePDFReal_pos w hw hw1 m (t • N) (hN.smul ht) x
  have hd := hasDerivAt_gaussianMixturePDFReal_smul w m N hN x ht
  convert! hd.mul (hd.log hp.ne') using 1
  field_simp
  ring

lemma abs_gaussianHeatTimeScore_le (m x : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    |gaussianHeatTimeScore m N t x| ≤
      (Fintype.card ι : ℝ) / (2 * a) + ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * a ^ 2) := by
  have ht := ha.trans_le hat
  have hq := gaussianHeat_quadratic_nonneg m x N hN
  have hd := div_nonneg (Nat.cast_nonneg (Fintype.card ι))
    (mul_pos (by norm_num : (0 : ℝ) < 2) ht).le
  have hqt := div_nonneg hq (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos ht)).le
  simp only [WithLp.ofLp_sub] at hqt
  calc
    _ ≤ (Fintype.card ι : ℝ) / (2 * t) +
        ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * t ^ 2) := by
      apply abs_le.mpr
      unfold gaussianHeatTimeScore
      simp only [WithLp.ofLp_sub, neg_div] at hd hqt ⊢
      constructor <;> linarith
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_left (Nat.cast_nonneg (Fintype.card ι))
        (mul_pos (by norm_num) ha) (mul_le_mul_of_nonneg_left hat (by norm_num)))
      (div_le_div_of_nonneg_left hq (mul_pos (by norm_num) (sq_pos_of_pos ha))
        (mul_le_mul_of_nonneg_left (sq_le_sq₀ ha.le ht.le |>.mpr hat) (by norm_num)))

lemma memLp_two_gaussianHeatQuadratic (m k : EuclideanSpace ℝ ι)
    (N S : Matrix ι ι ℝ) :
    MemLp (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ N *ᵥ (x - m)) 2
      (multivariateGaussian k S) := by
  apply memLp_two_covarianceQuadratic id
  intro i
  simpa only [id_eq, EuclideanSpace.coe_proj] using
    (IsGaussian.memLp_id (multivariateGaussian k S) 4 (by norm_num)).continuousLinearMap_comp
      (EuclideanSpace.proj (𝕜 := ℝ) i)

noncomputable def gaussianHeatScoreBound (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ)
    (a : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  (Fintype.card ι : ℝ) / (2 * a) + ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * a ^ 2)

noncomputable def gaussianMixtureLogBound (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (j : α) (a b : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  |gaussianHeatLogNormalizer N a| + |gaussianHeatLogNormalizer N b| + |log (w j)| +
    ((x - m j) ⬝ᵥ N⁻¹ *ᵥ (x - m j)) / (2 * a)

noncomputable def gaussianMixtureEntropyDerivBound (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (j : α) (a b : ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  exp ((Fintype.card ι : ℝ) * (log b - log a) / 2) *
    ∑ k, w k * (multivariateGaussianPDFReal (m k) (b • N) x *
      (gaussianHeatScoreBound (m k) N a x * (1 + gaussianMixtureLogBound w m N j a b x)))

lemma gaussianHeatScoreBound_nonneg (m x : EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) {a : ℝ} (ha : 0 < a) :
    0 ≤ gaussianHeatScoreBound m N a x := by
  exact add_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity))
    (div_nonneg (gaussianHeat_quadratic_nonneg m x N hN) (by positivity))

theorem abs_gaussianMixtureHeatDeriv_mul_log_le (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (j : α) (hj : 0 < w j)
    (x : EuclideanSpace ℝ ι) {a t b : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) :
    |gaussianMixtureHeatDeriv w m N t x *
      (1 + log (gaussianMixturePDFReal w m (t • N) x))| ≤
        gaussianMixtureEntropyDerivBound w m N j a b x := by
  let C := exp ((Fintype.card ι : ℝ) * (log b - log a) / 2)
  have ht := ha.trans_le hat
  have hd : |gaussianMixtureHeatDeriv w m N t x| ≤
      C * ∑ k, w k * (multivariateGaussianPDFReal (m k) (b • N) x *
        gaussianHeatScoreBound (m k) N a x) := by
    calc
      _ ≤ ∑ k, |w k * (gaussianHeatTimeScore (m k) N t x *
          multivariateGaussianPDFReal (m k) (t • N) x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, w k * (gaussianHeatScoreBound (m k) N a x *
          (C * multivariateGaussianPDFReal (m k) (b • N) x)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_of_nonneg (hw k), abs_mul,
          abs_of_pos (multivariateGaussianPDFReal_pos (m k) (t • N) (hN.smul ht) x)]
        apply mul_le_mul_of_nonneg_left _ (hw k)
        exact mul_le_mul (abs_gaussianHeatTimeScore_le (m k) x N hN ha hat)
          (multivariateGaussianPDFReal_smul_le (m k) x N hN ha hat htb)
          (multivariateGaussianPDFReal_pos (m k) (t • N) (hN.smul ht) x).le
          (gaussianHeatScoreBound_nonneg (m k) x N hN ha)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hl : |1 + log (gaussianMixturePDFReal w m (t • N) x)| ≤
      1 + gaussianMixtureLogBound w m N j a b x := by
    calc
      _ ≤ |(1 : ℝ)| + |log (gaussianMixturePDFReal w m (t • N) x)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_one]
        exact add_le_add le_rfl (abs_log_gaussianMixturePDFReal_smul_le
          w hw hw1 m N hN j hj x ha hat htb)
  rw [abs_mul]
  calc
    _ ≤ (C * ∑ k, w k * (multivariateGaussianPDFReal (m k) (b • N) x *
        gaussianHeatScoreBound (m k) N a x)) *
          (1 + gaussianMixtureLogBound w m N j a b x) :=
      mul_le_mul hd hl (abs_nonneg _) ((abs_nonneg _).trans hd)
    _ = _ := by
      unfold gaussianMixtureEntropyDerivBound
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma memLp_two_gaussianHeatScoreBound (m k : EuclideanSpace ℝ ι)
    (N S : Matrix ι ι ℝ) (a : ℝ) :
    MemLp (gaussianHeatScoreBound m N a) 2 (multivariateGaussian k S) := by
  change MemLp (fun x : EuclideanSpace ℝ ι ↦ (Fintype.card ι : ℝ) / (2 * a) +
    ((x - m) ⬝ᵥ N⁻¹ *ᵥ (x - m)) / (2 * a ^ 2)) 2 (multivariateGaussian k S)
  simpa only [div_eq_mul_inv, Pi.add_def] using
    (memLp_const ((Fintype.card ι : ℝ) / (2 * a))).add
      ((memLp_two_gaussianHeatQuadratic m k N⁻¹ S).mul_const (2 * a ^ 2)⁻¹)

omit [Fintype α] in
lemma memLp_two_gaussianMixtureLogBound (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (j : α) (a b : ℝ) (k : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    MemLp (gaussianMixtureLogBound w m N j a b) 2 (multivariateGaussian k S) := by
  change MemLp (fun x : EuclideanSpace ℝ ι ↦ |gaussianHeatLogNormalizer N a| + |gaussianHeatLogNormalizer N b| +
    |log (w j)| + ((x - m j) ⬝ᵥ N⁻¹ *ᵥ (x - m j)) / (2 * a)) 2 (multivariateGaussian k S)
  simpa only [div_eq_mul_inv, Pi.add_def] using
    (memLp_const (|gaussianHeatLogNormalizer N a| + |gaussianHeatLogNormalizer N b| +
      |log (w j)|)).add ((memLp_two_gaussianHeatQuadratic (m j) k N⁻¹ S).mul_const (2 * a)⁻¹)

/-- The entropy derivative has a concrete integrable fourth-degree Gaussian envelope. -/
theorem integrable_gaussianMixtureEntropyDerivBound (w : α → ℝ)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (j : α) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (gaussianMixtureEntropyDerivBound w m N j a b) volume := by
  have hrow (k : α) : Integrable (fun x ↦ multivariateGaussianPDFReal (m k) (b • N) x *
      (gaussianHeatScoreBound (m k) N a x * (1 + gaussianMixtureLogBound w m N j a b x))) volume := by
    have hc : MemLp (fun _ : EuclideanSpace ℝ ι ↦ (1 : ℝ)) 2
        (multivariateGaussian (m k) (b • N)) := memLp_const 1
    have hl : MemLp (fun x ↦ 1 + gaussianMixtureLogBound w m N j a b x) 2
        (multivariateGaussian (m k) (b • N)) :=
      hc.add (memLp_two_gaussianMixtureLogBound w m N j a b (m k) (b • N))
    apply (integrable_multivariateGaussianPDFReal_mul_iff (m k) (b • N) (hN.smul hb) _).mpr
    exact (memLp_two_gaussianHeatScoreBound (m k) (m k) N (b • N) a).integrable_mul hl
  exact (integrable_finsetSum _ (fun k _ ↦ (hrow k).const_mul (w k))).const_mul _

@[fun_prop]
lemma measurable_gaussianHeatTimeScore (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (t : ℝ) :
    Measurable (gaussianHeatTimeScore m N t) := by
  unfold gaussianHeatTimeScore dotProduct Matrix.mulVec
  fun_prop

@[fun_prop]
lemma measurable_gaussianMixtureHeatDeriv (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (t : ℝ) : Measurable (gaussianMixtureHeatDeriv w m N t) := by
  unfold gaussianMixtureHeatDeriv
  fun_prop

lemma memLp_two_log_gaussianMixturePDFReal_smul (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (j : α) (hj : 0 < w j)
    {t : ℝ} (ht : 0 < t) (k : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    MemLp (fun x ↦ log (gaussianMixturePDFReal w m (t • N) x)) 2
      (multivariateGaussian k S) := by
  apply (memLp_two_gaussianMixtureLogBound w m N j t t k S).mono'
    (measurable_gaussianMixturePDFReal w m (t • N)).log.aestronglyMeasurable
  filter_upwards with x
  exact (Real.norm_eq_abs _).trans_le
    (abs_log_gaussianMixturePDFReal_smul_le w hw hw1 m N hN j hj x ht le_rfl le_rfl)

theorem integrable_gaussianMixturePDFReal_mul_log (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) (hN : N.PosDef) (j : α) (hj : 0 < w j)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x ↦ gaussianMixturePDFReal w m (t • N) x *
      log (gaussianMixturePDFReal w m (t • N) x)) volume := by
  have hrow (k : α) : Integrable (fun x ↦ multivariateGaussianPDFReal (m k) (t • N) x *
      log (gaussianMixturePDFReal w m (t • N) x)) volume := by
    apply (integrable_multivariateGaussianPDFReal_mul_iff (m k) (t • N) (hN.smul ht) _).mpr
    exact (memLp_two_log_gaussianMixturePDFReal_smul w hw hw1 m N hN j hj ht
      (m k) (t • N)).integrable (by norm_num)
  convert! integrable_finsetSum Finset.univ (fun k _ ↦ (hrow k).const_mul (w k)) using 1
  ext x
  simp only [gaussianMixturePDFReal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Differentiation of the actual finite-mixture entropy integral, with domination proved. -/
theorem hasDerivAt_integral_gaussianMixturePDFReal_mul_log
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ ∫ x, gaussianMixturePDFReal w m (s • N) x *
      log (gaussianMixturePDFReal w m (s • N) x))
      (∫ x, gaussianMixtureHeatDeriv w m N t x *
        (1 + log (gaussianMixturePDFReal w m (t • N) x))) t := by
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun a (_ : a ∈ Finset.univ) ↦ hw a)).mp
    (show 0 < ∑ a, w a by rw [hw1]; norm_num)
  have ha : 0 < t / 2 := by positivity
  have hb : 0 < 2 * t := by positivity
  have hnb : Set.Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s x ↦ gaussianMixturePDFReal w m (s • N) x *
      log (gaussianMixturePDFReal w m (s • N) x))
    (F' := fun s x ↦ gaussianMixtureHeatDeriv w m N s x *
      (1 + log (gaussianMixturePDFReal w m (s • N) x)))
    (bound := gaussianMixtureEntropyDerivBound w m N j (t / 2) (2 * t)) hnb
    (Eventually.of_forall (fun _ ↦ by fun_prop))
    (integrable_gaussianMixturePDFReal_mul_log w hw hw1 m N hN j hj ht)
    (by fun_prop) _ (integrable_gaussianMixtureEntropyDerivBound w m N hN j (t / 2) hb) _).2
  · filter_upwards with x
    intro s hs
    exact (Real.norm_eq_abs _).trans_le
      (abs_gaussianMixtureHeatDeriv_mul_log_le w hw hw1 m N hN j hj x ha hs.1.le hs.2.le)
  · filter_upwards with x
    intro s hs
    exact hasDerivAt_gaussianMixturePDFReal_mul_log w hw hw1 m N hN x (ha.trans hs.1)

end CapacityAtlas.MeasureInformation
