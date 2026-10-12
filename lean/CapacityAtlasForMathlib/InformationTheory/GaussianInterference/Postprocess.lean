/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Probability.GaussianBlocks
import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureEntropyBounds

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace CapacityAtlas.Gaussian.Interference

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

noncomputable def affineGaussianKernel (H : Matrix ο ι ℝ)
    (c : EuclideanSpace ℝ ο) (R : Matrix ο ο ℝ) :
    Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ο) :=
  (gaussianChannel H R).map (fun y ↦ c + y)

instance (H : Matrix ο ι ℝ) (c : EuclideanSpace ℝ ο) (R : Matrix ο ο ℝ) :
    IsMarkovKernel (affineGaussianKernel H c R) := by
  unfold affineGaussianKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem affineGaussianKernel_comp (H : Matrix ο ι ℝ)
    (c : EuclideanSpace ℝ ο) (R : Matrix ο ο ℝ) (hR : R.PosSemidef)
    (m : EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosSemidef) :
    affineGaussianKernel H c R ∘ₘ multivariateGaussian m N =
      multivariateGaussian (c + H.toEuclideanLin m) (R + H * N * H.transpose) := by
  rw [affineGaussianKernel, ← Measure.map_comp _ _ (by fun_prop),
    gaussianChannel_comp_multivariateGaussian H R hR m N hN,
    multivariateGaussian_map_const_add]

theorem affineGaussianKernel_residual (H : Matrix ο ι ℝ)
    (c : EuclideanSpace ℝ ο) (N : Matrix ι ι ℝ) (T : Matrix ο ο ℝ)
    (hN : N.PosSemidef) (hR : (T - H * N * H.transpose).PosSemidef)
    (m : EuclideanSpace ℝ ι) :
    affineGaussianKernel H c (T - H * N * H.transpose) ∘ₘ multivariateGaussian m N =
      multivariateGaussian (c + H.toEuclideanLin m) T := by
  rw [affineGaussianKernel_comp H c _ hR m N hN, sub_add_cancel]

theorem inv_scalar_matrix (t : ℝ) :
    (t • (1 : Matrix ι ι ℝ))⁻¹ = t⁻¹ • (1 : Matrix ι ι ℝ) := by
  by_cases ht : t = 0
  · simp [ht]
  · apply Matrix.inv_eq_left_inv
    simp [ht]

theorem scalar_inverse_quadratic (t : ℝ) (x : EuclideanSpace ℝ ι) :
    x ⬝ᵥ (t • (1 : Matrix ι ι ℝ))⁻¹ *ᵥ x = t⁻¹ * ‖x‖ ^ 2 := by
  rw [inv_scalar_matrix]
  simp only [smul_mulVec, one_mulVec, EuclideanSpace.real_norm_sq_eq,
    dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem trace_inverse_scalar (t s : ℝ) :
    trace ((t • (1 : Matrix ι ι ℝ))⁻¹ * (s • 1)) =
      (Fintype.card ι : ℝ) * s / t := by
  rw [inv_scalar_matrix]
  simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
    trace_smul, trace_one, smul_eq_mul]
  ring

theorem log_det_scalar_matrix (t : ℝ) :
    Real.log (t • (1 : Matrix ι ι ℝ)).det = (Fintype.card ι : ℝ) * Real.log t := by
  rw [det_smul, det_one, mul_one, Real.log_pow]

end CapacityAtlas.Gaussian.Interference
