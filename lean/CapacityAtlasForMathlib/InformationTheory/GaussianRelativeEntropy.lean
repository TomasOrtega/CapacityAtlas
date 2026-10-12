/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MultivariateGaussianEntropy

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators NNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma memLp_eval_multivariateGaussian (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (i : ι) :
    MemLp (fun x : EuclideanSpace ℝ ι ↦ x i) 2 (multivariateGaussian m S) := by
  simpa only [id_eq, EuclideanSpace.coe_proj] using
    (IsGaussian.memLp_two_id (μ := multivariateGaussian m S)).continuousLinearMap_comp
      (EuclideanSpace.proj (𝕜 := ℝ) i)

lemma integral_eval_multivariateGaussian (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (i : ι) :
    (∫ x : EuclideanSpace ℝ ι, x i ∂multivariateGaussian m S) = m i := by
  change (∫ x : EuclideanSpace ℝ ι, (EuclideanSpace.proj i) x ∂multivariateGaussian m S) = _
  rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id
      (EuclideanSpace.proj (𝕜 := ℝ) i),
    integral_id_multivariateGaussian]
  rfl

lemma integral_quadratic_multivariateGaussian (m a : EuclideanSpace ℝ ι)
    (S A : Matrix ι ι ℝ) (hS : S.PosSemidef) :
    (∫ x : EuclideanSpace ℝ ι, (x - a) ⬝ᵥ A *ᵥ (x - a) ∂multivariateGaussian m S) =
      trace (A * S) + (m - a) ⬝ᵥ A *ᵥ (m - a) :=
  integral_quadratic_eq_trace_add (memLp_eval_multivariateGaussian m S) m a A S
    (integral_eval_multivariateGaussian m S) (covariance_eval_multivariateGaussian hS)
    (isHermitian_iff_isSymm.mp hS.isHermitian)

end ProbabilityTheory

namespace CapacityAtlas.MeasureInformation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem klDiv_multivariateGaussian_ne_top (m a : EuclideanSpace ℝ ι)
    (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef) :
    _root_.InformationTheory.klDiv (multivariateGaussian m S) (multivariateGaussian a T) ≠ ⊤ := by
  have hexp : Integrable (fun x ↦ exp (log (multivariateGaussianPDFReal a T x))) volume := by
    simpa only [exp_log (multivariateGaussianPDFReal_pos a T hT _)] using
      integrable_multivariateGaussianPDFReal a T hT
  rw [multivariateGaussian_eq_tilted_log_density a T hT]
  exact _root_.InformationTheory.klDiv_ne_top
    ((multivariateGaussian_absolutelyContinuous m S hS).trans (absolutelyContinuous_tilted hexp))
    (integrable_llr_tilted_right (multivariateGaussian_absolutelyContinuous m S hS)
      (integrable_log_multivariateGaussianPDFReal a T hT
        (integrable_covarianceQuadratic (memLp_eval_multivariateGaussian m S) a T⁻¹))
      (integrable_llr_multivariateGaussian_volume m S hS) hexp)

/-- Relative entropy of two nondegenerate native vector Gaussian laws, in nats. -/
theorem toReal_klDiv_multivariateGaussian (m a : EuclideanSpace ℝ ι)
    (S T : Matrix ι ι ℝ) (hS : S.PosDef) (hT : T.PosDef) :
    (_root_.InformationTheory.klDiv (multivariateGaussian m S) (multivariateGaussian a T)).toReal =
      (log T.det - log S.det - Fintype.card ι + trace (T⁻¹ * S) +
        (m - a) ⬝ᵥ T⁻¹ *ᵥ (m - a)) / 2 := by
  rw [klDiv_multivariateGaussian_eq_crossEntropy_sub_entropy
      (multivariateGaussian_absolutelyContinuous m S hS)
      (integrable_llr_multivariateGaussian_volume m S hS) a T hT
      (integrable_covarianceQuadratic (memLp_eval_multivariateGaussian m S) a T⁻¹),
    entropyWith_multivariateGaussian m S hS,
    integral_quadratic_multivariateGaussian m a S T⁻¹ hS.posSemidef]
  ring

end CapacityAtlas.MeasureInformation
