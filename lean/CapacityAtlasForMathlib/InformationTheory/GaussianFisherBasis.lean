/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureAffine
import Mathlib.Analysis.InnerProductSpace.Dual

open MeasureTheory ProbabilityTheory Real Matrix
open scoped BigOperators ENNReal

namespace CapacityAtlas.MeasureInformation

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

omit [DecidableEq ι] in
lemma sum_directionalScore_sq_eq_of_orthonormalBasis
    (p : EuclideanSpace ℝ ι → ℝ) (hp : Differentiable ℝ p)
    (b b' : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (x : EuclideanSpace ℝ ι) :
    (∑ i, directionalScore p (b i) x ^ 2) = ∑ i, directionalScore p (b' i) x ^ 2 := by
  let L := (p x)⁻¹ • fderiv ℝ p x
  have hscore (v : EuclideanSpace ℝ ι) : directionalScore p v x = L v := by
    rw [directionalScore, ((hp x).hasFDerivAt.hasLineDerivAt v).lineDeriv]
    simp only [L, _root_.smul_apply, smul_eq_mul]
    ring
  simp_rw [hscore]
  exact b.norm_dual L |>.symm.trans (b'.norm_dual L)

@[fun_prop]
lemma differentiable_gaussianMixturePDFReal (w : α → ℝ) (m : α → EuclideanSpace ℝ ι)
    (N : Matrix ι ι ℝ) : Differentiable ℝ (gaussianMixturePDFReal w m N) := by
  have hcoord (i : ι) : Differentiable ℝ (fun x : EuclideanSpace ℝ ι ↦ x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable
  change Differentiable ℝ (fun x ↦ gaussianMixturePDFReal w m N x)
  simp only [gaussianMixturePDFReal, multivariateGaussianPDFReal, dotProduct, Matrix.mulVec,
    WithLp.ofLp_sub, Pi.sub_apply]
  fun_prop

/-- The total Fisher information is independent of the orthonormal basis. -/
theorem sum_directionalFisherWith_gaussianMixturePDFReal_basis
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (b b' : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) :
    (∑ i, directionalFisherWith volume (gaussianMixturePDFReal w m N) (b i)) =
      ∑ i, directionalFisherWith volume (gaussianMixturePDFReal w m N) (b' i) := by
  have hint (v : EuclideanSpace ℝ ι) : Integrable
      (fun x ↦ directionalScore (gaussianMixturePDFReal w m N) v x ^ 2)
      (gaussianMixtureMeasure w m N) := by
    apply integrable_gaussianMixtureMeasure
    intro a
    exact (memLp_two_iff_integrable_sq
      (measurable_directionalScore_gaussianMixturePDFReal w m N hN v).aestronglyMeasurable).mp
      (memLp_directionalScore_gaussianMixturePDFReal w hw hw1 m N hN v (m a) N 2 (by norm_num))
  simp_rw [directionalFisherWith_eq_gaussianMixtureMeasure w hw m N hN]
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ hint (b i)), ← integral_finsetSum Finset.univ (fun i _ ↦ hint (b' i))]
  apply integral_congr_ae
  filter_upwards with x
  exact sum_directionalScore_sq_eq_of_orthonormalBasis _
    (differentiable_gaussianMixturePDFReal w m N) b b' x

end CapacityAtlas.MeasureInformation
