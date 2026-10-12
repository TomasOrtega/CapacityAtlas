/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.PairwiseBound

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal

namespace CapacityAtlas.Gaussian.Interference

variable {A B ι : Type*}
  [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [Fintype ι] [DecidableEq ι]

/-- The second receiver's interfering coefficient is invertible in the physical application;
`H` transfers its contribution at receiver one to its contribution at receiver two. -/
theorem twoUser_linear_gaussian_fano
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (u u' : A → EuclideanSpace ℝ ι) (v : B → EuclideanSpace ℝ ι)
    (c₁ c₂ : EuclideanSpace ℝ ι) (H : Matrix ι ι ℝ)
    {e t q : ℝ} (he : 0 < e) (ht : 0 < t) (heq : e ≤ q)
    (hres : (q • 1 - H * (e • 1) * H.transpose).PosSemidef)
    (d₁ : EuclideanSpace ℝ ι → A) (hd₁ : Measurable d₁)
    (d₂ : EuclideanSpace ℝ ι → B) (hd₂ : Measurable d₂)
    (hμ : ∀ a, μ {a} = (Fintype.card A : ℝ≥0∞)⁻¹)
    (hν : ∀ b, ν {b} = (Fintype.card B : ℝ≥0∞)⁻¹) :
    Real.log (Fintype.card A) + Real.log (Fintype.card B) ≤
      (Fintype.card ι : ℝ) / 2 * Real.log (t / e) +
      ((Fintype.card ι : ℝ) * e + (∫ p : A × B, ‖u p.1 + v p.2‖ ^ 2 ∂μ.prod ν)) /
        (2 * t) - (Fintype.card ι : ℝ) / 2 + 2 * Real.log 2 +
      (∫ a, ∫ b, (multivariateGaussian (u a + v b + c₁) (q • 1)).real
        {y | d₁ y ≠ a} ∂ν ∂μ) * Real.log (Fintype.card A) +
      (∫ a, ∫ b, (multivariateGaussian (u' a + H.toEuclideanLin (v b) + c₂) (q • 1)).real
        {z | d₂ z ≠ b} ∂ν ∂μ) * Real.log (Fintype.card B) := by
  let η₁ := affineGaussianKernel (1 : Matrix ι ι ℝ) c₁ ((q - e) • 1)
  let η₂ := fun a ↦ affineGaussianKernel H
    (u' a + c₂ - H.toEuclideanLin (u a)) (q • 1 - H * (e • 1) * H.transpose)
  have hr₁ (a : A) (b : B) : η₁ ∘ₘ multivariateGaussian (u a + v b) (e • 1) =
      multivariateGaussian (u a + v b + c₁) (q • 1) := by
    rw [affineGaussianKernel_comp 1 c₁ _ (PosSemidef.one.smul (sub_nonneg.mpr heq))
      _ _ (PosDef.one.smul he).posSemidef]
    congr 1
    · simp only [Matrix.toLpLin_apply, Matrix.one_mulVec, WithLp.toLp_ofLp]
      abel
    · simp only [transpose_one, one_mul, mul_one, ← add_smul]
      congr 1
      ring
  have hr₂ (a : A) (b : B) : η₂ a ∘ₘ multivariateGaussian (u a + v b) (e • 1) =
      multivariateGaussian (u' a + H.toEuclideanLin (v b) + c₂) (q • 1) := by
    rw [affineGaussianKernel_residual H _ _ _ (PosDef.one.smul he).posSemidef hres]
    congr 1
    rw [map_add]
    abel
  have hf := twoUser_gaussian_fano_isotropic μ ν (fun a b ↦ u a + v b) he ht
    η₁ η₂ d₁ hd₁ (fun _ ↦ d₂) (fun _ ↦ hd₂) hμ hν
  simp_rw [hr₁, hr₂] at hf
  exact hf

end CapacityAtlas.Gaussian.Interference
