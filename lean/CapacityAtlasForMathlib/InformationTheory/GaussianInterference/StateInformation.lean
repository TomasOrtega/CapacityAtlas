/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureEntropyBounds

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal

namespace CapacityAtlas.Gaussian.Interference

open MeasureInformation

variable {A B Y Z ι : Type*}
  [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [MeasurableSpace Y] [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]

/-- Two independent messages observed through a common Gaussian mixture, with a genie
giving the first message to the second decoder. -/
theorem twoUser_gaussian_fano
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (m : A → B → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (hN : N.PosDef)
    (η₁ : Kernel (EuclideanSpace ℝ ι) Y) [IsMarkovKernel η₁]
    (η₂ : A → Kernel (EuclideanSpace ℝ ι) Z) [∀ a, IsMarkovKernel (η₂ a)]
    (d₁ : Y → A) (hd₁ : Measurable d₁)
    (d₂ : A → Z → B) (hd₂ : ∀ a, Measurable (d₂ a))
    (hμ : ∀ a, μ {a} = (Fintype.card A : ℝ≥0∞)⁻¹)
    (hν : ∀ b, ν {b} = (Fintype.card B : ℝ≥0∞)⁻¹) :
    Real.log (Fintype.card A) + Real.log (Fintype.card B) ≤
      entropyWith (gaussianCodebookKernel (fun p : A × B ↦ m p.1 p.2) N ∘ₘ μ.prod ν)
        volume - entropyWith (multivariateGaussian 0 N) volume + 2 * Real.log 2 +
      (∫ a, ∫ b, (η₁ ∘ₘ multivariateGaussian (m a b) N).real
        {y | d₁ y ≠ a} ∂ν ∂μ) * Real.log (Fintype.card A) +
      (∫ a, ∫ b, (η₂ a ∘ₘ multivariateGaussian (m a b) N).real
        {z | d₂ a z ≠ b} ∂ν ∂μ) * Real.log (Fintype.card B) := by
  let κ₁ := gaussianMarginalCodebookKernel ν m N
  have hf₁ := fano_uniform_joint_log (μ ⊗ₘ (η₁ ∘ₖ κ₁)) hd₁
    (fun a ↦ by simpa only [Measure.fst_compProd] using hμ a)
  have hi₁ : (mutualInfo (μ ⊗ₘ (η₁ ∘ₖ κ₁))).toReal ≤
      (mutualInfo (μ ⊗ₘ κ₁)).toReal :=
    ENNReal.toReal_mono
      (mutualInfo_ne_top_of_uniform (μ ⊗ₘ κ₁)
        (fun a ↦ by simpa only [Measure.fst_compProd] using hμ a))
      (mutualInfo_kernel_comp_le μ κ₁ η₁)
  rw [decodingError_postprocess_gaussianMarginalCodebookKernel μ ν m N η₁ d₁ hd₁] at hf₁
  rw [mutualInfo_gaussianMarginalCodebookKernel μ ν m N hN] at hi₁
  have hf₂ (a : A) :
      Real.log (Fintype.card B) ≤
        entropyWith (gaussianCodebookKernel (m a) N ∘ₘ ν) volume -
          entropyWith (multivariateGaussian 0 N) volume + Real.log 2 +
        (∫ b, (η₂ a ∘ₘ multivariateGaussian (m a b) N).real
          {z | d₂ a z ≠ b} ∂ν) * Real.log (Fintype.card B) := by
    let κ₂ := gaussianCodebookKernel (m a) N
    have hf := fano_uniform_joint_log (ν ⊗ₘ (η₂ a ∘ₖ κ₂)) (hd₂ a)
      (fun b ↦ by simpa only [Measure.fst_compProd] using hν b)
    have hi : (mutualInfo (ν ⊗ₘ (η₂ a ∘ₖ κ₂))).toReal ≤
        (mutualInfo (ν ⊗ₘ κ₂)).toReal :=
      ENNReal.toReal_mono
        (mutualInfo_ne_top_of_uniform (ν ⊗ₘ κ₂)
          (fun b ↦ by simpa only [Measure.fst_compProd] using hν b))
        (mutualInfo_kernel_comp_le ν κ₂ (η₂ a))
    rw [mutualInfo_gaussianMixture_eq_entropy_sub ν κ₂ (m a) N hN (fun _ ↦ rfl)] at hi
    have he : decodingError (ν ⊗ₘ (η₂ a ∘ₖ κ₂)) (d₂ a) =
        ∫ b, (η₂ a ∘ₘ multivariateGaussian (m a b) N).real
          {z | d₂ a z ≠ b} ∂ν := by
      have hs : MeasurableSet {p : B × Z | d₂ a p.2 ≠ p.1} :=
        (measurableSet_eq_fun ((hd₂ a).comp measurable_snd) measurable_fst).compl
      unfold decodingError
      rw [real_compProd_finite ν _ _ hs]
      rfl
    rw [he] at hf
    linarith
  have hsum := integral_mono (μ := μ) (integrable_const (Real.log (Fintype.card B)))
    Integrable.of_finite hf₂
  simp only [integral_const, probReal_univ, one_smul,
    integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite, integral_mul_const] at hsum
  linarith

/-- A fixed Gaussian reference turns the two-message converse into an energy bound. -/
theorem twoUser_gaussian_fano_reference
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (m : A → B → EuclideanSpace ℝ ι) (N T : Matrix ι ι ℝ)
    (hN : N.PosDef) (hT : T.PosDef)
    (η₁ : Kernel (EuclideanSpace ℝ ι) Y) [IsMarkovKernel η₁]
    (η₂ : A → Kernel (EuclideanSpace ℝ ι) Z) [∀ a, IsMarkovKernel (η₂ a)]
    (d₁ : Y → A) (hd₁ : Measurable d₁)
    (d₂ : A → Z → B) (hd₂ : ∀ a, Measurable (d₂ a))
    (hμ : ∀ a, μ {a} = (Fintype.card A : ℝ≥0∞)⁻¹)
    (hν : ∀ b, ν {b} = (Fintype.card B : ℝ≥0∞)⁻¹) :
    Real.log (Fintype.card A) + Real.log (Fintype.card B) ≤
      (Real.log T.det - Real.log N.det) / 2 +
      (trace (T⁻¹ * N) + (∫ p : A × B,
        m p.1 p.2 ⬝ᵥ T⁻¹ *ᵥ m p.1 p.2 ∂μ.prod ν) - Fintype.card ι) / 2 +
      2 * Real.log 2 +
      (∫ a, ∫ b, (η₁ ∘ₘ multivariateGaussian (m a b) N).real
        {y | d₁ y ≠ a} ∂ν ∂μ) * Real.log (Fintype.card A) +
      (∫ a, ∫ b, (η₂ a ∘ₘ multivariateGaussian (m a b) N).real
        {z | d₂ a z ≠ b} ∂ν ∂μ) * Real.log (Fintype.card B) := by
  have hf := twoUser_gaussian_fano μ ν m N hN η₁ η₂ d₁ hd₁ d₂ hd₂ hμ hν
  have he := entropyWith_gaussianCodebook_le_reference (μ.prod ν)
    (fun p : A × B ↦ m p.1 p.2) N T hN hT
  rw [entropyWith_multivariateGaussian 0 N hN] at hf
  rw [entropyWith_multivariateGaussian 0 T hT] at he
  linarith

/-- Integrate a pointwise code bound over the channel state. No state entropy is needed. -/
theorem integrate_fano_energy {S : Type*} [MeasurableSpace S]
    (σ : Measure S) [IsProbabilityMeasure σ]
    {L₁ L₂ C : ℝ} {energy error₁ error₂ : S → ℝ}
    (henergy : Integrable energy σ) (herr₁ : Integrable error₁ σ)
    (herr₂ : Integrable error₂ σ)
    (hpointwise : ∀ᵐ s ∂σ,
      L₁ + L₂ ≤ C + energy s + error₁ s * L₁ + error₂ s * L₂) :
    L₁ + L₂ ≤ C + (∫ s, energy s ∂σ) +
      (∫ s, error₁ s ∂σ) * L₁ + (∫ s, error₂ s ∂σ) * L₂ := by
  have h := integral_mono_ae (integrable_const (L₁ + L₂))
    (((integrable_const C).add henergy).add (herr₁.mul_const L₁) |>.add
      (herr₂.mul_const L₂)) hpointwise
  change (∫ _ : S, L₁ + L₂ ∂σ) ≤
    ∫ s, C + energy s + error₁ s * L₁ + error₂ s * L₂ ∂σ at h
  rw [integral_add (f := fun s ↦ C + energy s + error₁ s * L₁)
      (g := fun s ↦ error₂ s * L₂) (((integrable_const C).add henergy).add
      (herr₁.mul_const L₁)) (herr₂.mul_const L₂),
    integral_add (f := fun s ↦ C + energy s) (g := fun s ↦ error₁ s * L₁)
      ((integrable_const C).add henergy) (herr₁.mul_const L₁),
    integral_add (f := fun _ ↦ C) (g := energy) (integrable_const C) henergy] at h
  simpa only [integral_const, probReal_univ, one_smul, integral_mul_const] using h

end CapacityAtlas.Gaussian.Interference
