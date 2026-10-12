/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.StateInformation
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Postprocess

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal

namespace CapacityAtlas.Gaussian.Interference

open MeasureInformation

variable {A B Y Z ι : Type*}
  [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
  [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSingletonClass A] [MeasurableSingletonClass B]
  [MeasurableSpace Y] [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]

theorem twoUser_gaussian_fano_isotropic
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (m : A → B → EuclideanSpace ℝ ι) {e t : ℝ} (he : 0 < e) (ht : 0 < t)
    (η₁ : Kernel (EuclideanSpace ℝ ι) Y) [IsMarkovKernel η₁]
    (η₂ : A → Kernel (EuclideanSpace ℝ ι) Z) [∀ a, IsMarkovKernel (η₂ a)]
    (d₁ : Y → A) (hd₁ : Measurable d₁)
    (d₂ : A → Z → B) (hd₂ : ∀ a, Measurable (d₂ a))
    (hμ : ∀ a, μ {a} = (Fintype.card A : ℝ≥0∞)⁻¹)
    (hν : ∀ b, ν {b} = (Fintype.card B : ℝ≥0∞)⁻¹) :
    Real.log (Fintype.card A) + Real.log (Fintype.card B) ≤
      (Fintype.card ι : ℝ) / 2 * Real.log (t / e) +
      ((Fintype.card ι : ℝ) * e + (∫ p : A × B, ‖m p.1 p.2‖ ^ 2 ∂μ.prod ν)) /
        (2 * t) - (Fintype.card ι : ℝ) / 2 + 2 * Real.log 2 +
      (∫ a, ∫ b, (η₁ ∘ₘ multivariateGaussian (m a b) (e • 1)).real
        {y | d₁ y ≠ a} ∂ν ∂μ) * Real.log (Fintype.card A) +
      (∫ a, ∫ b, (η₂ a ∘ₘ multivariateGaussian (m a b) (e • 1)).real
        {z | d₂ a z ≠ b} ∂ν ∂μ) * Real.log (Fintype.card B) := by
  have h := twoUser_gaussian_fano_reference μ ν m (e • 1) (t • 1)
    (PosDef.one.smul he) (PosDef.one.smul ht) η₁ η₂ d₁ hd₁ d₂ hd₂ hμ hν
  simp_rw [log_det_scalar_matrix, trace_inverse_scalar, scalar_inverse_quadratic] at h
  rw [integral_const_mul] at h
  convert h using 1
  rw [Real.log_div ht.ne' he.ne']
  field_simp
  ring

/-- Integrating the pair converse with a power-matched reference cancels the energy term. -/
theorem pair_bound_of_integrated_energy {S : Type*} [MeasurableSpace S]
    (σ : Measure S) [IsProbabilityMeasure σ]
    {n : ℕ} {e t L₁ L₂ ε : ℝ} (ht : 0 < t)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    {energy error₁ error₂ : S → ℝ}
    (henergy : Integrable energy σ) (herr₁ : Integrable error₁ σ)
    (herr₂ : Integrable error₂ σ)
    (hpower : (∫ s, energy s ∂σ) ≤ 2 * n * (t - e))
    (herror₁ : (∫ s, error₁ s ∂σ) ≤ ε) (herror₂ : (∫ s, error₂ s ∂σ) ≤ ε)
    (hpointwise : ∀ᵐ s ∂σ,
      L₁ + L₂ ≤ (n : ℝ) * Real.log (t / e) +
        ((2 * n : ℝ) * e + energy s) / (2 * t) - n + 2 * Real.log 2 +
        error₁ s * L₁ + error₂ s * L₂) :
    (1 - ε) * (L₁ + L₂) ≤ (n : ℝ) * Real.log (t / e) + 2 * Real.log 2 := by
  have hi : Integrable (fun s ↦ energy s / (2 * t)) σ := henergy.div_const _
  have hp : ∀ᵐ s ∂σ,
      L₁ + L₂ ≤ ((n : ℝ) * Real.log (t / e) + (2 * n : ℝ) * e / (2 * t) - n +
        2 * Real.log 2) + energy s / (2 * t) + error₁ s * L₁ + error₂ s * L₂ := by
    filter_upwards [hpointwise] with s hs
    convert hs using 1
    ring
  have hf := integrate_fano_energy σ hi herr₁ herr₂ hp
  rw [integral_div] at hf
  have hec : (2 * n : ℝ) * e / (2 * t) - n +
      (∫ s, energy s ∂σ) / (2 * t) ≤ 0 := by
    have hh := (div_le_div_of_nonneg_right hpower (by positivity : 0 ≤ 2 * t))
    have hid : (2 * n : ℝ) * e / (2 * t) - n + 2 * n * (t - e) / (2 * t) = 0 := by
      field_simp
      ring
    linarith
  have her₁ := mul_le_mul_of_nonneg_right herror₁ hL₁
  have her₂ := mul_le_mul_of_nonneg_right herror₂ hL₂
  nlinarith

end CapacityAtlas.Gaussian.Interference
