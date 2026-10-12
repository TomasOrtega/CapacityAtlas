/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Alignment
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.PolynomialMeasure
import Mathlib.Topology.Instances.Matrix

open scoped BigOperators Matrix
open MeasureTheory

namespace CapacityAtlas.Gaussian.Interference

variable {U : Type*} [Fintype U] [DecidableEq U] {n : ℕ}

theorem continuous_beam (a : Box U n) : Continuous (fun h : U × U → ℂ ↦ beam h a) := by
  unfold beam
  fun_prop

theorem continuous_decodingMatrix (i : U) :
    Continuous (fun h : FadingBlock U n ℂ ↦ decodingMatrix h i) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro c
  cases c with
  | inl a =>
    change Continuous (fun h : FadingBlock U n ℂ ↦ h r (i, i) * beam (h r) a)
    unfold beam
    fun_prop
  | inr a =>
    change Continuous (fun h : FadingBlock U n ℂ ↦ beam (h r) a)
    exact (continuous_beam a).comp (continuous_apply r)

noncomputable local instance : MeasurableSpace (Matrix (Columns U n) (Columns U n) ℂ) :=
  inferInstanceAs (MeasurableSpace (Columns U n → Columns U n → ℂ))

local instance : BorelSpace (Matrix (Columns U n) (Columns U n) ℂ) :=
  inferInstanceAs (BorelSpace (Columns U n → Columns U n → ℂ))

theorem measurable_inverse_decodingMatrix (i : U) :
    Measurable (fun h : FadingBlock U n ℂ ↦ (decodingMatrix h i)⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact (continuous_decodingMatrix i).matrix_det.measurable.inv.smul
    (continuous_decodingMatrix i).matrix_adjugate.measurable

theorem measurable_decoder_apply (i : U) (a : Box U n) :
    Measurable (fun hy : FadingBlock U n ℂ × (Columns U n → ℂ) ↦
      decoder hy.1 i hy.2 a) := by
  change Measurable (fun hy : FadingBlock U n ℂ × (Columns U n → ℂ) ↦
    ∑ r, ((decodingMatrix hy.1 i)⁻¹) (Sum.inl a) r * hy.2 r)
  apply Finset.measurable_sum
  intro r _
  exact ((measurable_pi_apply r).comp
    ((measurable_pi_apply (Sum.inl a)).comp
      ((measurable_inverse_decodingMatrix i).comp measurable_fst))).mul
    ((measurable_pi_apply r).comp measurable_snd)

/-- All receivers' desired and interference columns are independent almost surely. -/
theorem ae_decodingMatrix_nonsingular
    (μ : Columns U n × (U × U) → Measure ℂ)
    [∀ p, IsProbabilityMeasure (μ p)] [∀ p, NullSingletonClass (μ p)] :
    ∀ᵐ h ∂Measure.pi μ, ∀ i : U,
      (decodingMatrix (fun r p ↦ h (r, p)) i).det ≠ 0 := by
  rw [ae_all_iff]
  intro i
  filter_upwards [ae_eval_ne_zero (decodingPolynomial (n := n) i)
    (decodingPolynomial_ne_zero i) μ] with h hh
  exact (eval_decodingPolynomial (fun r p ↦ h (r, p)) i) ▸ hh

theorem ae_decoder_received_add_noise
    (μ : Columns U n × (U × U) → Measure ℂ)
    [∀ p, IsProbabilityMeasure (μ p)] [∀ p, NullSingletonClass (μ p)] :
    ∀ᵐ h ∂Measure.pi μ, ∀ (i : U) (x : U → Box U n → ℂ) (z : Columns U n → ℂ),
      decoder (fun r p ↦ h (r, p)) i (received (fun r p ↦ h (r, p)) x i + z) =
        x i + decoder (fun r p ↦ h (r, p)) i z := by
  filter_upwards [ae_decodingMatrix_nonsingular μ] with h hh
  exact fun i x z ↦ decoder_received_add_noise _ i (hh i) x z

end CapacityAtlas.Gaussian.Interference
