/-
Adapted from the PFR contributors' code, licensed under Apache-2.0.
See LICENSES/PFR-Apache-2.0.txt.
Sources at https://github.com/teorth/pfr/tree/85d5879ae144170098815201491639f6e7d3c352:
PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean
PFR/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean
Adaptations: combined only the integral lemmas needed by entropy.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

lemma lintegral_eq_setLIntegral (hs : μ sᶜ = 0) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ x in s, f x ∂μ := by
  rw [← setLIntegral_univ, ← setLIntegral_congr]; rwa [ae_eq_univ]

variable [MeasurableSingletonClass α]

lemma setLIntegral_eq_sum (μ : Measure α) (s : Finset α) (f : α → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ = ∑ x ∈ s, μ {x} * f x := by
  simp_rw [mul_comm, lintegral_finset]

end MeasureTheory
