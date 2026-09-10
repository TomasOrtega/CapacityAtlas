/-
Adapted from the PFR contributors' code, licensed under Apache-2.0.
See LICENSES/PFR-Apache-2.0.txt.
Sources at https://github.com/teorth/pfr/tree/85d5879ae144170098815201491639f6e7d3c352:
PFR/Mathlib/MeasureTheory/Measure/Prod.lean
PFR/Mathlib/MeasureTheory/Measure/Real.lean
Adaptations: kept needed lemmas and reused mathlib for coordinate exchange.
-/

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real

open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- The law of a pair with its coordinates exchanged. -/
lemma map_prod_comap_swap {X : Ω → α} {Z : Ω → β}
    (hX : Measurable X) (hZ : Measurable Z) (μ : Measure Ω) :
    (μ.map (fun ω ↦ (X ω, Z ω))).comap Prod.swap = μ.map (fun ω ↦ (Z ω, X ω)) := by
  rw [Measure.comap_swap, Measure.map_map measurable_swap (hX.prodMk hZ)]
  rfl

lemma ennreal_smul_real_apply (c : ℝ≥0∞) (μ : Measure Ω) (s : Set Ω) :
    (c • μ).real s = c.toReal • μ.real s := by simp

end MeasureTheory.Measure
