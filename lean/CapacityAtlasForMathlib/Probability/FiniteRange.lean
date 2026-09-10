/-
Adapted from selected declarations by the PFR contributors; imports and API subset changed.
Licensed under Apache-2.0; see LICENSES/PFR-Apache-2.0.txt.
Source: https://github.com/teorth/pfr/blob/85d5879ae144170098815201491639f6e7d3c352/PFR/ForMathlib/FiniteRange/Defs.lean
-/

import Mathlib.MeasureTheory.Measure.Map

/-- The property of having a finite range. -/
class FiniteRange {Ω G : Type*} (X : Ω → G) : Prop where
  finite : (Set.range X).Finite

/-- Fintype structure on the range of a finite range map. -/
noncomputable abbrev FiniteRange.fintype {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Fintype (Set.range X) := hX.finite.fintype

/-- The range of a finite range map, as a finset. -/
noncomputable def FiniteRange.toFinset {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] : Finset G :=
  @Set.toFinset _ _ hX.fintype

/-- If the codomain of X is finite, then X has finite range. -/
instance {Ω G : Type*} (X : Ω → G) [Finite G] : FiniteRange X where
  finite := Set.toFinite (Set.range X)

lemma FiniteRange.range {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Set.range X = FiniteRange.toFinset X := by simp [FiniteRange.toFinset]

@[simp]
lemma FiniteRange.mem_iff {Ω G : Type*} (X : Ω → G) [FiniteRange X] (x : G) :
    x ∈ FiniteRange.toFinset X ↔ ∃ ω, X ω = x := by
  simp_rw [← Finset.mem_coe, ← FiniteRange.range X, Set.mem_range]

/-- If X has finite range, then any function of X has finite range. -/
instance {Ω G H : Type*} (X : Ω → G) (f : G → H) [hX : FiniteRange X] : FiniteRange (f ∘ X) where
  finite := (Set.range_comp f X) ▸ Set.Finite.image f hX.finite

/-- If X, Y have finite range, then so does their pair. -/
instance {Ω G H : Type*} (X : Ω → G) (Y : Ω → H) [hX : FiniteRange X] [hY : FiniteRange Y] :
    FiniteRange fun ω ↦ (X ω, Y ω) where
  finite := (hX.finite.prod hY.finite).subset (Set.range_pair_subset ..)

open MeasureTheory

lemma FiniteRange.null_of_compl {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) [FiniteRange X] :
    (μ.map X) (FiniteRange.toFinset X : Set G)ᶜ = 0 := by
  by_cases hX : AEMeasurable X μ
  · rw [Measure.map_apply₀ hX (by measurability)]
    convert measure_empty (μ := μ)
    ext ω
    simp
  · simp [hX]
