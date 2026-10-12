/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]

def spliceProduct (p : ι → Prop) [DecidablePred p] (x y : ∀ i, α i) : ∀ i, α i :=
  fun i ↦ if p i then x i else y i

omit [Fintype ι] in
@[fun_prop] theorem measurable_spliceProduct (p : ι → Prop) [DecidablePred p] :
    Measurable (fun z : (∀ i, α i) × (∀ i, α i) ↦ spliceProduct p z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : p i <;> simp only [spliceProduct, hi, ↓reduceIte] <;> fun_prop

theorem measurePreserving_spliceProduct (μ : (i : ι) → Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (fun z : (∀ i, α i) × (∀ i, α i) ↦ spliceProduct p z.1 z.2)
      ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := by
  refine ⟨measurable_spliceProduct p, (Measure.pi_eq (fun s hs ↦ ?_)).symm⟩
  have he : (fun z : (∀ i, α i) × (∀ i, α i) ↦ spliceProduct p z.1 z.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi fun i ↦ if p i then s i else Set.univ) ×ˢ
        (Set.univ.pi fun i ↦ if p i then Set.univ else s i) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, spliceProduct]
    constructor
    · intro hz
      constructor <;> intro i <;> specialize hz i <;> split_ifs at * <;>
        first | exact hz | exact Set.mem_univ _
    · rintro ⟨h₁, h₂⟩ i
      specialize h₁ i
      specialize h₂ i
      split_ifs at * <;> assumption
  rw [Measure.map_apply (measurable_spliceProduct p) (MeasurableSet.univ_pi hs), he,
    Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : p i <;> simp [hi]

variable [DecidableEq ι]

theorem measurePreserving_updateProduct (μ : (i : ι) → Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun z : α i × (∀ j, α j) ↦ Function.update z.2 i z.1)
      ((μ i).prod (Measure.pi μ)) (Measure.pi μ) := by
  have hproj : ((Measure.pi μ).prod (Measure.pi μ)).map
      (fun z : (∀ j, α j) × (∀ j, α j) ↦ (z.1 i, z.2)) = (μ i).prod (Measure.pi μ) := by
    have he := Measure.map_prod_map (Measure.pi μ) (Measure.pi μ) (measurable_pi_apply i) measurable_id
    rw [(measurePreserving_eval μ i).map_eq, Measure.map_id] at he
    exact he.symm
  refine ⟨by fun_prop, ?_⟩
  rw [← hproj, Measure.map_map (by fun_prop) (by fun_prop)]
  convert (measurePreserving_spliceProduct μ (fun j ↦ j = i)).map_eq using 1
  congr 1
  ext z j
  by_cases hj : j = i
  · subst j
    simp [spliceProduct]
  · simp [spliceProduct, hj]

theorem integral_updateProduct [∀ i, Fintype (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (f : (∀ j, α j) → ℝ) :
    (∫ a, ∫ x, f (Function.update x i a) ∂Measure.pi μ ∂μ i) = ∫ x, f x ∂Measure.pi μ := by
  rw [← integral_prod (fun z : α i × (∀ j, α j) ↦ f (Function.update z.2 i z.1))
    Integrable.of_finite]
  have h := (measurePreserving_updateProduct μ i).map_eq
  conv_rhs => rw [← h]
  rw [integral_map (by fun_prop) (measurable_of_countable _).aestronglyMeasurable]

omit [DecidableEq ι] in
theorem integral_spliceProduct [∀ i, Fintype (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] (f : (∀ j, α j) → ℝ) :
    (∫ x, ∫ y, f (spliceProduct p x y) ∂Measure.pi μ ∂Measure.pi μ) = ∫ x, f x ∂Measure.pi μ := by
  rw [← integral_prod (fun z : (∀ i, α i) × (∀ i, α i) ↦ f (spliceProduct p z.1 z.2))
    Integrable.of_finite]
  have h := (measurePreserving_spliceProduct μ p).map_eq
  conv_rhs => rw [← h]
  rw [integral_map (measurable_spliceProduct p).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]

end MeasureTheory
