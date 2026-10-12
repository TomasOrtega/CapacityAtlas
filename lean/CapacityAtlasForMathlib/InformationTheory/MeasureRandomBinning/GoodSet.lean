/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.OneShot

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.MeasureBinning

variable {S U X Y M L : Type*} [MeasurableSpace S] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def conditionalMiss (κ : Kernel (S × X) Y) (input : S × U → X)
    (A : Set (U × Y)) (z : S × U) : ℝ≥0∞ :=
  κ (z.1, input z) {y | (z.2, y) ∉ A}

theorem measurable_conditionalMiss (κ : Kernel (S × X) Y) [IsSFiniteKernel κ]
    {input : S × U → X} (hinput : Measurable input)
    {A : Set (U × Y)} (hA : MeasurableSet A) : Measurable (conditionalMiss κ input A) := by
  let κ' := κ.comap (fun z : S × U ↦ (z.1, input z)) (measurable_fst.prodMk hinput)
  exact Kernel.measurable_kernel_prodMk_left (κ := κ')
    (hA.compl.preimage (measurable_fst.snd.prodMk measurable_snd))

def encoderAcceptance (κ : Kernel (S × X) Y) (input : S × U → X)
    (A : Set (U × Y)) (g : S × U → ℝ≥0∞) (T δ : ℝ≥0∞) (allowed : Set (S × X)) :
    Set (S × U) :=
  {z | g z ≤ T ∧ (z.1, input z) ∈ allowed ∧ conditionalMiss κ input A z ≤ δ}

theorem measurableSet_encoderAcceptance (κ : Kernel (S × X) Y) [IsSFiniteKernel κ]
    {input : S × U → X} (hinput : Measurable input)
    {A : Set (U × Y)} (hA : MeasurableSet A)
    {g : S × U → ℝ≥0∞} (hg : Measurable g) (T δ : ℝ≥0∞)
    {allowed : Set (S × X)} (hallowed : MeasurableSet allowed) :
    MeasurableSet (encoderAcceptance κ input A g T δ allowed) :=
  (measurableSet_le hg measurable_const).inter
    ((hallowed.preimage (measurable_fst.prodMk hinput)).inter
      (measurableSet_le (measurable_conditionalMiss κ hinput hA) measurable_const))

theorem measure_encoderAcceptance_compl_le
    (κ : Kernel (S × X) Y) [IsSFiniteKernel κ] (ν : Measure (S × U))
    {input : S × U → X} (hinput : Measurable input)
    {A : Set (U × Y)} (hA : MeasurableSet A) (g : S × U → ℝ≥0∞)
    (T : ℝ≥0∞) {δ : ℝ≥0∞} (hδ₀ : δ ≠ 0) (hδtop : δ ≠ ∞)
    (allowed : Set (S × X)) :
    ν (encoderAcceptance κ input A g T δ allowed)ᶜ ≤
      ν {z | T < g z} + ν {z | (z.1, input z) ∉ allowed} +
        (∫⁻ z, conditionalMiss κ input A z ∂ν) / δ := by
  have hsubset : (encoderAcceptance κ input A g T δ allowed)ᶜ ⊆
      ({z | T < g z} ∪ {z | (z.1, input z) ∉ allowed}) ∪
        {z | δ ≤ conditionalMiss κ input A z} := by
    intro z hz
    change ¬(g z ≤ T ∧ (z.1, input z) ∈ allowed ∧ conditionalMiss κ input A z ≤ δ) at hz
    by_cases hg : g z ≤ T
    · by_cases hc : (z.1, input z) ∈ allowed
      · exact Or.inr (le_of_lt (not_le.mp (fun hm ↦ hz ⟨hg, hc, hm⟩)))
      · exact Or.inl (Or.inr hc)
    · exact Or.inl (Or.inl (not_le.mp hg))
  apply (measure_mono hsubset).trans
  apply (measure_union_le _ _).trans
  exact add_le_add (measure_union_le _ _)
    (meas_ge_le_lintegral_div (measurable_conditionalMiss κ hinput hA).aemeasurable hδ₀ hδtop)

/-- The acceptance set is built from density, cost, and conditional missed-detection tests. -/
theorem exists_stateCode_error_le_likelihood_tails
    [MeasurableSpace M] [Fintype M] [Nonempty M] [Fintype L] [Nonempty L]
    (κ : Kernel (S × X) Y) [IsMarkovKernel κ]
    (σ : Measure S) [IsProbabilityMeasure σ]
    (η : Kernel S U) [IsMarkovKernel η] (μ : Measure U) [IsProbabilityMeasure μ]
    (g : S × U → ℝ≥0∞) (hg : Measurable g)
    (hη : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    (reverse : Kernel Y U) [IsMarkovKernel reverse]
    (f : U × Y → ℝ≥0∞) (hf : Measurable f)
    (hreverse : ∀ y, reverse y = μ.withDensity (fun u ↦ f (u, y)))
    {T : ℝ} (hT : 0 < T) {F δ : ℝ≥0∞}
    (hF₀ : F ≠ 0) (hFtop : F ≠ ∞) (hδ₀ : δ ≠ 0) (hδtop : δ ≠ ∞)
    (input : S × U → X) (hinput : Measurable input) (fallback : S → X)
    (hfallback : Measurable fallback) (allowed : Set (S × X))
    (hallowed : MeasurableSet allowed) (hfallback_mem : ∀ s, (s, fallback s) ∈ allowed) :
    ∃ code : StateCode S X Y M, (∀ m s, (s, code.encode m s) ∈ allowed) ∧
      stateAverageError κ σ code ≤
        2 * ((σ ⊗ₘ η) {z | ENNReal.ofReal T < g z} +
          (σ ⊗ₘ η) {z | (z.1, input z) ∉ allowed} +
          (∫⁻ z, conditionalMiss κ input {p | F < f p} z ∂(σ ⊗ₘ η)) / δ) +
          ENNReal.ofReal (Real.exp (-((Fintype.card L : ℝ) * ((1 / 2) / T)))) + δ +
          (Fintype.card M - 1 : ℕ) * Fintype.card L * F⁻¹ := by
  let A : Set (U × Y) := {p | F < f p}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf
  let B := encoderAcceptance κ input A g (ENNReal.ofReal T) δ allowed
  have hB : MeasurableSet B := measurableSet_encoderAcceptance κ hinput hA hg _ _ hallowed
  obtain ⟨code, hcode, herror⟩ := exists_stateCode_error_le (M := M) (L := L)
    κ σ η μ g hη B hB hT (fun _ hz ↦ hz.1) input hinput fallback hfallback A hA
    (fun _ hz ↦ hz.2.2)
    (reverseLikelihood_threshold_mass_le reverse μ f hf hreverse hF₀ hFtop)
    allowed (fun _ hz ↦ hz.2.1) hfallback_mem
  refine ⟨code, hcode, herror.trans ?_⟩
  gcongr
  exact measure_encoderAcceptance_compl_le κ (σ ⊗ₘ η) hinput hA g _ hδ₀ hδtop allowed

end CapacityAtlas.MeasureBinning
