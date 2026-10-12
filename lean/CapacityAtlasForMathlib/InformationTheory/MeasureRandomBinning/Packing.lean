/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Code

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.MeasureBinning

open MeasureChannel

variable {U Y M L : Type*} [MeasurableSpace U] [MeasurableSpace Y]

theorem reverseLikelihood_threshold_mass_le
    (η : Kernel Y U) [IsMarkovKernel η] (μ : Measure U)
    (f : U × Y → ℝ≥0∞) (hf : Measurable f)
    (hrow : ∀ y, η y = μ.withDensity (fun u ↦ f (u, y)))
    {T : ℝ≥0∞} (hT₀ : T ≠ 0) (hTtop : T ≠ ∞) (y : Y) :
    μ {u | T < f (u, y)} ≤ T⁻¹ := by
  have hnorm : (∫⁻ u, f (u, y) ∂μ) = 1 := by
    have h := congrArg (fun ν : Measure U ↦ ν Set.univ) (hrow y)
    simpa [withDensity_apply] using h.symm
  have hmarkov := meas_ge_le_lintegral_div (μ := μ) (f := fun u ↦ f (u, y))
    (hf.comp (measurable_id.prodMk measurable_const)).aemeasurable hT₀ hTtop
  have hmono : μ {u | T < f (u, y)} ≤ μ {u | T ≤ f (u, y)} := by
    apply measure_mono
    intro u hu
    exact (show T < f (u, y) from hu).le
  exact hmono.trans (hmarkov.trans_eq (by rw [hnorm, one_div]))

theorem lintegral_acceptance_le (μ : Measure U) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] {A : Set (U × Y)} (hA : MeasurableSet A)
    {c : ℝ≥0∞} (hAuniform : ∀ y, μ {u | (u, y) ∈ A} ≤ c) :
    (∫⁻ u, ν {y | (u, y) ∈ A} ∂μ) ≤ c := by
  calc
    _ = μ.prod ν A := (Measure.prod_apply hA).symm
    _ = ∫⁻ y, μ {u | (u, y) ∈ A} ∂ν := Measure.prod_apply_symm hA
    _ ≤ ∫⁻ _y : Y, c ∂ν := lintegral_mono hAuniform
    _ = c := by simp

theorem lintegral_independent_bin_falseAcceptance [Fintype M] [Fintype L]
    (μ : Measure U) [IsProbabilityMeasure μ]
    (ρ : Kernel (L → U) Y) [IsMarkovKernel ρ]
    {A : Set (U × Y)} (hA : MeasurableSet A) {c : ℝ≥0∞}
    (hAuniform : ∀ y, μ {u | (u, y) ∈ A} ≤ c)
    {m j : M} (hmj : m ≠ j) (l : L) :
    (∫⁻ book : M → L → U, ρ (book m) {y | (book j l, y) ∈ A}
      ∂Measure.pi (fun _ : M ↦ Measure.pi (fun _ : L ↦ μ))) ≤ c := by
  let A' : Set ((L → U) × Y) := {p | (p.1 l, p.2) ∈ A}
  have hA' : MeasurableSet A' :=
    hA.preimage (((measurable_pi_apply l).comp measurable_fst).prodMk measurable_snd)
  change (∫⁻ book : M → L → U, falseAcceptance ρ A' (book m) (book j)
    ∂Measure.pi (fun _ : M ↦ Measure.pi (fun _ : L ↦ μ))) ≤ c
  rw [lintegral_codebook_falseAcceptance ρ A' hA' _ hmj]
  apply le_trans (lintegral_mono (fun row ↦ ?_)) (by simp : (∫⁻ _ : L → U, c
    ∂Measure.pi (fun _ : L ↦ μ)) ≤ c)
  change (∫⁻ row' : L → U, ρ row {y | (row' l, y) ∈ A}
    ∂Measure.pi (fun _ : L ↦ μ)) ≤ c
  have hsection : Measurable (fun u ↦ ρ row {y | (u, y) ∈ A}) :=
    measurable_measure_prodMk_left hA
  rw [(measurePreserving_eval (fun _ : L ↦ μ) l).lintegral_comp hsection]
  exact lintegral_acceptance_le μ (ρ row) hA hAuniform

end CapacityAtlas.MeasureBinning
