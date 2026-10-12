/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Packing

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.MeasureBinning

open MeasureChannel

variable {S U Y M L : Type*} [MeasurableSpace S] [MeasurableSpace U] [MeasurableSpace Y]
  [Fintype M] [Fintype L]

noncomputable def binningPointwiseBound (ρ : Kernel ((L → U) × S) Y) (δ : ℝ≥0∞)
    (B : Set (S × U)) (A : Set (U × Y)) (book : M → L → U) (m : M) (s : S) : ℝ≥0∞ :=
  (if coveringFailure B (book m) s then 1 else 0) + δ +
    ∑ j ∈ Finset.univ.erase m, ∑ l : L, ρ (book m, s) {y | (book j l, y) ∈ A}

noncomputable def binningBound (ρ : Kernel ((L → U) × S) Y) (σ : Measure S) (δ : ℝ≥0∞)
    (B : Set (S × U)) (A : Set (U × Y)) (book : M → L → U) : ℝ≥0∞ :=
  (Fintype.card M : ℝ≥0∞)⁻¹ * ∑ m, ∫⁻ s, binningPointwiseBound ρ δ B A book m s ∂σ

omit [Fintype M] [Fintype L] in
theorem measurable_competingAcceptance (ρ : Kernel ((L → U) × S) Y) [IsSFiniteKernel ρ]
    {A : Set (U × Y)} (hA : MeasurableSet A) (m j : M) (l : L) :
    Measurable (fun p : (M → L → U) × S ↦ ρ (p.1 m, p.2) {y | (p.1 j l, y) ∈ A}) := by
  let ρ' := ρ.comap (fun p : (M → L → U) × S ↦ (p.1 m, p.2))
    (((measurable_pi_apply m).comp measurable_fst).prodMk measurable_snd)
  have hmap : Measurable (fun p : ((M → L → U) × S) × Y ↦ (p.1.1 j l, p.2)) :=
    ((measurable_pi_apply l).comp
      ((measurable_pi_apply j).comp measurable_fst.fst)).prodMk measurable_snd
  exact Kernel.measurable_kernel_prodMk_left (κ := ρ')
    (hA.preimage hmap)

theorem measurable_binningPointwiseBound (ρ : Kernel ((L → U) × S) Y) [IsSFiniteKernel ρ]
    (δ : ℝ≥0∞) {B : Set (S × U)} (hB : MeasurableSet B)
    {A : Set (U × Y)} (hA : MeasurableSet A) (m : M) :
    Measurable (fun p : (M → L → U) × S ↦ binningPointwiseBound ρ δ B A p.1 m p.2) := by
  have hproj : Measurable (fun p : (M → L → U) × S ↦ (p.1 m, p.2)) :=
    ((measurable_pi_apply m).comp measurable_fst).prodMk measurable_snd
  have hfail : MeasurableSet {p : (M → L → U) × S | coveringFailure B (p.1 m) p.2} :=
    (measurableSet_coveringFailure hB).preimage hproj
  exact ((Measurable.ite hfail measurable_const measurable_const).add measurable_const).add
    (Finset.measurable_sum _ (fun j _ ↦ Finset.measurable_sum _
      (fun l _ ↦ measurable_competingAcceptance ρ hA m j l)))

theorem measurable_binningBound (ρ : Kernel ((L → U) × S) Y) [IsSFiniteKernel ρ]
    (σ : Measure S) [SFinite σ] (δ : ℝ≥0∞) {B : Set (S × U)} (hB : MeasurableSet B)
    {A : Set (U × Y)} (hA : MeasurableSet A) :
    Measurable (binningBound (M := M) ρ σ δ B A) :=
  measurable_const.mul (Finset.measurable_sum _ (fun m _ ↦
    (measurable_binningPointwiseBound ρ δ hB hA m).lintegral_prod_right'))

theorem lintegral_binningPointwiseBound_le
    (μ : Measure U) [IsProbabilityMeasure μ]
    (ρ : Kernel ((L → U) × S) Y) [IsMarkovKernel ρ]
    (δ : ℝ≥0∞) {B : Set (S × U)} (hB : MeasurableSet B)
    {A : Set (U × Y)} (hA : MeasurableSet A) {c : ℝ≥0∞}
    (hAuniform : ∀ y, μ {u | (u, y) ∈ A} ≤ c) (m : M) (s : S) :
    (∫⁻ book : M → L → U, binningPointwiseBound ρ δ B A book m s
      ∂Measure.pi (fun _ : M ↦ Measure.pi (fun _ : L ↦ μ))) ≤
      (Measure.pi (fun _ : L ↦ μ)) {row | coveringFailure B row s} + δ +
        (Fintype.card M - 1 : ℕ) * Fintype.card L * c := by
  let π := Measure.pi (fun _ : L ↦ μ)
  have hfail : MeasurableSet {row : L → U | coveringFailure B row s} :=
    (measurableSet_coveringFailure hB).preimage (measurable_id.prodMk measurable_const)
  have hind : Measurable (fun row : L → U ↦ if coveringFailure B row s then
      (1 : ℝ≥0∞) else 0) := Measurable.ite hfail measurable_const measurable_const
  have hindBook : Measurable (fun book : M → L → U ↦
      if coveringFailure B (book m) s then (1 : ℝ≥0∞) else 0) :=
    hind.comp (measurable_pi_apply m)
  have hcomp (j : M) (l : L) : Measurable (fun book : M → L → U ↦
      ρ (book m, s) {y | (book j l, y) ∈ A}) :=
    (measurable_competingAcceptance ρ hA m j l).comp (measurable_id.prodMk measurable_const)
  have hindInt : (∫⁻ book : M → L → U,
      (if coveringFailure B (book m) s then (1 : ℝ≥0∞) else 0)
      ∂Measure.pi (fun _ : M ↦ π)) = π {row | coveringFailure B row s} := by
    rw [(measurePreserving_eval (fun _ : M ↦ π) m).lintegral_comp hind]
    exact lintegral_indicator_one hfail
  have hindAdd : Measurable (fun book : M → L → U ↦
      (if coveringFailure B (book m) s then (1 : ℝ≥0∞) else 0) + δ) :=
    hindBook.add measurable_const
  unfold binningPointwiseBound
  rw [lintegral_add_left hindAdd, lintegral_add_left hindBook,
    lintegral_finsetSum _ (fun j _ ↦ Finset.measurable_sum _ (fun l _ ↦ hcomp j l))]
  simp_rw [lintegral_finsetSum _ (fun l _ ↦ hcomp _ l)]
  rw [hindInt]
  simp only [lintegral_const, measure_univ, mul_one]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase m, ∑ _l : L, c := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro l _
      let ρs := ρ.comap (fun row : L → U ↦ (row, s)) (measurable_id.prodMk measurable_const)
      exact lintegral_independent_bin_falseAcceptance μ ρs hA hAuniform
        (Finset.mem_erase.mp hj).1.symm l
    _ = _ := by simp [Finset.card_erase_of_mem, mul_assoc]

theorem lintegral_binningBound_le [Nonempty M]
    (σ : Measure S) [IsProbabilityMeasure σ] (μ : Measure U) [IsProbabilityMeasure μ]
    (ρ : Kernel ((L → U) × S) Y) [IsMarkovKernel ρ]
    (δ : ℝ≥0∞) {B : Set (S × U)} (hB : MeasurableSet B)
    {A : Set (U × Y)} (hA : MeasurableSet A) {c : ℝ≥0∞}
    (hAuniform : ∀ y, μ {u | (u, y) ∈ A} ≤ c) :
    (∫⁻ book : M → L → U, binningBound ρ σ δ B A book
      ∂Measure.pi (fun _ : M ↦ Measure.pi (fun _ : L ↦ μ))) ≤
      (∫⁻ s, (Measure.pi (fun _ : L ↦ μ)) {row | coveringFailure B row s} ∂σ) + δ +
        (Fintype.card M - 1 : ℕ) * Fintype.card L * c := by
  have hcover : Measurable (fun s ↦
      (Measure.pi (fun _ : L ↦ μ)) {row | coveringFailure B row s}) :=
    measurable_measure_prodMk_right (measurableSet_coveringFailure hB)
  have hcoverAdd : Measurable (fun s ↦
      (Measure.pi (fun _ : L ↦ μ)) {row | coveringFailure B row s} + δ) :=
    hcover.add measurable_const
  have hterm (m : M) : Measurable (fun book : M → L → U ↦
      ∫⁻ s, binningPointwiseBound ρ δ B A book m s ∂σ) :=
    (measurable_binningPointwiseBound ρ δ hB hA m).lintegral_prod_right'
  have htermBound (m : M) :
      (∫⁻ book : M → L → U, ∫⁻ s, binningPointwiseBound ρ δ B A book m s ∂σ
        ∂Measure.pi (fun _ : M ↦ Measure.pi (fun _ : L ↦ μ))) ≤
      (∫⁻ s, (Measure.pi (fun _ : L ↦ μ)) {row | coveringFailure B row s} ∂σ) + δ +
        (Fintype.card M - 1 : ℕ) * Fintype.card L * c := by
    rw [lintegral_lintegral_swap (measurable_binningPointwiseBound ρ δ hB hA m).aemeasurable]
    calc
      _ ≤ ∫⁻ s, (Measure.pi (fun _ : L ↦ μ)) {row | coveringFailure B row s} + δ +
          (Fintype.card M - 1 : ℕ) * Fintype.card L * c ∂σ :=
        lintegral_mono (lintegral_binningPointwiseBound_le μ ρ δ hB hA hAuniform m)
      _ = _ := by rw [lintegral_add_left hcoverAdd, lintegral_add_left hcover]; simp
  unfold binningBound
  rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun m _ ↦ hterm m)),
    lintegral_finsetSum _ (fun m _ ↦ hterm m)]
  calc
    _ ≤ (Fintype.card M : ℝ≥0∞)⁻¹ * ∑ _m : M,
        ((∫⁻ s, (Measure.pi (fun _ : L ↦ μ)) {row | coveringFailure B row s} ∂σ) + δ +
          (Fintype.card M - 1 : ℕ) * Fintype.card L * c) := by
      gcongr with m
      exact htermBound m
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact ENNReal.inv_mul_cancel_left (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)

end CapacityAtlas.MeasureBinning
