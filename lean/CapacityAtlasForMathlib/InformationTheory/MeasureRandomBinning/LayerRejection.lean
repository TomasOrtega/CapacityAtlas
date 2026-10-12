/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Rejection

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace CapacityAtlas.MeasureBinning

variable {S U : Type*} [MeasurableSpace S] [MeasurableSpace U]

def seededAcceptanceSection (g : S × U → ℝ≥0∞) (B : Set (S × U)) (T : ℝ) :
    Set (S × (U × ℝ)) := {p | p.2 ∈ seededAcceptance (fun u ↦ g (p.1, u))
      {u | (p.1, u) ∈ B} T}

theorem measurableSet_seededAcceptanceSection {g : S × U → ℝ≥0∞} (hg : Measurable g)
    {B : Set (S × U)} (hB : MeasurableSet B) (T : ℝ) :
    MeasurableSet (seededAcceptanceSection g B T) :=
  (measurableSet_seededAcceptance hg hB T).preimage
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

def goodState (η : Kernel S U) (B : Set (S × U)) : Set S :=
  {s | ENNReal.ofReal (1 / 2 : ℝ) ≤ η s {u | (s, u) ∈ B}}

theorem measurableSet_goodState (η : Kernel S U) [IsSFiniteKernel η]
    {B : Set (S × U)} (hB : MeasurableSet B) : MeasurableSet (goodState η B) :=
  measurableSet_le measurable_const (Kernel.measurable_kernel_prodMk_left hB)

noncomputable def seededFirstHitKernel (μ : Measure U) [IsProbabilityMeasure μ]
    {g : S × U → ℝ≥0∞} (hg : Measurable g) {B : Set (S × U)}
    (hB : MeasurableSet B) (T : ℝ) (fallback : U × ℝ) (n : ℕ) : Kernel S U :=
  (firstHitKernel (μ.prod seedLaw) (measurableSet_seededAcceptanceSection hg hB T)
    fallback n).map Prod.fst

instance (μ : Measure U) [IsProbabilityMeasure μ]
    {g : S × U → ℝ≥0∞} (hg : Measurable g) {B : Set (S × U)}
    (hB : MeasurableSet B) (T : ℝ) (fallback : U × ℝ) (n : ℕ) :
    IsFiniteKernel (seededFirstHitKernel μ hg hB T fallback n) := by
  unfold seededFirstHitKernel
  infer_instance

theorem seededFirstHitKernel_apply (μ : Measure U) [IsProbabilityMeasure μ]
    {g : S × U → ℝ≥0∞} (hg : Measurable g) {B : Set (S × U)}
    (hB : MeasurableSet B) (T : ℝ) (fallback : U × ℝ) (n : ℕ) (s : S)
    {E : Set U} (hE : MeasurableSet E) :
    seededFirstHitKernel μ hg hB T fallback n s E =
      (Measure.pi (fun _ : Fin n ↦ μ.prod seedLaw))
        (firstHitEvent (seededAcceptance (fun u ↦ g (s, u)) {u | (s, u) ∈ B} T)
          (Prod.fst ⁻¹' E) fallback n) := by
  rw [seededFirstHitKernel, Kernel.map_apply' _ measurable_fst _ hE, firstHitKernel_apply]
  exact firstHitLaw_apply (μ.prod seedLaw)
    (measurableSet_seededAcceptance (hg.comp measurable_prodMk_left)
      (hB.preimage measurable_prodMk_left) T) (hE.preimage measurable_fst) fallback n

noncomputable def rejectionKernel (η : Kernel S U) [IsSFiniteKernel η]
    (μ : Measure U) [IsProbabilityMeasure μ]
    {g : S × U → ℝ≥0∞} (hg : Measurable g) {B : Set (S × U)}
    (hB : MeasurableSet B) (T : ℝ) (fallback : U × ℝ) (n : ℕ) : Kernel S U :=
  Kernel.piecewise (measurableSet_goodState η hB)
    (seededFirstHitKernel μ hg hB T fallback n) 0

instance (η : Kernel S U) [IsSFiniteKernel η] (μ : Measure U) [IsProbabilityMeasure μ]
    {g : S × U → ℝ≥0∞} (hg : Measurable g) {B : Set (S × U)}
    (hB : MeasurableSet B) (T : ℝ) (fallback : U × ℝ) (n : ℕ) :
    IsFiniteKernel (rejectionKernel η μ hg hB T fallback n) := by
  unfold rejectionKernel
  infer_instance

theorem rejectionKernel_le_two (η : Kernel S U) [IsSFiniteKernel η]
    (μ : Measure U) [IsProbabilityMeasure μ]
    {g : S × U → ℝ≥0∞} (hg : Measurable g)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    {B : Set (S × U)} (hB : MeasurableSet B) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ z ∈ B, g z ≤ ENNReal.ofReal T) (fallback : U × ℝ) (n : ℕ) (s : S) :
    rejectionKernel η μ hg hB T fallback n s ≤ (2 : ℝ≥0∞) • η s := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [rejectionKernel, Kernel.piecewise_apply']
  split_ifs with hs
  · rw [seededFirstHitKernel_apply μ hg hB T fallback n s hE, Measure.smul_apply,
      smul_eq_mul, hrow]
    apply measure_seededFirstHit_le_two μ (hg.comp measurable_prodMk_left)
      (hB.preimage measurable_prodMk_left) hE hT (fun u hu ↦ hcut (s, u) hu)
    simpa only [goodState, mem_setOf_eq, hrow, Function.comp_def, Set.preimage] using hs
  · simp

theorem rejectionKernel_univ_le_one (η : Kernel S U) [IsSFiniteKernel η]
    (μ : Measure U) [IsProbabilityMeasure μ]
    {g : S × U → ℝ≥0∞} (hg : Measurable g) {B : Set (S × U)}
    (hB : MeasurableSet B) (T : ℝ) (fallback : U × ℝ) (n : ℕ) (s : S) :
    rejectionKernel η μ hg hB T fallback n s univ ≤ 1 := by
  rw [rejectionKernel, Kernel.piecewise_apply']
  split_ifs
  · rw [seededFirstHitKernel_apply μ hg hB T fallback n s MeasurableSet.univ]
    exact prob_le_one
  · simp

noncomputable def rejectionFailure (η : Kernel S U) (μ : Measure U)
    (g : S × U → ℝ≥0∞) (B : Set (S × U)) (T : ℝ) (n : ℕ) (s : S) : ℝ≥0∞ :=
  if s ∈ goodState η B then
    (Measure.pi (fun _ : Fin n ↦ μ.prod seedLaw))
      {book | ¬hasHit (seededAcceptance (fun u ↦ g (s, u)) {u | (s, u) ∈ B} T) book}
  else 1

theorem measurable_rejectionFailure (η : Kernel S U) [IsSFiniteKernel η]
    (μ : Measure U) [IsProbabilityMeasure μ] {g : S × U → ℝ≥0∞} (hg : Measurable g)
    {B : Set (S × U)} (hB : MeasurableSet B) (T : ℝ) (n : ℕ) :
    Measurable (rejectionFailure η μ g B T n) :=
  Measurable.ite (measurableSet_goodState η hB)
    (measurable_measure_prodMk_left
      (measurableSet_hasHit_section (measurableSet_seededAcceptanceSection hg hB T) n).compl)
    measurable_const

theorem rejectionKernel_univ_add_failure (η : Kernel S U) [IsSFiniteKernel η]
    (μ : Measure U) [IsProbabilityMeasure μ] {g : S × U → ℝ≥0∞} (hg : Measurable g)
    {B : Set (S × U)} (hB : MeasurableSet B) (T : ℝ) (fallback : U × ℝ) (n : ℕ) (s : S) :
    rejectionKernel η μ hg hB T fallback n s univ + rejectionFailure η μ g B T n s = 1 := by
  rw [rejectionKernel, Kernel.piecewise_apply', rejectionFailure]
  split_ifs
  · have hacc : MeasurableSet
        (seededAcceptance (fun u ↦ g (s, u)) {u | (s, u) ∈ B} T) :=
      measurableSet_seededAcceptance (hg.comp measurable_prodMk_left)
        (hB.preimage measurable_prodMk_left) T
    rw [seededFirstHitKernel_apply μ hg hB T fallback n s MeasurableSet.univ, preimage_univ,
      ← firstHitLaw_apply _ hacc MeasurableSet.univ]
    exact firstHitLaw_univ_add_noHit _ hacc fallback n
  · simp

theorem rejectionFailure_le (η : Kernel S U) [IsMarkovKernel η]
    (μ : Measure U) [IsProbabilityMeasure μ] {g : S × U → ℝ≥0∞} (hg : Measurable g)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    {B : Set (S × U)} (hB : MeasurableSet B) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ z ∈ B, g z ≤ ENNReal.ofReal T) (n : ℕ) (s : S) :
    rejectionFailure η μ g B T n s ≤ 2 * η s {u | (s, u) ∉ B} +
      ENNReal.ofReal (Real.exp (-((n : ℝ) * ((1 / 2) / T)))) := by
  rw [rejectionFailure]
  split_ifs with hs
  · apply (measure_seededNoHit_le_exp μ (hg.comp measurable_prodMk_left)
      (hB.preimage measurable_prodMk_left) hT (fun u hu ↦ hcut (s, u) hu) ?_ n).trans
      (le_add_left le_rfl)
    simpa only [goodState, mem_setOf_eq, hrow, Function.comp_def, Set.preimage] using hs
  · have hsmall : η s {u | (s, u) ∈ B} ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
      (lt_of_not_ge hs).le
    have hrej : ENNReal.ofReal (1 / 2 : ℝ) ≤ η s {u | (s, u) ∉ B} := by
      have hcomp := measure_compl (hB.preimage (measurable_prodMk_left (x := s)))
        (measure_ne_top (η s) _)
      change η s {u | (s, u) ∉ B} = _ at hcomp
      rw [hcomp, measure_univ]
      have hhalf : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 2 : ℝ) =
          ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num)]
        norm_num
      rw [← hhalf]
      exact tsub_le_tsub_left hsmall 1
    have hbound : (1 : ℝ≥0∞) ≤ 2 * η s {u | (s, u) ∉ B} := by
      calc
        _ = 2 * ENNReal.ofReal (1 / 2 : ℝ) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
            ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        _ ≤ _ := mul_le_mul_right hrej 2
    exact hbound.trans (le_add_right le_rfl)

theorem lintegral_rejectionFailure_le (σ : Measure S) [IsProbabilityMeasure σ]
    (η : Kernel S U) [IsMarkovKernel η] (μ : Measure U) [IsProbabilityMeasure μ]
    {g : S × U → ℝ≥0∞} (hg : Measurable g)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    {B : Set (S × U)} (hB : MeasurableSet B) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ z ∈ B, g z ≤ ENNReal.ofReal T) (n : ℕ) :
    (∫⁻ s, rejectionFailure η μ g B T n s ∂σ) ≤
      2 * (σ ⊗ₘ η) Bᶜ + ENNReal.ofReal (Real.exp (-((n : ℝ) * ((1 / 2) / T)))) := by
  have hm : Measurable (fun s ↦ η s {u | (s, u) ∉ B}) :=
    Kernel.measurable_kernel_prodMk_left hB.compl
  have h2m : Measurable (fun s ↦ 2 * η s {u | (s, u) ∉ B}) := measurable_const.mul hm
  calc
    _ ≤ ∫⁻ s, 2 * η s {u | (s, u) ∉ B} +
        ENNReal.ofReal (Real.exp (-((n : ℝ) * ((1 / 2) / T)))) ∂σ :=
      lintegral_mono (rejectionFailure_le η μ hg hrow hB hT hcut n)
    _ = _ := by
      rw [lintegral_add_left h2m, lintegral_const_mul _ hm,
        Measure.compProd_apply hB.compl]
      simp
      rfl

theorem compProd_le_mul_of_row_le (ψ σ : Measure S) [SFinite ψ] [SFinite σ]
    (κ η : Kernel S U) [IsSFiniteKernel κ] [IsSFiniteKernel η] (C D : ℝ≥0∞)
    (hprefix : ψ ≤ C • σ) (hrow : ∀ s, κ s ≤ D • η s) :
    ψ ⊗ₘ κ ≤ (C * D) • (σ ⊗ₘ η) := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.compProd_apply hE, Measure.smul_apply, smul_eq_mul,
    Measure.compProd_apply hE]
  calc
    _ ≤ ∫⁻ s, D * η s (Prod.mk s ⁻¹' E) ∂ψ :=
      lintegral_mono (fun s ↦ hrow s _)
    _ ≤ ∫⁻ s, D * η s (Prod.mk s ⁻¹' E) ∂(C • σ) :=
      lintegral_mono' hprefix le_rfl
    _ = _ := by
      rw [lintegral_smul_measure,
        lintegral_const_mul _ (Kernel.measurable_kernel_prodMk_left hE), mul_assoc]
      rfl

theorem compProd_rejectionKernel_le (ψ σ : Measure S) [SFinite ψ] [SFinite σ]
    (η : Kernel S U) [IsSFiniteKernel η] (μ : Measure U) [IsProbabilityMeasure μ]
    {g : S × U → ℝ≥0∞} (hg : Measurable g)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    {B : Set (S × U)} (hB : MeasurableSet B) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ z ∈ B, g z ≤ ENNReal.ofReal T) (fallback : U × ℝ) (n : ℕ)
    (C : ℝ≥0∞) (hprefix : ψ ≤ C • σ) :
    ψ ⊗ₘ rejectionKernel η μ hg hB T fallback n ≤ (C * 2) • (σ ⊗ₘ η) :=
  compProd_le_mul_of_row_le ψ σ _ η C 2 hprefix
    (rejectionKernel_le_two η μ hg hrow hB hT hcut fallback n)

end CapacityAtlas.MeasureBinning
