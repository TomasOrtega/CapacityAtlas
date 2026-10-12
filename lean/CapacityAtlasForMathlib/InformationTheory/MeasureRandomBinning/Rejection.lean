/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.FirstSuccess
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace CapacityAtlas.MeasureBinning

noncomputable def seedLaw : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure seedLaw where
  measure_univ := by simp [seedLaw, Real.volume_Icc]

theorem seedLaw_Iic {r : ℝ} (hr : r ≤ 1) : seedLaw (Iic r) = ENNReal.ofReal r := by
  rw [seedLaw, Measure.restrict_apply measurableSet_Iic]
  have heq : Iic r ∩ Icc (0 : ℝ) 1 = Icc 0 r := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans hr⟩⟩
  rw [heq, Real.volume_Icc, sub_zero]

variable {U : Type*} [MeasurableSpace U]

def seededAcceptance (g : U → ℝ≥0∞) (B : Set U) (T : ℝ) : Set (U × ℝ) :=
  {p | p.1 ∈ B ∧ p.2 ≤ (g p.1).toReal / T}

theorem measurableSet_seededAcceptance {g : U → ℝ≥0∞} (hg : Measurable g)
    {B : Set U} (hB : MeasurableSet B) (T : ℝ) :
    MeasurableSet (seededAcceptance g B T) :=
  (hB.preimage measurable_fst).inter
    (measurableSet_le measurable_snd ((hg.comp measurable_fst).ennreal_toReal.div_const T))

theorem measure_seededAcceptance_inter (μ : Measure U) [SFinite μ]
    {g : U → ℝ≥0∞} (hg : Measurable g) {B E : Set U}
    (hB : MeasurableSet B) (hE : MeasurableSet E) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ u ∈ B, g u ≤ ENNReal.ofReal T) :
    (μ.prod seedLaw) (seededAcceptance g B T ∩ Prod.fst ⁻¹' E) =
      (μ.withDensity g) (B ∩ E) / ENNReal.ofReal T := by
  rw [Measure.prod_apply ((measurableSet_seededAcceptance hg hB T).inter
    (hE.preimage measurable_fst))]
  have hsection (u : U) :
      seedLaw {v | (u, v) ∈ seededAcceptance g B T ∩ Prod.fst ⁻¹' E} =
        (B ∩ E).indicator (fun u ↦ g u / ENNReal.ofReal T) u := by
    by_cases hu : u ∈ B ∩ E
    · have hfinite : g u ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hcut u hu.1)
      have hle : (g u).toReal / T ≤ 1 := by
        rw [div_le_one hT]
        exact ENNReal.toReal_le_of_le_ofReal hT.le (hcut u hu.1)
      simp only [mem_inter_iff, mem_preimage, seededAcceptance, mem_setOf_eq,
        hu.1, hu.2, true_and, and_true, indicator_of_mem hu]
      rw [show {v : ℝ | v ≤ (g u).toReal / T} = Iic ((g u).toReal / T) from rfl,
        seedLaw_Iic hle, ENNReal.ofReal_div_of_pos hT, ENNReal.ofReal_toReal hfinite]
    · have hempty : {v : ℝ | (u, v) ∈ seededAcceptance g B T ∩ Prod.fst ⁻¹' E} = ∅ := by
        ext v
        simp only [mem_inter_iff, seededAcceptance, mem_setOf_eq, mem_preimage, mem_empty_iff_false,
          iff_false]
        exact fun h ↦ hu ⟨h.1.1, h.2⟩
      rw [hempty, measure_empty, indicator_of_notMem hu]
  change (∫⁻ u, seedLaw {v | (u, v) ∈ seededAcceptance g B T ∩ Prod.fst ⁻¹' E} ∂μ) = _
  simp_rw [hsection]
  rw [lintegral_indicator (hB.inter hE)]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ hg, withDensity_apply _ (hB.inter hE)]

theorem measure_seededAcceptance (μ : Measure U) [SFinite μ]
    {g : U → ℝ≥0∞} (hg : Measurable g) {B : Set U} (hB : MeasurableSet B)
    {T : ℝ} (hT : 0 < T) (hcut : ∀ u ∈ B, g u ≤ ENNReal.ofReal T) :
    (μ.prod seedLaw) (seededAcceptance g B T) =
      (μ.withDensity g) B / ENNReal.ofReal T := by
  simpa only [preimage_univ, inter_univ] using
    measure_seededAcceptance_inter μ hg hB MeasurableSet.univ hT hcut

theorem measure_seededFirstHit_le (μ : Measure U) [IsProbabilityMeasure μ]
    {g : U → ℝ≥0∞} (hg : Measurable g) {B E : Set U}
    (hB : MeasurableSet B) (hE : MeasurableSet E) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ u ∈ B, g u ≤ ENNReal.ofReal T)
    (hpositive : (μ.withDensity g) B ≠ 0) (fallback : U × ℝ) (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ μ.prod seedLaw))
      (firstHitEvent (seededAcceptance g B T) (Prod.fst ⁻¹' E) fallback n) ≤
      (μ.withDensity g) (B ∩ E) / (μ.withDensity g) B := by
  have hmass := measure_seededAcceptance μ hg hB hT hcut
  have hp : (μ.prod seedLaw) (seededAcceptance g B T) ≠ 0 := by
    rw [hmass]
    exact ENNReal.div_ne_zero.mpr ⟨hpositive, ENNReal.ofReal_ne_top⟩
  calc
    _ ≤ (μ.prod seedLaw) (seededAcceptance g B T ∩ Prod.fst ⁻¹' E) /
        (μ.prod seedLaw) (seededAcceptance g B T) :=
      measure_firstHitEvent_le_div (μ.prod seedLaw)
        (measurableSet_seededAcceptance hg hB T) (hE.preimage measurable_fst) fallback n hp
    _ = _ := by
      rw [measure_seededAcceptance_inter μ hg hB hE hT hcut, hmass]
      exact ENNReal.mul_div_mul_right _ _
        (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
        (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hT).ne')

theorem measure_seededFirstHit_le_two (μ : Measure U) [IsProbabilityMeasure μ]
    {g : U → ℝ≥0∞} (hg : Measurable g) {B E : Set U}
    (hB : MeasurableSet B) (hE : MeasurableSet E) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ u ∈ B, g u ≤ ENNReal.ofReal T)
    (hmass : ENNReal.ofReal (1 / 2 : ℝ) ≤ (μ.withDensity g) B)
    (fallback : U × ℝ) (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ μ.prod seedLaw))
      (firstHitEvent (seededAcceptance g B T) (Prod.fst ⁻¹' E) fallback n) ≤
      2 * (μ.withDensity g) E := by
  have hpositive : (μ.withDensity g) B ≠ 0 :=
    (lt_of_lt_of_le (by norm_num) hmass).ne'
  calc
    _ ≤ (μ.withDensity g) (B ∩ E) / (μ.withDensity g) B :=
      measure_seededFirstHit_le μ hg hB hE hT hcut hpositive fallback n
    _ ≤ (μ.withDensity g) (B ∩ E) / ENNReal.ofReal (1 / 2 : ℝ) :=
      ENNReal.div_le_div_left hmass _
    _ ≤ (μ.withDensity g) E / ENNReal.ofReal (1 / 2 : ℝ) :=
      ENNReal.div_le_div_right (measure_mono inter_subset_right) _
    _ = _ := by
      rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num [mul_comm]

theorem measure_seededNoHit_le_exp (μ : Measure U) [IsProbabilityMeasure μ]
    {g : U → ℝ≥0∞} (hg : Measurable g) {B : Set U} (hB : MeasurableSet B)
    {T : ℝ} (hT : 0 < T) (hcut : ∀ u ∈ B, g u ≤ ENNReal.ofReal T)
    (hmass : ENNReal.ofReal (1 / 2 : ℝ) ≤ (μ.withDensity g) B) (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ μ.prod seedLaw))
      {book | ¬hasHit (seededAcceptance g B T) book} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * ((1 / 2) / T)))) := by
  apply measure_noHit_le_exp (μ.prod seedLaw) (measurableSet_seededAcceptance hg hB T)
  have hlower : ENNReal.ofReal ((1 / 2) / T) ≤
      (μ.prod seedLaw) (seededAcceptance g B T) := by
    rw [measure_seededAcceptance μ hg hB hT hcut, ENNReal.ofReal_div_of_pos hT]
    exact ENNReal.div_le_div_right hmass _
  simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1 / 2) / T)] using
    ENNReal.toReal_mono (measure_ne_top (μ.prod seedLaw) _) hlower

end CapacityAtlas.MeasureBinning
