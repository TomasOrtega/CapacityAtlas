/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Basic

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference

def silentCode (K n : ℕ) : Code K n where
  messages := fun _ ↦ 1
  messages_pos := fun _ ↦ Nat.zero_lt_one
  encode := fun _ _ _ _ ↦ 0
  encode_measurable := fun _ _ _ ↦ measurable_const
  encode_causal := fun _ _ _ _ _ _ ↦ rfl
  decode := fun _ ↦
    { apply := fun _ ↦ 0
      measurable_fiber := by intro m; simp [Subsingleton.elim m 0] }

theorem silentCode_powerAdmissible (μ : Measure ℂ) {K n : ℕ} {P : ℝ} (hP : 0 ≤ P) :
    PowerAdmissible μ P (silentCode K n) := by
  constructor
  · intro m
    have he : energy (silentCode K n) m = fun _ ↦ 0 := by
      funext H
      simp [energy, silentCode]
    rw [he]
    exact integrable_zero _ _ _
  · simpa [energy, silentCode] using mul_nonneg (Nat.cast_nonneg n) hP

theorem silentCode_error (μ : Measure ℂ) (K n : ℕ) : error μ (silentCode K n) = 0 := by
  have hevent (m : (silentCode K n).Message) : errorEvent (silentCode K n) m = ∅ := by
    ext hz
    simp only [errorEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_exists, not_not]
    intro i
    change (0 : Fin 1) = m i
    exact Subsingleton.elim _ _
  simp [error, hevent]

theorem silentCode_rates (K n : ℕ) : rates (silentCode K n) = 0 := by
  ext i
  simp [rates, silentCode, Operational.messageRate]

theorem zero_mem_capacityRegion (μ : Measure ℂ) (K : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (0 : Fin K → ℝ) ∈ capacityRegion μ K P := by
  refine ⟨fun _ ↦ le_rfl, fun ε hε ↦ ⟨1, Nat.zero_lt_one, fun n _ ↦ ?_⟩⟩
  refine ⟨silentCode K n, silentCode_powerAdmissible μ hP, ?_, ?_⟩
  · simpa only [silentCode_error] using hε.le
  · intro i
    simpa only [silentCode_rates, Pi.zero_apply, zero_sub] using neg_nonpos.mpr hε.le

theorem PowerAdmissible.mono {μ : Measure ℂ} {K n : ℕ} {P P' : ℝ} {c : Code K n}
    (h : PowerAdmissible μ P c) (hPP' : P ≤ P') : PowerAdmissible μ P' c :=
  ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left hPP' (Nat.cast_nonneg n))⟩

theorem capacityRegion_mono (μ : Measure ℂ) (K : ℕ) {P P' : ℝ} (hPP' : P ≤ P') :
    capacityRegion μ K P ⊆ capacityRegion μ K P' := by
  rintro R ⟨hR, hcodes⟩
  refine ⟨hR, fun ε hε ↦ ?_⟩
  obtain ⟨N, hN, hc⟩ := hcodes ε hε
  refine ⟨N, hN, fun n hn ↦ ?_⟩
  obtain ⟨c, hP, he, hr⟩ := hc n hn
  exact ⟨c, hP.mono hPP', he, hr⟩

theorem capacityRegion_nonneg {μ : Measure ℂ} {K : ℕ} {P : ℝ} {R : Fin K → ℝ}
    (hR : R ∈ capacityRegion μ K P) (i : Fin K) : 0 ≤ R i := hR.1 i

theorem PowerAdmissible.power_nonneg {μ : Measure ℂ} {K n : ℕ} {P : ℝ} {c : Code K n}
    (h : PowerAdmissible μ P c) (hn : 0 < n) : 0 ≤ P := by
  have he : 0 ≤ (∏ i, (c.messages i : ℝ))⁻¹ *
      (∑ m, ∫ H, energy c m H ∂stateLaw μ K n) := by
    apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro m _
      apply integral_nonneg
      intro H
      unfold energy
      positivity
  have hnp : 0 ≤ (n : ℝ) * P := he.trans h.2
  exact nonneg_of_mul_nonneg_right hnp (Nat.cast_pos.mpr hn)

theorem capacityRegion_eq_empty_of_neg {μ : Measure ℂ} {K : ℕ} {P : ℝ} (hP : P < 0) :
    capacityRegion μ K P = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro R hR
  obtain ⟨N, hN, hc⟩ := hR.2 1 zero_lt_one
  obtain ⟨c, hpower, _, _⟩ := hc N le_rfl
  exact (not_le_of_gt hP) (hpower.power_nonneg hN)

theorem sumCapacity_eq_zero_of_neg {μ : Measure ℂ} {K : ℕ} {P : ℝ} (hP : P < 0) :
    sumCapacity μ K P = 0 := by
  simp [sumCapacity, capacityRegion_eq_empty_of_neg hP, Real.sSup_empty]

theorem sumRates_bddAbove_of_bound {μ : Measure ℂ} {K : ℕ} {P B : ℝ}
    (hB : ∀ R ∈ capacityRegion μ K P, ∑ i, R i ≤ B) :
    BddAbove {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i} := by
  refine ⟨B, ?_⟩
  rintro s ⟨R, hR, rfl⟩
  exact hB R hR

theorem sum_le_sumCapacity {μ : Measure ℂ} {K : ℕ} {P : ℝ}
    (hB : BddAbove {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i})
    {R : Fin K → ℝ} (hR : R ∈ capacityRegion μ K P) :
    ∑ i, R i ≤ sumCapacity μ K P := le_csSup hB ⟨R, hR, rfl⟩

theorem sumCapacity_nonneg {μ : Measure ℂ} {K : ℕ} {P : ℝ}
    (hB : BddAbove {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i}) :
    0 ≤ sumCapacity μ K P := by
  classical
  by_cases hne : ({s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i} : Set ℝ).Nonempty
  · obtain ⟨s, R, hR, rfl⟩ := hne
    exact (Finset.sum_nonneg (fun i _ ↦ hR.1 i)).trans (sum_le_sumCapacity hB hR)
  · have he : ({s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i} : Set ℝ) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    simp [sumCapacity, he, Real.sSup_empty]

theorem sumCapacity_le {μ : Measure ℂ} {K : ℕ} {P B : ℝ} (hP : 0 ≤ P)
    (hB : ∀ R ∈ capacityRegion μ K P, ∑ i, R i ≤ B) : sumCapacity μ K P ≤ B := by
  apply csSup_le
  · refine ⟨0, 0, zero_mem_capacityRegion μ K hP, ?_⟩
    simp
  · rintro s ⟨R, hR, rfl⟩
    exact hB R hR

theorem sumCapacity_mono {μ : Measure ℂ} {K : ℕ} {P P' : ℝ} (hPP' : P ≤ P')
    (hB : BddAbove {s | ∃ R ∈ capacityRegion μ K P', s = ∑ i, R i}) :
    sumCapacity μ K P ≤ sumCapacity μ K P' := by
  classical
  by_cases hne : ({s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i} : Set ℝ).Nonempty
  · apply csSup_le_csSup hB hne
    rintro s ⟨R, hR, hs⟩
    exact ⟨R, capacityRegion_mono μ K hPP' hR, hs⟩
  · have he : ({s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i} : Set ℝ) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    simpa [sumCapacity, he, Real.sSup_empty] using sumCapacity_nonneg hB

theorem monotone_sumCapacity (μ : Measure ℂ) (K : ℕ)
    (hB : ∀ P, BddAbove {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i}) :
    Monotone (sumCapacity μ K) := fun _ P' hPP' ↦ sumCapacity_mono hPP' (hB P')

end CapacityAtlas.Gaussian.Interference
