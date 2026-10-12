/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.SuperpositionCode
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.BlockBounds

open scoped BigOperators

namespace CapacityAtlas.ConfidentialBroadcast.SuperpositionCode

variable {B U V Y Z : Type*} [Fintype B] [Fintype U] [Fintype V] [Fintype Y] [Fintype Z]
  {C S L n : ℕ} [NeZero C] [NeZero S] [NeZero L]

theorem expected_average (p : FiniteDistribution B)
    (f : B → Fin C → Fin S → Fin L → ℝ) :
    (∑ b, p b * average (f b)) = average (fun c s l ↦ ∑ b, p b * f b c s l) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro c
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro s
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro l
  apply Fintype.sum_congr
  intro b
  ring

theorem average_const (r : ℝ) : (average (C := C) (S := S) (L := L) fun _ _ _ ↦ r) = r := by
  simp only [average, ← Finset.sum_mul,
    FiniteDistribution.sum_probability_eq_one, one_mul]

def blockEnsemble (p : FiniteDistribution U) (q : U → FiniteDistribution V) (n C S L : ℕ) :=
  superpositionEnsemble (C := Fin C) (S := Fin S × Fin L) (p.iid n) (conditionalProduct q n)

theorem average_nonnegative (f : Fin C → Fin S → Fin L → ℝ)
    (hf : ∀ c s l, 0 ≤ f c s l) : 0 ≤ average f := by
  rw [← average_const (C := C) (S := S) (L := L) 0]
  exact average_mono _ _ hf

theorem rawCommonError_nonnegative {A O : Type*} [Fintype A] [Fintype O]
    (p : FiniteDistribution A) (q : A → FiniteDistribution (Fin n → V))
    (cloud : Fin C → A) (satellites : Fin C → (Fin S × Fin L) → Fin n → V)
    (W : FiniteChannel (Fin n → V) O) (tau : ℝ) :
    0 ≤ rawCommonError p q cloud satellites W tau := by
  classical
  apply average_nonnegative
  intro c s l
  exact Finset.sum_nonneg fun y _ ↦ by split_ifs; exact W.nonnegative _ y; rfl

theorem rawSatelliteError_nonnegative {A O : Type*} [Fintype A] [Fintype O]
    (q : A → FiniteDistribution (Fin n → V)) (tau : A → ℝ)
    (cloud : Fin C → A) (satellites : Fin C → (Fin S × Fin L) → Fin n → V)
    (W : FiniteChannel (Fin n → V) O) :
    0 ≤ rawSatelliteError q tau cloud satellites W := by
  classical
  apply average_nonnegative
  intro c s l
  rw [OneShotCode.errorProbability_eq_sum_decode_ne]
  exact Finset.sum_nonneg fun y _ ↦ by split_ifs; exact W.nonnegative _ y; rfl

theorem upperLeakage_nonnegative (W : FiniteBroadcastChannel V Y Z)
    (satellites : Fin C → (Fin S × Fin L) → Fin n → V) : 0 ≤ upperLeakage W satellites := by
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg (FiniteDistribution.probability_nonnegative _ _)
  exact div_nonneg (FiniteChannel.mutualInformation_nonnegative _ _)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

theorem expected_rawCommonError_le {O : Type*} [Fintype O]
    (W : FiniteChannel V O) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ book, blockEnsemble p q n C S L book *
      rawCommonError (p.iid n) (conditionalProduct q n) book.1 book.2
        (W.block n) (commonThreshold W p q n δ)) ≤ commonCodingBound W p q n C δ := by
  classical
  unfold rawCommonError
  rw [expected_average]
  apply (average_mono _ _ (fun c s l ↦ ?_)).trans (le_of_eq (average_const _))
  have h := expected_block_common_error_le W p q hn hδ c (s, l)
  simp only [Fintype.card_fin] at h
  convert h using 1
  apply Fintype.sum_congr
  intro book
  congr 1

theorem expected_rawSatelliteError_le {O : Type*} [Fintype O]
    (W : FiniteChannel V O) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ book, blockEnsemble p q n C S L book *
      rawSatelliteError (conditionalProduct q n) (fun _ ↦ densityThreshold W p q n δ)
        book.1 book.2 (W.block n)) ≤ conditionalCodingBound W p q n (S * L) δ := by
  classical
  unfold rawSatelliteError
  rw [expected_average]
  apply (average_mono _ _ (fun c s l ↦ ?_)).trans (le_of_eq (average_const _))
  simpa only [blockEnsemble, Fintype.card_prod, Fintype.card_fin] using
    expected_block_satellite_error_le W p q hn hδ c (s, l)

noncomputable def leakageBound (W : FiniteChannel V Z) (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (n L : ℕ) (δ : ℝ) : ℝ :=
  (n : ℝ) * (conditionalMean W p q / Real.log 2) - Real.log L / Real.log 2 + 1 +
    conditionalCodingBound W p q n L δ * (Real.log L / Real.log 2)

theorem expected_upperLeakage_le (W : FiniteBroadcastChannel V Y Z)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ book, blockEnsemble p q n C S L book * upperLeakage W book.2) ≤
      leakageBound W.receiver₂ p q n L δ := by
  classical
  unfold upperLeakage
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ c, FiniteDistribution.uniform (Fin C) c *
        ∑ book, blockEnsemble p q n C S L book *
          (((W.receiver₂.block n).encoded (book.2 c)).averageSeed
            (fun _ ↦ FiniteDistribution.uniform (Fin L))).mutualInformationBits
            (FiniteDistribution.uniform (Fin S)) := by
      apply Fintype.sum_congr
      intro c
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro book
      ring
    _ ≤ ∑ c, FiniteDistribution.uniform (Fin C) c * leakageBound W.receiver₂ p q n L δ := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (FiniteDistribution.probability_nonnegative _ _)
      simpa only [blockEnsemble, leakageBound, Fintype.card_fin] using
        expected_block_leakage_le (S := Fin S) (L := Fin L) W.receiver₂ p q hn hδ c
    _ = _ := by rw [← Finset.sum_mul, FiniteDistribution.sum_probability_eq_one, one_mul]

noncomputable def commonErrorBound {O : Type*} [Fintype O] (W : FiniteChannel V O)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V) (n C : ℕ) (δ : ℝ) : ℝ :=
  if C = 1 then 0 else commonCodingBound W p q n C δ

noncomputable def satelliteErrorBound {O : Type*} [Fintype O] (W : FiniteChannel V O)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V) (n S L : ℕ) (δ : ℝ) : ℝ :=
  if S * L = 1 then 0 else conditionalCodingBound W p q n (S * L) δ

theorem expected_rawCommonError_le_adjusted {O : Type*} [Fintype O]
    (W : FiniteChannel V O) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ book, blockEnsemble p q n C S L book *
      rawCommonError (p.iid n) (conditionalProduct q n) book.1 book.2
        (W.block n) (commonThreshold W p q n δ)) ≤ commonErrorBound W p q n C δ := by
  classical
  unfold commonErrorBound
  split_ifs with hC
  · subst C
    simp only [rawCommonError_zero, mul_zero, Finset.sum_const_zero, le_refl]
  · exact expected_rawCommonError_le W p q hn hδ

theorem expected_rawSatelliteError_le_adjusted {O : Type*} [Fintype O]
    (W : FiniteChannel V O) (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (∑ book, blockEnsemble p q n C S L book *
      rawSatelliteError (conditionalProduct q n) (fun _ ↦ densityThreshold W p q n δ)
        book.1 book.2 (W.block n)) ≤ satelliteErrorBound W p q n S L δ := by
  classical
  unfold satelliteErrorBound
  split_ifs with hSL
  · have hL := Nat.eq_one_of_mul_eq_one_left hSL
    subst L
    have hS : S = 1 := by simpa using hSL
    subst S
    simp only [rawSatelliteError_zero, mul_zero, Finset.sum_const_zero, le_refl]
  · exact expected_rawSatelliteError_le W p q hn hδ

theorem defect_le_raw_bounds {A : Type*} [Fintype A]
    (W : FiniteBroadcastChannel V Y Z) (p : FiniteDistribution A)
    (q : A → FiniteDistribution (Fin n → V)) (tauY tauZ : ℝ) (tauSat : A → ℝ)
    (cloud : Fin C → A) (satellites : Fin C → (Fin S × Fin L) → Fin n → V) (hn : 0 < n) :
    (code W p q tauY tauZ tauSat cloud satellites).defect ≤
      commonYError W p q tauY cloud satellites + commonZError W p q tauZ cloud satellites +
        satelliteError W q tauSat cloud satellites + upperLeakage W satellites / n := by
  have hY := legitimateError_le W p q tauY tauZ tauSat cloud satellites
  have hZ := commonError_eq W p q tauY tauZ tauSat cloud satellites
  have hL := leakage_le W p q tauY tauZ tauSat cloud satellites hn
  have hY0 := rawCommonError_nonnegative p q cloud satellites (W.receiver₁.block n) tauY
  have hZ0 := rawCommonError_nonnegative p q cloud satellites (W.receiver₂.block n) tauZ
  have hS0 := rawSatelliteError_nonnegative q tauSat cloud satellites (W.receiver₁.block n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hU0 := div_nonneg (upperLeakage_nonnegative W satellites) hn0.le
  have hL' : (code W p q tauY tauZ tauSat cloud satellites).leakage ≤
      upperLeakage W satellites / n := by
    apply (le_div_iff₀ hn0).mpr
    nlinarith
  change max (max _ _) _ ≤ _
  apply max_le
  · apply max_le <;> dsimp [commonYError, commonZError, satelliteError] at * <;> linarith
  · dsimp [commonYError, commonZError, satelliteError] at *
    linarith

noncomputable def finiteCodingBound (W : FiniteBroadcastChannel V Y Z)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V) (n C S L : ℕ) (δ : ℝ) : ℝ :=
  commonErrorBound W.receiver₁ p q n C δ + commonErrorBound W.receiver₂ p q n C δ +
    satelliteErrorBound W.receiver₁ p q n S L δ +
      if S = 1 then 0 else leakageBound W.receiver₂ p q n L δ / n

/-- One fixed superposition code simultaneously meets reliability and weak secrecy. -/
theorem exists_code_defect_le (W : FiniteBroadcastChannel V Y Z)
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : Code W n, c.commonCount = C ∧ c.secretCount = S ∧
      c.defect ≤ finiteCodingBound W p q n C S L δ := by
  classical
  let P := blockEnsemble p q n C S L
  letI := P.nonempty
  let codeOf := fun book : (Fin C → Fin n → U) × (Fin C → (Fin S × Fin L) → Fin n → V) ↦
    code W (p.iid n) (conditionalProduct q n)
      (commonThreshold W.receiver₁ p q n δ) (commonThreshold W.receiver₂ p q n δ)
      (fun _ ↦ densityThreshold W.receiver₁ p q n δ) book.1 book.2
  obtain ⟨book, hbook⟩ := FiniteProductProbability.exists_value_le_weighted_mean
    P (fun book ↦ (codeOf book).defect) P.nonnegative P.sum_probability
  refine ⟨codeOf book, rfl, rfl, hbook.trans ?_⟩
  calc
    _ ≤ ∑ book, P book *
        (commonYError W (p.iid n) (conditionalProduct q n)
            (commonThreshold W.receiver₁ p q n δ) book.1 book.2 +
          commonZError W (p.iid n) (conditionalProduct q n)
            (commonThreshold W.receiver₂ p q n δ) book.1 book.2 +
          satelliteError W (conditionalProduct q n)
            (fun _ ↦ densityThreshold W.receiver₁ p q n δ) book.1 book.2 +
          (if S = 1 then 0 else upperLeakage W book.2 / n)) := by
      apply Finset.sum_le_sum
      intro book _
      apply mul_le_mul_of_nonneg_left _ (P.nonnegative book)
      by_cases hS : S = 1
      · subst S
        have hY := legitimateError_le W (p.iid n) (conditionalProduct q n)
          (commonThreshold W.receiver₁ p q n δ) (commonThreshold W.receiver₂ p q n δ)
          (fun _ ↦ densityThreshold W.receiver₁ p q n δ) book.1 book.2
        have hZ := commonError_eq W (p.iid n) (conditionalProduct q n)
          (commonThreshold W.receiver₁ p q n δ) (commonThreshold W.receiver₂ p q n δ)
          (fun _ ↦ densityThreshold W.receiver₁ p q n δ) book.1 book.2
        have hL := leakage_zero W (p.iid n) (conditionalProduct q n)
          (commonThreshold W.receiver₁ p q n δ) (commonThreshold W.receiver₂ p q n δ)
          (fun _ ↦ densityThreshold W.receiver₁ p q n δ) book.1 book.2
        have hY0 := rawCommonError_nonnegative (p.iid n) (conditionalProduct q n)
          book.1 book.2 (W.receiver₁.block n) (commonThreshold W.receiver₁ p q n δ)
        have hZ0 := rawCommonError_nonnegative (p.iid n) (conditionalProduct q n)
          book.1 book.2 (W.receiver₂.block n) (commonThreshold W.receiver₂ p q n δ)
        have hS0 := rawSatelliteError_nonnegative (conditionalProduct q n)
          (fun _ ↦ densityThreshold W.receiver₁ p q n δ) book.1 book.2 (W.receiver₁.block n)
        change max (max _ _) _ ≤ _
        rw [hL]
        apply max_le
        · apply max_le <;> dsimp [commonYError, commonZError, satelliteError] at * <;> linarith
        · dsimp [commonYError, commonZError, satelliteError] at *
          linarith
      · simp only [hS, if_false]
        exact defect_le_raw_bounds W _ _ _ _ _ _ _ hn
    _ ≤ _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (expected_rawCommonError_le_adjusted (C := C) (S := S) (L := L)
            W.receiver₁ p q hn hδ)
            (expected_rawCommonError_le_adjusted (C := C) (S := S) (L := L) W.receiver₂ p q hn hδ)
        · exact expected_rawSatelliteError_le_adjusted (C := C) (S := S) (L := L) W.receiver₁ p q hn hδ
      · by_cases hS : S = 1
        · simp only [hS, if_true, mul_zero, Finset.sum_const_zero, le_refl]
        · simp only [hS, if_false]
          calc
            _ = (∑ book, P book * upperLeakage W book.2) / n := by
              rw [Finset.sum_div]
              apply Fintype.sum_congr
              intro book
              exact (mul_div_assoc _ _ _).symm
            _ ≤ _ := div_le_div_of_nonneg_right
              (expected_upperLeakage_le (C := C) (S := S) (L := L) W p q hn hδ) (Nat.cast_nonneg n)

end CapacityAtlas.ConfidentialBroadcast.SuperpositionCode
