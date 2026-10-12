/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Average

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.MeasureChannel

variable {X Y M : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace M]

/-- A deterministic finite-message code with a measurable observation decoder. -/
structure OneShotCode (X Y M : Type*) [MeasurableSpace Y] [MeasurableSpace M] where
  encode : M → X
  decode : Y → M
  measurable_decode : Measurable decode

noncomputable def firstAccepted (accept : M → Y → Prop) (fallback : M) : List M → Y → M
  | [], _ => fallback
  | m :: ms, y => if accept m y then m else firstAccepted accept fallback ms y

theorem measurable_firstAccepted (accept : M → Y → Prop) (fallback : M)
    (haccept : ∀ m, MeasurableSet {y | accept m y}) (ms : List M) :
    Measurable (firstAccepted accept fallback ms) := by
  induction ms with
  | nil => exact measurable_const
  | cons m ms ih => exact Measurable.ite (haccept m) measurable_const ih

omit [MeasurableSpace Y] [MeasurableSpace M] in
theorem firstAccepted_eq_of_unique (accept : M → Y → Prop) (fallback : M)
    {ms : List M} {m : M} {y : Y} (hm : m ∈ ms) (haccept : accept m y)
    (hother : ∀ j ∈ ms, j ≠ m → ¬accept j y) :
    firstAccepted accept fallback ms y = m := by
  classical
  induction ms with
  | nil => simp at hm
  | cons j js ih =>
    by_cases hj : j = m
    · subst j
      simp [firstAccepted, haccept]
    · have hj' := hother j (by simp) hj
      simp only [firstAccepted, if_neg hj']
      exact ih (by simpa [Ne.symm hj] using hm) (fun k hk ↦ hother k (by simp [hk]))

section FiniteMessages

variable [Fintype M] [Nonempty M]

noncomputable def thresholdCode (A : Set (X × Y)) (hA : MeasurableSet A)
    (codebook : M → X) : OneShotCode X Y M := by
  classical
  exact {
    encode := codebook
    decode := firstAccepted (fun m y ↦ (codebook m, y) ∈ A)
      (Classical.choice inferInstance) Finset.univ.toList
    measurable_decode := measurable_firstAccepted _ _
      (fun m ↦ hA.preimage (measurable_const.prodMk measurable_id)) _ }

theorem measurable_thresholdCode_decode (A : Set (X × Y)) (hA : MeasurableSet A) :
    Measurable (fun p : (M → X) × Y ↦ (thresholdCode A hA p.1).decode p.2) := by
  have hlist (ms : List M) : Measurable (fun p : (M → X) × Y ↦
      firstAccepted (fun m y ↦ (p.1 m, y) ∈ A) (Classical.choice inferInstance) ms p.2) := by
    induction ms with
    | nil => exact measurable_const
    | cons m ms ih =>
      exact Measurable.ite (hA.preimage
        (((measurable_pi_apply m).comp measurable_fst).prodMk measurable_snd)) measurable_const ih
  exact hlist _

noncomputable def errorProbability (κ : Kernel X Y) (code : OneShotCode X Y M)
    (m : M) : ℝ≥0∞ := κ (code.encode m) {y | code.decode y ≠ m}

noncomputable def averageError (κ : Kernel X Y) (code : OneShotCode X Y M) : ℝ≥0∞ :=
  (Fintype.card M : ℝ≥0∞)⁻¹ * ∑ m, errorProbability κ code m

omit [Nonempty M] in
theorem averageError_eq_zero_of_subsingleton [Subsingleton M]
    (κ : Kernel X Y) (code : OneShotCode X Y M) : averageError κ code = 0 := by
  have herror (m : M) : {y | code.decode y ≠ m} = ∅ := by
    ext y
    simp [Subsingleton.elim (code.decode y) m]
  simp [averageError, errorProbability, herror]

theorem averageError_le_one (κ : Kernel X Y) [IsMarkovKernel κ]
    (code : OneShotCode X Y M) : averageError κ code ≤ 1 := by
  unfold averageError
  calc
    _ ≤ (Fintype.card M : ℝ≥0∞)⁻¹ * ∑ _m : M, (1 : ℝ≥0∞) := by
      gcongr
      exact prob_le_one
    _ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
        (by finiteness)

omit [Nonempty M] in
theorem averageError_toReal (κ : Kernel X Y) [IsMarkovKernel κ]
    (code : OneShotCode X Y M) :
    (averageError κ code).toReal =
      (Fintype.card M : ℝ)⁻¹ * ∑ m, (errorProbability κ code m).toReal := by
  simp only [averageError, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  exact ENNReal.toReal_sum (fun m _ ↦ measure_ne_top (κ (code.encode m)) _)

noncomputable def missedDetection (κ : Kernel X Y) (A : Set (X × Y)) (x : X) : ℝ≥0∞ :=
  κ x {y | (x, y) ∉ A}

noncomputable def falseAcceptance (κ : Kernel X Y) (A : Set (X × Y))
    (x x' : X) : ℝ≥0∞ := κ x {y | (x', y) ∈ A}

theorem measurable_missedDetection (κ : Kernel X Y) [IsSFiniteKernel κ]
    (A : Set (X × Y)) (hA : MeasurableSet A) : Measurable (missedDetection κ A) :=
  Kernel.measurable_kernel_prodMk_left hA.compl

theorem measurable_falseAcceptance (κ : Kernel X Y) [IsSFiniteKernel κ]
    (A : Set (X × Y)) (hA : MeasurableSet A) :
    Measurable (fun p : X × X ↦ falseAcceptance κ A p.1 p.2) := by
  exact Kernel.measurable_kernel_prodMk_left
    (κ := κ.comap Prod.fst measurable_fst)
    (hA.preimage (measurable_fst.snd.prodMk measurable_snd))

theorem thresholdCode_errorProbability_le (κ : Kernel X Y) (A : Set (X × Y))
    (hA : MeasurableSet A) (codebook : M → X) (m : M) :
    errorProbability κ (thresholdCode A hA codebook) m ≤
      missedDetection κ A (codebook m) +
        ∑ j ∈ Finset.univ.erase m, falseAcceptance κ A (codebook m) (codebook j) := by
  classical
  have hsubset : {y | (thresholdCode A hA codebook).decode y ≠ m} ⊆
      {y | (codebook m, y) ∉ A} ∪
        ⋃ j ∈ Finset.univ.erase m, {y | (codebook j, y) ∈ A} := by
    intro y hy
    by_cases hm : (codebook m, y) ∈ A
    · right
      by_contra hn
      have hother : ∀ j ∈ Finset.univ.toList, j ≠ m → (codebook j, y) ∉ A := by
        intro j _ hj hjA
        exact hn (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
          ⟨Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, hjA⟩⟩)
      exact hy (firstAccepted_eq_of_unique (fun j y ↦ (codebook j, y) ∈ A)
        _ (by simp) hm hother)
    · exact Or.inl hm
  exact (measure_mono hsubset).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (measure_biUnion_finset_le _ _)))

noncomputable def packingBound (κ : Kernel X Y) (A : Set (X × Y))
    (codebook : M → X) : ℝ≥0∞ := by
  classical
  exact (Fintype.card M : ℝ≥0∞)⁻¹ * ∑ m,
    (missedDetection κ A (codebook m) +
      ∑ j ∈ Finset.univ.erase m, falseAcceptance κ A (codebook m) (codebook j))

theorem thresholdCode_averageError_le (κ : Kernel X Y) (A : Set (X × Y))
    (hA : MeasurableSet A) (codebook : M → X) :
    averageError κ (thresholdCode A hA codebook) ≤ packingBound κ A codebook := by
  unfold averageError packingBound
  gcongr with m
  exact thresholdCode_errorProbability_le κ A hA codebook m

omit [MeasurableSpace M] [Nonempty M] in
theorem measurable_packingBound (κ : Kernel X Y) [IsSFiniteKernel κ]
    (A : Set (X × Y)) (hA : MeasurableSet A) :
    Measurable (packingBound (M := M) κ A) := by
  unfold packingBound
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro m _
  apply Measurable.add ((measurable_missedDetection κ A hA).comp (measurable_pi_apply m))
  apply Finset.measurable_sum
  intro j _
  exact (measurable_falseAcceptance κ A hA).comp
    (show Measurable (fun c : M → X ↦ (c m, c j)) from
      (measurable_pi_apply m).prodMk (measurable_pi_apply j))

omit [MeasurableSpace M] [Nonempty M] in
theorem measurePreserving_codebook_pair (μ : Measure X) [IsProbabilityMeasure μ]
    {m j : M} (hmj : m ≠ j) :
    MeasurePreserving (fun c : M → X ↦ (c m, c j))
      (Measure.pi (fun _ : M ↦ μ)) (μ.prod μ) where
  measurable := (measurable_pi_apply m).prodMk (measurable_pi_apply j)
  map_eq := by
    have hindep := (iIndepFun_pi (μ := fun _ : M ↦ μ)
      (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)).indepFun hmj
    have hmap := hindep.map_prod_eq_prod_map_map
      (measurable_pi_apply m).aemeasurable (measurable_pi_apply j).aemeasurable
    simpa only [id_eq, (measurePreserving_eval (fun _ : M ↦ μ) m).map_eq,
      (measurePreserving_eval (fun _ : M ↦ μ) j).map_eq] using hmap

omit [MeasurableSpace M] [Nonempty M] in
theorem lintegral_codebook_falseAcceptance (κ : Kernel X Y) [IsSFiniteKernel κ]
    (A : Set (X × Y)) (hA : MeasurableSet A)
    (μ : Measure X) [IsProbabilityMeasure μ] {m j : M} (hmj : m ≠ j) :
    (∫⁻ c : M → X, falseAcceptance κ A (c m) (c j) ∂Measure.pi (fun _ : M ↦ μ)) =
      ∫⁻ x, ∫⁻ x', falseAcceptance κ A x x' ∂μ ∂μ := by
  rw [(measurePreserving_codebook_pair μ hmj).lintegral_comp
    (measurable_falseAcceptance κ A hA)]
  exact lintegral_prod _ (measurable_falseAcceptance κ A hA).aemeasurable

omit [MeasurableSpace M] in
theorem lintegral_packingBound (κ : Kernel X Y) [IsSFiniteKernel κ]
    (A : Set (X × Y)) (hA : MeasurableSet A)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    (∫⁻ c : M → X, packingBound κ A c ∂Measure.pi (fun _ : M ↦ μ)) =
      (∫⁻ x, missedDetection κ A x ∂μ) +
        (Fintype.card M - 1 : ℕ) * ∫⁻ x, ∫⁻ x', falseAcceptance κ A x x' ∂μ ∂μ := by
  have hmiss (m : M) : Measurable (fun c : M → X ↦ missedDetection κ A (c m)) :=
    (measurable_missedDetection κ A hA).comp (measurable_pi_apply m)
  have hfalse (m j : M) :
      Measurable (fun c : M → X ↦ falseAcceptance κ A (c m) (c j)) :=
    (measurable_falseAcceptance κ A hA).comp
      (show Measurable (fun c : M → X ↦ (c m, c j)) from
        (measurable_pi_apply m).prodMk (measurable_pi_apply j))
  have hsum (m : M) := Finset.measurable_sum (s := Finset.univ.erase m)
    (fun j _ ↦ hfalse m j)
  have htermMeas (m : M) : Measurable (fun c : M → X ↦
      missedDetection κ A (c m) +
        ∑ j ∈ Finset.univ.erase m, falseAcceptance κ A (c m) (c j)) :=
    (hmiss m).add (hsum m)
  have hterm (m : M) :
      (∫⁻ c : M → X, (missedDetection κ A (c m) +
        ∑ j ∈ Finset.univ.erase m, falseAcceptance κ A (c m) (c j))
        ∂Measure.pi (fun _ : M ↦ μ)) =
      (∫⁻ x, missedDetection κ A x ∂μ) +
        (Fintype.card M - 1 : ℕ) * ∫⁻ x, ∫⁻ x', falseAcceptance κ A x x' ∂μ ∂μ := by
    rw [lintegral_add_left (hmiss m), lintegral_finsetSum _ (fun j _ ↦ hfalse m j)]
    rw [(measurePreserving_eval (fun _ : M ↦ μ) m).lintegral_comp
      (measurable_missedDetection κ A hA)]
    congr 1
    calc
      _ = ∑ _j ∈ Finset.univ.erase m,
          ∫⁻ x, ∫⁻ x', falseAcceptance κ A x x' ∂μ ∂μ := by
        apply Finset.sum_congr rfl
        intro j hj
        exact lintegral_codebook_falseAcceptance κ A hA μ (Finset.mem_erase.mp hj).1.symm
      _ = _ := by simp
  unfold packingBound
  rw [lintegral_const_mul _ (Finset.measurable_sum Finset.univ (fun m _ ↦ htermMeas m)),
    lintegral_finsetSum _ (fun m _ ↦ htermMeas m)]
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.inv_mul_cancel_left (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)

/-- Random coding over arbitrary measurable alphabets, with a deterministic selected codebook. -/
theorem exists_oneShotCode_averageError_le (κ : Kernel X Y) [IsSFiniteKernel κ]
    (A : Set (X × Y)) (hA : MeasurableSet A)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ code : OneShotCode X Y M,
      averageError κ code ≤ (∫⁻ x, missedDetection κ A x ∂μ) +
        (Fintype.card M - 1 : ℕ) * ∫⁻ x, ∫⁻ x', falseAcceptance κ A x x' ∂μ ∂μ := by
  obtain ⟨c, hc⟩ := exists_le_lintegral
    (μ := Measure.pi (fun _ : M ↦ μ)) (measurable_packingBound κ A hA).aemeasurable
  exact ⟨thresholdCode A hA c, (thresholdCode_averageError_le κ A hA c).trans
    (hc.trans_eq (lintegral_packingBound κ A hA μ))⟩

end FiniteMessages

end CapacityAtlas.MeasureChannel
