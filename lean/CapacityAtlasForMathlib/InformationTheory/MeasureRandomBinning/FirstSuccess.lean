/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Covering

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace CapacityAtlas.MeasureBinning

variable {U : Type*} [MeasurableSpace U]

noncomputable def firstHit (A : Set U) (fallback : U) :
    (n : ℕ) → (Fin n → U) → U
  | 0, _ => fallback
  | n + 1, book => if book 0 ∈ A then book 0 else firstHit A fallback n (fun i ↦ book i.succ)

def hasHit (A : Set U) {n : ℕ} (book : Fin n → U) : Prop := ∃ i, book i ∈ A

def firstHitEvent (A E : Set U) (fallback : U) (n : ℕ) : Set (Fin n → U) :=
  {book | hasHit A book ∧ firstHit A fallback n book ∈ E}

theorem measurable_firstHit {A : Set U} (hA : MeasurableSet A) (fallback : U) (n : ℕ) :
    Measurable (firstHit A fallback n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact Measurable.ite (hA.preimage (measurable_pi_apply 0)) (measurable_pi_apply 0)
        (ih.comp (measurable_pi_lambda _ (fun i ↦ measurable_pi_apply i.succ)))

theorem measurableSet_hasHit {A : Set U} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {book : Fin n → U | hasHit A book} := by
  simp only [hasHit, Set.setOf_exists]
  exact MeasurableSet.iUnion (fun i ↦ hA.preimage (measurable_pi_apply i))

theorem measurableSet_firstHitEvent {A E : Set U} (hA : MeasurableSet A)
    (hE : MeasurableSet E) (fallback : U) (n : ℕ) :
    MeasurableSet (firstHitEvent A E fallback n) :=
  (measurableSet_hasHit hA n).inter (hE.preimage (measurable_firstHit hA fallback n))

omit [MeasurableSpace U] in
theorem firstHit_mem {A : Set U} {fallback : U} {n : ℕ} {book : Fin n → U}
    (h : hasHit A book) : firstHit A fallback n book ∈ A := by
  induction n with
  | zero => obtain ⟨i, _⟩ := h; exact Fin.elim0 i
  | succ n ih =>
      by_cases hzero : book 0 ∈ A
      · simp [firstHit, hzero]
      · rw [firstHit, if_neg hzero]
        apply ih
        obtain ⟨i, hi⟩ := h
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact (hzero hi).elim
        · exact ⟨j, hi⟩

omit [MeasurableSpace U] in
theorem exists_firstHit_eq {A : Set U} {fallback : U} {n : ℕ} {book : Fin n → U}
    (h : hasHit A book) : ∃ i, firstHit A fallback n book = book i := by
  induction n with
  | zero => obtain ⟨i, _⟩ := h; exact Fin.elim0 i
  | succ n ih =>
      by_cases hzero : book 0 ∈ A
      · exact ⟨0, by simp [firstHit, hzero]⟩
      · have htail : hasHit A (fun i : Fin n ↦ book i.succ) := by
          obtain ⟨i, hi⟩ := h
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
          · exact (hzero hi).elim
          · exact ⟨j, hi⟩
        obtain ⟨i, hi⟩ := ih htail
        exact ⟨i.succ, by simpa only [firstHit, if_neg hzero] using hi⟩

omit [MeasurableSpace U] in
theorem firstHitEvent_succ {A E : Set U} (fallback : U) (n : ℕ) :
    (fun p : U × (Fin n → U) ↦ Fin.cons p.1 p.2) ⁻¹'
        firstHitEvent A E fallback (n + 1) =
      ((A ∩ E) ×ˢ Set.univ) ∪ (Aᶜ ×ˢ firstHitEvent A E fallback n) := by
  ext p
  simp only [Set.mem_preimage, firstHitEvent, Set.mem_setOf_eq, hasHit, Fin.exists_fin_succ,
    Fin.cons_zero, Fin.cons_succ, firstHit, Set.mem_union, Set.mem_prod, Set.mem_inter_iff,
    Set.mem_univ, and_true, Set.mem_compl_iff]
  by_cases h : p.1 ∈ A <;> simp [h]

theorem measure_firstHitEvent_succ (μ : Measure U) [IsProbabilityMeasure μ]
    {A E : Set U} (hA : MeasurableSet A) (hE : MeasurableSet E)
    (fallback : U) (n : ℕ) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ μ)) (firstHitEvent A E fallback (n + 1)) =
      μ (A ∩ E) + μ Aᶜ * (Measure.pi (fun _ : Fin n ↦ μ)) (firstHitEvent A E fallback n) := by
  have hequiv := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ μ) 0).symm
  rw [← hequiv.measure_preimage_equiv (firstHitEvent A E fallback (n + 1))]
  have hmap : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ U) 0).symm =
      (fun p : U × (Fin n → U) ↦ Fin.cons p.1 p.2) := by
    funext p
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
  rw [hmap, firstHitEvent_succ]
  have hdisj : Disjoint ((A ∩ E) ×ˢ (Set.univ : Set (Fin n → U)))
      (Aᶜ ×ˢ firstHitEvent A E fallback n) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hq.1 hp.1.1
  rw [measure_union hdisj (hA.compl.prod (measurableSet_firstHitEvent hA hE fallback n)),
    Measure.prod_prod, Measure.prod_prod]
  simp

theorem mul_measure_firstHitEvent_le (μ : Measure U) [IsProbabilityMeasure μ]
    {A E : Set U} (hA : MeasurableSet A) (hE : MeasurableSet E)
    (fallback : U) (n : ℕ) :
    μ A * (Measure.pi (fun _ : Fin n ↦ μ)) (firstHitEvent A E fallback n) ≤ μ (A ∩ E) := by
  induction n with
  | zero => simp [firstHitEvent, hasHit]
  | succ n ih =>
      rw [measure_firstHitEvent_succ μ hA hE fallback n, mul_add]
      calc
        _ = μ A * μ (A ∩ E) + μ Aᶜ *
            (μ A * (Measure.pi (fun _ : Fin n ↦ μ)) (firstHitEvent A E fallback n)) := by
          ring
        _ ≤ μ A * μ (A ∩ E) + μ Aᶜ * μ (A ∩ E) := by gcongr
        _ = μ (A ∩ E) := by
          rw [← add_mul, measure_add_measure_compl hA, measure_univ, one_mul]

theorem measure_firstHitEvent_le_div (μ : Measure U) [IsProbabilityMeasure μ]
    {A E : Set U} (hA : MeasurableSet A) (hE : MeasurableSet E)
    (fallback : U) (n : ℕ) (hp : μ A ≠ 0) :
    (Measure.pi (fun _ : Fin n ↦ μ)) (firstHitEvent A E fallback n) ≤ μ (A ∩ E) / μ A := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl hp) (Or.inl (measure_ne_top μ A))).mpr
  simpa only [mul_comm] using mul_measure_firstHitEvent_le μ hA hE fallback n

theorem measure_noHit (μ : Measure U) [IsProbabilityMeasure μ] (A : Set U) (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ μ)) {book | ¬hasHit A book} = (μ Aᶜ) ^ n := by
  have heq : {book : Fin n → U | ¬hasHit A book} = Set.univ.pi (fun _ ↦ Aᶜ) := by
    ext book
    simp [hasHit]
  rw [heq, Measure.pi_pi]
  simp

theorem measure_noHit_le_exp (μ : Measure U) [IsProbabilityMeasure μ]
    {A : Set U} (hA : MeasurableSet A) (n : ℕ) {p : ℝ} (hp : p ≤ (μ A).toReal) :
    (Measure.pi (fun _ : Fin n ↦ μ)) {book | ¬hasHit A book} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) * p))) := by
  simpa [coveringFailure, hasHit] using
    measure_coveringFailure_le_exp (L := Fin n) μ
      (B := (Set.univ : Set Unit) ×ˢ A) (MeasurableSet.univ.prod hA) () (by simpa using hp)

noncomputable def firstHitLaw (μ : Measure U) (A : Set U) (fallback : U) (n : ℕ) : Measure U :=
  ((Measure.pi (fun _ : Fin n ↦ μ)).restrict {book | hasHit A book}).map (firstHit A fallback n)

theorem firstHitLaw_apply (μ : Measure U) {A E : Set U} (hA : MeasurableSet A)
    (hE : MeasurableSet E) (fallback : U) (n : ℕ) :
    firstHitLaw μ A fallback n E =
      (Measure.pi (fun _ : Fin n ↦ μ)) (firstHitEvent A E fallback n) := by
  rw [firstHitLaw, Measure.map_apply (measurable_firstHit hA fallback n) hE,
    Measure.restrict_apply (hE.preimage (measurable_firstHit hA fallback n))]
  congr 1
  ext book
  exact and_comm

theorem firstHitLaw_univ_le (μ : Measure U) [IsProbabilityMeasure μ]
    {A : Set U} (hA : MeasurableSet A) (fallback : U) (n : ℕ) :
    firstHitLaw μ A fallback n Set.univ ≤ 1 := by
  rw [firstHitLaw_apply μ hA MeasurableSet.univ]
  exact prob_le_one

theorem firstHitLaw_univ_add_noHit (μ : Measure U) [IsProbabilityMeasure μ]
    {A : Set U} (hA : MeasurableSet A) (fallback : U) (n : ℕ) :
    firstHitLaw μ A fallback n Set.univ +
      (Measure.pi (fun _ : Fin n ↦ μ)) {book | ¬hasHit A book} = 1 := by
  rw [firstHitLaw_apply μ hA MeasurableSet.univ]
  have hevent : firstHitEvent A Set.univ fallback n = {book | hasHit A book} := by
    ext book
    simp [firstHitEvent]
  rw [hevent, ← measure_univ (μ := Measure.pi (fun _ : Fin n ↦ μ))]
  exact measure_add_measure_compl (measurableSet_hasHit hA n)

variable {S : Type*} [MeasurableSpace S]

theorem measurable_firstHit_section {A : Set (S × U)} (hA : MeasurableSet A)
    (fallback : U) (n : ℕ) :
    Measurable (fun p : S × (Fin n → U) ↦ firstHit {u | (p.1, u) ∈ A} fallback n p.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact Measurable.ite
        (hA.preimage (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)))
        ((measurable_pi_apply 0).comp measurable_snd)
        (ih.comp (measurable_fst.prodMk
          (measurable_pi_lambda _ (fun i ↦ (measurable_pi_apply i.succ).comp measurable_snd))))

theorem measurableSet_hasHit_section {A : Set (S × U)} (hA : MeasurableSet A) (n : ℕ) :
    MeasurableSet {p : S × (Fin n → U) | hasHit {u | (p.1, u) ∈ A} p.2} := by
  simp only [hasHit, Set.setOf_exists]
  exact MeasurableSet.iUnion (fun i ↦ hA.preimage
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))

noncomputable def firstHitKernel (μ : Measure U) [IsProbabilityMeasure μ]
    {A : Set (S × U)} (hA : MeasurableSet A) (fallback : U) (n : ℕ) : Kernel S U where
  toFun s := firstHitLaw μ {u | (s, u) ∈ A} fallback n
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    change Measurable (fun s : S ↦ firstHitLaw μ {u | (s, u) ∈ A} fallback n E)
    have hm : Measurable (fun s : S ↦ (Measure.pi (fun _ : Fin n ↦ μ))
        (firstHitEvent {u | (s, u) ∈ A} E fallback n)) :=
      measurable_measure_prodMk_left ((measurableSet_hasHit_section hA n).inter
        (hE.preimage (measurable_firstHit_section hA fallback n)))
    convert hm using 1
    funext s
    exact firstHitLaw_apply μ (hA.preimage measurable_prodMk_left) hE fallback n

theorem firstHitKernel_apply (μ : Measure U) [IsProbabilityMeasure μ]
    {A : Set (S × U)} (hA : MeasurableSet A) (fallback : U) (n : ℕ) (s : S) :
    firstHitKernel μ hA fallback n s = firstHitLaw μ {u | (s, u) ∈ A} fallback n := rfl

instance (μ : Measure U) [IsProbabilityMeasure μ]
    {A : Set (S × U)} (hA : MeasurableSet A) (fallback : U) (n : ℕ) :
    IsFiniteKernel (firstHitKernel μ hA fallback n) where
  exists_univ_le := ⟨1, ENNReal.one_lt_top, fun _ ↦
    firstHitLaw_univ_le μ (hA.preimage measurable_prodMk_left) fallback n⟩

end CapacityAtlas.MeasureBinning
