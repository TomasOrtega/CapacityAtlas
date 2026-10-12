/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding.Tensor

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CapacityAtlas.MeasureBinning

open MeasureChannel

variable {S U L : Type*} [MeasurableSpace S] [MeasurableSpace U]

theorem firstAccepted_accepts {A I : Type*} (accept : I → A → Prop) (fallback : I)
    {ls : List I} {a : A} (hex : ∃ i ∈ ls, accept i a) :
    accept (firstAccepted accept fallback ls a) a := by
  induction ls with
  | nil => simp at hex
  | cons i ls ih =>
      by_cases hi : accept i a
      · simp [firstAccepted, hi]
      · simp only [firstAccepted, if_neg hi]
        apply ih
        simpa only [List.mem_cons, exists_eq_or_imp, hi, false_or] using hex

variable [Fintype L] [Nonempty L]

noncomputable def selectIndex (B : Set (S × U)) (book : L → U) (s : S) : L :=
  firstAccepted (fun l s ↦ (s, book l) ∈ B) (Classical.choice inferInstance)
    Finset.univ.toList s

noncomputable def selectAux (B : Set (S × U)) (book : L → U) (s : S) : U :=
  book (selectIndex B book s)

def coveringFailure (B : Set (S × U)) (book : L → U) (s : S) : Prop :=
  ∀ l, (s, book l) ∉ B

omit [MeasurableSpace S] [MeasurableSpace U] in
theorem selectAux_mem (B : Set (S × U)) {book : L → U} {s : S}
    (h : ¬coveringFailure B book s) : (s, selectAux B book s) ∈ B := by
  exact firstAccepted_accepts (fun l t ↦ (t, book l) ∈ B) (Classical.choice inferInstance)
    (by simpa [coveringFailure] using h)

theorem measurable_selectIndex [MeasurableSpace L]
    {B : Set (S × U)} (hB : MeasurableSet B) :
    Measurable (fun p : (L → U) × S ↦ selectIndex B p.1 p.2) := by
  unfold selectIndex
  have haux (ls : List L) : Measurable (fun p : (L → U) × S ↦
      firstAccepted (fun l s ↦ (s, p.1 l) ∈ B) (Classical.choice inferInstance) ls p.2) := by
    induction ls with
    | nil => exact measurable_const
    | cons l ls ih =>
        exact Measurable.ite
          (hB.preimage (measurable_snd.prodMk ((measurable_pi_apply l).comp measurable_fst)))
          measurable_const ih
  exact haux _

theorem measurable_selectAux {B : Set (S × U)} (hB : MeasurableSet B) :
    Measurable (fun p : (L → U) × S ↦ selectAux B p.1 p.2) := by
  have haux (ls : List L) : Measurable (fun p : (L → U) × S ↦
      p.1 (firstAccepted (fun l s ↦ (s, p.1 l) ∈ B)
        (Classical.choice inferInstance) ls p.2)) := by
    induction ls with
    | nil => exact (measurable_pi_apply _).comp measurable_fst
    | cons l ls ih =>
        change Measurable (fun p : (L → U) × S ↦
          p.1 (if (p.2, p.1 l) ∈ B then l else
            firstAccepted (fun j s ↦ (s, p.1 j) ∈ B)
              (Classical.choice inferInstance) ls p.2))
        simp_rw [apply_ite]
        exact Measurable.ite
          (hB.preimage (measurable_snd.prodMk ((measurable_pi_apply l).comp measurable_fst)))
          ((measurable_pi_apply l).comp measurable_fst) ih
  exact haux _

omit [Nonempty L] in
theorem measurableSet_coveringFailure {B : Set (S × U)} (hB : MeasurableSet B) :
    MeasurableSet {p : (L → U) × S | coveringFailure B p.1 p.2} := by
  simp only [coveringFailure, Set.setOf_forall]
  exact MeasurableSet.iInter (fun l ↦ (hB.preimage
    (measurable_snd.prodMk ((measurable_pi_apply l).comp measurable_fst))).compl)

omit [MeasurableSpace S] [Nonempty L] in
theorem measure_coveringFailure (μ : Measure U) [IsProbabilityMeasure μ]
    (B : Set (S × U)) (s : S) :
    (Measure.pi (fun _ : L ↦ μ)) {book | coveringFailure B book s} =
      (μ {u | (s, u) ∉ B}) ^ Fintype.card L := by
  have hevent : {book : L → U | coveringFailure B book s} =
      Set.univ.pi (fun _ : L ↦ {u | (s, u) ∉ B}) := by
    ext book
    simp [coveringFailure]
  rw [hevent, Measure.pi_pi]
  simp

omit [Nonempty L] in
theorem measure_coveringFailure_le_exp (μ : Measure U) [IsProbabilityMeasure μ]
    {B : Set (S × U)} (hB : MeasurableSet B) (s : S) {p : ℝ}
    (hp : p ≤ (μ {u | (s, u) ∈ B}).toReal) :
    (Measure.pi (fun _ : L ↦ μ)) {book | coveringFailure B book s} ≤
      ENNReal.ofReal (Real.exp (-((Fintype.card L : ℝ) * p))) := by
  rw [measure_coveringFailure]
  have hsection : MeasurableSet {u | (s, u) ∈ B} := hB.preimage measurable_prodMk_left
  have hcompl : μ {u | (s, u) ∉ B} = 1 - μ {u | (s, u) ∈ B} := by
    exact (measure_compl hsection (measure_ne_top μ _)).trans (by rw [measure_univ])
  have htoReal : (μ {u | (s, u) ∉ B}).toReal = 1 - (μ {u | (s, u) ∈ B}).toReal := by
    rw [hcompl, ENNReal.toReal_sub_of_le (prob_le_one) ENNReal.one_ne_top,
      ENNReal.toReal_one]
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {u | (s, u) ∉ B}),
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.exp (-p)) ^ Fintype.card L := by
      apply pow_le_pow_left₀ ENNReal.toReal_nonneg
      rw [htoReal]
      exact (by linarith : 1 - (μ {u | (s, u) ∈ B}).toReal ≤ 1 - p).trans
        (Real.one_sub_le_exp_neg p)
    _ = _ := by rw [← Real.exp_nat_mul, mul_neg]

omit [Fintype L] [Nonempty L] in
theorem acceptanceMass_le_mul (η : Kernel S U) (μ : Measure U)
    (g : S × U → ℝ≥0∞)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    {B : Set (S × U)} (hB : MeasurableSet B) {T : ℝ≥0∞}
    (hcut : ∀ z ∈ B, g z ≤ T) (s : S) :
    η s {u | (s, u) ∈ B} ≤ T * μ {u | (s, u) ∈ B} := by
  have hsection : MeasurableSet {u | (s, u) ∈ B} := hB.preimage measurable_prodMk_left
  rw [hrow, withDensity_apply _ hsection]
  calc
    _ ≤ ∫⁻ u in {u | (s, u) ∈ B}, T ∂μ :=
      setLIntegral_mono measurable_const (fun u hu ↦ hcut (s, u) hu)
    _ = _ := by simp

omit [Nonempty L] in
theorem measure_coveringFailure_le_exp_of_density
    (η : Kernel S U) (μ : Measure U) [IsProbabilityMeasure μ]
    (g : S × U → ℝ≥0∞)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    {B : Set (S × U)} (hB : MeasurableSet B) {T q : ℝ} (hT : 0 < T) (hq : 0 ≤ q)
    (hcut : ∀ z ∈ B, g z ≤ ENNReal.ofReal T) (s : S)
    (hmass : ENNReal.ofReal q ≤ η s {u | (s, u) ∈ B}) :
    (Measure.pi (fun _ : L ↦ μ)) {book | coveringFailure B book s} ≤
      ENNReal.ofReal (Real.exp (-((Fintype.card L : ℝ) * (q / T)))) := by
  apply measure_coveringFailure_le_exp μ hB s
  have hlower : ENNReal.ofReal (q / T) ≤ μ {u | (s, u) ∈ B} := by
    rw [ENNReal.ofReal_div_of_pos hT]
    exact ENNReal.div_le_of_le_mul' (hmass.trans (acceptanceMass_le_mul η μ g hrow hB hcut s))
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hlower
  simpa only [ENNReal.toReal_ofReal (div_nonneg hq hT.le)] using hreal

omit [Nonempty L] in
theorem measure_coveringFailure_le_rejection_add_exp
    (η : Kernel S U) [IsMarkovKernel η] (μ : Measure U) [IsProbabilityMeasure μ]
    (g : S × U → ℝ≥0∞)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    {B : Set (S × U)} (hB : MeasurableSet B) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ z ∈ B, g z ≤ ENNReal.ofReal T) (s : S) :
    (Measure.pi (fun _ : L ↦ μ)) {book | coveringFailure B book s} ≤
      2 * η s {u | (s, u) ∉ B} +
        ENNReal.ofReal (Real.exp (-((Fintype.card L : ℝ) * ((1 / 2) / T)))) := by
  by_cases hgood : ENNReal.ofReal (1 / 2 : ℝ) ≤ η s {u | (s, u) ∈ B}
  · exact (measure_coveringFailure_le_exp_of_density η μ g hrow hB hT
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hcut s hgood).trans (le_add_left le_rfl)
  · have hbad : η s {u | (s, u) ∈ B} ≤ ENNReal.ofReal (1 / 2 : ℝ) :=
      (lt_of_not_ge hgood).le
    have hsection : MeasurableSet {u | (s, u) ∈ B} := hB.preimage measurable_prodMk_left
    have hrej : ENNReal.ofReal (1 / 2 : ℝ) ≤ η s {u | (s, u) ∉ B} := by
      have hcomp := measure_compl hsection (measure_ne_top (η s) _)
      change η s {u | (s, u) ∉ B} = _ at hcomp
      rw [hcomp, measure_univ]
      have hhalf : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 2 : ℝ) =
          ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num)]
        norm_num
      rw [← hhalf]
      exact tsub_le_tsub_left hbad 1
    have hbound : (1 : ℝ≥0∞) ≤ 2 * η s {u | (s, u) ∉ B} := by
      calc
        _ = 2 * ENNReal.ofReal (1 / 2 : ℝ) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
            ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        _ ≤ _ := mul_le_mul_right hrej 2
    exact prob_le_one.trans (hbound.trans (le_add_right le_rfl))

omit [Nonempty L] in
theorem lintegral_coveringFailure_le
    (σ : Measure S) [IsProbabilityMeasure σ]
    (η : Kernel S U) [IsMarkovKernel η] (μ : Measure U) [IsProbabilityMeasure μ]
    (g : S × U → ℝ≥0∞)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    {B : Set (S × U)} (hB : MeasurableSet B) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ z ∈ B, g z ≤ ENNReal.ofReal T) :
    (∫⁻ s, (Measure.pi (fun _ : L ↦ μ)) {book | coveringFailure B book s} ∂σ) ≤
      2 * (σ ⊗ₘ η) Bᶜ +
        ENNReal.ofReal (Real.exp (-((Fintype.card L : ℝ) * ((1 / 2) / T)))) := by
  have hrej : Measurable (fun s ↦ η s {u | (s, u) ∉ B}) :=
    Kernel.measurable_kernel_prodMk_left hB.compl
  have h2rej : Measurable (fun s ↦ 2 * η s {u | (s, u) ∉ B}) :=
    measurable_const.mul hrej
  calc
    _ ≤ ∫⁻ s, 2 * η s {u | (s, u) ∉ B} +
        ENNReal.ofReal (Real.exp (-((Fintype.card L : ℝ) * ((1 / 2) / T)))) ∂σ :=
      lintegral_mono (measure_coveringFailure_le_rejection_add_exp η μ g hrow hB hT hcut)
    _ = _ := by
      rw [lintegral_add_left h2rej,
        lintegral_const_mul _ hrej, Measure.compProd_apply hB.compl]
      simp
      rfl

omit [Nonempty L] in
theorem exists_covering_book
    (σ : Measure S) [IsProbabilityMeasure σ]
    (η : Kernel S U) [IsMarkovKernel η] (μ : Measure U) [IsProbabilityMeasure μ]
    (g : S × U → ℝ≥0∞)
    (hrow : ∀ s, η s = μ.withDensity (fun u ↦ g (s, u)))
    {B : Set (S × U)} (hB : MeasurableSet B) {T : ℝ} (hT : 0 < T)
    (hcut : ∀ z ∈ B, g z ≤ ENNReal.ofReal T) :
    ∃ book : L → U, σ {s | coveringFailure B book s} ≤
      2 * (σ ⊗ₘ η) Bᶜ +
        ENNReal.ofReal (Real.exp (-((Fintype.card L : ℝ) * ((1 / 2) / T)))) := by
  have hfail := measurableSet_coveringFailure (L := L) hB
  have hm : Measurable (fun book : L → U ↦ σ {s | coveringFailure B book s}) :=
    measurable_measure_prodMk_left hfail
  obtain ⟨book, hbook⟩ := exists_le_lintegral (μ := Measure.pi (fun _ : L ↦ μ)) hm.aemeasurable
  refine ⟨book, hbook.trans ?_⟩
  have hswap : (∫⁻ book : L → U, σ {s | coveringFailure B book s}
      ∂Measure.pi (fun _ : L ↦ μ)) =
      ∫⁻ s, (Measure.pi (fun _ : L ↦ μ)) {book | coveringFailure B book s} ∂σ := by
    calc
      _ = (Measure.pi (fun _ : L ↦ μ)).prod σ {p | coveringFailure B p.1 p.2} :=
        (Measure.prod_apply hfail).symm
      _ = _ := Measure.prod_apply_symm hfail
  rw [hswap]
  exact lintegral_coveringFailure_le σ η μ g hrow hB hT hcut

end CapacityAtlas.MeasureBinning
