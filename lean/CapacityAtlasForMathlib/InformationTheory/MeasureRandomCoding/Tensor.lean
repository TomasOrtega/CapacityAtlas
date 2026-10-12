/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding.IIDCoding
import Mathlib.Probability.Kernel.WithDensity

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.MeasureChannel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem measurable_iidKernel (κ : Kernel X Y) [IsMarkovKernel κ] (n : ℕ) :
    Measurable (fun x : Fin n → X ↦ Measure.pi (fun i ↦ κ (x i))) := by
  apply Measure.measurable_of_measurable_coe
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ ↦ Measurable (fun x : Fin n → X ↦ Measure.pi (fun i ↦ κ (x i)) s))
    generateFrom_pi.symm isPiSystem_pi (by simp) (fun s hs ↦ ?_)
    (fun s hs hmeas ↦ ?_) (fun s hdisj hs hmeas ↦ ?_)
  · rcases hs with ⟨t, ht, rfl⟩
    simp_rw [Measure.pi_pi]
    exact Finset.measurable_prod _ (fun i _ ↦
      (κ.measurable_coe (ht i (Set.mem_univ _))).comp (measurable_pi_apply i))
  · simpa only [measure_compl hs (measure_ne_top _ _), measure_univ] using
      Measurable.const_sub hmeas 1
  · simpa only [measure_iUnion hdisj hs] using Measurable.tsum hmeas

noncomputable def iidKernel (κ : Kernel X Y) [IsMarkovKernel κ] (n : ℕ) :
    Kernel (Fin n → X) (Fin n → Y) where
  toFun x := Measure.pi (fun i ↦ κ (x i))
  measurable' := measurable_iidKernel κ n

theorem iidKernel_apply (κ : Kernel X Y) [IsMarkovKernel κ] (n : ℕ) (x : Fin n → X) :
    iidKernel κ n x = Measure.pi (fun i ↦ κ (x i)) := rfl

instance (κ : Kernel X Y) [IsMarkovKernel κ] (n : ℕ) : IsMarkovKernel (iidKernel κ n) where
  isProbabilityMeasure x := by rw [iidKernel_apply]; infer_instance

theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : (i : Fin n) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E i.succ),
            f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
            ∂(μ 0).prod (Measure.pi (fun i ↦ μ i.succ)) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
          rfl
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f i.succ x ∂μ i.succ := by
          have htail : Measurable (fun x : (i : Fin n) → E i.succ ↦
              ∏ i, f i.succ (x i)) :=
            Finset.measurable_prod _ (fun i _ ↦ (hf i.succ).comp (measurable_pi_apply i))
          rw [lintegral_prod_mul (hf 0).aemeasurable htail.aemeasurable,
            ih (fun i ↦ μ i.succ) (fun i ↦ f i.succ) (fun i ↦ hf i.succ)]
        _ = _ := by rw [Fin.prod_univ_succ]

theorem iidKernel_output (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    iidKernel κ n ∘ₘ Measure.pi (fun _ : Fin n ↦ μ) =
      Measure.pi (fun _ : Fin n ↦ κ ∘ₘ μ) := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) (iidKernel κ n).aemeasurable]
  simp_rw [iidKernel_apply, Measure.pi_pi]
  rw [lintegral_fin_prod (fun _ : Fin n ↦ μ) (fun i x ↦ κ x (s i))
    (fun i ↦ κ.measurable_coe (hs i))]
  simp_rw [Measure.bind_apply (hs _) κ.aemeasurable]

theorem iidKernel_joint (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    ((Measure.pi (fun _ : Fin n ↦ μ)) ⊗ₘ iidKernel κ n).map (pairBlock n) =
      Measure.pi (fun _ : Fin n ↦ μ ⊗ₘ κ) := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [Measure.map_apply (measurable_pairBlock n) (MeasurableSet.univ_pi hs),
    Measure.compProd_apply ((MeasurableSet.univ_pi hs).preimage (measurable_pairBlock n))]
  have hsection (x : Fin n → X) :
      Prod.mk x ⁻¹' (pairBlock n ⁻¹' Set.univ.pi s) =
        Set.univ.pi (fun i ↦ Prod.mk (x i) ⁻¹' s i) := by
    ext y
    simp [pairBlock]
  simp_rw [hsection, iidKernel_apply, Measure.pi_pi]
  rw [lintegral_fin_prod (fun _ : Fin n ↦ μ)
    (fun i x ↦ κ x (Prod.mk x ⁻¹' s i))
    (fun i ↦ Kernel.measurable_kernel_prodMk_left (hs i))]
  simp_rw [Measure.compProd_apply (hs _)]

theorem iidKernel_withDensity (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X × Y → ℝ≥0∞) (hf : Measurable f)
    (hrow : ∀ x, κ x = (κ ∘ₘ μ).withDensity (fun y ↦ f (x, y)))
    (n : ℕ) (x : Fin n → X) :
    iidKernel κ n x = (iidKernel κ n ∘ₘ Measure.pi (fun _ : Fin n ↦ μ)).withDensity
      (fun y ↦ ∏ i, f (x i, y i)) := by
  rw [iidKernel_output, iidKernel_apply]
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [lintegral_fin_prod (fun i : Fin n ↦ (κ ∘ₘ μ).restrict (s i))
    (fun i y ↦ f (x i, y)) (fun i ↦ hf.comp (measurable_const.prodMk measurable_id))]
  congr 1
  ext i
  rw [hrow, withDensity_apply _ (hs i)]

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem iidLikelihood_eq_prod (info : X × Y → ℝ) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) :
    iidLikelihood info n (x, y) = ∏ i, ENNReal.ofReal (Real.exp (info (x i, y i))) := by
  unfold iidLikelihood iidSum pairBlock
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le)]

theorem iidKernel_likelihood (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {info : X × Y → ℝ} (hinfo : Measurable info)
    (hrow : ∀ x, κ x = (κ ∘ₘ μ).withDensity
      (fun y ↦ ENNReal.ofReal (Real.exp (info (x, y))))) (n : ℕ) (x : Fin n → X) :
    iidKernel κ n x = (iidKernel κ n ∘ₘ Measure.pi (fun _ : Fin n ↦ μ)).withDensity
      (fun y ↦ iidLikelihood info n (x, y)) := by
  simp_rw [iidLikelihood_eq_prod]
  exact iidKernel_withDensity κ μ _ hinfo.exp.ennreal_ofReal hrow n x

/-- A memoryless measurable channel admits codes below the mean log likelihood, with cost slack. -/
theorem exists_codes_of_memoryless_likelihood
    (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [IsProbabilityMeasure μ]
    {info : X × Y → ℝ} (hinfo : Measurable info) (hinfoLp : MemLp info 2 (μ ⊗ₘ κ))
    (hrow : ∀ x, κ x = (κ ∘ₘ μ).withDensity
      (fun y ↦ ENNReal.ofReal (Real.exp (info (x, y)))))
    {cost : X → ℝ} (hcost : Measurable cost) (hcostLp : MemLp cost 2 μ)
    {P R : ℝ} (hP : (∫ x, cost x ∂μ) < P) (x₀ : X) (hx₀ : cost x₀ ≤ P)
    (hR : 0 ≤ R) (hRate : R * Real.log 2 < ∫ z, info z ∂(μ ⊗ₘ κ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      ∃ code : OneShotCode (Fin n → X) (Fin n → Y)
          (Fin (FiniteChannel.messageCountAtRate R n)),
        (∀ m, iidSum cost n (code.encode m) ≤ (n : ℝ) * P) ∧
          (averageError (iidKernel κ n) code).toReal ≤ ε ∧
          R ≤ Real.logb 2 (FiniteChannel.messageCountAtRate R n : ℝ) / n :=
  exists_codes_of_iid_likelihood (iidKernel κ) μ (μ ⊗ₘ κ) hinfo hinfoLp
    (iidKernel_likelihood κ μ hinfo hrow) (iidKernel_joint κ μ)
    hcost hcostLp hP x₀ hx₀ hR hRate

end CapacityAtlas.MeasureChannel
