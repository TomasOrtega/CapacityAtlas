/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Asymptotic

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.MeasureBinning

open MeasureChannel

variable {S U X Y : Type*} [MeasurableSpace S] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]

theorem iidKernel_withDensity_base (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (f : X × Y → ℝ≥0∞) (hf : Measurable f)
    (hrow : ∀ x, κ x = μ.withDensity (fun y ↦ f (x, y))) (n : ℕ) (x : Fin n → X) :
    iidKernel κ n x = (Measure.pi (fun _ : Fin n ↦ μ)).withDensity
      (fun y ↦ ∏ i, f (x i, y i)) := by
  rw [iidKernel_apply]
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [lintegral_fin_prod (fun i : Fin n ↦ μ.restrict (s i))
    (fun i y ↦ f (x i, y)) (fun i ↦ hf.comp (measurable_const.prodMk measurable_id))]
  congr 1
  ext i
  rw [hrow, withDensity_apply _ (hs i)]

theorem iidKernel_expDensity_base (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {info : X × Y → ℝ} (hinfo : Measurable info)
    (hrow : ∀ x, κ x = μ.withDensity (fun y ↦ ENNReal.ofReal (Real.exp (info (x, y)))))
    (n : ℕ) (x : Fin n → X) :
    iidKernel κ n x = (Measure.pi (fun _ : Fin n ↦ μ)).withDensity
      (fun y ↦ iidLikelihood info n (x, y)) := by
  simp_rw [iidLikelihood_eq_prod]
  exact iidKernel_withDensity_base κ μ _ hinfo.exp.ennreal_ofReal hrow n x

noncomputable def blockChannel (κ : Kernel (S × X) Y) [IsMarkovKernel κ] (n : ℕ) :
    Kernel ((Fin n → S) × (Fin n → X)) (Fin n → Y) :=
  (iidKernel κ n).comap (pairBlock n) (measurable_pairBlock n)

instance (κ : Kernel (S × X) Y) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (blockChannel κ n) := by unfold blockChannel; infer_instance

def blockInput (input : S × U → X) (n : ℕ) (z : (Fin n → S) × (Fin n → U)) : Fin n → X :=
  fun i ↦ input (z.1 i, z.2 i)

theorem measurable_blockInput {input : S × U → X} (hinput : Measurable input) (n : ℕ) :
    Measurable (blockInput input n) :=
  measurable_pi_lambda _ (fun i ↦ hinput.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)))

noncomputable def auxiliaryChannel (κ : Kernel (S × X) Y) (input : S × U → X)
    (hinput : Measurable input) : Kernel (S × U) Y :=
  κ.comap (fun z ↦ (z.1, input z)) (measurable_fst.prodMk hinput)

instance (κ : Kernel (S × X) Y) [IsMarkovKernel κ] (input : S × U → X)
    (hinput : Measurable input) : IsMarkovKernel (auxiliaryChannel κ input hinput) := by
  unfold auxiliaryChannel
  infer_instance

theorem blockChannel_input_eq (κ : Kernel (S × X) Y) [IsMarkovKernel κ]
    (input : S × U → X) (hinput : Measurable input) (n : ℕ)
    (z : (Fin n → S) × (Fin n → U)) :
    blockChannel κ n (z.1, blockInput input n z) =
      iidKernel (auxiliaryChannel κ input hinput) n (pairBlock n z) := rfl

theorem iid_conditionalMiss_tendsto_zero
    (κ : Kernel (S × X) Y) [IsMarkovKernel κ]
    (σ : Measure S) [IsProbabilityMeasure σ] (η : Kernel S U) [IsMarkovKernel η]
    (input : S × U → X) (hinput : Measurable input)
    {info : U × Y → ℝ} (hinfo : Measurable info)
    (hinfoLp : MemLp (fun p : (S × U) × Y ↦ info (p.1.2, p.2)) 2
      ((σ ⊗ₘ η) ⊗ₘ auxiliaryChannel κ input hinput))
    {d : ℝ} (hd : d < ∫ p, info (p.1.2, p.2) ∂((σ ⊗ₘ η) ⊗ₘ auxiliaryChannel κ input hinput)) :
    Tendsto (fun n : ℕ ↦ ∫⁻ z, conditionalMiss (blockChannel κ n) (blockInput input n)
      {p | ENNReal.ofReal (Real.exp ((n : ℝ) * d)) < iidLikelihood info n p} z
      ∂((Measure.pi (fun _ : Fin n ↦ σ)) ⊗ₘ iidKernel η n)) atTop (𝓝 0) := by
  let K := auxiliaryChannel κ input hinput
  let J : (S × U) × Y → ℝ := fun p ↦ info (p.1.2, p.2)
  have hJ : Measurable J := hinfo.comp (measurable_fst.snd.prodMk measurable_snd)
  have heq (n : ℕ) :
      (∫⁻ z, conditionalMiss (blockChannel κ n) (blockInput input n)
        {p | ENNReal.ofReal (Real.exp ((n : ℝ) * d)) < iidLikelihood info n p} z
        ∂((Measure.pi (fun _ : Fin n ↦ σ)) ⊗ₘ iidKernel η n)) =
      ∫⁻ x, iidKernel K n x
        {y | iidLikelihood J n (x, y) ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * d))}
        ∂Measure.pi (fun _ : Fin n ↦ σ ⊗ₘ η) := by
    have hevent : MeasurableSet {p | iidLikelihood J n p ≤
        ENNReal.ofReal (Real.exp ((n : ℝ) * d))} :=
      measurableSet_le (measurable_iidLikelihood hJ n) measurable_const
    have hm : Measurable (fun x ↦ iidKernel K n x
        {y | iidLikelihood J n (x, y) ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * d))}) :=
      Kernel.measurable_kernel_prodMk_left hevent
    rw [← iidKernel_joint η σ n, lintegral_map hm (measurable_pairBlock n)]
    apply lintegral_congr
    intro z
    unfold conditionalMiss
    rw [blockChannel_input_eq κ input hinput n z]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, not_lt]
    rfl
  simp_rw [heq]
  exact likelihood_tail_tendsto_zero_of_iid_joint (iidKernel K) (σ ⊗ₘ η)
    ((σ ⊗ₘ η) ⊗ₘ K) (iidKernel_joint K (σ ⊗ₘ η)) hJ hinfoLp hd

theorem iid_joint_measure_event
    (σ : Measure S) [IsProbabilityMeasure σ] (η : Kernel S U) [IsMarkovKernel η]
    (n : ℕ) (E : Set (Fin n → S × U)) (hE : MeasurableSet E) :
    ((Measure.pi (fun _ : Fin n ↦ σ)) ⊗ₘ iidKernel η n) {z | pairBlock n z ∈ E} =
      (Measure.pi (fun _ : Fin n ↦ σ ⊗ₘ η)) E := by
  rw [← iidKernel_joint η σ n, Measure.map_apply (measurable_pairBlock n) hE]
  rfl

theorem iid_joint_upperTail_tendsto_zero
    (σ : Measure S) [IsProbabilityMeasure σ] (η : Kernel S U) [IsMarkovKernel η]
    {Z : S × U → ℝ} (hZ : Measurable Z) (hZLp : MemLp Z 2 (σ ⊗ₘ η))
    {a : ℝ} (ha : (∫ z, Z z ∂(σ ⊗ₘ η)) < a) :
    Tendsto (fun n : ℕ ↦ ((Measure.pi (fun _ : Fin n ↦ σ)) ⊗ₘ iidKernel η n)
      {z | (n : ℝ) * a ≤ iidSum Z n (pairBlock n z)}) atTop (𝓝 0) := by
  have heq (n : ℕ) :
      ((Measure.pi (fun _ : Fin n ↦ σ)) ⊗ₘ iidKernel η n)
        {z | (n : ℝ) * a ≤ iidSum Z n (pairBlock n z)} =
      (Measure.pi (fun _ : Fin n ↦ σ ⊗ₘ η)) {z | (n : ℝ) * a ≤ iidSum Z n z} :=
    iid_joint_measure_event σ η n _ (measurableSet_le measurable_const
      (Finset.measurable_sum _ (fun i _ ↦ hZ.comp (measurable_pi_apply i))))
  simp_rw [heq]
  exact iidSum_upperTail_tendsto_zero (σ ⊗ₘ η) hZLp ha

theorem iid_joint_exponential_upperTail_tendsto_zero
    (σ : Measure S) [IsProbabilityMeasure σ] (η : Kernel S U) [IsMarkovKernel η]
    {Z : S × U → ℝ} (hZ : Measurable Z) (hZLp : MemLp Z 2 (σ ⊗ₘ η))
    {a : ℝ} (ha : (∫ z, Z z ∂(σ ⊗ₘ η)) < a) :
    Tendsto (fun n : ℕ ↦ ((Measure.pi (fun _ : Fin n ↦ σ)) ⊗ₘ iidKernel η n)
      {z | ENNReal.ofReal (Real.exp ((n : ℝ) * a)) < iidLikelihood Z n z}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (iid_joint_upperTail_tendsto_zero σ η hZ hZLp ha) (fun _ ↦ zero_le)
  intro n
  apply measure_mono
  intro z hz
  change ENNReal.ofReal (Real.exp ((n : ℝ) * a)) <
    ENNReal.ofReal (Real.exp (iidSum Z n (pairBlock n z))) at hz
  exact (Real.exp_lt_exp.mp ((ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).mp hz)).le

theorem iid_joint_cost_rejection_tendsto_zero
    (σ : Measure S) [IsProbabilityMeasure σ] (η : Kernel S U) [IsMarkovKernel η]
    {cost : S × U → ℝ} (hcost : Measurable cost) (hcostLp : MemLp cost 2 (σ ⊗ₘ η))
    {P : ℝ} (hP : (∫ z, cost z ∂(σ ⊗ₘ η)) < P) :
    Tendsto (fun n : ℕ ↦ ((Measure.pi (fun _ : Fin n ↦ σ)) ⊗ₘ iidKernel η n)
      {z | ¬iidSum cost n (pairBlock n z) ≤ (n : ℝ) * P}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (iid_joint_upperTail_tendsto_zero σ η hcost hcostLp hP) (fun _ ↦ zero_le)
  intro n
  apply measure_mono
  intro z hz
  exact (not_le.mp (show ¬iidSum cost n (pairBlock n z) ≤ (n : ℝ) * P from hz)).le

end CapacityAtlas.MeasureBinning
