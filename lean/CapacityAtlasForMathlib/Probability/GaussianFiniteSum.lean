/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Probability.GaussianChannel
import Mathlib.Probability.Independence.CharacteristicFunction

open MeasureTheory Matrix
open scoped BigOperators

namespace ProbabilityTheory

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

theorem iIndepFun.map_finsetSum_multivariateGaussian
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : κ → Ω → EuclideanSpace ℝ ι)
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (Q : κ → Matrix ι ι ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (hLaw : ∀ i, μ.map (X i) = multivariateGaussian 0 (Q i)) (s : Finset κ) :
    μ.map (fun ω ↦ ∑ i ∈ s, X i ω) = multivariateGaussian 0 (∑ i ∈ s, Q i) := by
  apply Measure.ext_of_charFun
  ext t
  rw [(hInd.restrict s).charFun_map_fun_finsetSum_eq_prod (fun i _ ↦ (hX i).aemeasurable)]
  simp only [Finset.prod_apply]
  simp_rw [hLaw, charFun_multivariateGaussian (hQ _)]
  rw [charFun_multivariateGaussian (posSemidef_sum s (fun i _ ↦ hQ i))]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  simp only [sum_mulVec, dotProduct_sum, Complex.ofReal_sum, Finset.sum_div,
    Finset.sum_neg_distrib]

theorem map_finsetSum_pi_multivariateGaussian [Fintype κ]
    (Q : κ → Matrix ι ι ℝ) (hQ : ∀ i, (Q i).PosSemidef) (s : Finset κ) :
    (Measure.pi (fun i ↦ multivariateGaussian 0 (Q i))).map (fun x ↦ ∑ i ∈ s, x i) =
      multivariateGaussian 0 (∑ i ∈ s, Q i) := by
  refine iIndepFun.map_finsetSum_multivariateGaussian _
    (fun i (x : κ → EuclideanSpace ℝ ι) ↦ x i)
    (fun i ↦ measurable_pi_apply i) (iIndepFun_pi (fun _ ↦ aemeasurable_id)) Q hQ ?_ s
  intro i
  exact (measurePreserving_eval _ i).map_eq

theorem iIndepFun.indepFun_disjoint_finsetSum
    {E : Type*} [MeasurableSpace E] [AddCommMonoid E] [MeasurableAdd₂ E]
    {X : κ → Ω → E} {μ : Measure Ω} (hInd : iIndepFun X μ)
    (hX : ∀ i, Measurable (X i)) (s t : Finset κ) (hst : Disjoint s t) :
    IndepFun (fun ω ↦ ∑ i ∈ s, X i ω) (fun ω ↦ ∑ i ∈ t, X i ω) μ := by
  have h := (hInd.indepFun_finset s t hst hX).comp
    (show Measurable (fun x : s → E ↦ ∑ i, x i) by fun_prop)
    (show Measurable (fun x : t → E ↦ ∑ i, x i) by fun_prop)
  convert h using 1
  · funext ω
    exact (Finset.sum_coe_sort s (fun i ↦ X i ω)).symm
  · funext ω
    exact (Finset.sum_coe_sort t (fun i ↦ X i ω)).symm

theorem iIndepFun.indepFun_coordinate_sum_sum
    {E : Type*} [MeasurableSpace E] [AddCommMonoid E] [MeasurableAdd₂ E]
    {X : κ → Ω → E} {μ : Measure Ω} (hInd : iIndepFun X μ)
    (hX : ∀ i, Measurable (X i)) (s t : Finset κ) (hst : Disjoint s t)
    (k : κ) (hkt : k ∉ t) :
    IndepFun (fun ω ↦ (X k ω, ∑ i ∈ s, X i ω)) (fun ω ↦ ∑ i ∈ t, X i ω) μ := by
  classical
  have hd : Disjoint (insert k s) t := Finset.disjoint_insert_left.mpr ⟨hkt, hst⟩
  let f : (↥(insert k s) → E) → E × E := fun x ↦
    (x ⟨k, Finset.mem_insert_self k s⟩,
      ∑ i : s, x ⟨i, Finset.mem_insert_of_mem i.property⟩)
  have hf : Measurable f := by unfold f; fun_prop
  have h := (hInd.indepFun_finset (insert k s) t hd hX).comp hf
    (show Measurable (fun x : t → E ↦ ∑ i, x i) by fun_prop)
  convert h using 1
  · funext ω
    exact congrArg (Prod.mk (X k ω)) (Finset.sum_coe_sort s (fun i ↦ X i ω)).symm
  · funext ω
    exact (Finset.sum_coe_sort t (fun i ↦ X i ω)).symm

theorem map_coordinate_sum_sum_pi_multivariateGaussian [Fintype κ]
    (Q : κ → Matrix ι ι ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (s t : Finset κ) (hst : Disjoint s t) (k : κ) (hks : k ∉ s) (hkt : k ∉ t) :
    (Measure.pi (fun i ↦ multivariateGaussian 0 (Q i))).map
      (fun x ↦ ((x k, ∑ i ∈ s, x i), ∑ i ∈ t, x i)) =
      ((multivariateGaussian 0 (Q k)).prod (multivariateGaussian 0 (∑ i ∈ s, Q i))).prod
        (multivariateGaussian 0 (∑ i ∈ t, Q i)) := by
  let μ := Measure.pi (fun i ↦ multivariateGaussian 0 (Q i))
  have hInd : iIndepFun (fun i (x : κ → EuclideanSpace ℝ ι) ↦ x i) μ :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hgroupInd := hInd.indepFun_coordinate_sum_sum (fun i ↦ measurable_pi_apply i) s t hst k hkt
  have hgroups := hgroupInd.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  rw [hgroups]
  have hpair := (hInd.indepFun_finsetSum_of_notMem (fun i ↦ measurable_pi_apply i) hks).symm
  have hpair' : IndepFun (fun x : κ → EuclideanSpace ℝ ι ↦ x k)
      (fun x ↦ ∑ i ∈ s, x i) μ := by
    convert hpair using 1
    funext x
    simp only [Finset.sum_apply]
  have hp : μ.map (fun x ↦ (x k, ∑ i ∈ s, x i)) =
      (μ.map (fun x ↦ x k)).prod (μ.map (fun x ↦ ∑ i ∈ s, x i)) :=
    hpair'.map_prod_eq_prod_map_map (measurable_pi_apply k).aemeasurable (by fun_prop)
  rw [hp, (measurePreserving_eval (fun i ↦ multivariateGaussian 0 (Q i)) k).map_eq,
    map_finsetSum_pi_multivariateGaussian Q hQ s, map_finsetSum_pi_multivariateGaussian Q hQ t]

end ProbabilityTheory
