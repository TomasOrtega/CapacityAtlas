/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding.Asymptotic
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding.IID

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.MeasureChannel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def pairBlock (n : ℕ) (xy : (Fin n → X) × (Fin n → Y)) : Fin n → X × Y :=
  fun i ↦ (xy.1 i, xy.2 i)

theorem measurable_pairBlock (n : ℕ) : Measurable (pairBlock (X := X) (Y := Y) n) := by
  exact measurable_pi_lambda _ (fun i ↦
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

noncomputable def iidLikelihood (info : X × Y → ℝ) (n : ℕ)
    (xy : (Fin n → X) × (Fin n → Y)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (iidSum info n (pairBlock n xy)))

theorem measurable_iidLikelihood {info : X × Y → ℝ} (hinfo : Measurable info) (n : ℕ) :
    Measurable (iidLikelihood info n) := by
  apply Measurable.ennreal_ofReal
  apply Measurable.exp
  exact Finset.measurable_sum _ (fun i _ ↦ hinfo.comp
    (((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)))

theorem likelihood_tail_tendsto_zero_of_iid_joint
    (κ : (n : ℕ) → Kernel (Fin n → X) (Fin n → Y)) [∀ n, IsMarkovKernel (κ n)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (X × Y)) [IsProbabilityMeasure ν]
    (hjoint : ∀ n, ((Measure.pi (fun _ : Fin n ↦ μ)) ⊗ₘ κ n).map (pairBlock n) =
      Measure.pi (fun _ : Fin n ↦ ν))
    {info : X × Y → ℝ} (hinfo : Measurable info) (hinfoLp : MemLp info 2 ν)
    {a : ℝ} (ha : a < ∫ z, info z ∂ν) :
    Tendsto (fun n ↦ ∫⁻ x, κ n x
      {y | iidLikelihood info n (x, y) ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * a))}
      ∂Measure.pi (fun _ : Fin n ↦ μ)) atTop (𝓝 0) := by
  have heq (n : ℕ) :
      (∫⁻ x, κ n x
        {y | iidLikelihood info n (x, y) ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * a))}
        ∂Measure.pi (fun _ : Fin n ↦ μ)) =
      (Measure.pi (fun _ : Fin n ↦ ν))
        {z | ENNReal.ofReal (Real.exp (iidSum info n z)) ≤
          ENNReal.ofReal (Real.exp ((n : ℝ) * a))} := by
    have hsum : Measurable (iidSum info n) :=
      Finset.measurable_sum _ (fun i _ ↦ hinfo.comp (measurable_pi_apply i))
    have hevent : MeasurableSet {z | ENNReal.ofReal (Real.exp (iidSum info n z)) ≤
        ENNReal.ofReal (Real.exp ((n : ℝ) * a))} :=
      measurableSet_le hsum.exp.ennreal_ofReal measurable_const
    rw [← hjoint n, Measure.map_apply (measurable_pairBlock n) hevent,
      Measure.compProd_apply (hevent.preimage (measurable_pairBlock n))]
    rfl
  simp_rw [heq]
  exact iidLikelihood_lowerTail_tendsto_zero ν hinfoLp ha

/-- The exact iid joint law and likelihood factorization yield codes with a cost constraint. -/
theorem exists_codes_of_iid_likelihood
    (κ : (n : ℕ) → Kernel (Fin n → X) (Fin n → Y)) [∀ n, IsMarkovKernel (κ n)]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure (X × Y)) [IsProbabilityMeasure ν]
    {info : X × Y → ℝ} (hinfo : Measurable info) (hinfoLp : MemLp info 2 ν)
    (hrow : ∀ n x, κ n x = (κ n ∘ₘ Measure.pi (fun _ : Fin n ↦ μ)).withDensity
      (fun y ↦ iidLikelihood info n (x, y)))
    (hjoint : ∀ n, ((Measure.pi (fun _ : Fin n ↦ μ)) ⊗ₘ κ n).map (pairBlock n) =
      Measure.pi (fun _ : Fin n ↦ ν))
    {cost : X → ℝ} (hcost : Measurable cost) (hcostLp : MemLp cost 2 μ)
    {P R : ℝ} (hP : (∫ x, cost x ∂μ) < P) (x₀ : X) (hx₀ : cost x₀ ≤ P)
    (hR : 0 ≤ R) (hRate : R * Real.log 2 < ∫ z, info z ∂ν) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      ∃ code : OneShotCode (Fin n → X) (Fin n → Y)
          (Fin (FiniteChannel.messageCountAtRate R n)),
        (∀ m, iidSum cost n (code.encode m) ≤ (n : ℝ) * P) ∧
          (averageError (κ n) code).toReal ≤ ε ∧
          R ≤ Real.logb 2 (FiniteChannel.messageCountAtRate R n : ℝ) / n := by
  obtain ⟨a, hRa, ha⟩ := exists_between hRate
  apply exists_codes_of_likelihood_tail_tendsto_zero κ
    (fun n ↦ Measure.pi (fun _ : Fin n ↦ μ)) (iidLikelihood info)
    (measurable_iidLikelihood hinfo) hrow
    (fun n ↦ {x | iidSum cost n x ≤ (n : ℝ) * P})
    (fun n ↦ measurableSet_le
      (Finset.measurable_sum _ (fun i _ ↦ hcost.comp (measurable_pi_apply i))) measurable_const)
    (fun n ↦ ⟨fun _ ↦ x₀, ?_⟩) hR hRa
    (likelihood_tail_tendsto_zero_of_iid_joint κ μ ν hjoint hinfo hinfoLp ha)
    (iidCost_rejection_tendsto_zero μ hcostLp hP)
  change iidSum cost n (fun _ ↦ x₀) ≤ (n : ℝ) * P
  simp only [iidSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  gcongr

end CapacityAtlas.MeasureChannel
