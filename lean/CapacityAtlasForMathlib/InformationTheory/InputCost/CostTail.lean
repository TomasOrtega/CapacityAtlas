/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.

Adapted from TomasOrtega/CapacityAtlasInputCost, commit 5e6a432bc276aa4e08b7f27658daf40e029cda48,
CapacityAtlasCost/CostTail.lean. Imports and certificate types use the monorepo modules.
-/

import CapacityAtlasForMathlib.InformationTheory.InputCost
import CapacityAtlasForMathlib.InformationTheory.InformationDensity
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators

namespace CapacityAtlasCost

open CapacityAtlas

variable {X : Type*} [Fintype X]

noncomputable def costVariance (input : FiniteDistribution X) (cost : X → ℝ) : ℝ :=
  ∑ symbol, input symbol * (cost symbol - input.expectedCost cost) ^ 2

noncomputable def badCostMass (input : FiniteDistribution X) (cost : X → ℝ)
    (budget : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ word : Fin n → X, if (n : ℝ) * budget < ∑ i, cost (word i)
    then input.iid n word else 0

theorem costVariance_nonnegative (input : FiniteDistribution X) (cost : X → ℝ) :
    0 ≤ costVariance input cost :=
  Finset.sum_nonneg fun x _ ↦ mul_nonneg (input.nonnegative x) (sq_nonneg _)

theorem cost_centered_mean (input : FiniteDistribution X) (cost : X → ℝ) :
    FiniteProductProbability.mean input (fun x ↦ cost x - input.expectedCost cost) = 0 := by
  unfold FiniteProductProbability.mean
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, input.sum_probability_eq_one]
  simp [FiniteDistribution.expectedCost]

theorem cost_secondMoment (input : FiniteDistribution X) (cost : X → ℝ) (n : ℕ) :
    (∑ word : Fin n → X, input.iid n word *
      ((∑ i, cost (word i)) - (n : ℝ) * input.expectedCost cost) ^ 2) =
        (n : ℝ) * costVariance input cost := by
  have h := FiniteProductProbability.sum_mass_mul_centered_sum_sq
    (ι := Fin n) input (fun _ x ↦ cost x - input.expectedCost cost)
    input.sum_probability (fun _ ↦ cost_centered_mean input cost)
  simpa only [FiniteDistribution.iid_apply, FiniteProductProbability.mass,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, FiniteProductProbability.mean, costVariance] using h

theorem badCostMass_le (input : FiniteDistribution X) (cost : X → ℝ)
    (budget : ℝ) {n : ℕ} (hn : 0 < n) (hcost : input.expectedCost cost < budget) :
    badCostMass input cost budget n ≤
      ((n : ℝ) * costVariance input cost) /
        (((n : ℝ) * (budget - input.expectedCost cost)) ^ 2) := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgap : 0 < (n : ℝ) * (budget - input.expectedCost cost) :=
    mul_pos hnR (sub_pos.mpr hcost)
  rw [← cost_secondMoment input cost n]
  apply (le_div_iff₀ (sq_pos_of_pos hgap)).2
  unfold badCostMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro word _
  split_ifs with hword
  · have hdist : (n : ℝ) * (budget - input.expectedCost cost) <
        (∑ i, cost (word i)) - (n : ℝ) * input.expectedCost cost := by
      nlinarith
    exact mul_le_mul_of_nonneg_left (by nlinarith) ((input.iid n).nonnegative word)
  · simpa only [zero_mul] using mul_nonneg ((input.iid n).probability_nonnegative word)
      (sq_nonneg ((∑ i, cost (word i)) - (n : ℝ) * input.expectedCost cost))

theorem admissible_support_cost_eq (input : FiniteDistribution X) (cost : X → ℝ)
    (budget : ℝ) (hlower : ∀ x, budget ≤ cost x)
    (hadmissible : input.IsAdmissibleCost cost budget) (x : X) (hx : input x ≠ 0) :
    cost x = budget := by
  have hnonneg (a : X) : 0 ≤ input a * (cost a - budget) :=
    mul_nonneg (input.nonnegative a) (sub_nonneg.mpr (hlower a))
  have hsum : (∑ a, input a * (cost a - budget)) ≤ 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, input.sum_probability_eq_one, one_mul]
    exact sub_nonpos.mpr hadmissible
  have hterm : input x * (cost x - budget) ≤ 0 :=
    (Finset.single_le_sum (fun a _ ↦ hnonneg a) (Finset.mem_univ x)).trans hsum
  have hzero : input x * (cost x - budget) = 0 := le_antisymm hterm (hnonneg x)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hx)

theorem badCostMass_eq_zero (input : FiniteDistribution X) (cost : X → ℝ)
    (budget : ℝ) (hlower : ∀ x, budget ≤ cost x)
    (hadmissible : input.IsAdmissibleCost cost budget) (n : ℕ) :
    badCostMass input cost budget n = 0 := by
  classical
  unfold badCostMass
  apply Finset.sum_eq_zero
  intro word _
  split_ifs with hword
  · by_contra hmass
    have hprod : (∏ i, input (word i)) ≠ 0 := hmass
    have hcoordinates (i : Fin n) : input (word i) ≠ 0 := by
      exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
    have heq : (∑ i, cost (word i)) = (n : ℝ) * budget := by
      simp_rw [admissible_support_cost_eq input cost budget hlower hadmissible
        (word _) (hcoordinates _)]
      simp
    exact (not_lt_of_ge heq.le) hword
  · rfl

theorem badCostMass_nonnegative (input : FiniteDistribution X) (cost : X → ℝ)
    (budget : ℝ) (n : ℕ) : 0 ≤ badCostMass input cost budget n := by
  classical
  exact Finset.sum_nonneg fun word _ ↦ by
    split_ifs
    · exact (input.iid n).nonnegative word
    · rfl

theorem badCostMass_tendsto_zero (input : FiniteDistribution X) (cost : X → ℝ)
    (budget : ℝ) (hcost : input.expectedCost cost < budget) :
    Filter.Tendsto (badCostMass input cost budget) Filter.atTop (nhds 0) := by
  have hbound : Filter.Tendsto
      (fun n : ℕ ↦ ((costVariance input cost) /
        (budget - input.expectedCost cost) ^ 2) / (n : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop _
  apply squeeze_zero' (Filter.Eventually.of_forall
    (badCostMass_nonnegative input cost budget)) _ hbound
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hgap : budget - input.expectedCost cost ≠ 0 := (sub_pos.mpr hcost).ne'
  convert badCostMass_le input cost budget hn hcost using 1
  field_simp

end CapacityAtlasCost
