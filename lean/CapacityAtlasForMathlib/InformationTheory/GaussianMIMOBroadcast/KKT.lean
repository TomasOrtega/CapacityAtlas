/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Variation
import CapacityAtlasForMathlib.LinearAlgebra.PositiveTrace

open Matrix
open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ}

noncomputable def traceObjective (G Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) : ℝ :=
  ∑ i, trace (G i * Q i)

noncomputable def rankOneAllocation (P : ℝ) (i : Fin K) (v : Fin tx → ℝ) :
    Fin K → Matrix (Fin tx) (Fin tx) ℝ := Pi.single i ((P / (v ⬝ᵥ v)) • vecMulVec v v)

lemma rankOneAllocation_admissible {P : ℝ} (hP : 0 ≤ P) (i : Fin K)
    (v : Fin tx → ℝ) (hv : v ≠ 0) : AllocationAdmissible P (rankOneAllocation P i v) := by
  have hnorm : 0 < v ⬝ᵥ v := by simpa using (dotProduct_self_star_pos_iff.mpr hv)
  have hvec : (vecMulVec v v).PosSemidef := by
    simpa using posSemidef_vecMulVec_self_star v
  refine ⟨fun j ↦ ?_, ?_⟩
  · by_cases hj : j = i
    · subst j
      simpa only [rankOneAllocation, Pi.single_eq_same] using
        hvec.smul (div_nonneg hP hnorm.le)
    · simp only [rankOneAllocation, Pi.single_eq_of_ne hj]
      exact PosSemidef.zero
  · simp [rankOneAllocation, Pi.single_apply, apply_ite trace, trace_smul, trace_vecMulVec,
      div_mul_cancel₀ _ hnorm.ne']

lemma traceObjective_rankOneAllocation (G : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (P : ℝ) (i : Fin K) (v : Fin tx → ℝ) :
    traceObjective G (rankOneAllocation P i v) = (P / (v ⬝ᵥ v)) * (v ⬝ᵥ G i *ᵥ v) := by
  simp [traceObjective, rankOneAllocation, Pi.single_apply, apply_ite trace, trace_smul,
    mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

theorem traceMultiplier_nonneg {P : ℝ} (hP : 0 < P)
    (G Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hmax : ∀ Y, AllocationAdmissible P Y → traceObjective G Y ≤ traceObjective G Q) :
    0 ≤ traceObjective G Q / P := by
  have h := hmax 0 (allocationAdmissible_zero hP.le)
  have hg : 0 ≤ traceObjective G Q := by simpa [traceObjective] using h
  exact div_nonneg hg hP.le

/-- Rank-one feasible directions recover the positive semidefinite multiplier slacks. -/
theorem traceMultiplier_slack_posSemidef {P : ℝ} (hP : 0 < P)
    (G Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hG : ∀ i, (G i).IsHermitian)
    (hmax : ∀ Y, AllocationAdmissible P Y → traceObjective G Y ≤ traceObjective G Q)
    (i : Fin K) : ((traceObjective G Q / P) • (1 : Matrix (Fin tx) (Fin tx) ℝ) - G i).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_one.smul (IsSelfAdjoint.all _)).sub (hG i)
  · intro v
    by_cases hv : v = 0
    · simp [hv]
    have hnorm : 0 < v ⬝ᵥ v := by simpa using (dotProduct_self_star_pos_iff.mpr hv)
    have h := hmax (rankOneAllocation P i v) (rankOneAllocation_admissible hP.le i v hv)
    rw [traceObjective_rankOneAllocation] at h
    have hbound : v ⬝ᵥ G i *ᵥ v ≤ (traceObjective G Q / P) * (v ⬝ᵥ v) := by
      have h' := (div_le_iff₀ hnorm).mp
        (show P * (v ⬝ᵥ G i *ᵥ v) / (v ⬝ᵥ v) ≤ traceObjective G Q by
          simpa only [div_mul_eq_mul_div] using h)
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hP).mpr
      nlinarith
    simpa only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, sub_nonneg] using hbound

lemma sum_trace_slack_mul (G Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (lam : ℝ) :
    (∑ i, trace ((lam • 1 - G i) * Q i)) = lam * (∑ i, trace (Q i)) - traceObjective G Q := by
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, trace_sub, trace_smul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, traceObjective, smul_eq_mul]

theorem traceMultiplier_complementarity {P : ℝ} (hP : 0 < P)
    (G Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : AllocationAdmissible P Q)
    (hG : ∀ i, (G i).IsHermitian)
    (hmax : ∀ Y, AllocationAdmissible P Y → traceObjective G Y ≤ traceObjective G Q) :
    (∀ i, ((traceObjective G Q / P) • 1 - G i) * Q i = 0) ∧
      (traceObjective G Q / P) * (P - ∑ i, trace (Q i)) = 0 := by
  let lam := traceObjective G Q / P
  have hlam : 0 ≤ lam := traceMultiplier_nonneg hP G Q hmax
  have hslack := traceMultiplier_slack_posSemidef hP G Q hG hmax
  have hnonneg (i : Fin K) : 0 ≤ trace ((lam • 1 - G i) * Q i) :=
    (hslack i).trace_mul_nonneg (hQ.1 i)
  have hlamP : lam * P = traceObjective G Q := div_mul_cancel₀ _ hP.ne'
  have hsum : (∑ i, trace ((lam • 1 - G i) * Q i)) = 0 := by
    apply le_antisymm
    · rw [sum_trace_slack_mul, ← hlamP]
      exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hQ.2 hlam)
    · exact Finset.sum_nonneg (fun i _ ↦ hnonneg i)
  refine ⟨?_, ?_⟩
  · intro i
    apply ((hslack i).trace_mul_eq_zero_iff (hQ.1 i)).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ hnonneg j)).mp hsum i
      (Finset.mem_univ i)
  · rw [sum_trace_slack_mul] at hsum
    change lam * (P - ∑ i, trace (Q i)) = 0
    rw [mul_sub, hlamP]
    linarith

/-- Matrix KKT multipliers follow from the trace-budget variational inequality. -/
theorem exists_traceBudget_multipliers {P : ℝ} (hP : 0 < P)
    (G Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : AllocationAdmissible P Q)
    (hG : ∀ i, (G i).IsHermitian)
    (hmax : ∀ Y, AllocationAdmissible P Y → traceObjective G Y ≤ traceObjective G Q) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∃ M : Fin K → Matrix (Fin tx) (Fin tx) ℝ,
      (∀ i, (M i).PosSemidef) ∧ (∀ i, G i + M i = lam • 1) ∧
      (∀ i, M i * Q i = 0) ∧ lam * (P - ∑ i, trace (Q i)) = 0 := by
  refine ⟨traceObjective G Q / P, traceMultiplier_nonneg hP G Q hmax,
    fun i ↦ (traceObjective G Q / P) • 1 - G i,
    traceMultiplier_slack_posSemidef hP G Q hG hmax, ?_,
    traceMultiplier_complementarity hP G Q hQ hG hmax⟩
  intro i
  rw [add_comm, sub_add_cancel]

end CapacityAtlas.Gaussian.MIMOBroadcast
