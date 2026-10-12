/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianOperational
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcastRegion
import Mathlib.Topology.Instances.Matrix

open scoped BigOperators

namespace Matrix

variable {ι : Type*} [Fintype ι]

theorem PosSemidef.diag_le_trace {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι) :
    S i i ≤ S.trace :=
  Finset.single_le_sum (fun j _ ↦ hS.diag_nonneg (i := j)) (Finset.mem_univ i)

/-- Testing the quadratic form on two signed basis vectors bounds each entry. -/
theorem PosSemidef.abs_apply_le_trace [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j : ι) :
    |S i j| ≤ S.trace := by
  have hsym : S j i = S i j := by simpa using hS.isHermitian.apply i j
  have hplus := hS.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hminus := hS.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, mulVec_add, add_dotProduct, dotProduct_add,
    single_one_dotProduct, mulVec_single_one, col_apply] at hplus
  simp only [star_trivial, mulVec_sub, sub_dotProduct, dotProduct_sub,
    single_one_dotProduct, mulVec_single_one, col_apply] at hminus
  rw [abs_le]
  constructor <;> linarith [hS.diag_le_trace i, hS.diag_le_trace j]

theorem isClosed_setOf_posSemidef_real : IsClosed {S : Matrix ι ι ℝ | S.PosSemidef} := by
  simp only [posSemidef_iff_dotProduct_mulVec, Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const (by fun_prop)

end Matrix

namespace CapacityAtlas.Gaussian

variable {tx K : ℕ}

theorem isClosed_admissibleCovariance (P : ℝ) :
    IsClosed {S : Matrix (Fin tx) (Fin tx) ℝ | AdmissibleCovariance P S} := by
  exact Matrix.isClosed_setOf_posSemidef_real.inter
    (isClosed_le (f := fun S : Matrix (Fin tx) (Fin tx) ℝ ↦ Matrix.trace S)
      (by unfold Matrix.trace; fun_prop) continuous_const)

theorem isCompact_admissibleCovariance (P : ℝ) :
    IsCompact {S : Matrix (Fin tx) (Fin tx) ℝ | AdmissibleCovariance P S} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (-P) P)).matrix.of_isClosed_subset
    (isClosed_admissibleCovariance P)
  intro S hS i j
  exact abs_le.mp ((hS.1.abs_apply_le_trace i j).trans hS.2)

namespace MIMOBroadcast

theorem isClosed_allocationAdmissible (P : ℝ) :
    IsClosed {Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ | AllocationAdmissible P Q} := by
  change IsClosed ({Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ | ∀ i, (Q i).PosSemidef} ∩
    {Q | ∑ i, Matrix.trace (Q i) ≤ P})
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun i ↦
      (Matrix.isClosed_setOf_posSemidef_real (ι := Fin tx)).preimage
        (continuous_apply i : Continuous (fun Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ ↦ Q i))
  · exact isClosed_le (by unfold Matrix.trace; fun_prop) continuous_const

theorem isCompact_allocationAdmissible (P : ℝ) :
    IsCompact {Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ | AllocationAdmissible P Q} := by
  apply (isCompact_pi_infinite fun _ : Fin K ↦
    isCompact_admissibleCovariance (tx := tx) P).of_isClosed_subset
    (isClosed_allocationAdmissible P)
  intro Q hQ i
  refine ⟨hQ.1 i, le_trans ?_ hQ.2⟩
  exact Finset.single_le_sum (fun j _ ↦ (hQ.1 j).trace_nonneg) (Finset.mem_univ i)

end MIMOBroadcast

end CapacityAtlas.Gaussian
