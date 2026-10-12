/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.CovarianceConstraint
import Mathlib.Topology.Sequences

open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ} {n : ℕ}

/-- Uncentered input second moment, averaged over messages and channel uses. -/
noncomputable def inputSecondMoment (c : Code K tx rx n) : Matrix (Fin tx) (Fin tx) ℝ :=
  ((n : ℝ)⁻¹ * (∏ i, (c.messages i : ℝ))⁻¹) •
    ∑ m, ∑ s, Matrix.vecMulVec (fun a ↦ c.encode m s a) (fun a ↦ c.encode m s a)

theorem inputSecondMoment_posSemidef (c : Code K tx rx n) :
    (inputSecondMoment c).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · apply Matrix.posSemidef_sum
    intro m _
    apply Matrix.posSemidef_sum
    intro s _
    simpa using Matrix.posSemidef_vecMulVec_self_star (fun a ↦ c.encode m s a)
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (inv_nonneg.mpr (Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg (c.messages i)))

theorem trace_inputSecondMoment (c : Code K tx rx n) :
    Matrix.trace (inputSecondMoment c) =
      (n : ℝ)⁻¹ * ((∏ i, (c.messages i : ℝ))⁻¹ *
        (∑ m, ∑ s, ∑ a, (c.encode m s a) ^ 2)) := by
  simp [inputSecondMoment, Matrix.trace_sum, Matrix.trace_vecMulVec, dotProduct,
    pow_two, mul_assoc]

/-- The operational power constraint is exactly a trace constraint on the input moment. -/
theorem powerAdmissible_iff_trace_inputSecondMoment (c : Code K tx rx n) (hn : 0 < n)
    (P : ℝ) : PowerAdmissible P c ↔ Matrix.trace (inputSecondMoment c) ≤ P := by
  rw [trace_inputSecondMoment]
  exact (inv_mul_le_iff₀ (Nat.cast_pos.mpr hn)).symm

theorem inputSecondMoment_admissible (c : Code K tx rx n) (hn : 0 < n)
    {P : ℝ} (hP : PowerAdmissible P c) : AdmissibleCovariance P (inputSecondMoment c) :=
  ⟨inputSecondMoment_posSemidef c, (powerAdmissible_iff_trace_inputSecondMoment c hn P).mp hP⟩

/-- Bounded-power code sequences have a convergent subsequence of input second moments. -/
theorem exists_inputSecondMoment_subseq {lengths : ℕ → ℕ}
    (codes : (j : ℕ) → Code K tx rx (lengths j)) (hlen : ∀ j, 0 < lengths j)
    {P : ℝ} (hP : ∀ j, PowerAdmissible P (codes j)) :
    ∃ S : Matrix (Fin tx) (Fin tx) ℝ, AdmissibleCovariance P S ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (fun j ↦ inputSecondMoment (codes (φ j))) Filter.atTop (nhds S) := by
  letI : FirstCountableTopology (Matrix (Fin tx) (Fin tx) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin tx → Fin tx → ℝ))
  exact (isCompact_admissibleCovariance P).tendsto_subseq
    (fun j ↦ inputSecondMoment_admissible (codes j) (hlen j) (hP j))

end CapacityAtlas.Gaussian.MIMOBroadcast
