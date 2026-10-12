/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Basic
import CapacityAtlasForMathlib.InformationTheory.FiniteEntropy

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteInformation

theorem joint_map_fst {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (p : FiniteDistribution A) (W : FiniteChannel A B) :
    (joint p W).map Prod.fst = p := by
  ext a
  change (∑ z : A × B with z.1 = a, p z.1 * W.transition z.1 z.2) = p a
  simp [Fintype.sum_prod_type, Finset.sum_filter, ← Finset.mul_sum]

end FiniteInformation

namespace FiniteDistribution

theorem uniform_map_fst {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [DecidableEq A] :
    (uniform (A × B)).map Prod.fst = uniform A := by
  ext a
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change (∑ z : A × B with z.1 = a, (Fintype.card (A × B) : ℝ)⁻¹) =
    (Fintype.card A : ℝ)⁻¹
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [hB, mul_inv_rev]

theorem uniform_map_snd {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [DecidableEq B] :
    (uniform (A × B)).map Prod.snd = uniform B := by
  ext b
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change (∑ z : A × B with z.2 = b, (Fintype.card (A × B) : ℝ)⁻¹) =
    (Fintype.card B : ℝ)⁻¹
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [hA, mul_inv_rev, mul_comm]

end FiniteDistribution

namespace ConfidentialBroadcast.Code

variable {X Y Z O : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype O]
    {W : FiniteBroadcastChannel X Y Z} {n : ℕ}

theorem joint_pair_uniform (c : Code W n) (V : FiniteChannel X O) :
    (c.joint V).map Prod.fst = c.messages :=
  FiniteInformation.joint_map_fst _ _

theorem joint_common_uniform (c : Code W n) (V : FiniteChannel X O)
    [Nonempty (Fin c.commonCount)] :
    (c.joint V).map (fun a ↦ a.1.1) = FiniteDistribution.uniform (Fin c.commonCount) := by
  letI : Nonempty (Fin c.secretCount) := Fin.pos_iff_nonempty.mp c.secretCount_pos
  have h := congrArg (fun p : FiniteDistribution (Fin c.commonCount × Fin c.secretCount) ↦
    p.map Prod.fst) (joint_pair_uniform c V)
  have h' : c.messages.map Prod.fst = FiniteDistribution.uniform (Fin c.commonCount) :=
    FiniteDistribution.uniform_map_fst
  simpa only [FiniteDistribution.map_map, Function.comp_def] using h.trans h'

theorem joint_secret_uniform (c : Code W n) (V : FiniteChannel X O)
    [Nonempty (Fin c.secretCount)] :
    (c.joint V).map (fun a ↦ a.1.2) = FiniteDistribution.uniform (Fin c.secretCount) := by
  letI : Nonempty (Fin c.commonCount) := Fin.pos_iff_nonempty.mp c.commonCount_pos
  have h := congrArg (fun p : FiniteDistribution (Fin c.commonCount × Fin c.secretCount) ↦
    p.map Prod.snd) (joint_pair_uniform c V)
  have h' : c.messages.map Prod.snd = FiniteDistribution.uniform (Fin c.secretCount) :=
    FiniteDistribution.uniform_map_snd
  simpa only [FiniteDistribution.map_map, Function.comp_def] using h.trans h'

theorem legitimateError_nonneg (c : Code W n) : 0 ≤ c.legitimateError := by
  classical
  unfold legitimateError
  exact Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun y _ ↦ by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (c.messages.nonnegative _) ((c.induced W.receiver₁).nonnegative _ _)

theorem commonError_nonneg (c : Code W n) : 0 ≤ c.commonError := by
  classical
  unfold commonError
  exact Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun z _ ↦ by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (c.messages.nonnegative _) ((c.induced W.receiver₂).nonnegative _ _)

theorem error_nonneg (c : Code W n) : 0 ≤ c.error :=
  c.legitimateError_nonneg.trans (le_max_left _ _)

theorem defect_nonneg (c : Code W n) : 0 ≤ c.defect :=
  c.error_nonneg.trans (le_max_left _ _)

end ConfidentialBroadcast.Code

end CapacityAtlas
