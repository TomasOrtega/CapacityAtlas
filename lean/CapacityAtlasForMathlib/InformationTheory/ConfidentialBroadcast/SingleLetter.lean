/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.CoordinateLaw
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.AuxiliaryLaws
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation.SequenceInformation

open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

variable {I A B C : Type*} [Fintype I] [Fintype A] [Fintype B] [Fintype C]

@[capacity_shared_api]
theorem map_joint_fst [DecidableEq B] [DecidableEq C]
    (p : FiniteDistribution A) (f : A → B) (rows : B → FiniteDistribution C) :
    (p.joint (fun a ↦ rows (f a))).map (fun z ↦ (f z.1, z.2)) = (p.map f).joint rows := by
  classical
  ext point
  rcases point with ⟨b, c⟩
  change (∑ z : A × C with (f z.1, z.2) = (b, c), p z.1 * rows (f z.1) z.2) =
    (∑ a with f a = b, p a) * rows b c
  simp only [Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp [h]

@[capacity_shared_api]
theorem mixture_joint (p : FiniteDistribution I) (rows : I → FiniteDistribution A)
    (kernel : A → FiniteDistribution B) :
    p.mixture (fun i ↦ (rows i).joint kernel) = (p.mixture rows).joint kernel := by
  ext point
  simp only [mixture_apply, joint_apply, Finset.sum_mul, mul_assoc]

@[capacity_shared_api]
theorem map_joint_snd_dependent [DecidableEq I] [DecidableEq B]
    (p : FiniteDistribution I) (rows : I → FiniteDistribution A) (f : I → A → B) :
    (p.joint rows).map (fun z ↦ (z.1, f z.1 z.2)) =
      p.joint (fun i ↦ (rows i).map (f i)) := by
  classical
  ext point
  rcases point with ⟨i, b⟩
  change (∑ z : I × A with (z.1, f z.1 z.2) = (i, b), p z.1 * rows z.1 z.2) =
    p i * ∑ a with f i a = b, rows i a
  simp [Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and,
    Finset.mul_sum, mul_ite, mul_zero]

end CapacityAtlas.FiniteDistribution

namespace CapacityAtlas.FiniteInformation

variable {I Ω A B C : Type*} [Fintype I] [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

@[capacity_shared_api]
theorem entropy_joint_observable (p : FiniteDistribution I)
    (rows : I → FiniteDistribution Ω) (f : I → Ω → A) :
    entropy (p.joint rows) (fun z ↦ (z.1, f z.1 z.2)) =
      p.entropyBits + ∑ i, p i * entropy (rows i) (f i) := by
  classical
  simp only [entropy_eq_map, FiniteDistribution.map_joint_snd_dependent,
    FiniteDistribution.entropyBits_joint]

@[capacity_shared_api]
theorem conditional_joint_with_context (p : FiniteDistribution I)
    (rows : I → FiniteDistribution Ω) (f : I → Ω → A)
    (g : I → Ω → B) (h : I → Ω → C) :
    conditional (p.joint rows) (fun z ↦ (z.1, f z.1 z.2)) (fun z ↦ g z.1 z.2)
      (fun z ↦ (z.1, h z.1 z.2)) =
      ∑ i, p i * conditional (rows i) (f i) (g i) (h i) := by
  have hfh := entropy_comp_injective (p.joint rows)
    (fun z ↦ (z.1, f z.1 z.2, h z.1 z.2))
    (fun z : I × A × C ↦ ((z.1, z.2.1), (z.1, z.2.2))) (by
      intro a b hab
      rcases a with ⟨i, a, c⟩
      rcases b with ⟨j, b, d⟩
      simp only [Prod.mk.injEq] at hab ⊢
      exact ⟨hab.1.1, hab.1.2, hab.2.2⟩)
  have hgh := entropy_comp_injective (p.joint rows)
    (fun z ↦ (z.1, g z.1 z.2, h z.1 z.2))
    (fun z : I × B × C ↦ (z.2.1, z.1, z.2.2)) (by
      intro a b hab
      rcases a with ⟨i, a, c⟩
      rcases b with ⟨j, b, d⟩
      simpa only [Prod.mk.injEq, and_assoc, and_left_comm] using hab)
  have htrip := entropy_comp_injective (p.joint rows)
    (fun z ↦ (z.1, f z.1 z.2, g z.1 z.2, h z.1 z.2))
    (fun z : I × A × B × C ↦ ((z.1, z.2.1), z.2.2.1, (z.1, z.2.2.2))) (by
      intro x y hab
      rcases x with ⟨i, a, b, c⟩
      rcases y with ⟨j, d, e, f⟩
      simp only [Prod.mk.injEq] at hab ⊢
      exact ⟨hab.1.1, hab.1.2, hab.2.1, hab.2.2.2⟩)
  simp only [Function.comp_def] at hfh hgh htrip
  unfold conditional
  rw [hfh, hgh, htrip]
  rw [entropy_joint_observable p rows (fun i ω ↦ (f i ω, h i ω)),
    entropy_joint_observable p rows (fun i ω ↦ (g i ω, h i ω)),
    entropy_joint_observable p rows h,
    entropy_joint_observable p rows (fun i ω ↦ (f i ω, g i ω, h i ω))]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

@[capacity_shared_api]
theorem average_information_le_joint (p : FiniteDistribution I)
    (rows : I → FiniteDistribution Ω) (f : I → Ω → A) (g : I → Ω → B) :
    (∑ i, p i * information (rows i) (f i) (g i)) ≤
      information (p.joint rows) (fun z ↦ (z.1, f z.1 z.2)) (fun z ↦ g z.1 z.2) := by
  have h := conditional_joint_with_context p rows f g (fun _ _ ↦ ())
  have hconst := conditional_condition_comp_injective (p.joint rows)
    (fun z ↦ (z.1, f z.1 z.2)) (fun z ↦ g z.1 z.2) Prod.fst
    (fun i ↦ (i, ())) (fun _ _ h ↦ (Prod.mk.inj h).1)
  simp only [Function.comp_def, conditional_const] at h hconst
  rw [hconst] at h
  rw [← h]
  have hle := conditional_le_information_pair (p.joint rows)
    (fun z ↦ (z.1, f z.1 z.2)) (fun z ↦ g z.1 z.2) Prod.fst
  have hinj := information_comp_left_injective (p.joint rows)
    (fun z ↦ (z.1, f z.1 z.2)) (fun z ↦ g z.1 z.2)
    (fun z : I × A ↦ (z, z.1)) (fun _ _ h ↦ (Prod.mk.inj h).1)
  exact hle.trans_eq hinj

@[capacity_shared_api]
theorem conditional_pair_condition (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    conditional p (fun ω ↦ (f ω, h ω)) g h = conditional p f g h := by
  have hfh := entropy_comp_injective p (fun ω ↦ (f ω, h ω))
    (fun z : A × C ↦ (z, z.2)) (fun _ _ h ↦ (Prod.mk.inj h).1)
  have htrip := entropy_comp_injective p (fun ω ↦ (f ω, g ω, h ω))
    (fun z : A × B × C ↦ ((z.1, z.2.2), z.2.1, z.2.2)) (by
      intro x y hxy
      exact Prod.ext (Prod.mk.inj (Prod.mk.inj hxy).1).1
        (Prod.ext (Prod.mk.inj (Prod.mk.inj hxy).2).1
          (Prod.mk.inj (Prod.mk.inj hxy).2).2))
  simp only [Function.comp_def] at hfh htrip
  unfold conditional
  rw [hfh, htrip]

end CapacityAtlas.FiniteInformation

namespace CapacityAtlas.ConfidentialBroadcast

theorem auxiliaryJoint_conditionalRows {U V X O : Type*}
    [Fintype U] [Fintype V] [Fintype X] [Fintype O]
    [DecidableEq U] [DecidableEq V] [DecidableEq X] [DecidableEq O]
    (p : FiniteDistribution (V × X)) (f : V → U) (W : FiniteChannel X O) :
    auxiliaryJoint (p.map (fun z ↦ (f z.1, z.1)))
      (FiniteChannel.ofRows p.conditionalRows) W =
    (p.joint (fun z ↦ W.rowDistribution z.2)).map
      (fun z ↦ ((f z.1.1, z.1.1), z.2)) := by
  classical
  let P := FiniteChannel.ofRows p.conditionalRows
  have hcomp := FiniteInformation.joint_comp (p.map Prod.fst) P W
  have hj : FiniteInformation.joint (p.map Prod.fst) P = p := p.joint_conditionalRows
  rw [hj] at hcomp
  have h := congrArg (fun q : FiniteDistribution (V × O) ↦
    q.map (fun z ↦ ((f z.1, z.1), z.2))) hcomp
  rw [FiniteDistribution.map_map] at h
  have hattach := FiniteDistribution.map_joint_fst (p.map Prod.fst)
    (fun v ↦ (f v, v)) (fun v : U × V ↦ (W.comp P).rowDistribution v.2)
  rw [FiniteDistribution.map_map] at hattach
  exact (h.trans hattach).symm

end CapacityAtlas.ConfidentialBroadcast

namespace CapacityAtlas.ConfidentialBroadcast.Code

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
  {W : FiniteBroadcastChannel X Y Z} {n : ℕ}

abbrev TimedCommonAux (c : Code W n) := Fin n × c.CommonAux
abbrev TimedSecretAux (c : Code W n) := Fin n × c.SecretAux
abbrev TimedSample (c : Code W n) := Fin n × c.FullSample

noncomputable local instance : DecidableEq X := Classical.typeDecidableEq _
noncomputable local instance : DecidableEq Y := Classical.typeDecidableEq _
noncomputable local instance : DecidableEq Z := Classical.typeDecidableEq _
noncomputable local instance (c : Code W n) : DecidableEq c.TimedSecretAux :=
  Classical.typeDecidableEq _
noncomputable local instance (c : Code W n) : DecidableEq c.TimedCommonAux :=
  Classical.typeDecidableEq _

def dropSecret (c : Code W n) (v : c.TimedSecretAux) : c.TimedCommonAux := (v.1, v.2.2)

noncomputable def timedJoint (c : Code W n) [NeZero n] : FiniteDistribution c.TimedSample :=
  (FiniteDistribution.uniform (Fin n)).joint (fun _ ↦ c.fullJoint)

def timedSecret (c : Code W n) (z : c.TimedSample) : c.TimedSecretAux :=
  (z.1, c.secretObservation z.1 z.2)

def timedCommon (c : Code W n) (z : c.TimedSample) : c.TimedCommonAux :=
  c.dropSecret (c.timedSecret z)

noncomputable def inputJoint (c : Code W n) [NeZero n] :
    FiniteDistribution (c.TimedSecretAux × X) := by
  classical
  exact c.timedJoint.map (fun z ↦ (c.timedSecret z, z.2.1.2 z.1))

noncomputable def auxiliaryLaw (c : Code W n) [NeZero n] :
    FiniteDistribution (c.TimedCommonAux × c.TimedSecretAux) := by
  classical
  exact c.inputJoint.map (fun z ↦ (c.dropSecret z.1, z.1))

noncomputable def prefixing (c : Code W n) [NeZero n] : FiniteChannel c.TimedSecretAux X := by
  classical
  exact FiniteChannel.ofRows c.inputJoint.conditionalRows

variable [NeZero n]

theorem timedJoint_coordinate_pair (c : Code W n) :
    c.timedJoint.map (fun z ↦ ((c.timedSecret z, z.2.1.2 z.1), z.2.2 z.1)) =
      c.inputJoint.joint (fun v ↦ (receiverPair W).rowDistribution v.2) := by
  classical
  have hrow (i : Fin n) :
      c.fullJoint.map (fun z ↦ (((i, c.secretObservation i z), z.1.2 i), z.2 i)) =
        (c.fullJoint.map (fun z ↦ ((i, c.secretObservation i z), z.1.2 i))).joint
          (fun v ↦ (receiverPair W).rowDistribution v.2) := by
    have h := congrArg
      (fun p : FiniteDistribution ((c.SecretAux × X) × (Y × Z)) ↦
        p.map (fun z ↦ (((i, z.1.1), z.1.2), z.2))) (c.fullJoint_coordinate_pair i)
    rw [FiniteDistribution.map_map] at h
    have hright := FiniteDistribution.map_joint_fst
      (c.fullJoint.map (fun z ↦ (c.secretObservation i z, z.1.2 i)))
      (fun v : c.SecretAux × X ↦ ((i, v.1), v.2))
      (fun v : c.TimedSecretAux × X ↦ (receiverPair W).rowDistribution v.2)
    rw [FiniteDistribution.map_map] at hright
    exact h.trans hright
  unfold inputJoint timedJoint
  rw [FiniteDistribution.map_joint_eq_mixture, FiniteDistribution.map_joint_eq_mixture]
  simp only [timedSecret, hrow]
  exact FiniteDistribution.mixture_joint _ _ _

theorem auxiliaryJoint_pair (c : Code W n) :
    auxiliaryJoint c.auxiliaryLaw c.prefixing (receiverPair W) =
      c.timedJoint.map (fun z ↦ ((c.timedCommon z, c.timedSecret z), z.2.2 z.1)) := by
  classical
  rw [auxiliaryLaw, prefixing, auxiliaryJoint_conditionalRows,
    ← c.timedJoint_coordinate_pair, FiniteDistribution.map_map]
  rfl

theorem timedJoint_coordinate_observe {O : Type*} [Fintype O] [DecidableEq O]
    (c : Code W n) (V : FiniteChannel X O) (observe : Y × Z → O)
    (hobserve : ∀ x, ((receiverPair W).rowDistribution x).map observe = V.rowDistribution x) :
    c.timedJoint.map (fun z ↦ ((c.timedSecret z, z.2.1.2 z.1), observe (z.2.2 z.1))) =
      c.inputJoint.joint (fun v ↦ V.rowDistribution v.2) := by
  classical
  have h := congrArg
    (fun p : FiniteDistribution ((c.TimedSecretAux × X) × (Y × Z)) ↦
      p.map (fun z ↦ (z.1, observe z.2))) (c.timedJoint_coordinate_pair)
  simpa only [FiniteDistribution.map_map, Function.comp_def,
    FiniteDistribution.map_joint_snd, hobserve] using h

theorem auxiliaryJoint_observe {O : Type*} [Fintype O] [DecidableEq O]
    (c : Code W n) (V : FiniteChannel X O) (observe : Y × Z → O)
    (hobserve : ∀ x, ((receiverPair W).rowDistribution x).map observe = V.rowDistribution x) :
    auxiliaryJoint c.auxiliaryLaw c.prefixing V =
      c.timedJoint.map (fun z ↦ ((c.timedCommon z, c.timedSecret z), observe (z.2.2 z.1))) := by
  classical
  rw [auxiliaryLaw, prefixing, auxiliaryJoint_conditionalRows,
    ← c.timedJoint_coordinate_observe V observe hobserve, FiniteDistribution.map_map]
  rfl

theorem auxiliaryJoint_legitimate (c : Code W n) :
    auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₁ =
      c.timedJoint.map (fun z ↦ ((c.timedCommon z, c.timedSecret z), (z.2.2 z.1).1)) := by
  apply c.auxiliaryJoint_observe W.receiver₁ Prod.fst
  intro x
  exact FiniteDistribution.map_fst_joint (W.receiver₁.rowDistribution x)
    (fun _ ↦ W.receiver₂.rowDistribution x)

theorem auxiliaryJoint_eavesdropper (c : Code W n) :
    auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₂ =
      c.timedJoint.map (fun z ↦ ((c.timedCommon z, c.timedSecret z), (z.2.2 z.1).2)) := by
  apply c.auxiliaryJoint_observe W.receiver₂ Prod.snd
  intro x
  simpa only [receiverPair, FiniteChannel.rowDistribution_ofRows,
    FiniteDistribution.mixture_const] using
      FiniteDistribution.map_snd_joint (W.receiver₁.rowDistribution x)
        (fun _ ↦ W.receiver₂.rowDistribution x)

open FiniteInformation

theorem common_information_le_auxiliary_legitimate (c : Code W n) :
    information (c.joint W.receiver₁) (fun z ↦ z.1.1) Prod.snd / n ≤
      information (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₁)
        (fun z ↦ z.1.1) Prod.snd := by
  have hsum := information_le_sum_common_prefix_suffix_left c.fullJoint
    (fun z ↦ z.1.1.1) (fun z j ↦ (z.2 j).1) (fun z j ↦ (z.2 j).2)
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have htime := average_information_le_joint (FiniteDistribution.uniform (Fin n))
    (fun _ ↦ c.fullJoint) (fun i ↦ c.commonObservation i) (fun i z ↦ (z.2 i).1)
  rw [← c.fullJoint_legitimate, information_map, c.auxiliaryJoint_legitimate, information_map]
  simp only [FiniteDistribution.uniform_apply, Fintype.card_fin, ← Finset.mul_sum] at htime
  change _ ≤ information c.timedJoint c.timedCommon (fun z ↦ (z.2.2 z.1).1)
  have hc : c.commonObservation = fun i z ↦
      (z.1.1.1, sequencePrefix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).1) i.val z,
        sequenceSuffix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).2) (i.val + 1) z) := rfl
  have ht : c.timedCommon = fun z ↦ (z.1, c.commonObservation z.1 z.2) := rfl
  rw [ht]
  rw [hc] at htime
  rw [hc]
  exact hdiv.trans (by simpa only [div_eq_mul_inv, mul_comm, timedJoint] using htime)

theorem common_information_le_auxiliary_eavesdropper (c : Code W n) :
    information (c.joint W.receiver₂) (fun z ↦ z.1.1) Prod.snd / n ≤
      information (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₂)
        (fun z ↦ z.1.1) Prod.snd := by
  have hsum := information_le_sum_common_prefix_suffix_right c.fullJoint
    (fun z ↦ z.1.1.1) (fun z j ↦ (z.2 j).1) (fun z j ↦ (z.2 j).2)
  have hdiv := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have htime := average_information_le_joint (FiniteDistribution.uniform (Fin n))
    (fun _ ↦ c.fullJoint) (fun i ↦ c.commonObservation i) (fun i z ↦ (z.2 i).2)
  rw [← c.fullJoint_eavesdropper, information_map, c.auxiliaryJoint_eavesdropper, information_map]
  simp only [FiniteDistribution.uniform_apply, Fintype.card_fin, ← Finset.mul_sum] at htime
  change _ ≤ information c.timedJoint c.timedCommon (fun z ↦ (z.2.2 z.1).2)
  have hc : c.commonObservation = fun i z ↦
      (z.1.1.1, sequencePrefix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).1) i.val z,
        sequenceSuffix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).2) (i.val + 1) z) := rfl
  have ht : c.timedCommon = fun z ↦ (z.1, c.commonObservation z.1 z.2) := rfl
  rw [ht]
  rw [hc] at htime
  rw [hc]
  exact hdiv.trans (by simpa only [div_eq_mul_inv, mul_comm, timedJoint] using htime)

theorem auxiliary_conditional_legitimate_eq_average (c : Code W n) :
    conditional (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₁)
      (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) =
    (n : ℝ)⁻¹ * ∑ i : Fin n, conditional c.fullJoint (fun z ↦ z.1.1.2)
      (fun z ↦ (z.2 i).1) (c.commonObservation i) := by
  rw [c.auxiliaryJoint_legitimate, conditional_map]
  have h := conditional_joint_with_context (FiniteDistribution.uniform (Fin n))
    (fun _ ↦ c.fullJoint) (fun i ↦ c.secretObservation i) (fun i z ↦ (z.2 i).1)
    (fun i ↦ c.commonObservation i)
  have hrow (i : Fin n) :
      conditional c.fullJoint (c.secretObservation i) (fun z ↦ (z.2 i).1) (c.commonObservation i) =
      conditional c.fullJoint (fun z ↦ z.1.1.2) (fun z ↦ (z.2 i).1) (c.commonObservation i) :=
    conditional_pair_condition c.fullJoint (fun z ↦ z.1.1.2) _ (c.commonObservation i)
  simp only [hrow, FiniteDistribution.uniform_apply, Fintype.card_fin, ← Finset.mul_sum] at h
  simpa only [timedJoint, timedCommon, dropSecret, timedSecret, secretObservation, Function.comp_def] using h

theorem auxiliary_conditional_eavesdropper_eq_average (c : Code W n) :
    conditional (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₂)
      (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) =
    (n : ℝ)⁻¹ * ∑ i : Fin n, conditional c.fullJoint (fun z ↦ z.1.1.2)
      (fun z ↦ (z.2 i).2) (c.commonObservation i) := by
  rw [c.auxiliaryJoint_eavesdropper, conditional_map]
  have h := conditional_joint_with_context (FiniteDistribution.uniform (Fin n))
    (fun _ ↦ c.fullJoint) (fun i ↦ c.secretObservation i) (fun i z ↦ (z.2 i).2)
    (fun i ↦ c.commonObservation i)
  have hrow (i : Fin n) :
      conditional c.fullJoint (c.secretObservation i) (fun z ↦ (z.2 i).2) (c.commonObservation i) =
      conditional c.fullJoint (fun z ↦ z.1.1.2) (fun z ↦ (z.2 i).2) (c.commonObservation i) :=
    conditional_pair_condition c.fullJoint (fun z ↦ z.1.1.2) _ (c.commonObservation i)
  simp only [hrow, FiniteDistribution.uniform_apply, Fintype.card_fin, ← Finset.mul_sum] at h
  simpa only [timedJoint, timedCommon, dropSecret, timedSecret, secretObservation, Function.comp_def] using h

omit [NeZero n] in
theorem conditional_commonObservation_swap {O : Type*} [Fintype O]
    (c : Code W n) (i : Fin n) (output : c.FullSample → O) :
    conditional c.fullJoint (fun z ↦ z.1.1.2) output (c.commonObservation i) =
    conditional c.fullJoint (fun z ↦ z.1.1.2) output
      (fun z ↦ ((sequencePrefix (fun z j ↦ (z.2 j).1) i.val z,
        sequenceSuffix (fun z j ↦ (z.2 j).2) (i.val + 1) z), z.1.1.1)) := by
  change conditional c.fullJoint (fun z ↦ z.1.1.2) output
    (fun z ↦ (z.1.1.1, sequencePrefix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).1) i.val z,
      sequenceSuffix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).2) (i.val + 1) z)) = _
  exact conditional_condition_comp_injective c.fullJoint (fun z ↦ z.1.1.2) output
    (fun z ↦ ((sequencePrefix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).1) i.val z,
      sequenceSuffix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).2) (i.val + 1) z), z.1.1.1))
    Prod.swap Prod.swap_injective

theorem secrecy_difference_eq (c : Code W n) :
    conditional (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₁)
      (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) -
    conditional (auxiliaryJoint c.auxiliaryLaw c.prefixing W.receiver₂)
      (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) =
    (conditional (c.joint W.receiver₁) (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) -
      conditional (c.joint W.receiver₂) (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1)) / n := by
  rw [auxiliary_conditional_legitimate_eq_average, auxiliary_conditional_eavesdropper_eq_average,
    ← mul_sub, ← Finset.sum_sub_distrib,
    ← c.fullJoint_legitimate, conditional_map, ← c.fullJoint_eavesdropper, conditional_map]
  have h := csiszar_sum_identity c.fullJoint (fun z ↦ z.1.1.2) (fun z ↦ z.1.1.1)
    (fun z j ↦ (z.2 j).1) (fun z j ↦ (z.2 j).2)
  simp_rw [conditional_commonObservation_swap]
  rw [← h]
  simp only [Function.comp_def]
  ring

end CapacityAtlas.ConfidentialBroadcast.Code
