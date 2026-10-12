/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Basic
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation.Identities
import CapacityAtlasForMathlib.InformationTheory.FiniteProductDistribution

open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B] [DecidableEq I]

@[capacity_shared_api]
theorem map_productFamily_splitAt [DecidableEq A]
    (rows : I → FiniteDistribution A) (i : I) :
    (productFamily rows).map (Equiv.funSplitAt i A) =
      (rows i).joint (fun _ ↦ productFamily (fun j : {j // j ≠ i} ↦ rows j)) := by
  classical
  ext pair
  obtain ⟨word, rfl⟩ := (Equiv.funSplitAt i A).surjective pair
  change (∑ other with Equiv.funSplitAt i A other = Equiv.funSplitAt i A word,
    productFamily rows other) = rows i (word i) * ∏ j : {j // j ≠ i}, rows j (word j)
  simp only [(Equiv.funSplitAt i A).injective.eq_iff, Finset.sum_filter,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, productFamily_apply]
  exact Fintype.prod_eq_mul_prod_subtype_ne (fun j ↦ rows j (word j)) i

/-- A function of all other coordinates is independent of the selected coordinate. -/
@[capacity_shared_api]
theorem map_productFamily_observation_coordinate [DecidableEq A] [DecidableEq B]
    (rows : I → FiniteDistribution A) (i : I) (f : (I → A) → B)
    (hf : ∀ word a, f (Function.update word i a) = f word) :
    (productFamily rows).map (fun word ↦ (f word, word i)) =
      ((productFamily rows).map f).joint (fun _ ↦ rows i) := by
  classical
  let a₀ := Classical.choice (rows i).nonempty
  let e := Equiv.funSplitAt i A
  let rest := productFamily (fun j : {j // j ≠ i} ↦ rows j)
  let observe := fun z : {j // j ≠ i} → A ↦ f (e.symm (a₀, z))
  have hfrest (word : I → A) : f word = observe (fun j : {j // j ≠ i} ↦ word j) := by
    have heq : e.symm (a₀, fun j : {j // j ≠ i} ↦ word j) =
        Function.update word i a₀ := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
      · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hji, Function.update_of_ne]
    dsimp [observe]
    rw [heq, hf]
  have hmap : (productFamily rows).map (fun word ↦ (f word, word i)) =
      (rest.map observe).joint (fun _ ↦ rows i) := by
    calc
      _ = ((productFamily rows).map e).map (fun pair ↦ (observe pair.2, pair.1)) := by
        rw [map_map]
        congr 1
        funext word
        exact Prod.ext (hfrest word) rfl
      _ = ((rows i).joint (fun _ ↦ rest)).map (fun pair ↦ (observe pair.2, pair.1)) := by
        rw [map_productFamily_splitAt]
      _ = ((rows i).joint (fun _ ↦ rest.map observe)).map Prod.swap := by
        rw [← map_joint_snd, map_map]
        rfl
      _ = (rest.map observe).joint (fun _ ↦ rows i) := by
        ext pair
        change (∑ z : A × B with z.swap = pair, rows i z.1 * rest.map observe z.2) =
          rest.map observe pair.1 * rows i pair.2
        rcases pair with ⟨b, a⟩
        simp [Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and, mul_comm]
  have hmarginal : (productFamily rows).map f = rest.map observe := by
    have h := congrArg (fun d : FiniteDistribution (B × A) ↦ d.map Prod.fst) hmap
    simpa only [map_map, Function.comp_def, map_fst_joint] using h
  rw [hmap, hmarginal]

@[capacity_shared_api]
theorem map_joint_eq_mixture {C : Type*} [Fintype C] [DecidableEq C]
    (p : FiniteDistribution A) (rows : A → FiniteDistribution B) (f : A × B → C) :
    (p.joint rows).map f = p.mixture (fun a ↦ (rows a).map (fun b ↦ f (a, b))) := by
  classical
  ext c
  change (∑ z with f z = c, p z.1 * rows z.1 z.2) =
    ∑ a, p a * ∑ b with f (a, b) = c, rows a b
  simp only [Finset.sum_filter, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

end CapacityAtlas.FiniteDistribution

namespace CapacityAtlas.FiniteInformation

@[capacity_shared_api]
theorem joint_comp {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq C]
    (p : FiniteDistribution A) (V : FiniteChannel A B) (W : FiniteChannel B C) :
    ((joint p V).joint (fun a ↦ W.rowDistribution a.2)).map (fun z ↦ (z.1.1, z.2)) =
      joint p (W.comp V) := by
  classical
  ext point
  rcases point with ⟨a, c⟩
  change (∑ z : (A × B) × C with (z.1.1, z.2) = (a, c),
    (p z.1.1 * V.transition z.1.1 z.1.2) * W.transition z.1.2 z.2) =
      p a * ∑ b, V.transition a b * W.transition b c
  simp [Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and,
    Finset.mul_sum, mul_assoc]

end CapacityAtlas.FiniteInformation

namespace CapacityAtlas.FiniteChannel

variable {I A X O V : Type*} [Fintype I] [Fintype A] [Fintype X]
  [Fintype O] [Fintype V] [DecidableEq I]

/-- An observation omitting one output coordinate leaves its physical channel law intact. -/
@[capacity_shared_api]
theorem product_joint_coordinate [DecidableEq X] [DecidableEq O] [DecidableEq V]
    (W : FiniteChannel X O) (p : FiniteDistribution A) (input : A → I → X)
    (observe : A → (I → O) → V) (i : I)
    (hobserve : ∀ a word o, observe a (Function.update word i o) = observe a word) :
    let full := p.joint (fun a ↦ FiniteDistribution.productFamily
      (fun j ↦ W.rowDistribution (input a j)))
    full.map (fun z ↦ ((observe z.1 z.2, input z.1 i), z.2 i)) =
      (full.map (fun z ↦ (observe z.1 z.2, input z.1 i))).joint
        (fun v ↦ W.rowDistribution v.2) := by
  classical
  dsimp only
  rw [FiniteDistribution.map_joint_eq_mixture, FiniteDistribution.map_joint_eq_mixture]
  have hrow (a : A) :
      (FiniteDistribution.productFamily (fun j ↦ W.rowDistribution (input a j))).map
          (fun word ↦ ((observe a word, input a i), word i)) =
        ((FiniteDistribution.productFamily (fun j ↦ W.rowDistribution (input a j))).map
          (fun word ↦ (observe a word, input a i))).joint
            (fun _ ↦ W.rowDistribution (input a i)) :=
    FiniteDistribution.map_productFamily_observation_coordinate _ i
      (fun word ↦ (observe a word, input a i)) (fun word o ↦ by rw [hobserve])
  ext point
  rcases point with ⟨⟨v, x⟩, o⟩
  simp only [FiniteDistribution.mixture_apply, hrow, FiniteDistribution.joint_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : input a i = x
  · simp only [hx, mul_assoc]
  · have hzero :
        (FiniteDistribution.productFamily (fun j ↦ W.rowDistribution (input a j))).map
          (fun word ↦ (observe a word, input a i)) (v, x) = 0 := by
      change (∑ word with (observe a word, input a i) = (v, x), _) = 0
      simp [Prod.mk.injEq, hx]
    rw [hzero]
    ring

end CapacityAtlas.FiniteChannel

namespace CapacityAtlas.ConfidentialBroadcast

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/-- Independent receiver noises give a joint law with the prescribed marginals. -/
def receiverPair (W : FiniteBroadcastChannel X Y Z) : FiniteChannel X (Y × Z) :=
  FiniteChannel.ofRows fun x ↦
    (W.receiver₁.rowDistribution x).joint (fun _ ↦ W.receiver₂.rowDistribution x)

namespace Code

variable {W : FiniteBroadcastChannel X Y Z} {n : ℕ}

abbrev FullSample (c : Code W n) :=
  ((Fin c.commonCount × Fin c.secretCount) × (Fin n → X)) × (Fin n → Y × Z)

noncomputable def fullJoint (c : Code W n) : FiniteDistribution c.FullSample :=
  (FiniteInformation.joint c.messages c.encode).joint fun a ↦
    FiniteDistribution.productFamily (fun i ↦ (receiverPair W).rowDistribution (a.2 i))

abbrev CommonAux (c : Code W n) :=
  Fin c.commonCount × (Fin n → Option Y) × (Fin n → Option Z)

abbrev SecretAux (c : Code W n) := Fin c.secretCount × c.CommonAux

def commonObservation (c : Code W n) (i : Fin n) (z : c.FullSample) : c.CommonAux :=
  (z.1.1.1,
    FiniteInformation.sequencePrefix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).1) i.val z,
    FiniteInformation.sequenceSuffix (fun z : c.FullSample ↦ fun j ↦ (z.2 j).2) (i.val + 1) z)

def secretObservation (c : Code W n) (i : Fin n) (z : c.FullSample) : c.SecretAux :=
  (z.1.1.2, c.commonObservation i z)

private theorem secretObservation_update (c : Code W n) (i : Fin n)
    (a : (Fin c.commonCount × Fin c.secretCount) × (Fin n → X))
    (word : Fin n → Y × Z) (o : Y × Z) :
    c.secretObservation i (a, Function.update word i o) = c.secretObservation i (a, word) := by
  dsimp only [secretObservation, commonObservation]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext j
    dsimp [secretObservation, commonObservation, FiniteInformation.sequencePrefix]
    by_cases hji : j.val < i.val
    · have hne : j ≠ i := by intro h; subst j; omega
      simp only [hji, if_true, Function.update_of_ne hne]
    · simp only [hji, if_false]
  · funext j
    dsimp [secretObservation, commonObservation, FiniteInformation.sequenceSuffix]
    by_cases hij : i.val + 1 ≤ j.val
    · have hne : j ≠ i := by intro h; subst j; omega
      simp only [hij, if_true, Function.update_of_ne hne]
    · simp only [hij, if_false]

variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

noncomputable local instance (c : Code W n) : DecidableEq c.SecretAux := Classical.typeDecidableEq _

@[capacity_shared_api]
theorem fullJoint_coordinate_pair (c : Code W n) (i : Fin n) :
    c.fullJoint.map (fun z ↦ ((c.secretObservation i z, z.1.2 i), z.2 i)) =
      (c.fullJoint.map (fun z ↦ (c.secretObservation i z, z.1.2 i))).joint
        (fun v ↦ (receiverPair W).rowDistribution v.2) := by
  classical
  exact (receiverPair W).product_joint_coordinate
    (FiniteInformation.joint c.messages c.encode) Prod.snd
    (fun a word ↦ c.secretObservation i (a, word)) i
    (c.secretObservation_update i)

@[capacity_shared_api]
theorem fullJoint_coordinate_legitimate (c : Code W n) (i : Fin n) :
    c.fullJoint.map (fun z ↦ ((c.secretObservation i z, z.1.2 i), (z.2 i).1)) =
      (c.fullJoint.map (fun z ↦ (c.secretObservation i z, z.1.2 i))).joint
        (fun v ↦ W.receiver₁.rowDistribution v.2) := by
  classical
  have h := congrArg (fun p : FiniteDistribution ((c.SecretAux × X) × (Y × Z)) ↦
    p.map (fun z ↦ (z.1, z.2.1)))
    (c.fullJoint_coordinate_pair i)
  simpa only [FiniteDistribution.map_map, Function.comp_def,
    FiniteDistribution.map_joint_snd, receiverPair, FiniteChannel.rowDistribution_ofRows,
    FiniteDistribution.map_fst_joint] using h

@[capacity_shared_api]
theorem fullJoint_coordinate_eavesdropper (c : Code W n) (i : Fin n) :
    c.fullJoint.map (fun z ↦ ((c.secretObservation i z, z.1.2 i), (z.2 i).2)) =
      (c.fullJoint.map (fun z ↦ (c.secretObservation i z, z.1.2 i))).joint
        (fun v ↦ W.receiver₂.rowDistribution v.2) := by
  classical
  have h := congrArg (fun p : FiniteDistribution ((c.SecretAux × X) × (Y × Z)) ↦
    p.map (fun z ↦ (z.1, z.2.2)))
    (c.fullJoint_coordinate_pair i)
  simpa only [FiniteDistribution.map_map, Function.comp_def,
    FiniteDistribution.map_joint_snd, receiverPair, FiniteChannel.rowDistribution_ofRows,
    FiniteDistribution.map_snd_joint, FiniteDistribution.mixture_const] using h

omit [DecidableEq Y] [DecidableEq Z] in
@[capacity_shared_api]
theorem fullJoint_observe {O : Type*} [Fintype O] [DecidableEq O]
    (c : Code W n) (V : FiniteChannel X O) (observe : Y × Z → O)
    (hobserve : ∀ x, ((receiverPair W).rowDistribution x).map observe = V.rowDistribution x) :
    c.fullJoint.map (fun z ↦ (z.1.1, fun j ↦ observe (z.2 j))) = c.joint V := by
  classical
  have hrows (a : (Fin c.commonCount × Fin c.secretCount) × (Fin n → X)) :
      (FiniteDistribution.productFamily (fun i ↦ (receiverPair W).rowDistribution (a.2 i))).map
        (fun word j ↦ observe (word j)) = (V.block n).rowDistribution a.2 := by
    rw [FiniteDistribution.map_productFamily]
    simp_rw [hobserve]
    rfl
  have hfirst : c.fullJoint.map (fun z ↦ (z.1, fun j ↦ observe (z.2 j))) =
      (FiniteInformation.joint c.messages c.encode).joint
        (fun a ↦ (V.block n).rowDistribution a.2) := by
    rw [fullJoint]
    rw [(FiniteInformation.joint c.messages c.encode).map_joint_snd
      (fun a ↦ FiniteDistribution.productFamily
        (fun i ↦ (receiverPair W).rowDistribution (a.2 i)))
      (fun word j ↦ observe (word j))]
    congr 1
    funext a
    exact hrows a
  have h := congrArg
    (fun p : FiniteDistribution (((Fin c.commonCount × Fin c.secretCount) × (Fin n → X)) ×
      (Fin n → O)) ↦ p.map (fun z ↦ (z.1.1, z.2))) hfirst
  simpa only [FiniteDistribution.map_map, Function.comp_def, FiniteInformation.joint_comp,
    joint, induced] using h

omit [DecidableEq Z] in
@[capacity_shared_api]
theorem fullJoint_legitimate (c : Code W n) :
    c.fullJoint.map (fun z ↦ (z.1.1, fun j ↦ (z.2 j).1)) = c.joint W.receiver₁ := by
  classical
  apply c.fullJoint_observe W.receiver₁ Prod.fst
  intro x
  change ((W.receiver₁.rowDistribution x).joint
    (fun _ ↦ W.receiver₂.rowDistribution x)).map Prod.fst = W.receiver₁.rowDistribution x
  exact FiniteDistribution.map_fst_joint (W.receiver₁.rowDistribution x)
    (fun _ ↦ W.receiver₂.rowDistribution x)

omit [DecidableEq Y] in
@[capacity_shared_api]
theorem fullJoint_eavesdropper (c : Code W n) :
    c.fullJoint.map (fun z ↦ (z.1.1, fun j ↦ (z.2 j).2)) = c.joint W.receiver₂ := by
  classical
  apply c.fullJoint_observe W.receiver₂ Prod.snd
  intro x
  change ((W.receiver₁.rowDistribution x).joint
    (fun _ ↦ W.receiver₂.rowDistribution x)).map Prod.snd = W.receiver₂.rowDistribution x
  simpa only [FiniteDistribution.mixture_const] using
    FiniteDistribution.map_snd_joint (W.receiver₁.rowDistribution x)
      (fun _ ↦ W.receiver₂.rowDistribution x)

end Code

end CapacityAtlas.ConfidentialBroadcast
