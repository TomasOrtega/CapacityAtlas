/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Basic
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation.Disintegration

open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

@[capacity_shared_api]
theorem map_equiv_apply {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (p : FiniteDistribution A) (e : A ≃ B) (b : B) : p.map e b = p (e.symm b) := by
  classical
  change (∑ a with e a = b, p a) = _
  simp [Equiv.apply_eq_iff_eq_symm_apply, Finset.sum_filter]

end CapacityAtlas.FiniteDistribution

namespace CapacityAtlas.FiniteInformation

variable {Ω A B C A' B' C' : Type*} [Fintype Ω] [Fintype A] [Fintype B]
  [Fintype C] [Fintype A'] [Fintype B'] [Fintype C']

@[capacity_shared_api]
theorem information_equiv (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B)
    (e : A ≃ A') (d : B ≃ B') :
    information p (e ∘ f) (d ∘ g) = information p f g := by
  have hab := entropy_comp_injective p (fun ω ↦ (f ω, g ω))
    (e.prodCongr d) (e.prodCongr d).injective
  unfold information
  rw [entropy_comp_injective _ _ e e.injective, entropy_comp_injective _ _ d d.injective]
  exact congrArg (fun x ↦ entropy p f + entropy p g - x) hab

@[capacity_shared_api]
theorem conditional_equiv (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B)
    (h : Ω → C) (e : A ≃ A') (d : B ≃ B') (k : C ≃ C') :
    conditional p (e ∘ f) (d ∘ g) (k ∘ h) = conditional p f g h := by
  have hfh := entropy_comp_injective p (fun ω ↦ (f ω, h ω))
    (e.prodCongr k) (e.prodCongr k).injective
  have hgh := entropy_comp_injective p (fun ω ↦ (g ω, h ω))
    (d.prodCongr k) (d.prodCongr k).injective
  have htrip := entropy_comp_injective p (fun ω ↦ (f ω, g ω, h ω))
    (e.prodCongr (d.prodCongr k)) (e.prodCongr (d.prodCongr k)).injective
  unfold conditional
  rw [entropy_comp_injective _ _ k k.injective]
  change entropy p ((e.prodCongr k) ∘ (fun ω ↦ (f ω, h ω))) +
    entropy p ((d.prodCongr k) ∘ (fun ω ↦ (g ω, h ω))) - entropy p h -
    entropy p ((e.prodCongr (d.prodCongr k)) ∘ (fun ω ↦ (f ω, g ω, h ω))) = _
  rw [hfh, hgh, htrip]

end CapacityAtlas.FiniteInformation

namespace CapacityAtlas.ConfidentialBroadcast

open FiniteInformation

variable {U V X O : Type*} [Fintype U] [Fintype V] [Fintype X] [Fintype O]

theorem auxiliaryJoint_equiv {U' V' : Type*} [Fintype U'] [Fintype V']
    [DecidableEq U'] [DecidableEq V'] [DecidableEq O]
    (p : FiniteDistribution (U × V)) (P : FiniteChannel V X) (W : FiniteChannel X O)
    (e : U ≃ U') (d : V ≃ V') :
    auxiliaryJoint (p.map (e.prodCongr d)) (P.encoded d.symm) W =
      (auxiliaryJoint p P W).map ((e.prodCongr d).prodCongr (Equiv.refl O)) := by
  ext z
  rw [FiniteDistribution.map_equiv_apply]
  change p.map (e.prodCongr d) z.1 *
    (W.comp (P.encoded d.symm)).transition z.1.2 z.2 = _
  rw [FiniteDistribution.map_equiv_apply]
  rfl

theorem auxiliaryJoint_joint [DecidableEq U] [DecidableEq V] [DecidableEq O]
    (p : FiniteDistribution U) (q : U → FiniteDistribution V)
    (P : FiniteChannel V X) (W : FiniteChannel X O) :
    auxiliaryJoint (p.joint q) P W =
      (p.joint (fun u ↦ joint (q u) (W.comp P))).map
        (Equiv.prodAssoc U V O).symm := by
  classical
  ext z
  rw [FiniteDistribution.map_equiv_apply]
  change (p z.1.1 * q z.1.1 z.1.2) * (W.comp P).transition z.1.2 z.2 =
    p z.1.1 * (q z.1.1 z.1.2 * (W.comp P).transition z.1.2 z.2)
  exact mul_assoc _ _ _

theorem auxiliary_conditional_eq_average (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (P : FiniteChannel V X) (W : FiniteChannel X O) :
    conditional (auxiliaryJoint (p.joint q) P W) (fun z ↦ z.1.2) Prod.snd
      (fun z ↦ z.1.1) = ∑ u, p u * (W.comp P).mutualInformationBits (q u) := by
  classical
  rw [auxiliaryJoint_joint, conditional_map]
  change conditional (p.joint (fun u ↦ joint (q u) (W.comp P)))
    (fun z ↦ z.2.1) (fun z ↦ z.2.2) Prod.fst = _
  rw [conditional_joint]
  simp only [information_joint_fst_snd]

theorem auxiliary_information_equiv {U' V' : Type*} [Fintype U'] [Fintype V']
    [DecidableEq U'] [DecidableEq V']
    (p : FiniteDistribution (U × V)) (P : FiniteChannel V X) (W : FiniteChannel X O)
    (e : U ≃ U') (d : V ≃ V') :
    information (auxiliaryJoint (p.map (e.prodCongr d)) (P.encoded d.symm) W)
      (fun z ↦ z.1.1) Prod.snd =
      information (auxiliaryJoint p P W) (fun z ↦ z.1.1) Prod.snd := by
  classical
  rw [auxiliaryJoint_equiv, information_map]
  exact information_equiv (auxiliaryJoint p P W) (fun z ↦ z.1.1) Prod.snd e (Equiv.refl O)

theorem auxiliary_conditional_equiv {U' V' : Type*} [Fintype U'] [Fintype V']
    [DecidableEq U'] [DecidableEq V']
    (p : FiniteDistribution (U × V)) (P : FiniteChannel V X) (W : FiniteChannel X O)
    (e : U ≃ U') (d : V ≃ V') :
    conditional (auxiliaryJoint (p.map (e.prodCongr d)) (P.encoded d.symm) W)
      (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) =
      conditional (auxiliaryJoint p P W) (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) := by
  classical
  rw [auxiliaryJoint_equiv, conditional_map]
  exact conditional_equiv (auxiliaryJoint p P W) (fun z ↦ z.1.2) Prod.snd
    (fun z ↦ z.1.1) d (Equiv.refl O) e

/-- Arbitrary finite auxiliary alphabets can be relabeled by finite ordinals. -/
theorem mem_auxiliaryRegion_of_finite {Y Z : Type*} [Fintype Y] [Fintype Z]
    (W : FiniteBroadcastChannel X Y Z) (p : FiniteDistribution (U × V))
    (P : FiniteChannel V X) {r : RatePair} (hr₀ : 0 ≤ r.1) (hr₁ : 0 ≤ r.2)
    (hy : r.1 ≤ information (auxiliaryJoint p P W.receiver₁) (fun z ↦ z.1.1) Prod.snd)
    (hz : r.1 ≤ information (auxiliaryJoint p P W.receiver₂) (fun z ↦ z.1.1) Prod.snd)
    (hs : r.2 ≤
      conditional (auxiliaryJoint p P W.receiver₁) (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1) -
      conditional (auxiliaryJoint p P W.receiver₂) (fun z ↦ z.1.2) Prod.snd (fun z ↦ z.1.1)) :
    r ∈ auxiliaryRegion W := by
  classical
  let e := Fintype.equivFin U
  let d := Fintype.equivFin V
  refine ⟨hr₀, hr₁, Fintype.card U, Fintype.card V, p.map (e.prodCongr d),
    P.encoded d.symm, ?_, ?_, ?_⟩
  · simpa only [auxiliary_information_equiv] using hy
  · simpa only [auxiliary_information_equiv] using hz
  · simpa only [auxiliary_conditional_equiv] using hs

theorem auxiliary_information_eq_composed (p : FiniteDistribution U)
    (q : U → FiniteDistribution V) (P : FiniteChannel V X) (W : FiniteChannel X O) :
    information (auxiliaryJoint (p.joint q) P W) (fun z ↦ z.1.1) Prod.snd =
      ((W.comp P).comp (FiniteChannel.ofRows q)).mutualInformationBits p := by
  classical
  have hmap : (auxiliaryJoint (p.joint q) P W).map (fun z ↦ (z.1.1, z.2)) =
      joint p ((W.comp P).comp (FiniteChannel.ofRows q)) := by
    rw [auxiliaryJoint_joint, FiniteDistribution.map_map]
    change (p.joint (fun u ↦ joint (q u) (W.comp P))).map
      (fun z ↦ (z.1, z.2.2)) = _
    rw [FiniteDistribution.map_joint_snd]
    simp only [joint, FiniteDistribution.map_snd_joint]
    rfl
  have hinfo := information_map (auxiliaryJoint (p.joint q) P W)
    (fun z ↦ (z.1.1, z.2)) Prod.fst Prod.snd
  rw [hmap, information_joint_fst_snd] at hinfo
  exact hinfo.symm

end CapacityAtlas.ConfidentialBroadcast
