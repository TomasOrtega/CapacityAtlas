/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteMixture
import CapacityAtlasForMathlib.InformationTheory.DecoderSideInformation

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteDistribution

variable {I A B C : Type*} [Fintype I] [Fintype A] [Fintype B] [Fintype C]

/-- An injective observation preserves finite entropy. -/
@[capacity_shared_api]
theorem entropy_map_of_injective [DecidableEq B] (distribution : FiniteDistribution A)
    (f : A → B) (hf : Function.Injective f) :
    (distribution.map f).entropy = distribution.entropy := by
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSpace B := ⊤
  rw [entropy_map_eq_probabilityTheory, entropy_eq_probabilityTheory]
  exact ProbabilityTheory.entropy_comp_of_injective distribution.toPMF.toMeasure measurable_id f hf

@[simp, capacity_shared_api]
theorem map_fst_joint [DecidableEq A] (distribution : FiniteDistribution A)
    (rows : A → FiniteDistribution B) :
    (distribution.joint rows).map Prod.fst = distribution := by
  ext a
  change (∑ x : A × B with x.1 = a, distribution x.1 * rows x.1 x.2) = distribution a
  simp [Finset.sum_filter, Fintype.sum_prod_type, ← Finset.mul_sum]

@[simp, capacity_shared_api]
theorem map_snd_joint [DecidableEq B] (distribution : FiniteDistribution A)
    (rows : A → FiniteDistribution B) :
    (distribution.joint rows).map Prod.snd = mixture distribution rows := by
  ext b
  change (∑ x : A × B with x.2 = b, distribution x.1 * rows x.1 x.2) =
    ∑ a, distribution a * rows a b
  simp [Finset.sum_filter, Fintype.sum_prod_type]

@[capacity_shared_api]
theorem map_joint_snd [DecidableEq A] [DecidableEq C] (distribution : FiniteDistribution A)
    (rows : A → FiniteDistribution B) (f : B → C) :
    (distribution.joint rows).map (fun x ↦ (x.1, f x.2)) =
      distribution.joint (fun a ↦ (rows a).map f) := by
  classical
  ext x
  change (∑ y : A × B with (y.1, f y.2) = x, distribution y.1 * rows y.1 y.2) =
    distribution x.1 * ∑ b with f b = x.2, rows x.1 b
  rcases x with ⟨a, c⟩
  simp [Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, Finset.mul_sum,
    mul_ite, ite_and]

@[capacity_shared_api]
theorem map_mixture [DecidableEq B] (weights : FiniteDistribution I)
    (rows : I → FiniteDistribution A) (f : A → B) :
    (mixture weights rows).map f = mixture weights (fun i ↦ (rows i).map f) := by
  ext b
  change (∑ a with f a = b, ∑ i, weights i * rows i a) =
    ∑ i, weights i * ∑ a with f a = b, rows i a
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]

@[simp, capacity_shared_api]
theorem mixture_const (weights : FiniteDistribution I) (distribution : FiniteDistribution A) :
    mixture weights (fun _ ↦ distribution) = distribution := by
  ext a
  simp [mixture_apply, ← Finset.sum_mul]

@[capacity_shared_api]
theorem entropy_of_subsingleton [Subsingleton A] (distribution : FiniteDistribution A) :
    distribution.entropy = 0 := by
  letI : Unique A := ⟨⟨Classical.choice distribution.nonempty⟩, fun _ ↦ Subsingleton.elim _ _⟩
  apply le_antisymm _ distribution.entropy_nonnegative
  simpa using distribution.entropy_le_log_card

/-- Joint entropy is at most the sum of the marginal entropies. -/
@[capacity_shared_api]
theorem entropy_le_entropy_fst_add_entropy_snd [DecidableEq A] [DecidableEq B]
    (distribution : FiniteDistribution (A × B)) :
    distribution.entropy ≤
      (distribution.map Prod.fst).entropy + (distribution.map Prod.snd).entropy := by
  have h := distribution.entropy_map_strong_subadditivity
    Prod.fst Prod.snd (fun _ ↦ ())
  have hleft : Function.Injective (fun x : A × B ↦ (x.1, (x.2, ()))) := by
    intro x y hxy
    exact Prod.ext (Prod.mk.inj hxy).1 (Prod.mk.inj (Prod.mk.inj hxy).2).1
  have hfst := (distribution.map Prod.fst).entropy_map_of_injective
    (fun a ↦ (a, ())) (by intro a b h; exact (Prod.mk.inj h).1)
  have hsnd := (distribution.map Prod.snd).entropy_map_of_injective
    (fun b ↦ (b, ())) (by intro a b h; exact (Prod.mk.inj h).1)
  rw [distribution.entropy_map_of_injective _ hleft,
    (distribution.map (fun _ ↦ ())).entropy_of_subsingleton, add_zero] at h
  simp only [map_map, Function.comp_def] at hfst hsnd
  rwa [hfst, hsnd] at h

/-- Independent rows remain a source of conditional entropy after their index is hidden. -/
@[capacity_shared_api]
theorem entropy_mixture_product_ge [DecidableEq A] [DecidableEq B]
    (weights : FiniteDistribution I) (left : I → FiniteDistribution A)
    (right : I → FiniteDistribution B) :
    (mixture weights left).entropy + (∑ i, weights i * (right i).entropy) ≤
      (mixture weights (fun i ↦ (left i).joint fun _ ↦ right i)).entropy := by
  classical
  let rows := fun i ↦ (left i).joint fun _ ↦ right i
  let joint := weights.joint rows
  have h := joint.entropy_map_strong_subadditivity
    Prod.fst (fun x ↦ x.2.2) (fun x ↦ x.2.1)
  have hinj : Function.Injective (fun x : I × (A × B) ↦ (x.1, (x.2.2, x.2.1))) := by
    intro x y hxy
    rcases Prod.mk.inj hxy with ⟨h1, h2⟩
    rcases Prod.mk.inj h2 with ⟨h3, h4⟩
    exact Prod.ext h1 (Prod.ext h4 h3)
  rw [joint.entropy_map_of_injective _ hinj] at h
  have hfirst : joint.map (fun x ↦ (x.1, x.2.1)) = weights.joint left := by
    simpa only [joint, rows, map_fst_joint] using
      weights.map_joint_snd rows Prod.fst
  have hpast : joint.map (fun x ↦ x.2.1) = mixture weights left := by
    have heq := congrArg (fun d : FiniteDistribution (I × A) ↦ d.map Prod.snd) hfirst
    simpa only [map_map, Function.comp_def, joint, map_snd_joint] using heq
  have hpair :
      (joint.map (fun x ↦ (x.2.2, x.2.1))).entropy = (mixture weights rows).entropy := by
    have heq := (joint.map Prod.snd).entropy_map_of_injective Prod.swap Prod.swap_injective
    rw [map_map] at heq
    change (joint.map (fun x ↦ (x.2.2, x.2.1))).entropy = (joint.map Prod.snd).entropy at heq
    rw [show joint.map Prod.snd = mixture weights rows from weights.map_snd_joint rows] at heq
    exact heq
  rw [hfirst, hpast, hpair] at h
  have hsum : joint.entropy = weights.entropy +
      (∑ i, weights i * (left i).entropy) + ∑ i, weights i * (right i).entropy := by
    simp [joint, rows, entropy_joint, ← Finset.sum_mul,
      mul_add, Finset.sum_add_distrib, add_assoc]
  rw [hsum, entropy_joint] at h
  linarith

end FiniteDistribution

namespace FiniteChannel

variable {M J A B T : Type*}
  [Fintype M] [Fintype J] [Fintype A] [Fintype B] [Fintype T]

/-- Apply a deterministic observation to a channel's output. -/
@[capacity_shared_api]
noncomputable def relabelOutput [DecidableEq B] (channel : FiniteChannel M A)
    (f : A → B) : FiniteChannel M B :=
  ofRows fun m ↦ (channel.rowDistribution m).map f

@[simp, capacity_shared_api]
theorem rowDistribution_relabelOutput [DecidableEq B] (channel : FiniteChannel M A)
    (f : A → B) (m : M) :
    (channel.relabelOutput f).rowDistribution m = (channel.rowDistribution m).map f := rfl

@[capacity_shared_api]
theorem outputDistribution_relabelOutput [DecidableEq B] (channel : FiniteChannel M A)
    (f : A → B) (input : FiniteDistribution M) :
    (channel.relabelOutput f).outputDistribution input =
      (channel.outputDistribution input).map f := by
  exact (FiniteDistribution.map_mixture input channel.rowDistribution f).symm

/-- An injective output relabeling preserves mutual information. -/
@[capacity_shared_api]
theorem relabelOutput_mutualInformation [DecidableEq B] (channel : FiniteChannel M A)
    (f : A → B) (hf : Function.Injective f) (input : FiniteDistribution M) :
    (channel.relabelOutput f).mutualInformation input = channel.mutualInformation input := by
  simp only [mutualInformation, outputDistribution_relabelOutput,
    FiniteDistribution.entropy_map_of_injective _ f hf, conditionalOutputEntropy,
    rowDistribution_relabelOutput]

/-- A past observation with an independent finite latent index hidden from its observer. -/
@[capacity_shared_api]
noncomputable def latentPast (weights : FiniteDistribution J)
    (past : M → J → FiniteDistribution A) : FiniteChannel M A :=
  ofRows fun m ↦ FiniteDistribution.mixture weights (past m)

/-- Append a channel observation conditionally independent of the past given message and index. -/
@[capacity_shared_api]
noncomputable def latentExtension (weights : FiniteDistribution J)
    (past : M → J → FiniteDistribution A) (next : FiniteChannel T B)
    (strategy : M → J → T) : FiniteChannel M (A × B) :=
  ofRows fun m ↦ FiniteDistribution.mixture weights fun j ↦
    (past m j).joint fun _ ↦ next.rowDistribution (strategy m j)

@[simp, capacity_shared_api]
theorem latentPast_transition (weights : FiniteDistribution J)
    (past : M → J → FiniteDistribution A) (m : M) (a : A) :
    (latentPast weights past).transition m a = ∑ j, weights j * past m j a := rfl

@[simp, capacity_shared_api]
theorem latentExtension_transition (weights : FiniteDistribution J)
    (past : M → J → FiniteDistribution A) (next : FiniteChannel T B)
    (strategy : M → J → T) (m : M) (output : A × B) :
    (latentExtension weights past next strategy).transition m output =
      ∑ j, weights j * (past m j output.1 * next.transition (strategy m j) output.2) := rfl

@[simp, capacity_shared_api]
theorem rowDistribution_latentPast (weights : FiniteDistribution J)
    (past : M → J → FiniteDistribution A) (m : M) :
    (latentPast weights past).rowDistribution m =
      FiniteDistribution.mixture weights (past m) := rfl

@[simp, capacity_shared_api]
theorem rowDistribution_latentExtension (weights : FiniteDistribution J)
    (past : M → J → FiniteDistribution A) (next : FiniteChannel T B)
    (strategy : M → J → T) (m : M) :
    (latentExtension weights past next strategy).rowDistribution m =
      FiniteDistribution.mixture weights (fun j ↦
        (past m j).joint fun _ ↦ next.rowDistribution (strategy m j)) := rfl

@[capacity_shared_api]
theorem latentExtension_output_fst [DecidableEq A] (weights : FiniteDistribution J)
    (past : M → J → FiniteDistribution A) (next : FiniteChannel T B)
    (strategy : M → J → T) (input : FiniteDistribution M) :
    ((latentExtension weights past next strategy).outputDistribution input).map Prod.fst =
      (latentPast weights past).outputDistribution input := by
  change (FiniteDistribution.mixture input _).map Prod.fst = _
  simp only [FiniteDistribution.map_mixture,
    FiniteDistribution.map_fst_joint]
  rfl

@[capacity_shared_api]
theorem latentExtension_output_snd [DecidableEq B] [DecidableEq T]
    (weights : FiniteDistribution J) (past : M → J → FiniteDistribution A)
    (next : FiniteChannel T B) (strategy : M → J → T) (input : FiniteDistribution M) :
    ((latentExtension weights past next strategy).outputDistribution input).map Prod.snd =
      next.outputDistribution
        ((input.joint fun _ ↦ weights).map fun mj ↦ strategy mj.1 mj.2) := by
  change (FiniteDistribution.mixture input _).map Prod.snd = _
  simp only [FiniteDistribution.map_mixture,
    FiniteDistribution.map_snd_joint, FiniteDistribution.mixture_const]
  ext b
  rw [outputDistribution_apply, FiniteDistribution.sum_map_mul]
  simp only [FiniteDistribution.mixture_apply, Fintype.sum_prod_type,
    FiniteDistribution.joint_apply, Finset.mul_sum, mul_assoc, rowDistribution_apply]

/-- The information in one additional observation is bounded by its channel's information. -/
@[capacity_shared_api]
theorem latentExtension_mutualInformation_le [DecidableEq T]
    (weights : FiniteDistribution J) (past : M → J → FiniteDistribution A)
    (next : FiniteChannel T B) (strategy : M → J → T) (input : FiniteDistribution M) :
    (latentExtension weights past next strategy).mutualInformation input ≤
      (latentPast weights past).mutualInformation input +
        next.mutualInformation
          ((input.joint fun _ ↦ weights).map fun mj ↦ strategy mj.1 mj.2) := by
  classical
  let d := (input.joint fun _ ↦ weights).map fun mj ↦ strategy mj.1 mj.2
  have hout := FiniteDistribution.entropy_le_entropy_fst_add_entropy_snd
    ((latentExtension weights past next strategy).outputDistribution input)
  rw [latentExtension_output_fst, latentExtension_output_snd] at hout
  have hrows : (latentPast weights past).conditionalOutputEntropy input +
      next.conditionalOutputEntropy d ≤
        (latentExtension weights past next strategy).conditionalOutputEntropy input := by
    have h := Finset.sum_le_sum fun m (_ : m ∈ (Finset.univ : Finset M)) ↦
      mul_le_mul_of_nonneg_left
        (FiniteDistribution.entropy_mixture_product_ge weights (past m)
          (fun j ↦ next.rowDistribution (strategy m j))) (input.nonnegative m)
    simp only [conditionalOutputEntropy, rowDistribution_latentPast,
      rowDistribution_latentExtension, d, FiniteDistribution.sum_map_mul,
      Fintype.sum_prod_type, FiniteDistribution.joint_apply, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] at h ⊢
    exact h
  unfold mutualInformation
  change _ - _ ≤ _ - _ + ((next.outputDistribution d).entropy - next.conditionalOutputEntropy d)
  change _ ≤ _ + (next.outputDistribution d).entropy at hout
  linarith

/-- Append a channel observation whose input depends on the message and preceding output. -/
@[capacity_shared_api]
noncomputable def sequentialExtension (past : FiniteChannel M A) (next : FiniteChannel T B)
    (strategy : M → A → T) : FiniteChannel M (A × B) :=
  ofRows fun m ↦ (past.rowDistribution m).joint fun a ↦ next.rowDistribution (strategy m a)

@[simp, capacity_shared_api]
theorem sequentialExtension_transition (past : FiniteChannel M A) (next : FiniteChannel T B)
    (strategy : M → A → T) (m : M) (output : A × B) :
    (sequentialExtension past next strategy).transition m output =
      past.transition m output.1 * next.transition (strategy m output.1) output.2 := rfl

@[simp, capacity_shared_api]
theorem rowDistribution_sequentialExtension (past : FiniteChannel M A)
    (next : FiniteChannel T B) (strategy : M → A → T) (m : M) :
    (sequentialExtension past next strategy).rowDistribution m =
      (past.rowDistribution m).joint (fun a ↦ next.rowDistribution (strategy m a)) := rfl

@[capacity_shared_api]
theorem sequentialExtension_output_fst [DecidableEq A] (past : FiniteChannel M A)
    (next : FiniteChannel T B) (strategy : M → A → T) (input : FiniteDistribution M) :
    ((sequentialExtension past next strategy).outputDistribution input).map Prod.fst =
      past.outputDistribution input := by
  change (FiniteDistribution.mixture input _).map Prod.fst = _
  simp only [FiniteDistribution.map_mixture, FiniteDistribution.map_fst_joint]
  rfl

@[capacity_shared_api]
theorem sequentialExtension_output_snd [DecidableEq B] [DecidableEq T]
    (past : FiniteChannel M A) (next : FiniteChannel T B) (strategy : M → A → T)
    (input : FiniteDistribution M) :
    ((sequentialExtension past next strategy).outputDistribution input).map Prod.snd =
      next.outputDistribution
        ((input.joint past.rowDistribution).map fun ma ↦ strategy ma.1 ma.2) := by
  change (FiniteDistribution.mixture input _).map Prod.snd = _
  simp only [FiniteDistribution.map_mixture, FiniteDistribution.map_snd_joint]
  ext b
  rw [outputDistribution_apply, FiniteDistribution.sum_map_mul]
  simp only [FiniteDistribution.mixture_apply, Fintype.sum_prod_type,
    FiniteDistribution.joint_apply, Finset.mul_sum, mul_assoc, rowDistribution_apply]

/-- The new row entropy is averaged under the actual input selected from the preceding output. -/
@[capacity_shared_api]
theorem sequentialExtension_conditionalOutputEntropy [DecidableEq T]
    (past : FiniteChannel M A) (next : FiniteChannel T B) (strategy : M → A → T)
    (input : FiniteDistribution M) :
    (sequentialExtension past next strategy).conditionalOutputEntropy input =
      past.conditionalOutputEntropy input + next.conditionalOutputEntropy
        ((input.joint past.rowDistribution).map fun ma ↦ strategy ma.1 ma.2) := by
  simp only [conditionalOutputEntropy, rowDistribution_sequentialExtension,
    FiniteDistribution.entropy_joint, FiniteDistribution.sum_map_mul,
    Fintype.sum_prod_type, FiniteDistribution.joint_apply, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- The additional information is bounded by the next channel's information at its induced input. -/
@[capacity_shared_api]
theorem sequentialExtension_mutualInformation_le [DecidableEq T]
    (past : FiniteChannel M A) (next : FiniteChannel T B) (strategy : M → A → T)
    (input : FiniteDistribution M) :
    (sequentialExtension past next strategy).mutualInformation input ≤
      past.mutualInformation input + next.mutualInformation
        ((input.joint past.rowDistribution).map fun ma ↦ strategy ma.1 ma.2) := by
  classical
  have hout := FiniteDistribution.entropy_le_entropy_fst_add_entropy_snd
    ((sequentialExtension past next strategy).outputDistribution input)
  rw [sequentialExtension_output_fst, sequentialExtension_output_snd] at hout
  simp only [mutualInformation, sequentialExtension_conditionalOutputEntropy]
  linarith

/-- Adapting the next input to a preceding observation adds at most one channel capacity. -/
@[capacity_shared_api]
theorem sequentialExtension_mutualInformation_le_add_capacity
    (past : FiniteChannel M A) (next : FiniteChannel T B) (strategy : M → A → T)
    (input : FiniteDistribution M) :
    (sequentialExtension past next strategy).mutualInformation input ≤
      past.mutualInformation input + next.informationCapacityBits * Real.log 2 := by
  classical
  apply (sequentialExtension_mutualInformation_le past next strategy input).trans
  exact add_le_add le_rfl
    ((div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
      (next.mutualInformationBits_le_informationCapacityBits _))

end FiniteChannel

end CapacityAtlas
