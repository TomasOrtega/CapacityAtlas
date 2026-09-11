/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.

Adapted from TomasOrtega/CapacityAtlasMAC, commit ec5be554b9644df94dd58190963793f3f1d1da52,
CapacityAtlasMAC/TimeSharing.lean. Local imports and sender-swap reuse for conditional information.
-/

import CapacityAtlasForMathlib.InformationTheory.MultipleAccess
import CapacityAtlasForMathlib.InformationTheory.FiniteProductDistribution

open scoped BigOperators

namespace CapacityAtlas.MultipleAccess

variable {X₁ X₂ Y Q : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y] [Fintype Q] [DecidableEq Q]

/-- Strategy symbols expose the sampled time-sharing index to the decoder. -/
noncomputable def timeSharingChannel (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) : FiniteChannel ((Q → X₁) × (Q → X₂)) (Q × Y) :=
  FiniteChannel.withDecoderState weights fun q ↦ W.encoded fun t ↦ (t.1 q, t.2 q)

@[simp]
theorem timeSharingChannel_transition (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) (t : (Q → X₁) × (Q → X₂)) (output : Q × Y) :
    (timeSharingChannel W weights).transition t output =
      weights output.1 * W.transition (t.1 output.1, t.2 output.1) output.2 := rfl


theorem leftInformation_timeSharing (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) (p₁ : Q → FiniteDistribution X₁)
    (p₂ : Q → FiniteDistribution X₂) :
    leftInformation (timeSharingChannel W weights)
        (FiniteDistribution.productFamily p₁) (FiniteDistribution.productFamily p₂) =
      ∑ q, weights q * leftInformation W (p₁ q) (p₂ q) := by
  classical
  have hs (t₂ : Q → X₂) : leftSlice (timeSharingChannel W weights) t₂ =
      FiniteChannel.withDecoderState weights
        (fun q ↦ (leftSlice W (t₂ q)).encoded (fun t₁ : Q → X₁ ↦ t₁ q)) := by
    ext t₁ output
    rfl
  unfold leftInformation
  simp_rw [hs, FiniteChannel.withDecoderState_mutualInformationBits,
    FiniteChannel.encoded_mutualInformationBits, FiniteDistribution.map_productFamily_eval,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [FiniteDistribution.sum_productFamily_mul_eval p₂
    (fun x₂ ↦ weights q * (leftSlice W x₂).mutualInformationBits (p₁ q)) q]
  apply Finset.sum_congr rfl
  intro t₂ _
  ring

theorem rightInformation_timeSharing (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) (p₁ : Q → FiniteDistribution X₁)
    (p₂ : Q → FiniteDistribution X₂) :
    rightInformation (timeSharingChannel W weights)
        (FiniteDistribution.productFamily p₁) (FiniteDistribution.productFamily p₂) =
      ∑ q, weights q * rightInformation W (p₁ q) (p₂ q) := by
  have hswap : timeSharingChannel (swap W) weights = swap (timeSharingChannel W weights) := rfl
  simpa only [hswap, leftInformation_swap] using
    leftInformation_timeSharing (swap W) weights p₂ p₁

theorem jointInformation_timeSharing (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) (p₁ : Q → FiniteDistribution X₁)
    (p₂ : Q → FiniteDistribution X₂) :
    jointInformation (timeSharingChannel W weights)
        (FiniteDistribution.productFamily p₁) (FiniteDistribution.productFamily p₂) =
      ∑ q, weights q * jointInformation W (p₁ q) (p₂ q) := by
  classical
  unfold jointInformation timeSharingChannel
  rw [FiniteChannel.withDecoderState_mutualInformationBits]
  simp_rw [FiniteChannel.encoded_mutualInformationBits, productInput,
    FiniteDistribution.map_joint_productFamily_eval]

/-- A fixed schedule evaluates each sender's own strategy word. -/
def BlockCode.fixTimeSharing (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) {n : ℕ}
    (code : BlockCode (timeSharingChannel W weights) n) (schedule : Fin n → Q) :
    BlockCode W n where
  messageCount₁ := code.messageCount₁
  messageCount₂ := code.messageCount₂
  messageCount₁_pos := code.messageCount₁_pos
  messageCount₂_pos := code.messageCount₂_pos
  encode₁ message i := code.encode₁ message i (schedule i)
  encode₂ message i := code.encode₂ message i (schedule i)
  decode output := code.decode fun i ↦ (schedule i, output i)

@[simp]
theorem BlockCode.rate₁_fixTimeSharing (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) {n : ℕ}
    (code : BlockCode (timeSharingChannel W weights) n) (schedule : Fin n → Q) :
    (code.fixTimeSharing W weights schedule).rate₁ = code.rate₁ := rfl

@[simp]
theorem BlockCode.rate₂_fixTimeSharing (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) {n : ℕ}
    (code : BlockCode (timeSharingChannel W weights) n) (schedule : Fin n → Q) :
    (code.fixTimeSharing W weights schedule).rate₂ = code.rate₂ := rfl

/-- The lifted error averages physical-code errors over independent schedules. -/
theorem BlockCode.averageErrorProbability_fixTimeSharing (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) {n : ℕ}
    (code : BlockCode (timeSharingChannel W weights) n) :
    code.averageErrorProbability = ∑ schedule, weights.iid n schedule *
      (code.fixTimeSharing W weights schedule).averageErrorProbability := by
  classical
  have hmessage (message : Fin code.messageCount₁ × Fin code.messageCount₂) :
      code.toOneShotCode.errorProbability message =
        ∑ schedule, weights.iid n schedule *
          (code.fixTimeSharing W weights schedule).toOneShotCode.errorProbability message := by
    simp only [CapacityAtlas.OneShotCode.errorProbability_eq_sum_decode_ne]
    rw [← (FiniteChannel.wordPairEquiv (X := Q) (Y := Y) n).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro schedule _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro output _
    change (if code.decode (fun i ↦ (schedule i, output i)) ≠ message then
        (∏ i, weights (schedule i) *
          W.transition (code.encode₁ message.1 i (schedule i),
            code.encode₂ message.2 i (schedule i)) (output i)) else 0) =
      (∏ i, weights (schedule i)) *
        (if code.decode (fun i ↦ (schedule i, output i)) ≠ message then
          ∏ i, W.transition (code.encode₁ message.1 i (schedule i),
            code.encode₂ message.2 i (schedule i)) (output i) else 0)
    split_ifs <;> simp [Finset.prod_mul_distrib]
  simp only [BlockCode.averageErrorProbability,
    CapacityAtlas.OneShotCode.averageErrorProbability_eq, hmessage]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro schedule _
  rw [← Finset.mul_sum]
  exact mul_left_comm _ _ _

/-- Some deterministic schedule has no larger error than the lifted code. -/
theorem BlockCode.exists_fixTimeSharing (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) {n : ℕ}
    (code : BlockCode (timeSharingChannel W weights) n) :
    ∃ schedule : Fin n → Q,
      (code.fixTimeSharing W weights schedule).averageErrorProbability ≤
        code.averageErrorProbability := by
  letI : Nonempty Q := weights.nonempty
  obtain ⟨schedule, h⟩ := FiniteProductProbability.exists_value_le_weighted_mean
    (weights.iid n) (fun schedule ↦
      (code.fixTimeSharing W weights schedule).averageErrorProbability)
    (weights.iid n).nonnegative (weights.iid n).sum_probability
  exact ⟨schedule, by rwa [← code.averageErrorProbability_fixTimeSharing W weights] at h⟩

/-- A fixed schedule removes the lifted channel's random time-sharing index. -/
theorem achievableRate_of_timeSharing (W : FiniteChannel (X₁ × X₂) Y)
    (weights : FiniteDistribution Q) {r : RatePair}
    (hr : AchievableRate (timeSharingChannel W weights) r) : AchievableRate W r := by
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro ε hε
  obtain ⟨N, hN, hcodes⟩ := hr.2.2 ε hε
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨code, herror, hrate₁, hrate₂⟩ := hcodes n hn
  obtain ⟨schedule, hs⟩ := code.exists_fixTimeSharing W weights
  exact ⟨code.fixTimeSharing W weights schedule, hs.trans herror, hrate₁, hrate₂⟩

end CapacityAtlas.MultipleAccess
