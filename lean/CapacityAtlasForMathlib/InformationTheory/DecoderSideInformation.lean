/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteDistribution

variable {S Y : Type*} [Fintype S] [Fintype Y]

/-- The joint law of a state and an output sampled from its corresponding row. -/
@[capacity_shared_api]
def joint (state : FiniteDistribution S) (rows : S → FiniteDistribution Y) :
    FiniteDistribution (S × Y) where
  probability output := state output.1 * rows output.1 output.2
  nonnegative output := mul_nonneg (state.nonnegative _) ((rows _).nonnegative _)
  sum_probability := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum]

@[simp, capacity_shared_api]
theorem joint_apply (state : FiniteDistribution S) (rows : S → FiniteDistribution Y)
    (output : S × Y) : state.joint rows output = state output.1 * rows output.1 output.2 :=
  rfl

/-- Entropy of a joint law, including states with zero probability. -/
@[capacity_shared_api]
theorem entropy_joint (state : FiniteDistribution S) (rows : S → FiniteDistribution Y) :
    (state.joint rows).entropy = state.entropy + ∑ s, state s * (rows s).entropy := by
  simp [entropy, Fintype.sum_prod_type, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]

@[capacity_shared_api]
theorem entropyBits_joint (state : FiniteDistribution S)
    (rows : S → FiniteDistribution Y) :
    (state.joint rows).entropyBits = state.entropyBits +
      ∑ s, state s * (rows s).entropyBits := by
  simp [entropyBits, entropy_joint, add_div, Finset.sum_div, mul_div_assoc]

end FiniteDistribution

namespace FiniteChannel

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]

/-- An independent state is observed by the decoder along with the channel output. -/
@[capacity_shared_api]
def withDecoderState (state : FiniteDistribution S) (channels : S → FiniteChannel X Y) :
    FiniteChannel X (S × Y) :=
  ofRows fun input ↦ state.joint fun s ↦ (channels s).rowDistribution input

@[simp, capacity_shared_api]
theorem withDecoderState_transition (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : X) (output : S × Y) :
    (withDecoderState state channels).transition input output =
      state output.1 * (channels output.1).transition input output.2 :=
  rfl

/-- The product channel exposes the iid state law and the conditional output law. -/
@[capacity_shared_api]
theorem withDecoderState_block_transition (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (n : ℕ)
    (input : Fin n → X) (output : Fin n → S × Y) :
    ((withDecoderState state channels).block n).transition input output =
      (∏ i, state (output i).1) *
        ∏ i, (channels (output i).1).transition (input i) (output i).2 := by
  simp [Finset.prod_mul_distrib]

@[capacity_shared_api]
theorem withDecoderState_rowDistribution (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : X) :
    (withDecoderState state channels).rowDistribution input =
      state.joint (fun s ↦ (channels s).rowDistribution input) :=
  rfl

@[capacity_shared_api]
theorem withDecoderState_outputDistribution_apply (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) (output : S × Y) :
    (withDecoderState state channels).outputDistribution input output =
      state output.1 * (channels output.1).outputDistribution input output.2 := by
  simp only [outputDistribution_apply, withDecoderState_transition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

@[capacity_shared_api]
theorem withDecoderState_outputDistribution (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) :
    (withDecoderState state channels).outputDistribution input =
      state.joint (fun s ↦ (channels s).outputDistribution input) := by
  ext output
  exact withDecoderState_outputDistribution_apply state channels input output

@[capacity_shared_api]
theorem withDecoderState_conditionalOutputEntropy (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) :
    (withDecoderState state channels).conditionalOutputEntropy input =
      state.entropy + ∑ s, state s * (channels s).conditionalOutputEntropy input := by
  unfold conditionalOutputEntropy
  simp_rw [withDecoderState_rowDistribution, FiniteDistribution.entropy_joint,
    mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, input.sum_probability_eq_one,
    one_mul, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The same input distribution is used in every state. -/
@[capacity_shared_api]
theorem withDecoderState_mutualInformation (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) :
    (withDecoderState state channels).mutualInformation input =
      ∑ s, state s * (channels s).mutualInformation input := by
  simp only [mutualInformation, withDecoderState_outputDistribution,
    FiniteDistribution.entropy_joint, withDecoderState_conditionalOutputEntropy]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  simp only [mul_sub]

@[capacity_shared_api]
theorem withDecoderState_mutualInformationBits (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X) :
    (withDecoderState state channels).mutualInformationBits input =
      ∑ s, state s * (channels s).mutualInformationBits input := by
  simp [mutualInformationBits, withDecoderState_mutualInformation,
    Finset.sum_div, mul_div_assoc]

end FiniteChannel

end CapacityAtlas
