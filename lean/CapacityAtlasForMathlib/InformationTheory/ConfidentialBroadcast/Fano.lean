/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.ModelLaws
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation.Identities
import CapacityAtlasForMathlib.InformationTheory.CodingConverse

open scoped BigOperators

namespace CapacityAtlas.FiniteInformation

variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

private theorem map_fst_apply [DecidableEq A] (q : FiniteDistribution (A × B)) (a : A) :
    q.map Prod.fst a = ∑ b, q (a, b) := by
  classical
  change (∑ x with x.1 = a, q x) = _
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

private noncomputable def channelOfUniform [Nonempty A] [DecidableEq A]
    (q : FiniteDistribution (A × B))
    (hu : q.map Prod.fst = FiniteDistribution.uniform A) : FiniteChannel A B where
  transition a b := (Fintype.card A : ℝ) * q (a, b)
  nonnegative a b := mul_nonneg (Nat.cast_nonneg _) (q.nonnegative _)
  row_sum a := by
    rw [← Finset.mul_sum, ← map_fst_apply, hu, FiniteDistribution.uniform_apply]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

private theorem joint_channelOfUniform [Nonempty A] [DecidableEq A]
    (q : FiniteDistribution (A × B))
    (hu : q.map Prod.fst = FiniteDistribution.uniform A) :
    joint (FiniteDistribution.uniform A) (channelOfUniform q hu) = q := by
  ext a
  change (Fintype.card A : ℝ)⁻¹ * ((Fintype.card A : ℝ) * q a) = q a
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

/-- Fano in bits for a finite joint law with a uniform message marginal. -/
@[capacity_shared_api]
theorem fano_joint_uniform [Nonempty A] [DecidableEq A]
    (q : FiniteDistribution (A × B)) (decode : B → A)
    (hu : q.map Prod.fst = FiniteDistribution.uniform A) :
    Real.log (Fintype.card A) / Real.log 2 ≤ information q Prod.fst Prod.snd + 1 +
      (∑ a, if decode a.2 = a.1 then 0 else q a) *
        (Real.log (Fintype.card A) / Real.log 2) := by
  classical
  let W := channelOfUniform q hu
  let code : OneShotCode W A := ⟨id, decode⟩
  have hfano := W.fano_uniform decode
  change Real.log (Fintype.card A) ≤ W.mutualInformation (FiniteDistribution.uniform A) +
    Real.log 2 + code.averageErrorProbability * Real.log (Fintype.card A) at hfano
  have herr : code.averageErrorProbability =
      ∑ a, if decode a.2 = a.1 then 0 else q a := by
    rw [OneShotCode.averageErrorProbability_eq]
    simp only [OneShotCode.errorProbability_eq_sum_decode_ne,
      Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : decode b = a
    · simp [code, h]
    · simp [code, h, W, channelOfUniform]
  rw [herr] at hfano
  have hbits := div_le_div_of_nonneg_right hfano
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hinfo : W.mutualInformation (FiniteDistribution.uniform A) / Real.log 2 =
      information q Prod.fst Prod.snd := by
    rw [← FiniteChannel.mutualInformationBits, ← information_joint_fst_snd]
    rw [joint_channelOfUniform]
  simpa only [add_div, hinfo, div_self (Real.log_ne_zero_of_pos_of_ne_one
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)), mul_div_assoc] using hbits

/-- Fano for finite observables of any underlying finite probability space. -/
@[capacity_shared_api]
theorem fano_uniform [Nonempty A] [DecidableEq A]
    (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) (decode : B → A)
    (hu : p.map f = FiniteDistribution.uniform A) :
    Real.log (Fintype.card A) / Real.log 2 ≤ information p f g + 1 +
      (∑ ω, if decode (g ω) = f ω then 0 else p ω) *
        (Real.log (Fintype.card A) / Real.log 2) := by
  classical
  let q := p.map (fun ω ↦ (f ω, g ω))
  have hq : q.map Prod.fst = FiniteDistribution.uniform A := by
    simpa only [q, FiniteDistribution.map_map, Function.comp_def] using hu
  have h := fano_joint_uniform q decode hq
  have hinfo : information q Prod.fst Prod.snd = information p f g := by
    simp only [information, entropy, q, FiniteDistribution.map_map, Function.comp_def]
  have herr : (∑ a, if decode a.2 = a.1 then 0 else q a) =
      ∑ ω, if decode (g ω) = f ω then 0 else p ω := by
    have hs := p.sum_map_mul (fun ω ↦ (f ω, g ω))
      (fun a ↦ if decode a.2 = a.1 then 0 else 1)
    simpa only [mul_ite, mul_zero, mul_one] using hs
  simpa only [hinfo, herr] using h

@[capacity_shared_api]
theorem entropy_of_uniform [Nonempty A] [DecidableEq A]
    (p : FiniteDistribution Ω) (f : Ω → A)
    (hu : p.map f = FiniteDistribution.uniform A) :
    entropy p f = Real.log (Fintype.card A) / Real.log 2 := by
  rw [entropy_eq_map, hu, FiniteDistribution.entropyBits, FiniteDistribution.entropy_uniform]

end CapacityAtlas.FiniteInformation

namespace CapacityAtlas.ConfidentialBroadcast.Code

open FiniteInformation

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {W : FiniteBroadcastChannel X Y Z} {n : ℕ}

private theorem projected_legitimate_error_le (c : Code W n) {M : Type*}
    [Fintype M] [DecidableEq M] (f : Fin c.commonCount × Fin c.secretCount → M) :
    (∑ a, if f (c.decodeLegitimate a.2) = f a.1 then 0
      else c.joint W.receiver₁ a) ≤ c.error := by
  classical
  apply le_trans _ (le_max_left _ _)
  rw [Fintype.sum_prod_type]
  unfold legitimateError
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro y _
  by_cases h : c.decodeLegitimate y = a
  · simp [h]
  · simp only [h, if_false]
    split_ifs
    · exact mul_nonneg (c.messages.nonnegative _) ((c.induced W.receiver₁).nonnegative _ _)
    · exact le_rfl

private theorem uniform_fano_error_bound {M O Ω : Type*}
    [Fintype M] [Fintype O] [Fintype Ω] [Nonempty M] [DecidableEq M]
    (p : FiniteDistribution Ω) (f : Ω → M) (g : Ω → O) (decode : O → M)
    (hu : p.map f = FiniteDistribution.uniform M) {e : ℝ}
    (he : (∑ ω, if decode (g ω) = f ω then 0 else p ω) ≤ e) :
    (1 - e) * (Real.log (Fintype.card M) / Real.log 2) ≤ information p f g + 1 := by
  have hf := FiniteInformation.fano_uniform p f g decode hu
  have hl : 0 ≤ Real.log (Fintype.card M) / Real.log 2 := by
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have he' := mul_le_mul_of_nonneg_right he hl
  nlinarith

/-- The common message is decodable at the legitimate receiver. -/
theorem common_fano_legitimate (c : Code W n) :
    (1 - c.error) * (Real.log c.commonCount / Real.log 2) ≤
      information (c.joint W.receiver₁) (fun a ↦ a.1.1) Prod.snd + 1 := by
  classical
  letI : Nonempty (Fin c.commonCount) := Fin.pos_iff_nonempty.mp c.commonCount_pos
  simpa only [Fintype.card_fin] using uniform_fano_error_bound (c.joint W.receiver₁)
    (fun a ↦ a.1.1) Prod.snd (fun y ↦ (c.decodeLegitimate y).1)
    (c.joint_common_uniform _) (c.projected_legitimate_error_le Prod.fst)

/-- The common message is also decodable at the receiver without the secret message. -/
theorem common_fano (c : Code W n) :
    (1 - c.error) * (Real.log c.commonCount / Real.log 2) ≤
      information (c.joint W.receiver₂) (fun a ↦ a.1.1) Prod.snd + 1 := by
  classical
  letI : Nonempty (Fin c.commonCount) := Fin.pos_iff_nonempty.mp c.commonCount_pos
  have he : (∑ a, if c.decodeCommon a.2 = a.1.1 then 0
      else c.joint W.receiver₂ a) ≤ c.error := by
    have heq : (∑ a, if c.decodeCommon a.2 = a.1.1 then 0
        else c.joint W.receiver₂ a) = c.commonError := by
      rw [Fintype.sum_prod_type]
      rfl
    rw [heq]
    exact le_max_right _ _
  simpa only [Fintype.card_fin] using uniform_fano_error_bound (c.joint W.receiver₂)
    (fun a ↦ a.1.1) Prod.snd c.decodeCommon (c.joint_common_uniform _) he

/-- Secret-message decoding remains valid when the common message is supplied. -/
theorem secret_fano_with_common (c : Code W n) :
    (1 - c.error) * (Real.log c.secretCount / Real.log 2) ≤
      information (c.joint W.receiver₁) (fun a ↦ a.1.2) (fun a ↦ (a.2, a.1.1)) + 1 := by
  classical
  letI : Nonempty (Fin c.secretCount) := Fin.pos_iff_nonempty.mp c.secretCount_pos
  simpa only [Fintype.card_fin] using uniform_fano_error_bound (c.joint W.receiver₁)
    (fun a ↦ a.1.2) (fun a ↦ (a.2, a.1.1)) (fun y ↦ (c.decodeLegitimate y.1).2)
    (c.joint_secret_uniform _) (c.projected_legitimate_error_le Prod.snd)

/-- Fano for the secret message alone. -/
theorem secret_fano (c : Code W n) :
    (1 - c.error) * (Real.log c.secretCount / Real.log 2) ≤
      information (c.joint W.receiver₁) (fun a ↦ a.1.2) Prod.snd + 1 := by
  classical
  letI : Nonempty (Fin c.secretCount) := Fin.pos_iff_nonempty.mp c.secretCount_pos
  simpa only [Fintype.card_fin] using uniform_fano_error_bound (c.joint W.receiver₁)
    (fun a ↦ a.1.2) Prod.snd (fun y ↦ (c.decodeLegitimate y).2)
    (c.joint_secret_uniform _) (c.projected_legitimate_error_le Prod.snd)

/-- The uncertainty in the common message at the second receiver vanishes with error. -/
theorem common_conditionalEntropy_fano (c : Code W n) :
    conditionalEntropy (c.joint W.receiver₂) (fun a ↦ a.1.1) Prod.snd ≤
      1 + c.error * (Real.log c.commonCount / Real.log 2) := by
  classical
  letI : Nonempty (Fin c.commonCount) := Fin.pos_iff_nonempty.mp c.commonCount_pos
  have hf := c.common_fano
  have he := entropy_of_uniform (c.joint W.receiver₂) (fun a ↦ a.1.1)
    (c.joint_common_uniform W.receiver₂)
  simp only [Fintype.card_fin] at he
  unfold information at hf
  unfold conditionalEntropy
  rw [he] at hf
  nlinarith

/-- Both messages are jointly decodable at the legitimate receiver. -/
theorem pair_fano (c : Code W n) :
    (1 - c.error) * (Real.log c.commonCount / Real.log 2 +
      Real.log c.secretCount / Real.log 2) ≤
      information (c.joint W.receiver₁) Prod.fst Prod.snd + 1 := by
  classical
  letI : Nonempty (Fin c.commonCount) := Fin.pos_iff_nonempty.mp c.commonCount_pos
  letI : Nonempty (Fin c.secretCount) := Fin.pos_iff_nonempty.mp c.secretCount_pos
  have hu : (c.joint W.receiver₁).map Prod.fst =
      FiniteDistribution.uniform (Fin c.commonCount × Fin c.secretCount) :=
    c.joint_pair_uniform W.receiver₁
  have hf := uniform_fano_error_bound (c.joint W.receiver₁) Prod.fst Prod.snd
    c.decodeLegitimate hu (c.projected_legitimate_error_le id)
  have hcommon : (c.commonCount : ℝ) ≠ 0 := by exact_mod_cast c.commonCount_pos.ne'
  have hsecret : (c.secretCount : ℝ) ≠ 0 := by exact_mod_cast c.secretCount_pos.ne'
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Real.log_mul hcommon hsecret, add_div] using hf

theorem common_rate_fano (c : Code W n) :
    (1 - c.error) * c.rates.1 ≤
      information (c.joint W.receiver₂) (fun a ↦ a.1.1) Prod.snd / n + (n : ℝ)⁻¹ := by
  have h := div_le_div_of_nonneg_right c.common_fano (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [rates, Operational.messageRate, Real.logb, add_div, one_div,
    mul_div_assoc] using h

theorem secret_rate_fano_with_common (c : Code W n) :
    (1 - c.error) * c.rates.2 ≤
      information (c.joint W.receiver₁) (fun a ↦ a.1.2)
        (fun a ↦ (a.2, a.1.1)) / n + (n : ℝ)⁻¹ := by
  have h := div_le_div_of_nonneg_right c.secret_fano_with_common
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [rates, Operational.messageRate, Real.logb, add_div, one_div,
    mul_div_assoc] using h

/-- A singleton secret-message set has no information to leak. -/
theorem leakage_zero (c : Code W n) [Subsingleton (Fin c.secretCount)] : c.leakage = 0 := by
  let s : Fin c.secretCount := ⟨0, c.secretCount_pos⟩
  have hf : (fun a : (Fin c.commonCount × Fin c.secretCount) × (Fin n → Z) ↦ a.1.2) =
      fun _ ↦ s := by funext a; exact Subsingleton.elim _ _
  have hp := entropy_comp_injective (c.joint W.receiver₂) Prod.snd
    (fun z : Fin n → Z ↦ (s, z)) (fun _ _ h ↦ (Prod.mk.inj h).2)
  simp only [Function.comp_def] at hp
  unfold leakage information
  rw [hf, entropy_const, hp]
  ring

theorem leakage_zero_of_secretCount_eq_one (c : Code W n) (h : c.secretCount = 1) :
    c.leakage = 0 := by
  letI : Subsingleton (Fin c.secretCount) := by rw [h]; infer_instance
  exact c.leakage_zero

end CapacityAtlas.ConfidentialBroadcast.Code
