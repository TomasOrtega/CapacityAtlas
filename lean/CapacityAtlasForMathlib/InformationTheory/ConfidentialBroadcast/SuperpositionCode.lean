/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.Converse
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.EnsembleLeakage
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.AuxiliaryLaws

open scoped BigOperators

namespace CapacityAtlas.ConfidentialBroadcast.SuperpositionCode

open FiniteInformation

variable {A V Y Z O : Type*} [Fintype A] [Fintype V] [Fintype Y] [Fintype Z] [Fintype O]
    {n C S L : ℕ} [NeZero C] [NeZero S] [NeZero L]

variable (W : FiniteBroadcastChannel V Y Z) (p : FiniteDistribution A)
    (q : A → FiniteDistribution (Fin n → V)) (tauY tauZ : ℝ) (tauSat : A → ℝ)
    (cloud : Fin C → A) (satellites : Fin C → (Fin S × Fin L) → Fin n → V)

noncomputable def commonDecoder (B : FiniteChannel (Fin n → V) O) (tau : ℝ) : O → Fin C :=
  (B.comp (FiniteChannel.ofRows q)).thresholdDecoder p tau cloud

noncomputable def satelliteDecoder (B : FiniteChannel (Fin n → V) O)
    (c : Fin C) : O → Fin S × Fin L :=
  B.thresholdDecoder (q (cloud c)) (tauSat (cloud c)) (satellites c)

/-- The encoder hides an independent uniform seed inside each satellite subcode. -/
noncomputable abbrev code : Code W n := by
  classical
  exact {
    commonCount := C
    secretCount := S
    commonCount_pos := NeZero.pos C
    secretCount_pos := NeZero.pos S
    encode := FiniteChannel.ofRows fun cs ↦
      (FiniteDistribution.uniform (Fin L)).map (fun l ↦ satellites cs.1 (cs.2, l))
    decodeLegitimate := fun y ↦
      let c := commonDecoder p q cloud (W.receiver₁.block n) tauY y
      (c, (satelliteDecoder q tauSat cloud satellites (W.receiver₁.block n) c y).1)
    decodeCommon := commonDecoder p q cloud (W.receiver₂.block n) tauZ }

noncomputable def average (f : Fin C → Fin S → Fin L → ℝ) : ℝ :=
  ∑ c, FiniteDistribution.uniform (Fin C) c *
    ∑ s, FiniteDistribution.uniform (Fin S) s *
      ∑ l, FiniteDistribution.uniform (Fin L) l * f c s l

noncomputable def rawCommonError (B : FiniteChannel (Fin n → V) O) (tau : ℝ) : ℝ := by
  classical
  exact average fun c s l ↦ ∑ y,
    if commonDecoder p q cloud B tau y ≠ c then B.transition (satellites c (s, l)) y else 0

noncomputable def rawSatelliteError (B : FiniteChannel (Fin n → V) O) : ℝ :=
  average fun c s l ↦
    (B.thresholdCode (q (cloud c)) (tauSat (cloud c)) (satellites c)).errorProbability (s, l)

noncomputable def commonYError : ℝ := rawCommonError p q cloud satellites (W.receiver₁.block n) tauY

noncomputable def commonZError : ℝ := rawCommonError p q cloud satellites (W.receiver₂.block n) tauZ

noncomputable def satelliteError : ℝ := rawSatelliteError q tauSat cloud satellites (W.receiver₁.block n)

noncomputable def upperLeakage : ℝ :=
  ∑ c, FiniteDistribution.uniform (Fin C) c *
    (((W.receiver₂.block n).encoded (satellites c)).averageSeed
      (fun _ ↦ FiniteDistribution.uniform (Fin L))).mutualInformationBits
        (FiniteDistribution.uniform (Fin S))

theorem messages_apply (cs : Fin C × Fin S) :
    (code W p q tauY tauZ tauSat cloud satellites).messages cs =
      FiniteDistribution.uniform (Fin C) cs.1 * FiniteDistribution.uniform (Fin S) cs.2 := by
  change (Fintype.card (Fin C × Fin S) : ℝ)⁻¹ =
    (Fintype.card (Fin C) : ℝ)⁻¹ * (Fintype.card (Fin S) : ℝ)⁻¹
  simp [Fintype.card_prod, Nat.cast_mul, mul_inv_rev, mul_comm]

theorem induced_transition (B : FiniteChannel V O) (cs : Fin C × Fin S) (y : Fin n → O) :
    ((code W p q tauY tauZ tauSat cloud satellites).induced B).transition cs y =
      ∑ l, FiniteDistribution.uniform (Fin L) l * (B.block n).transition (satellites cs.1 (cs.2, l)) y := by
  classical
  change (∑ x, (FiniteDistribution.uniform (Fin L)).map
    (fun l ↦ satellites cs.1 (cs.2, l)) x * (B.block n).transition x y) = _
  exact (FiniteDistribution.uniform (Fin L)).sum_map_mul
    (fun l ↦ satellites cs.1 (cs.2, l)) (fun x ↦ (B.block n).transition x y)

private theorem error_sum (B : FiniteChannel V O)
    (failed : (Fin C × Fin S) → (Fin n → O) → Prop)
    [∀ cs y, Decidable (failed cs y)] :
    (∑ cs, ∑ y, if failed cs y then
      (code W p q tauY tauZ tauSat cloud satellites).messages cs *
      ((code W p q tauY tauZ tauSat cloud satellites).induced B).transition cs y else 0) =
      average fun c s l ↦ ∑ y, if failed (c, s) y then
        (B.block n).transition (satellites c (s, l)) y else 0 := by
  classical
  simp only [messages_apply W p q tauY tauZ tauSat cloud satellites, induced_transition, average, Fintype.sum_prod_type,
    Finset.mul_sum, ← mul_assoc]
  apply Fintype.sum_congr
  intro c
  apply Fintype.sum_congr
  intro s
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro y
  by_cases h : failed (c, s) y
  · simp [h]
  · simp [h]

theorem average_mono (f g : Fin C → Fin S → Fin L → ℝ)
    (h : ∀ c s l, f c s l ≤ g c s l) : average f ≤ average g := by
  unfold average
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (FiniteDistribution.probability_nonnegative _ _)
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (FiniteDistribution.probability_nonnegative _ _)
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul_of_nonneg_left (h c s l) (FiniteDistribution.probability_nonnegative _ _)

theorem average_add (f g : Fin C → Fin S → Fin L → ℝ) :
    average (fun c s l ↦ f c s l + g c s l) = average f + average g := by
  simp only [average, mul_add, Finset.sum_add_distrib]

set_option maxHeartbeats 800000 in
/-- Successive decoding fails only if a cloud or its correct-cloud satellite decoder fails. -/
theorem legitimateError_le :
    (code W p q tauY tauZ tauSat cloud satellites).legitimateError ≤
      commonYError W p q tauY cloud satellites + satelliteError W q tauSat cloud satellites := by
  classical
  have he := error_sum W p q tauY tauZ tauSat cloud satellites W.receiver₁
    (fun cs y ↦ (code W p q tauY tauZ tauSat cloud satellites).decodeLegitimate y ≠ cs)
  have heq : (code W p q tauY tauZ tauSat cloud satellites).legitimateError =
      ∑ cs, ∑ y, if (code W p q tauY tauZ tauSat cloud satellites).decodeLegitimate y ≠ cs then
        (code W p q tauY tauZ tauSat cloud satellites).messages cs *
        ((code W p q tauY tauZ tauSat cloud satellites).induced W.receiver₁).transition cs y else 0 := by
    unfold Code.legitimateError
    apply Fintype.sum_congr
    intro cs
    apply Fintype.sum_congr
    intro y
    by_cases h : (code W p q tauY tauZ tauSat cloud satellites).decodeLegitimate y = cs <;> simp [h]
  rw [heq, he]
  unfold commonYError satelliteError rawCommonError rawSatelliteError
  rw [← average_add]
  apply average_mono
  intro c s l
  rw [OneShotCode.errorProbability_eq_sum_decode_ne, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  let d₀ := commonDecoder p q cloud (W.receiver₁.block n) tauY
  let d₁ := satelliteDecoder q tauSat cloud satellites (W.receiver₁.block n)
  change (if (d₀ y, (d₁ (d₀ y) y).1) ≠ (c, s) then
    (W.receiver₁.block n).transition (satellites c (s, l)) y else 0) ≤
    (if d₀ y ≠ c then (W.receiver₁.block n).transition (satellites c (s, l)) y else 0) +
    (if d₁ c y ≠ (s, l) then (W.receiver₁.block n).transition (satellites c (s, l)) y else 0)
  have hp := (W.receiver₁.block n).nonnegative (satellites c (s, l)) y
  by_cases hc : d₀ y = c
  · rw [hc]
    by_cases hs : d₁ c y = (s, l)
    · simp [hs]
    · simp only [ne_eq, hs, not_false_eq_true, if_true, not_true_eq_false, if_false, zero_add]
      split_ifs <;> linarith
  · simp only [hc, ne_eq, not_false_eq_true, if_true]
    split_ifs <;> simp_all

set_option maxHeartbeats 800000 in
/-- The second decoder's operational error is the raw common-message error. -/
theorem commonError_eq :
    (code W p q tauY tauZ tauSat cloud satellites).commonError =
      commonZError W p q tauZ cloud satellites := by
  classical
  have he := error_sum W p q tauY tauZ tauSat cloud satellites W.receiver₂
    (fun cs y ↦ commonDecoder p q cloud (W.receiver₂.block n) tauZ y ≠ cs.1)
  have heq : (code W p q tauY tauZ tauSat cloud satellites).commonError =
      ∑ cs, ∑ y, if commonDecoder p q cloud (W.receiver₂.block n) tauZ y ≠ cs.1 then
        (code W p q tauY tauZ tauSat cloud satellites).messages cs *
        ((code W p q tauY tauZ tauSat cloud satellites).induced W.receiver₂).transition cs y else 0 := by
    unfold Code.commonError
    apply Fintype.sum_congr
    intro cs
    apply Fintype.sum_congr
    intro y
    change (if commonDecoder p q cloud (W.receiver₂.block n) tauZ y = cs.1 then 0 else _) = _
    by_cases h : commonDecoder p q cloud (W.receiver₂.block n) tauZ y = cs.1 <;> simp [h]
  exact heq.trans he

theorem rawCommonError_zero [Subsingleton (Fin C)]
    (B : FiniteChannel (Fin n → V) O) (tau : ℝ) :
    rawCommonError p q cloud satellites B tau = 0 := by
  unfold rawCommonError
  have h : (fun (c : Fin C) (s : Fin S) (l : Fin L) ↦
      ∑ y, if commonDecoder p q cloud B tau y ≠ c then
        B.transition (satellites c (s, l)) y else 0) = fun _ _ _ ↦ (0 : ℝ) := by
    funext c s l
    apply Finset.sum_eq_zero
    intro y _
    exact if_neg (not_not_intro (Subsingleton.elim _ _))
  rw [h]
  simp [average]

omit [Fintype A] in
theorem rawSatelliteError_zero [Subsingleton (Fin S × Fin L)]
    (B : FiniteChannel (Fin n → V) O) : rawSatelliteError q tauSat cloud satellites B = 0 := by
  have h (c : Fin C) (sl : Fin S × Fin L) :
      (B.thresholdCode (q (cloud c)) (tauSat (cloud c)) (satellites c)).errorProbability sl = 0 := by
    rw [OneShotCode.errorProbability_eq_sum_decode_ne]
    have hd (y : O) :
        (B.thresholdCode (q (cloud c)) (tauSat (cloud c)) (satellites c)).decode y = sl :=
      Subsingleton.elim _ _
    simp [hd]
  simp [rawSatelliteError, average, h]

private noncomputable def seedChannel (c : Fin C) : FiniteChannel (Fin S) (Fin n → Z) :=
  ((W.receiver₂.block n).encoded (satellites c)).averageSeed
    (fun _ ↦ FiniteDistribution.uniform (Fin L))

set_option maxHeartbeats 800000 in
private theorem joint_seedChannel [DecidableEq Z] :
    (code W p q tauY tauZ tauSat cloud satellites).joint W.receiver₂ =
      ((FiniteDistribution.uniform (Fin C)).joint fun c ↦
        FiniteInformation.joint (FiniteDistribution.uniform (Fin S))
          (seedChannel W satellites c)).map
            (Equiv.prodAssoc (Fin C) (Fin S) (Fin n → Z)).symm := by
  classical
  ext a
  rw [FiniteDistribution.map_equiv_apply]
  change (code W p q tauY tauZ tauSat cloud satellites).messages a.1 *
    ((code W p q tauY tauZ tauSat cloud satellites).induced W.receiver₂).transition a.1 a.2 =
    FiniteDistribution.uniform (Fin C) a.1.1 *
      (FiniteDistribution.uniform (Fin S) a.1.2 * (seedChannel W satellites a.1.1).transition a.1.2 a.2)
  rw [messages_apply, induced_transition]
  change (_ * _) * (∑ l : Fin L, _ * _) = _ * (_ * ∑ l : Fin L, _ * _)
  simp only [FiniteChannel.encoded_transition]
  ring

/-- Revealing the independent common message upper-bounds secret-message leakage. -/
theorem leakage_le (hn : 0 < n) :
    (n : ℝ) * (code W p q tauY tauZ tauSat cloud satellites).leakage ≤
      upperLeakage W satellites := by
  classical
  let c := code W p q tauY tauZ tauSat cloud satellites
  have hi := information_le_conditional_of_independent (c.joint W.receiver₂)
    (fun a ↦ a.1.2) Prod.snd (fun a ↦ a.1.1) (c.secret_common_independent _)
  have hcond : conditional (c.joint W.receiver₂) (fun a ↦ a.1.2) Prod.snd (fun a ↦ a.1.1) =
      upperLeakage W satellites := by
    rw [joint_seedChannel, conditional_map]
    change conditional ((FiniteDistribution.uniform (Fin C)).joint fun c ↦
      FiniteInformation.joint (FiniteDistribution.uniform (Fin S)) (seedChannel W satellites c))
      (fun a ↦ a.2.1) (fun a ↦ a.2.2) Prod.fst = _
    rw [conditional_joint]
    simp only [information_joint_fst_snd]
    rfl
  rw [hcond] at hi
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hscale : (n : ℝ) * c.leakage =
      information (c.joint W.receiver₂) (fun a ↦ a.1.2) Prod.snd := by
    unfold Code.leakage
    field_simp
  rw [hscale]
  exact hi

theorem leakage_zero [Subsingleton (Fin S)] :
    (code W p q tauY tauZ tauSat cloud satellites).leakage = 0 :=
  Code.leakage_zero _

end CapacityAtlas.ConfidentialBroadcast.SuperpositionCode
