/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Tests

private def constantDecoder {Observation : Type*} [MeasurableSpace Observation]
    {messages : ℕ} (m : Fin messages) : Gaussian.Decoder Observation messages where
  apply := fun _ ↦ m
  measurable_fiber m' := by
    change MeasurableSet {_y : Observation | m = m'}
    by_cases h : m = m' <;> simp [h]

private def firstBroadcastMessage (i : Fin 2) : Fin (![2, 3] i) :=
  ⟨0, by fin_cases i <;> decide⟩

/-- One of the six message tuples uses energy four; every other tuple uses zero. -/
noncomputable def unevenMIMOBroadcastCode : Gaussian.MIMOBroadcast.Code 2 1 (fun _ ↦ 1) 1 where
  messages := ![2, 3]
  messages_pos i := by fin_cases i <;> decide
  encode m _ := WithLp.toLp 2 (fun _ ↦ if (m 0).val = 1 ∧ (m 1).val = 2 then 2 else 0)
  decode i := constantDecoder (firstBroadcastMessage i)

private theorem sum_broadcast_messages (f : ((i : Fin 2) → Fin (![2, 3] i)) → ℝ) :
    (∑ m, f m) = ∑ m₀ : Fin 2, ∑ m₁ : Fin 3,
      f ((piFinTwoEquiv (fun i ↦ Fin (![2, 3] i))).symm (m₀, m₁)) := by
  calc
    _ = ∑ m : Fin (![2, 3] 0) × Fin (![2, 3] 1),
        f ((piFinTwoEquiv (fun i ↦ Fin (![2, 3] i))).symm m) :=
      ((piFinTwoEquiv (fun i ↦ Fin (![2, 3] i))).symm.sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

@[capacity_test]
theorem mimoBroadcast_message_average_power :
    Gaussian.MIMOBroadcast.PowerAdmissible (2 / 3) unevenMIMOBroadcastCode ∧
      ¬Gaussian.MIMOBroadcast.PowerAdmissible (1 / 2) unevenMIMOBroadcastCode := by
  unfold Gaussian.MIMOBroadcast.PowerAdmissible
  have henergy : (∑ m : (i : Fin 2) → Fin (unevenMIMOBroadcastCode.messages i),
      ∑ s, ∑ a, (unevenMIMOBroadcastCode.encode m s a) ^ 2) = 4 := by
    simp only [Fin.sum_univ_one]
    change (∑ m : (i : Fin 2) → Fin (![2, 3] i),
      (if (m 0).val = 1 ∧ (m 1).val = 2 then (2 : ℝ) else 0) ^ 2) = 4
    rw [sum_broadcast_messages]
    norm_num [Fin.sum_univ_succ, piFinTwoEquiv]
  rw [henergy]
  norm_num [unevenMIMOBroadcastCode, Fin.prod_univ_two]

@[capacity_test]
theorem mimoBroadcast_message_average_allows_uneven_codeword :
    ∃ m, (∑ s, ∑ a, (unevenMIMOBroadcastCode.encode m s a) ^ 2) > (2 / 3 : ℝ) := by
  refine ⟨(piFinTwoEquiv (fun i ↦ Fin (![2, 3] i))).symm ((1 : Fin 2), (2 : Fin 3)), ?_⟩
  simp only [Fin.sum_univ_one]
  change (2 / 3 : ℝ) < 2 ^ 2
  norm_num

noncomputable def twoAntennaMIMOBroadcastCode : Gaussian.MIMOBroadcast.Code 2 2 (fun _ ↦ 1) 1 where
  messages := fun _ ↦ 1
  messages_pos _ := by decide
  encode _ _ := WithLp.toLp 2 ![1, 1]
  decode _ := constantDecoder 0

@[capacity_test]
theorem mimoBroadcast_power_shared_across_antennas :
    Gaussian.MIMOBroadcast.PowerAdmissible 2 twoAntennaMIMOBroadcastCode ∧
      ¬Gaussian.MIMOBroadcast.PowerAdmissible 1 twoAntennaMIMOBroadcastCode := by
  unfold Gaussian.MIMOBroadcast.PowerAdmissible
  dsimp [twoAntennaMIMOBroadcastCode]
  norm_num [Fin.sum_univ_succ]

/-- The joint event counts five erroneous message tuples, not an average of receiver errors. -/
@[capacity_test]
theorem mimoBroadcast_constant_decoders_joint_error
    (H : (i : Fin 2) → Matrix (Fin 1) (Fin 1) ℝ)
    (N : (i : Fin 2) → Matrix (Fin 1) (Fin 1) ℝ) :
    Gaussian.MIMOBroadcast.error H N unevenMIMOBroadcastCode = (5 / 6 : ℝ) := by
  classical
  have hevent (m : (i : Fin 2) → Fin (unevenMIMOBroadcastCode.messages i)) :
      Gaussian.MIMOBroadcast.errorEvent H unevenMIMOBroadcastCode m =
        if m = firstBroadcastMessage then ∅ else Set.univ := by
    ext z
    change (∃ i, firstBroadcastMessage i ≠ m i) ↔
      z ∈ if m = firstBroadcastMessage then ∅ else Set.univ
    by_cases h : m = firstBroadcastMessage
    · subst m
      simp
    · have hi : ∃ i, firstBroadcastMessage i ≠ m i := by
        by_contra hn
        push Not at hn
        exact h (funext hn).symm
      simp [h, hi]
  unfold Gaussian.MIMOBroadcast.error
  simp_rw [hevent]
  simp only [apply_ite, measure_empty, measure_univ, ENNReal.toReal_zero, ENNReal.toReal_one]
  have hcard : Fintype.card ((i : Fin 2) → Fin (unevenMIMOBroadcastCode.messages i)) = 6 := by
    rw [Fintype.card_pi]
    norm_num [unevenMIMOBroadcastCode, Fin.prod_univ_two]
  have hsum : (∑ m : (i : Fin 2) → Fin (unevenMIMOBroadcastCode.messages i),
      if m = firstBroadcastMessage then (0 : ℝ) else 1) = 5 := by
    calc
      _ = ∑ m : (i : Fin 2) → Fin (unevenMIMOBroadcastCode.messages i),
          (1 - if m = firstBroadcastMessage then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro m _
        split_ifs <;> norm_num
      _ = 5 := by
        norm_num [Finset.sum_sub_distrib, hcard]
  rw [hsum]
  norm_num [unevenMIMOBroadcastCode, Fin.prod_univ_two]

@[capacity_test]
theorem mimoBroadcast_noise_normalized {K : ℕ} {rx : Fin K → ℕ}
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (n : ℕ) :
    Gaussian.MIMOBroadcast.blockNoise N n Set.univ = 1 :=
  measure_univ

end CapacityAtlas.Tests
