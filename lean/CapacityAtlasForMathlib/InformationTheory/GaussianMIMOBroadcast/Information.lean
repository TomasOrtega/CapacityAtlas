/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Basic
import CapacityAtlasForMathlib.InformationTheory.MeasureFano
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n : ℕ} {rx : Fin K → ℕ}

noncomputable def uniformFinLaw (m : ℕ) (hm : 0 < m) : Measure (Fin m) :=
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  (PMF.uniformOfFintype (Fin m)).toMeasure

instance uniformFinLaw_isProbabilityMeasure (m : ℕ) (hm : 0 < m) :
    IsProbabilityMeasure (uniformFinLaw m hm) := by
  unfold uniformFinLaw
  infer_instance

theorem uniformFinLaw_singleton (m : ℕ) (hm : 0 < m) (a : Fin m) :
    uniformFinLaw m hm {a} = (m : ℝ≥0∞)⁻¹ := by
  simp [uniformFinLaw]

abbrev MessageTuple (c : Code K tx rx n) := (i : Fin K) → Fin (c.messages i)

abbrev ExperimentSpace (c : Code K tx rx n) :=
  MessageTuple c × ((i : Fin K) → Fin n → EuclideanSpace ℝ (Fin (rx i)))

/-- Independent uniform private messages, before any encoding. -/
noncomputable def messageLaw (c : Code K tx rx n) : Measure (MessageTuple c) :=
  Measure.pi (fun i ↦ uniformFinLaw (c.messages i) (c.messages_pos i))

instance messageLaw_isProbabilityMeasure (c : Code K tx rx n) :
    IsProbabilityMeasure (messageLaw c) := by
  unfold messageLaw
  infer_instance

theorem messageLaw_singleton (c : Code K tx rx n) (m : MessageTuple c) :
    messageLaw c {m} = (∏ i, (c.messages i : ℝ≥0∞))⁻¹ := by
  simp only [messageLaw, Measure.pi_singleton, uniformFinLaw_singleton]
  rw [ENNReal.prod_inv_distrib (fun _ _ _ _ _ ↦ Or.inr (by simp))]

theorem messageLaw_real_singleton (c : Code K tx rx n) (m : MessageTuple c) :
    (messageLaw c).real {m} = (∏ i, (c.messages i : ℝ))⁻¹ := by
  simp [Measure.real, messageLaw_singleton, ENNReal.toReal_prod]

/-- The actual code experiment pairs its uniform messages with the prescribed block noise. -/
noncomputable def experiment
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) : Measure (ExperimentSpace c) :=
  (messageLaw c).prod (blockNoise N n)

instance experiment_isProbabilityMeasure
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) : IsProbabilityMeasure (experiment N c) := by
  unfold experiment
  infer_instance

def messageRV (c : Code K tx rx n) (i : Fin K) : ExperimentSpace c → Fin (c.messages i) :=
  fun p ↦ p.1 i

noncomputable def receivedRV
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (c : Code K tx rx n) (i : Fin K) :
    ExperimentSpace c → Fin n → EuclideanSpace ℝ (Fin (rx i)) :=
  fun p ↦ output H (c.encode p.1) p.2 i

theorem measurable_messageRV (c : Code K tx rx n) (i : Fin K) :
    Measurable (messageRV c i) := (measurable_pi_apply i).comp measurable_fst

theorem measurable_receivedRV
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (c : Code K tx rx n) (i : Fin K) : Measurable (receivedRV H c i) :=
  measurable_from_prod_countable_right fun m ↦ measurable_output H (c.encode m) i

theorem decoder_measurable {Observation : Type*} [MeasurableSpace Observation] {m : ℕ}
    (decode : Decoder Observation m) : Measurable decode.apply :=
  measurable_to_countable' decode.measurable_fiber

theorem experiment_map_messageRV
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) :
    (experiment N c).map (messageRV c i) = uniformFinLaw (c.messages i) (c.messages_pos i) := by
  have heval := (measurePreserving_eval
    (fun j ↦ uniformFinLaw (c.messages j) (c.messages_pos j)) i).map_eq
  rw [← heval]
  change ((messageLaw c).prod (blockNoise N n)).map ((fun m ↦ m i) ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_pi_apply i) measurable_fst, Measure.map_fst_prod]
  simp [messageLaw]

theorem experiment_message_uniform
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) (m : Fin (c.messages i)) :
    (experiment N c).map (messageRV c i) {m} = (c.messages i : ℝ≥0∞)⁻¹ := by
  rw [experiment_map_messageRV, uniformFinLaw_singleton]

theorem experiment_real_apply
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) {s : Set (ExperimentSpace c)} (hs : MeasurableSet s) :
    (experiment N c).real s = (∏ i, (c.messages i : ℝ))⁻¹ *
      ∑ m, (blockNoise N n).real (Prod.mk m ⁻¹' s) := by
  rw [Measure.real, experiment, Measure.prod_apply hs, lintegral_fintype]
  simp_rw [messageLaw_singleton]
  rw [← Finset.sum_mul, ENNReal.toReal_mul, ENNReal.toReal_sum (by intro m _; finiteness)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_prod, ENNReal.toReal_natCast]
  exact mul_comm _ _

theorem experiment_receiver_error
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) :
    (experiment N c).real {p | (c.decode i).apply (receivedRV H c i p) ≠ messageRV c i p} =
      receiverError H N c i := by
  have hs : MeasurableSet {p | (c.decode i).apply (receivedRV H c i p) ≠ messageRV c i p} :=
    (measurableSet_eq_fun ((decoder_measurable (c.decode i)).comp (measurable_receivedRV H c i))
      (measurable_messageRV c i)).compl
  rw [experiment_real_apply N c hs]
  rfl

theorem experiment_joint_error
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) :
    (experiment N c).real {p | ∃ i,
      (c.decode i).apply (receivedRV H c i p) ≠ messageRV c i p} = error H N c := by
  have hs : MeasurableSet {p | ∃ i,
      (c.decode i).apply (receivedRV H c i p) ≠ messageRV c i p} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion fun i ↦
      (measurableSet_eq_fun ((decoder_measurable (c.decode i)).comp (measurable_receivedRV H c i))
        (measurable_messageRV c i)).compl
  rw [experiment_real_apply N c hs]
  rfl

/-- Information about a private message in exactly that receiver's block observations. -/
noncomputable def receiverMutualInfo
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) : ℝ≥0∞ :=
  MeasureInformation.mutualInfoRV (messageRV c i) (receivedRV H c i) (experiment N c)

theorem receiverMutualInfo_ne_top
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) : receiverMutualInfo H N c i ≠ ⊤ := by
  letI : Nonempty (Fin (c.messages i)) := ⟨⟨0, c.messages_pos i⟩⟩
  exact MeasureInformation.mutualInfoRV_ne_top_of_uniform (experiment N c)
    (measurable_messageRV c i) (measurable_receivedRV H c i)
    (fun m ↦ by simpa using experiment_message_uniform N c i m)

theorem receiverMutualInfo_le_log
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) :
    (receiverMutualInfo H N c i).toReal ≤ Real.log (c.messages i) := by
  letI : Nonempty (Fin (c.messages i)) := ⟨⟨0, c.messages_pos i⟩⟩
  simpa only [receiverMutualInfo, Fintype.card_fin] using
    MeasureInformation.mutualInfoRV_toReal_le_log_card (experiment N c)
      (measurable_messageRV c i) (measurable_receivedRV H c i)
      (fun m ↦ by simpa using experiment_message_uniform N c i m)

theorem fano_receiver
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) :
    Real.log (c.messages i) ≤ (receiverMutualInfo H N c i).toReal + Real.log 2 +
      receiverError H N c i * Real.log (c.messages i) := by
  letI : Nonempty (Fin (c.messages i)) := ⟨⟨0, c.messages_pos i⟩⟩
  have h := MeasureInformation.fano_uniform (experiment N c)
    (measurable_messageRV c i) (measurable_receivedRV H c i) (decoder_measurable (c.decode i))
    (fun m ↦ by simpa using experiment_message_uniform N c i m)
  simpa only [Fintype.card_fin, experiment_receiver_error, receiverMutualInfo] using h

/-- The production joint error controls each receiver's Fano remainder. -/
theorem fano_joint_error
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) :
    Real.log (c.messages i) ≤ (receiverMutualInfo H N c i).toReal + Real.log 2 +
      error H N c * Real.log (c.messages i) := by
  have hlog : 0 ≤ Real.log (c.messages i) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ c.messages i from c.messages_pos i))
  have h := fano_receiver H N c i
  have herror := mul_le_mul_of_nonneg_right (receiverError_le_error H N c i) hlog
  linarith

theorem fano_joint_error_ennreal
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (i : Fin K) :
    ENNReal.ofReal ((1 - error H N c) * Real.log (c.messages i) - Real.log 2) ≤
      receiverMutualInfo H N c i := by
  rw [ENNReal.ofReal_le_iff_le_toReal (receiverMutualInfo_ne_top H N c i)]
  have h := fano_joint_error H N c i
  nlinarith

end CapacityAtlas.Gaussian.MIMOBroadcast
