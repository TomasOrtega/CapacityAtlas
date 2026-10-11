/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianOperational
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

/-- One joint encoder and a measurable decoder with only its own receiver's observations. -/
structure Code (K tx : ℕ) (rx : Fin K → ℕ) (n : ℕ) where
  messages : Fin K → ℕ
  messages_pos : ∀ i, 0 < messages i
  encode : ((i : Fin K) → Fin (messages i)) → Fin n → EuclideanSpace ℝ (Fin tx)
  decode : (i : Fin K) → Decoder (Fin n → EuclideanSpace ℝ (Fin (rx i))) (messages i)

variable {K tx : ℕ} {rx : Fin K → ℕ}

/-- Coordinates within a receiver may be correlated; receivers and uses are independent. -/
noncomputable def blockNoise
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (n : ℕ) :
    Measure ((i : Fin K) → Fin n → EuclideanSpace ℝ (Fin (rx i))) :=
  Measure.pi (fun i ↦ Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 (N i)))

instance blockNoise_isProbabilityMeasure
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (n : ℕ) :
    IsProbabilityMeasure (blockNoise N n) := by
  unfold blockNoise
  infer_instance

theorem blockNoise_eval
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {n : ℕ} (i : Fin K) (s : Fin n) :
    MeasurePreserving (fun z ↦ z i s) (blockNoise N n) (multivariateGaussian 0 (N i)) :=
  (measurePreserving_eval (fun _ : Fin n ↦ multivariateGaussian 0 (N i)) s).comp
    (measurePreserving_eval (fun j ↦
      Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 (N j))) i)

/-- The full block law retains each receiver's prescribed coordinate covariances. -/
theorem blockNoise_covariance
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {n : ℕ} (i : Fin K) (s : Fin n) (hN : (N i).PosDef) (a b : Fin (rx i)) :
    cov[fun z ↦ z i s a, fun z ↦ z i s b; blockNoise N n] = N i a b := by
  calc
    _ = cov[fun x ↦ x a, fun x ↦ x b;
        (blockNoise N n).map (fun z ↦ z i s)] :=
      (covariance_map_fun (by fun_prop) (by fun_prop)
        (blockNoise_eval N i s).measurable.aemeasurable).symm
    _ = N i a b := by
      rw [(blockNoise_eval N i s).map_eq]
      exact covariance_eval_multivariateGaussian hN.posSemidef a b

noncomputable def output
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) {n : ℕ}
    (x : Fin n → EuclideanSpace ℝ (Fin tx))
    (z : (i : Fin K) → Fin n → EuclideanSpace ℝ (Fin (rx i)))
    (i : Fin K) : Fin n → EuclideanSpace ℝ (Fin (rx i)) :=
  fun s ↦ (H i).toEuclideanLin (x s) + z i s

theorem measurable_output
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) {n : ℕ}
    (x : Fin n → EuclideanSpace ℝ (Fin tx)) (i : Fin K) :
    Measurable (fun z ↦ output H x z i) := by
  unfold output
  fun_prop

/-- Average over independent uniform messages, with one budget for all transmit antennas. -/
def PowerAdmissible (P : ℝ) {n : ℕ} (c : Code K tx rx n) : Prop :=
  (∏ i, (c.messages i : ℝ))⁻¹ *
    (∑ m, ∑ s, ∑ a, (c.encode m s a) ^ 2) ≤ (n : ℝ) * P

def errorEvent (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    {n : ℕ} (c : Code K tx rx n) (m : (i : Fin K) → Fin (c.messages i)) :
    Set ((i : Fin K) → Fin n → EuclideanSpace ℝ (Fin (rx i))) :=
  {z | ∃ i, (c.decode i).apply (output H (c.encode m) z i) ≠ m i}

theorem measurableSet_errorEvent
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    {n : ℕ} (c : Code K tx rx n) (m : (i : Fin K) → Fin (c.messages i)) :
    MeasurableSet (errorEvent H c m) := by
  unfold errorEvent
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  exact ((c.decode i).measurable_fiber (m i)).preimage (measurable_output H (c.encode m) i) |>.compl

/-- Joint error, averaged over the entire uniform message tuple. -/
noncomputable def error
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {n : ℕ} (c : Code K tx rx n) : ℝ :=
  (∏ i, (c.messages i : ℝ))⁻¹ *
    ∑ m, ((blockNoise N n) (errorEvent H c m)).toReal

noncomputable def rates {n : ℕ} (c : Code K tx rx n) : Fin K → ℝ :=
  fun i ↦ Operational.messageRate (c.messages i) n

/-- Closed operational region with joint reliability and message-averaged power. -/
noncomputable def capacityRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (P : ℝ) : Set (Fin K → ℝ) :=
  closure (Operational.achievableVectorRegion (Code K tx rx)
    (fun _ c ↦ PowerAdmissible P c) (fun _ c ↦ error H N c) (fun _ c ↦ rates c))

end CapacityAtlas.Gaussian.MIMOBroadcast
