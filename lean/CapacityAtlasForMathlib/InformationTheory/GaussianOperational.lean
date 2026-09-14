/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalRegion
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian

noncomputable def noise (N : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ gaussianReal 0 N.toNNReal)

noncomputable def vectorNoise (N : ℝ) (n d : ℕ) : Measure (Fin n → Fin d → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ noise N d)

/-- Measurability of every finite decision region is required. -/
structure Decoder (Observation : Type*) [MeasurableSpace Observation] (messages : ℕ) where
  apply : Observation → Fin messages
  measurable_fiber : ∀ m, MeasurableSet {y | apply y = m}

structure Code (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → Fin n → ℝ
  decode : Decoder (Fin n → ℝ) messages

/-- Maximum-codeword block-average power. -/
def CodewordPowerAdmissible (P : ℝ) {n : ℕ} (c : Code n) : Prop :=
  ∀ m, (∑ t, (c.encode m t) ^ 2) ≤ (n : ℝ) * P

noncomputable def error (N : ℝ) {n : ℕ} (c : Code n) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m,
    ((noise N n) {z | c.decode.apply (fun t ↦ c.encode m t + z t) ≠ m}).toReal

noncomputable def capacity (P N : ℝ) : ℝ :=
  Operational.capacity Code (fun _ c ↦ CodewordPowerAdmissible P c) (fun _ c ↦ error N c)
    (fun n c ↦ Operational.messageRate c.messages n)

/-- Alternative expected-power convention: average over the uniform message.
This is not the registered AWGN code class. Its capacity equivalence is a proof task. -/
def MessageAveragePowerAdmissible (P : ℝ) {n : ℕ} (c : Code n) : Prop :=
  (c.messages : ℝ)⁻¹ * (∑ m, ∑ t, (c.encode m t) ^ 2) ≤ (n : ℝ) * P

noncomputable def messageAverageCapacity (P N : ℝ) : ℝ :=
  Operational.capacity Code (fun _ c ↦ MessageAveragePowerAdmissible P c)
    (fun _ c ↦ error N c) (fun n c ↦ Operational.messageRate c.messages n)

noncomputable def awgnFormula (P N : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (1 + P / N)

structure VectorCode (tx rx n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → Fin n → Fin tx → ℝ
  decode : Decoder (Fin n → Fin rx → ℝ) messages

noncomputable def vectorOutput {tx rx n : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (x : Fin n → Fin tx → ℝ) (z : Fin n → Fin rx → ℝ) : Fin n → Fin rx → ℝ :=
  fun t r ↦ (∑ k, H r k * x t k) + z t r

def CodewordVectorPowerAdmissible (P : ℝ) {tx rx n : ℕ} (c : VectorCode tx rx n) : Prop :=
  ∀ m, (∑ t, ∑ k, (c.encode m t k) ^ 2) ≤ (n : ℝ) * P

noncomputable def vectorError {tx rx n : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (N : ℝ) (c : VectorCode tx rx n) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m,
    ((vectorNoise N n rx) {z | c.decode.apply (vectorOutput H (c.encode m) z) ≠ m}).toReal

noncomputable def mimoCapacity {tx rx : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (P N : ℝ) : ℝ :=
  Operational.capacity (VectorCode tx rx) (fun _ c ↦ CodewordVectorPowerAdmissible P c)
    (fun _ c ↦ vectorError H N c) (fun n c ↦ Operational.messageRate c.messages n)

/-- Real symmetric positive-semidefinite covariance with the specified trace budget. -/
def AdmissibleCovariance {tx : ℕ} (P : ℝ) (Q : Matrix (Fin tx) (Fin tx) ℝ) : Prop :=
  Q.PosSemidef ∧ Matrix.trace Q ≤ P

noncomputable def logDet {tx rx : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (N : ℝ) (Q : Matrix (Fin tx) (Fin tx) ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (Matrix.det
    (fun i j ↦ (if i = j then 1 else 0) +
      (∑ k, ∑ l, H i k * Q k l * H j l) / N))

noncomputable def mimoFormula {tx rx : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (P N : ℝ) : ℝ :=
  sSup {r | ∃ Q : Matrix (Fin tx) (Fin tx) ℝ, AdmissibleCovariance P Q ∧ r = logDet H N Q}

/-- Peak amplitude is not replaced by average power. -/
def AmplitudeAdmissible (A : ℝ) {n : ℕ} (c : Code n) : Prop :=
  ∀ m t, |c.encode m t| ≤ A

noncomputable def amplitudeCapacity (A N : ℝ) : ℝ :=
  Operational.capacity Code (fun _ c ↦ AmplitudeAdmissible A c) (fun _ c ↦ error N c)
    (fun n c ↦ Operational.messageRate c.messages n)

noncomputable def outputDensity (μ : Measure ℝ) (N y : ℝ) : ℝ :=
  ∫ x, gaussianPDFReal x N.toNNReal y ∂μ

/-- Actual AWGN mutual information in bits. Claims use compactly supported
probability measures and positive noise variance, where these integrals are finite. -/
noncomputable def mutualInformation (μ : Measure ℝ) (N : ℝ) : ℝ :=
  (∫ x, ∫ y, gaussianPDFReal x N.toNNReal y *
    Real.log (gaussianPDFReal x N.toNNReal y / outputDensity μ N y) ∂volume ∂μ) / Real.log 2

noncomputable def amplitudeFormula (A N : ℝ) : ℝ :=
  sSup {r | ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Icc (-A) A) = 1 ∧
    r = mutualInformation μ N}

end CapacityAtlas.Gaussian
