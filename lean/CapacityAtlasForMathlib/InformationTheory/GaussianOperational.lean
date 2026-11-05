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

/-- Independent centered real Gaussian noise over `n` coordinates, with variance `N.toNNReal`. -/
noncomputable def noise (N : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ gaussianReal 0 N.toNNReal)

/-- Independent centered Gaussian noise for every time and receiver coordinate. -/
noncomputable def vectorNoise (N : ℝ) (n d : ℕ) : Measure (Fin n → Fin d → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ noise N d)

/-- Measurability of every finite decision region is required. -/
structure Decoder (Observation : Type*) [MeasurableSpace Observation] (messages : ℕ) where
  /-- Decision rule assigning a message index to each observation. -/
  apply : Observation → Fin messages
  /-- Every message decision region is measurable. -/
  measurable_fiber : ∀ m, MeasurableSet {y | apply y = m}

/-- Finite-message real block code with a deterministic encoder and measurable decoder fibers. -/
structure Code (n : ℕ) where
  /-- Number of messages in the finite alphabet. -/
  messages : ℕ
  /-- The message alphabet contains at least one element. -/
  messages_pos : 0 < messages
  /-- Real input block assigned to each message. -/
  encode : Fin messages → Fin n → ℝ
  /-- Measurable decoding rule for a real output block. -/
  decode : Decoder (Fin n → ℝ) messages

/-- Maximum-codeword block-average power. -/
def CodewordPowerAdmissible (P : ℝ) {n : ℕ} (c : Code n) : Prop :=
  ∀ m, (∑ t, (c.encode m t) ^ 2) ≤ (n : ℝ) * P

/-- Decoding-error probability averaged uniformly over messages and Gaussian noise. -/
noncomputable def error (N : ℝ) {n : ℕ} (c : Code n) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m,
    ((noise N n) {z | c.decode.apply (fun t ↦ c.encode m t + z t) ≠ m}).toReal

/-- Scalar Gaussian operational capacity under a power constraint for every codeword. -/
noncomputable def capacity (P N : ℝ) : ℝ :=
  Operational.capacity Code (fun _ c ↦ CodewordPowerAdmissible P c) (fun _ c ↦ error N c)
    (fun n c ↦ Operational.messageRate c.messages n)

/-- Alternative expected-power convention: average over the uniform message.
This is not the registered AWGN code class. Its capacity equivalence is a proof task. -/
def MessageAveragePowerAdmissible (P : ℝ) {n : ℕ} (c : Code n) : Prop :=
  (c.messages : ℝ)⁻¹ * (∑ m, ∑ t, (c.encode m t) ^ 2) ≤ (n : ℝ) * P

/-- Scalar Gaussian operational capacity under power averaged uniformly over messages. -/
noncomputable def messageAverageCapacity (P N : ℝ) : ℝ :=
  Operational.capacity Code (fun _ c ↦ MessageAveragePowerAdmissible P c)
    (fun _ c ↦ error N c) (fun n c ↦ Operational.messageRate c.messages n)

/-- The scalar expression `log₂ (1 + P / N) / 2`, measured in bits per channel use. -/
noncomputable def awgnFormula (P N : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (1 + P / N)

/-- Finite-message block code with `tx` real input coordinates and `rx` real output coordinates. -/
structure VectorCode (tx rx n : ℕ) where
  /-- Number of messages in the finite alphabet. -/
  messages : ℕ
  /-- The message alphabet contains at least one element. -/
  messages_pos : 0 < messages
  /-- Input vector at each time coordinate for the selected message. -/
  encode : Fin messages → Fin n → Fin tx → ℝ
  /-- Measurable decoding rule for the complete received vector block. -/
  decode : Decoder (Fin n → Fin rx → ℝ) messages

/-- Apply the channel matrix at each time coordinate and add the receiver noise block. -/
noncomputable def vectorOutput {tx rx n : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (x : Fin n → Fin tx → ℝ) (z : Fin n → Fin rx → ℝ) : Fin n → Fin rx → ℝ :=
  fun t r ↦ (∑ k, H r k * x t k) + z t r

/-- Bound every vector codeword’s total energy over time and input coordinates by `n * P`. -/
def CodewordVectorPowerAdmissible (P : ℝ) {tx rx n : ℕ} (c : VectorCode tx rx n) : Prop :=
  ∀ m, (∑ t, ∑ k, (c.encode m t k) ^ 2) ≤ (n : ℝ) * P

/-- Uniform-message decoding-error probability for the vector Gaussian channel. -/
noncomputable def vectorError {tx rx n : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (N : ℝ) (c : VectorCode tx rx n) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m,
    ((vectorNoise N n rx) {z | c.decode.apply (vectorOutput H (c.encode m) z) ≠ m}).toReal

/-- Vector Gaussian operational capacity under a separate power bound on every codeword. -/
noncomputable def mimoCapacity {tx rx : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (P N : ℝ) : ℝ :=
  Operational.capacity (VectorCode tx rx) (fun _ c ↦ CodewordVectorPowerAdmissible P c)
    (fun _ c ↦ vectorError H N c) (fun n c ↦ Operational.messageRate c.messages n)

/-- Real symmetric positive-semidefinite covariance with the specified trace budget. -/
def AdmissibleCovariance {tx : ℕ} (P : ℝ) (Q : Matrix (Fin tx) (Fin tx) ℝ) : Prop :=
  Q.PosSemidef ∧ Matrix.trace Q ≤ P

/-- Gaussian covariance log-determinant expression in bits, with scalar noise level `N`. -/
noncomputable def logDet {tx rx : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (N : ℝ) (Q : Matrix (Fin tx) (Fin tx) ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 (Matrix.det
    (fun i j ↦ (if i = j then 1 else 0) +
      (∑ k, ∑ l, H i k * Q k l * H j l) / N))

/-- Supremum of the Gaussian log-determinant expression over admissible input covariances. -/
noncomputable def mimoFormula {tx rx : ℕ} (H : Matrix (Fin rx) (Fin tx) ℝ)
    (P N : ℝ) : ℝ :=
  sSup {r | ∃ Q : Matrix (Fin tx) (Fin tx) ℝ, AdmissibleCovariance P Q ∧ r = logDet H N Q}

/-- Peak amplitude is not replaced by average power. -/
def AmplitudeAdmissible (A : ℝ) {n : ℕ} (c : Code n) : Prop :=
  ∀ m t, |c.encode m t| ≤ A

/-- Scalar Gaussian operational capacity when each transmitted symbol has amplitude at most `A`. -/
noncomputable def amplitudeCapacity (A N : ℝ) : ℝ :=
  Operational.capacity Code (fun _ c ↦ AmplitudeAdmissible A c) (fun _ c ↦ error N c)
    (fun n c ↦ Operational.messageRate c.messages n)

/-- Gaussian output-density mixture induced by an input measure `μ`. -/
noncomputable def outputDensity (μ : Measure ℝ) (N y : ℝ) : ℝ :=
  ∫ x, gaussianPDFReal x N.toNNReal y ∂μ

/-- Actual AWGN mutual information in bits. Claims use compactly supported
probability measures and positive noise variance, where these integrals are finite. -/
noncomputable def mutualInformation (μ : Measure ℝ) (N : ℝ) : ℝ :=
  (∫ x, ∫ y, gaussianPDFReal x N.toNNReal y *
    Real.log (gaussianPDFReal x N.toNNReal y / outputDensity μ N y) ∂volume ∂μ) / Real.log 2

/-- Supremum of input/output mutual information over probability laws supported on `[-A, A]`. -/
noncomputable def amplitudeFormula (A N : ℝ) : ℝ :=
  sSup {r | ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Icc (-A) A) = 1 ∧
    r = mutualInformation μ N}

end CapacityAtlas.Gaussian
