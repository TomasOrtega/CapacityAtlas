/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.RemainingModels
import CapacityAtlasForMathlib.InformationTheory.OperationalCapacity

/-!
# Unproved interface obligations

These definitions specify propositions, not proofs or assumed axioms. The backlog
tracks them as `specified-unproved`, with the problem families that should discharge
them before using the corresponding bridge. No capacity theorem imports this file.
The trusted definitions do not depend on these obligations.
-/

open scoped BigOperators

namespace CapacityAtlas.Obligations

/-- The epsilon-rate convention is the nonnegative rate closure of the original one.
Do not identify achievable sets themselves at their boundary. -/
def finiteDMCRateClosure {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : FiniteChannel X Y) : Prop :=
  ∀ r : ℝ,
    Operational.Achievable (FiniteChannel.BlockCode W) (fun _ _ ↦ True)
      (fun _ c ↦ c.averageErrorProbability) (fun _ c ↦ c.rate) r ↔
    0 ≤ r ∧ ∀ δ : ℝ, 0 < δ → W.AchievableRate (r - δ)

/-- Supremal capacity agrees even though the boundary-rate conventions differ. -/
def finiteDMCCapacityBridge {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (W : FiniteChannel X Y) : Prop :=
  Operational.capacity (FiniteChannel.BlockCode W) (fun _ _ ↦ True)
    (fun _ c ↦ c.averageErrorProbability) (fun _ c ↦ c.rate) = W.operationalCapacityBits

/-- Connect the entropy-sum wrapper to the existing channel information interface. -/
def channelInformationBridge {X Y : Type*} [Fintype X] [Fintype Y]
    (W : FiniteChannel X Y) : Prop :=
  ∀ p : FiniteDistribution X,
    FiniteInformation.information (FiniteInformation.joint p W) Prod.fst Prod.snd =
      W.mutualInformationBits p

/-- Conditional information agrees with the existing conditional-entropy interface,
including zero-mass conditioning events. All logarithms here are converted to bits. -/
def conditionalInformationBridge {Ω A B C : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) (h : Ω → C) : Prop :=
  FiniteInformation.conditional p f g h =
    (ProbabilityTheory.condEntropy f h p.toPMF.toMeasure -
      ProbabilityTheory.condEntropy f (fun ω ↦ (g ω, h ω)) p.toPMF.toMeasure) / Real.log 2

/-- Normalized finite-state output laws agree with the raw sum over hidden paths. -/
def finiteStatePathSum {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]
    (W : FiniteStateChannel X S Y) (initial : FiniteDistribution S) : Prop :=
  ∀ n, ∀ c : FiniteStateOperational.FeedbackCode W n, ∀ m y,
    FiniteStateOperational.outputLaw initial c m y =
      FiniteStateOperational.likelihood W initial (FiniteStateOperational.inputs c m y) y

/-- One-step specialization of the normalized law recovers the physical row. -/
def finiteStateOneStep {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]
    (W : FiniteStateChannel X S Y) : Prop :=
  ∀ s x y next,
    FiniteStateOperational.historyLaw W (FiniteStateOperational.fixedInitial s)
      1 (fun _ _ ↦ x) ((fun _ ↦ y), next) = W.transition x s y next

/-- An earlier output of the deterministic recursion cannot depend on future noise. -/
def causalRunNonanticipative {Y Z : Type*} (initial : Y) : Prop :=
  ∀ n, ∀ step : (t : Fin n) → (Fin t.val → Y) → Z → Y,
    ∀ z z' : Fin n → Z, ∀ t : Fin n,
      (∀ j : Fin n, j.val ≤ t.val → z j = z' j) →
        CausalHistories.run initial step z t = CausalHistories.run initial step z' t

/-- Relaying uses one normalized physical joint law, despite the adaptive relay input. -/
def relayLikelihoodNormalized {X R Z Y : Type*}
    [Fintype X] [Fintype R] [Fintype Z] [Fintype Y]
    (W : Relay.Channel X R Z Y) : Prop :=
  ∀ n, ∀ c : Relay.Code W n, ∀ m,
    (∑ z : Fin n → Z, ∑ y : Fin n → Y,
      ∏ t, W.transition (c.encode m t, c.relay t (CausalHistories.past z t)) (z t, y t)) = 1

/-- Feedback MAC path probabilities sum to one for each fixed message pair. -/
def feedbackMACLikelihoodNormalized {X₁ X₂ Y : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y] (W : FiniteChannel (X₁ × X₂) Y) : Prop :=
  ∀ n, ∀ c : MACFeedback.Code W n, ∀ m₁ m₂,
    (∑ y : Fin n → Y, ∏ t, W.transition
      (c.encode₁ m₁ t (CausalHistories.past y t),
        c.encode₂ m₂ t (CausalHistories.past y t)) (y t)) = 1

/-- Interactive two-way path probabilities sum to one for each message pair. -/
def twoWayLikelihoodNormalized {A B Y Z : Type*}
    [Fintype A] [Fintype B] [Fintype Y] [Fintype Z]
    (W : FiniteChannel (A × B) (Y × Z)) : Prop :=
  ∀ n, ∀ c : TwoWay.Code W n, ∀ m₁ m₂,
    (∑ y : Fin n → Y, ∑ z : Fin n → Z, ∏ t, W.transition
      (c.encode₁ m₁ t (CausalHistories.past y t),
        c.encode₂ m₂ t (CausalHistories.past z t)) (y t, z t)) = 1

/-- Canonical PSD agrees with the former real quadratic-form description. -/
def covarianceBridge {tx : ℕ} (P : ℝ) (Q : Matrix (Fin tx) (Fin tx) ℝ) : Prop :=
  Gaussian.AdmissibleCovariance P Q ↔
    Q.transpose = Q ∧ (∀ v : Fin tx → ℝ, 0 ≤ ∑ i, ∑ j, v i * Q i j * v j) ∧
      (∑ i, Q i i) ≤ P

/-- The two AWGN power conventions are separate models until this is proved. -/
def awgnPowerConventionBridge (P N : ℝ) : Prop :=
  0 ≤ P → 0 < N → Gaussian.messageAverageCapacity P N = Gaussian.capacity P N

/-- Operational scalar/vector bridge, stronger than testing only the log determinant. -/
def scalarMIMOCapacityBridge (P N : ℝ) : Prop :=
  0 ≤ P → 0 < N →
    Gaussian.mimoCapacity (1 : Matrix (Fin 1) (Fin 1) ℝ) P N = Gaussian.capacity P N

/-- With the specified marginals, max marginal error and joint error differ by
at most a factor two. This is the bridge used for vanishing-error equivalence. -/
def broadcastErrorConventionBridge {X Y₁ Y₂ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : FiniteBroadcastChannel X Y₁ Y₂) (V : FiniteChannel X (Y₁ × Y₂)) : Prop :=
  (∀ x y₁, (∑ y₂, V.transition x (y₁, y₂)) = W.receiver₁.transition x y₁) →
  (∀ x y₂, (∑ y₁, V.transition x (y₁, y₂)) = W.receiver₂.transition x y₂) →
  ∀ n, ∀ c : PrivateMessageBroadcast.Code W n,
    PrivateMessageBroadcast.error c ≤ PrivateMessageBroadcast.jointError V c ∧
      PrivateMessageBroadcast.jointError V c ≤ 2 * PrivateMessageBroadcast.error c

end CapacityAtlas.Obligations
