/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.CausalState
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion

open scoped BigOperators

namespace CapacityAtlas.NoncausalState

variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

/-- The encoder sees the entire iid state word. The decoder sees outputs only. -/
structure Code (p : FiniteDistribution S) (W : S → FiniteChannel X Y) (n : ℕ) where
  /-- Number of distinct messages. -/
  messages : ℕ
  /-- The message set is nonempty. -/
  messages_pos : 0 < messages
  /-- Input word selected using the message and the complete state word. -/
  encode : Fin messages → (Fin n → S) → Fin n → X
  /-- Message estimate obtained from the output word. -/
  decode : (Fin n → Y) → Fin messages

/-- Average decoding error over uniform messages, iid states, and channel outputs. -/
noncomputable def error {p : FiniteDistribution S} {W : S → FiniteChannel X Y}
    {n : ℕ} (c : Code p W n) : ℝ := by
  classical
  exact (c.messages : ℝ)⁻¹ * ∑ m, ∑ s : Fin n → S, ∑ y : Fin n → Y,
    if c.decode y = m then 0 else
      (p.iid n s) * ∏ t, (W (s t)).transition (c.encode m s t) (y t)

/-- Message rate in bits per physical channel use. -/
noncomputable def rate {p : FiniteDistribution S} {W : S → FiniteChannel X Y}
    {n : ℕ} (c : Code p W n) := Operational.messageRate c.messages n

/-- Operational capacity with the entire iid state word available only to the encoder. -/
noncomputable def capacity (p : FiniteDistribution S) (W : S → FiniteChannel X Y) : ℝ :=
  Operational.capacity (Code p W) (fun _ _ ↦ True) (fun _ c ↦ error c) (fun _ c ↦ rate c)

/-- The state marginal is fixed and the physical transition is applied to that state. -/
def auxiliaryJoint {u : ℕ} (q : FiniteDistribution (Fin u × S × X))
    (W : S → FiniteChannel X Y) :=
  FiniteInformation.joint q
    (FiniteChannel.ofRows fun a ↦ (W a.2.1).rowDistribution a.2.2)

/-- Supremum of auxiliary-output minus auxiliary-state information for laws with the fixed state marginal. -/
noncomputable def informationCapacity (p : FiniteDistribution S)
    (W : S → FiniteChannel X Y) : ℝ := by
  classical
  exact sSup {r | ∃ u : ℕ, ∃ q : FiniteDistribution (Fin u × S × X),
    q.map (fun a ↦ a.2.1) = p ∧
    r = FiniteInformation.information (auxiliaryJoint q W) (fun a ↦ a.1.1) Prod.snd -
      FiniteInformation.information q Prod.fst (fun a ↦ a.2.1)}

/-- Memory-cell state determining whether the written bit is preserved or forced. -/
inductive Defect where
  /-- The cell preserves the written bit. -/
  | normal
  /-- The cell always outputs zero. -/
  | stuckZero
  /-- The cell always outputs one. -/
  | stuckOne
  deriving DecidableEq, Fintype

/-- Output bit for a normal, stuck-zero, or stuck-one memory cell. -/
def defectOutput : Defect → Bool → Bool
  | .normal, x => x
  | .stuckZero, _ => false
  | .stuckOne, _ => true

/-- Deterministic bit channel associated with a specified memory-cell defect. -/
def defectChannel (s : Defect) : FiniteChannel Bool Bool :=
  FiniteChannel.deterministic (defectOutput s)

/-- All probabilities of the physical defect law are fixed. -/
def IsDefectLaw (δ : ℝ) (p : FiniteDistribution Defect) : Prop :=
  p .normal = 1 - δ ∧ p .stuckZero = δ / 2 ∧ p .stuckOne = δ / 2

end CapacityAtlas.NoncausalState
