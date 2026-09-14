/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteStateChannel
import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution.Joint
import CapacityAtlasForMathlib.InformationTheory.CausalHistories
import CapacityAtlasForMathlib.InformationTheory.OperationalRegion

open scoped BigOperators

namespace CapacityAtlas.FiniteStateOperational

variable {X S Y : Type*} [Fintype X] [Fintype S] [Fintype Y]

/-- State is not observed. Only output feedback is available. -/
structure FeedbackCode (W : FiniteStateChannel X S Y) (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → (t : Fin n) → (Fin t.val → Y) → X
  decode : (Fin n → Y) → Fin messages

structure Code (W : FiniteStateChannel X S Y) (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  encode : Fin messages → Fin n → X
  decode : (Fin n → Y) → Fin messages

def inputs {W : FiniteStateChannel X S Y} {n : ℕ}
    (c : FeedbackCode W n) (m : Fin c.messages) (y : Fin n → Y) : Fin n → X :=
  fun t ↦ c.encode m t (CausalHistories.past y t)

def Code.toFeedback {W : FiniteStateChannel X S Y} {n : ℕ}
    (c : Code W n) : FeedbackCode W n where
  messages := c.messages
  messages_pos := c.messages_pos
  encode m t _ := c.encode m t
  decode := c.decode

/-- Every intermediate hidden state is summed out under the fixed initial law. -/
noncomputable def likelihood (W : FiniteStateChannel X S Y) (initial : FiniteDistribution S)
    {n : ℕ} (x : Fin n → X) (y : Fin n → Y) : ℝ :=
  ∑ s : Fin (n + 1) → S, initial (s 0) *
    ∏ t : Fin n, W.transition (x t) (s t.castSucc) (y t) (s t.succ)

/-- The one-step joint output/next-state channel, normalized using the supplied law. -/
def stepChannel (W : FiniteStateChannel X S Y) : FiniteChannel (X × S) (Y × S) where
  transition xs ys := W.transition xs.1 xs.2 ys.1 ys.2
  nonnegative xs ys := W.nonnegative xs.1 xs.2 ys.1 ys.2
  row_sum xs := by
    rw [Fintype.sum_prod_type]
    exact W.row_sum xs.1 xs.2

/-- Chronological transcript construction. Each bind is a normalized finite joint law.
The returned state is the hidden state after the last channel use. -/
noncomputable def historyLaw (W : FiniteStateChannel X S Y)
    (initial : FiniteDistribution S) :
    (n : ℕ) → ((t : Fin n) → (Fin t.val → Y) → X) →
      FiniteDistribution ((Fin n → Y) × S) := by
  classical
  exact fun n ↦ Nat.rec
    (fun _ ↦ initial.map (fun s ↦ ((fun t : Fin 0 ↦ Fin.elim0 t), s)))
    (fun k previous policy ↦
      ((previous (fun t ↦ policy t.castSucc)).joint (fun hs ↦
        (stepChannel W).rowDistribution (policy (Fin.last k) hs.1, hs.2))).map
          (fun trace ↦ (Fin.snoc trace.1.1 trace.2.1, trace.2.2))) n

/-- The receiver sees outputs, not the final hidden state. -/
noncomputable def outputLaw {W : FiniteStateChannel X S Y}
    (initial : FiniteDistribution S) {n : ℕ} (c : FeedbackCode W n)
    (m : Fin c.messages) : FiniteDistribution (Fin n → Y) := by
  classical
  exact (historyLaw W initial n (c.encode m)).map Prod.fst

/-- Average error computed from the normalized induced output law.
The raw path-sum formula is a separate, explicitly tracked interface obligation. -/
noncomputable def feedbackError {W : FiniteStateChannel X S Y}
    (initial : FiniteDistribution S) {n : ℕ} (c : FeedbackCode W n) : ℝ := by
  classical
  exact (c.messages : ℝ)⁻¹ * ∑ m, ∑ y : Fin n → Y,
    if c.decode y = m then 0 else outputLaw initial c m y

noncomputable def feedbackCapacity (W : FiniteStateChannel X S Y)
    (initial : FiniteDistribution S) (allowed : ∀ n, (Fin n → X) → Prop) : ℝ :=
  Operational.capacity (FeedbackCode W)
    (fun n c ↦ ∀ m y, allowed n (inputs c m y))
    (fun _ c ↦ feedbackError initial c)
    (fun n c ↦ Operational.messageRate c.messages n)

noncomputable def capacity (W : FiniteStateChannel X S Y)
    (initial : FiniteDistribution S) (allowed : ∀ n, (Fin n → X) → Prop) : ℝ :=
  Operational.capacity (Code W) (fun n c ↦ ∀ m, allowed n (c.encode m))
    (fun _ c ↦ feedbackError initial c.toFeedback)
    (fun n c ↦ Operational.messageRate c.messages n)

noncomputable def fixedInitial (s : S) : FiniteDistribution S := by
  classical
  exact (FiniteChannel.deterministic (fun _ : Unit ↦ s)).rowDistribution ()

def noConsecutiveOnes (n : ℕ) (word : Fin n → Bool) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → ¬(word i = true ∧ word j = true)

def memoryless (W : FiniteChannel X Y) : FiniteStateChannel X Unit Y where
  transition x _ y _ := W.transition x y
  nonnegative x _ y _ := W.nonnegative x y
  row_sum x _ := by simp [W.row_sum]

noncomputable def additiveMarkov {G : Type*} [Fintype G] [AddCommGroup G]
    (K : FiniteChannel G G) : FiniteStateChannel G G G := by
  classical
  exact {
    transition := fun x s y next ↦ if y = x + s then K.transition s next else 0
    nonnegative := fun x s y next ↦ by split <;> simp_all [K.nonnegative]
    row_sum := fun x s ↦ by simp [Finset.sum_ite_irrel, K.row_sum] }

noncomputable def transitionPower (K : FiniteChannel S S) (n : ℕ) : FiniteChannel S S := by
  classical
  exact Nat.rec (FiniteChannel.deterministic id) (fun _ previous ↦ K.comp previous) n

/-- Concrete finite irreducibility/aperiodicity convention. -/
def IsPrimitive (K : FiniteChannel S S) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → ∀ s t, 0 < (transitionPower K n).transition s t

noncomputable def markovEntropyRate (p : FiniteDistribution S) (K : FiniteChannel S S) : ℝ :=
  ∑ s, p s * (K.rowDistribution s).entropyBits

end CapacityAtlas.FiniteStateOperational
