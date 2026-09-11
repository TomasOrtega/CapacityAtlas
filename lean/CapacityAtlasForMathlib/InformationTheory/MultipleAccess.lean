/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.DecoderSideInformation
import CapacityAtlasForMathlib.InformationTheory.CodingConverse
import CapacityAtlasForMathlib.InformationTheory.RateRegion

open scoped BigOperators

namespace CapacityAtlas.MultipleAccess

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-- Exchange the two senders' input alphabets. -/
@[capacity_shared_api]
def swap (W : FiniteChannel (X₁ × X₂) Y) : FiniteChannel (X₂ × X₁) Y :=
  W.encoded Prod.swap

/-- Independent input laws for the two senders. -/
@[capacity_shared_api]
noncomputable def productInput (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) :
    FiniteDistribution (X₁ × X₂) :=
  p₁.joint fun _ ↦ p₂

/-- The first sender's channel when the second input is fixed. -/
@[capacity_shared_api]
def leftSlice (W : FiniteChannel (X₁ × X₂) Y) (x₂ : X₂) : FiniteChannel X₁ Y :=
  W.encoded fun x₁ ↦ (x₁, x₂)

/-- The second sender's channel when the first input is fixed. -/
@[capacity_shared_api]
def rightSlice (W : FiniteChannel (X₁ × X₂) Y) (x₁ : X₁) : FiniteChannel X₂ Y :=
  W.encoded fun x₂ ↦ (x₁, x₂)

/-- First-sender conditional information, in bits. -/
@[capacity_shared_api]
noncomputable def leftInformation (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) : ℝ :=
  ∑ x₂, p₂ x₂ * (leftSlice W x₂).mutualInformationBits p₁

/-- Second-sender conditional information, in bits. -/
@[capacity_shared_api]
noncomputable def rightInformation (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) : ℝ :=
  ∑ x₁, p₁ x₁ * (rightSlice W x₁).mutualInformationBits p₂

@[simp, capacity_shared_api]
theorem leftInformation_swap (W : FiniteChannel (X₁ × X₂) Y)
    (p₂ : FiniteDistribution X₂) (p₁ : FiniteDistribution X₁) :
    leftInformation (swap W) p₂ p₁ = rightInformation W p₁ p₂ := rfl

/-- Joint input information, in bits. -/
@[capacity_shared_api]
noncomputable def jointInformation (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) : ℝ :=
  W.mutualInformationBits (productInput p₁ p₂)

/-- One use of a MAC with separate deterministic encoders and a joint decoder. -/
@[capacity_shared_api]
structure OneShotCode (W : FiniteChannel (X₁ × X₂) Y)
    (M₁ M₂ : Type*) [Fintype M₁] [Fintype M₂] where
  encode₁ : M₁ → X₁
  encode₂ : M₂ → X₂
  decode : Y → M₁ × M₂

namespace OneShotCode

variable {W : FiniteChannel (X₁ × X₂) Y}
variable {M₁ M₂ : Type*} [Fintype M₁] [Fintype M₂]

@[capacity_shared_api]
def toOneShotCode (code : OneShotCode W M₁ M₂) : CapacityAtlas.OneShotCode W (M₁ × M₂) where
  encode message := (code.encode₁ message.1, code.encode₂ message.2)
  decode := code.decode

/-- Error under independent uniform messages. -/
@[capacity_shared_api]
noncomputable def averageErrorProbability [Nonempty M₁] [Nonempty M₂]
    [DecidableEq M₁] [DecidableEq M₂] (code : OneShotCode W M₁ M₂) : ℝ :=
  code.toOneShotCode.averageErrorProbability

end OneShotCode

/-- A block code preserves the independence of the senders' message maps. -/
@[capacity_shared_api]
structure BlockCode (W : FiniteChannel (X₁ × X₂) Y) (n : ℕ) where
  messageCount₁ : ℕ
  messageCount₂ : ℕ
  messageCount₁_pos : 0 < messageCount₁
  messageCount₂_pos : 0 < messageCount₂
  encode₁ : Fin messageCount₁ → (Fin n → X₁)
  encode₂ : Fin messageCount₂ → (Fin n → X₂)
  decode : (Fin n → Y) → Fin messageCount₁ × Fin messageCount₂

namespace BlockCode

variable {W : FiniteChannel (X₁ × X₂) Y} {n : ℕ}

@[capacity_shared_api]
instance (code : BlockCode W n) : Nonempty (Fin code.messageCount₁) :=
  Fin.pos_iff_nonempty.mp code.messageCount₁_pos

@[capacity_shared_api]
instance (code : BlockCode W n) : Nonempty (Fin code.messageCount₂) :=
  Fin.pos_iff_nonempty.mp code.messageCount₂_pos

@[capacity_shared_api]
def toOneShotCode (code : BlockCode W n) :
    CapacityAtlas.OneShotCode (W.block n) (Fin code.messageCount₁ × Fin code.messageCount₂) where
  encode message i := (code.encode₁ message.1 i, code.encode₂ message.2 i)
  decode := code.decode

/-- Joint decoding error averaged over both independent messages. -/
@[capacity_shared_api]
noncomputable def averageErrorProbability (code : BlockCode W n) : ℝ :=
  code.toOneShotCode.averageErrorProbability

@[capacity_shared_api]
noncomputable def rate₁ (code : BlockCode W n) : ℝ :=
  Real.log code.messageCount₁ / ((n : ℝ) * Real.log 2)

@[capacity_shared_api]
noncomputable def rate₂ (code : BlockCode W n) : ℝ :=
  Real.log code.messageCount₂ / ((n : ℝ) * Real.log 2)

/-- Exchange the senders and the corresponding decoder components. -/
@[capacity_shared_api]
def swap (code : BlockCode W n) : BlockCode (MultipleAccess.swap W) n where
  messageCount₁ := code.messageCount₂
  messageCount₂ := code.messageCount₁
  messageCount₁_pos := code.messageCount₂_pos
  messageCount₂_pos := code.messageCount₁_pos
  encode₁ := code.encode₂
  encode₂ := code.encode₁
  decode output := (code.decode output).swap

@[simp, capacity_shared_api]
theorem averageErrorProbability_swap (code : BlockCode W n) :
    code.swap.averageErrorProbability = code.averageErrorProbability := by
  classical
  simp only [averageErrorProbability, CapacityAtlas.OneShotCode.averageErrorProbability_eq,
    CapacityAtlas.OneShotCode.errorProbability_eq_sum_decode_ne,
    Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Fintype.sum_prod_type]
  change (↑code.messageCount₂ * ↑code.messageCount₁ : ℝ)⁻¹ *
      (∑ m₂, ∑ m₁, ∑ output,
        if (code.decode output).swap ≠ (m₂, m₁) then
          (W.block n).transition (code.toOneShotCode.encode (m₁, m₂)) output else 0) = _
  rw [mul_comm (code.messageCount₂ : ℝ), Finset.sum_comm]
  simp only [ne_eq, Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk, toOneShotCode]

end BlockCode

/-- All sufficiently large blocklengths, allowing arbitrarily small rate slack. -/
@[capacity_shared_api]
def AchievableRate (W : FiniteChannel (X₁ × X₂) Y) (r : RatePair) : Prop :=
  0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∃ code : BlockCode W n,
      code.averageErrorProbability ≤ ε ∧ r.1 - ε ≤ code.rate₁ ∧ r.2 - ε ≤ code.rate₂

/-- The average-error capacity region for two independent messages. -/
@[capacity_shared_api]
def operationalRegion (W : FiniteChannel (X₁ × X₂) Y) : Set RatePair :=
  {r | AchievableRate W r}

/-- The three MAC inequalities with arbitrary finite time sharing. -/
@[capacity_shared_api]
def informationRegion (W : FiniteChannel (X₁ × X₂) Y) : Set RatePair :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ k : ℕ, ∃ weights : FiniteDistribution (Fin k),
    ∃ p₁ : Fin k → FiniteDistribution X₁, ∃ p₂ : Fin k → FiniteDistribution X₂,
      r.1 ≤ ∑ q, weights q * leftInformation W (p₁ q) (p₂ q) ∧
      r.2 ≤ ∑ q, weights q * rightInformation W (p₁ q) (p₂ q) ∧
      r.1 + r.2 ≤ ∑ q, weights q * jointInformation W (p₁ q) (p₂ q)}

end CapacityAtlas.MultipleAccess
