/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.

Adapted from TomasOrtega/CapacityAtlasMAC, commit ec5be554b9644df94dd58190963793f3f1d1da52,
CapacityAtlasMAC/ProductTails.lean. Reuses shared modules and sender-swap symmetry.
-/

import CapacityAtlasForMathlib.InformationTheory.MultipleAccess.RandomCoding
import CapacityAtlasForMathlib.InformationTheory.DecoderStateInformationDensity

open scoped BigOperators

namespace CapacityAtlas.MultipleAccess

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

/-- The block channel retains two separate word alphabets. -/
def productBlockChannel (W : FiniteChannel (X₁ × X₂) Y) (n : ℕ) :
    FiniteChannel ((Fin n → X₁) × (Fin n → X₂)) (Fin n → Y) :=
  (W.block n).encoded (FiniteChannel.wordPairEquiv n)

theorem leftTail_productBlock (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) (n : ℕ) (t : ℝ) :
    (∑ x₂, p₂.iid n x₂ *
      (leftSlice (productBlockChannel W n) x₂).informationDensityLowerTailMass (p₁.iid n) t) =
    ((FiniteChannel.withDecoderState p₂ (leftSlice W)).block n).informationDensityLowerTailMass
       (p₁.iid n) t := by
  rw [← FiniteChannel.withDecoderState_informationDensityLowerTailMass]
  symm
  apply FiniteChannel.informationDensityLowerTailMass_eq_of_equiv
    (FiniteChannel.withDecoderState (p₂.iid n) (leftSlice (productBlockChannel W n)))
    ((FiniteChannel.withDecoderState p₂ (leftSlice W)).block n)
    (p₁.iid n) (p₁.iid n) (Equiv.refl _)
    (FiniteChannel.wordPairEquiv (X := X₂) (Y := Y) n)
  · intro x output
    change (∏ i, p₂ (output.1 i) * W.transition (x i, output.1 i) (output.2 i)) =
      (∏ i, p₂ (output.1 i)) * ∏ i, W.transition (x i, output.1 i) (output.2 i)
    exact Finset.prod_mul_distrib
  · intro x
    rfl

theorem rightTail_productBlock (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) (n : ℕ) (t : ℝ) :
    (∑ x₁, p₁.iid n x₁ *
      (rightSlice (productBlockChannel W n) x₁).informationDensityLowerTailMass (p₂.iid n) t) =
    ((FiniteChannel.withDecoderState p₁ (rightSlice W)).block n).informationDensityLowerTailMass
       (p₂.iid n) t :=
  leftTail_productBlock (swap W) p₂ p₁ n t

theorem jointTail_productBlock (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) (n : ℕ) (t : ℝ) :
    (productBlockChannel W n).informationDensityLowerTailMass
      (productInput (p₁.iid n) (p₂.iid n)) t =
    (W.block n).informationDensityLowerTailMass ((productInput p₁ p₂).iid n) t := by
  symm
  apply FiniteChannel.informationDensityLowerTailMass_eq_of_equiv
    (productBlockChannel W n) (W.block n)
    (productInput (p₁.iid n) (p₂.iid n)) ((productInput p₁ p₂).iid n)
    (FiniteChannel.wordPairEquiv n) (Equiv.refl _)
  · intro x y
    rfl
  · intro x
    change (∏ i, p₁ (x.1 i) * p₂ (x.2 i)) =
      (∏ i, p₁ (x.1 i)) * ∏ i, p₂ (x.2 i)
    exact Finset.prod_mul_distrib

theorem leftInformation_mul_log_two (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) :
    leftInformation W p₁ p₂ * Real.log 2 =
      (FiniteChannel.withDecoderState p₂ (leftSlice W)).mutualInformation p₁ := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp [leftInformation, FiniteChannel.mutualInformationBits,
    FiniteChannel.withDecoderState_mutualInformation, Finset.sum_mul,
    ← mul_div_assoc, div_mul_cancel₀ _ hlog]

theorem rightInformation_mul_log_two (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) :
    rightInformation W p₁ p₂ * Real.log 2 =
      (FiniteChannel.withDecoderState p₁ (rightSlice W)).mutualInformation p₂ :=
  leftInformation_mul_log_two (swap W) p₂ p₁

theorem jointInformation_mul_log_two (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) :
    jointInformation W p₁ p₂ * Real.log 2 = W.mutualInformation (productInput p₁ p₂) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  exact div_mul_cancel₀ _ hlog

private theorem block_tail_le {A B : Type*} [Fintype A] [Fintype B]
    (W : FiniteChannel A B) (p : FiniteDistribution A) (δ : ℝ) {n : ℕ}
    (hn : 0 < n) (hδ : 0 < δ) :
    (W.block n).informationDensityLowerTailMass (p.iid n)
      ((n : ℝ) * W.mutualInformation p - (n : ℝ) * δ) ≤
        (n : ℝ) * W.informationVariance p / (((n : ℝ) * δ) ^ 2) := by
  rw [W.block_informationDensityLowerTailMass_eq]
  exact W.blockInformationDensity_lowerTail_le p hn hδ

/-- Independent block codebooks have a variance bound with exact rival counts. -/
theorem hasProductRandomCodingBound (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ δ : ℝ, 0 < δ → ∀ n M₁ M₂ : ℕ,
      0 < n → 0 < M₁ → 0 < M₂ → ∃ code : BlockCode W n,
        code.messageCount₁ = M₁ ∧ code.messageCount₂ = M₂ ∧
        code.averageErrorProbability ≤
          (n : ℝ) * V / ((n : ℝ) * δ) ^ 2 +
          ((M₁ - 1 : ℕ) : ℝ) * Real.exp (-((n : ℝ) *
            (leftInformation W p₁ p₂ * Real.log 2) - (n : ℝ) * δ)) +
          ((M₂ - 1 : ℕ) : ℝ) * Real.exp (-((n : ℝ) *
            (rightInformation W p₁ p₂ * Real.log 2) - (n : ℝ) * δ)) +
          ((M₁ - 1 : ℕ) : ℝ) * ((M₂ - 1 : ℕ) : ℝ) * Real.exp (-((n : ℝ) *
            (jointInformation W p₁ p₂ * Real.log 2) - (n : ℝ) * δ)) := by
  classical
  let D₁ := FiniteChannel.withDecoderState p₂ (leftSlice W)
  let D₂ := FiniteChannel.withDecoderState p₁ (rightSlice W)
  let V₁ := D₁.informationVariance p₁
  let V₂ := D₂.informationVariance p₂
  let V₁₂ := W.informationVariance (productInput p₁ p₂)
  refine ⟨V₁ + V₂ + V₁₂, ?_, ?_⟩
  · exact add_nonneg (add_nonneg (D₁.informationVariance_nonnegative p₁)
      (D₂.informationVariance_nonnegative p₂)) (W.informationVariance_nonnegative _)
  intro δ hδ n M₁ M₂ hn hM₁ hM₂
  letI : Nonempty (Fin M₁) := Fin.pos_iff_nonempty.mp hM₁
  letI : Nonempty (Fin M₂) := Fin.pos_iff_nonempty.mp hM₂
  let t₁ := (n : ℝ) * D₁.mutualInformation p₁ - (n : ℝ) * δ
  let t₂ := (n : ℝ) * D₂.mutualInformation p₂ - (n : ℝ) * δ
  let t₁₂ := (n : ℝ) * W.mutualInformation (productInput p₁ p₂) - (n : ℝ) * δ
  obtain ⟨oneShot, hcode⟩ := exists_oneShotCode_averageErrorProbability_le
    (productBlockChannel W n) (p₁.iid n) (p₂.iid n) t₁ t₂ t₁₂
      (I := Fin M₁) (J := Fin M₂)
  let code : BlockCode W n := {
    messageCount₁ := M₁
    messageCount₂ := M₂
    messageCount₁_pos := hM₁
    messageCount₂_pos := hM₂
    encode₁ := oneShot.encode₁
    encode₂ := oneShot.encode₂
    decode := oneShot.decode }
  refine ⟨code, rfl, rfl, ?_⟩
  have herror : code.averageErrorProbability = oneShot.averageErrorProbability := rfl
  rw [herror, leftInformation_mul_log_two, rightInformation_mul_log_two,
    jointInformation_mul_log_two]
  rw [leftTail_productBlock, rightTail_productBlock, jointTail_productBlock] at hcode
  simp only [Fintype.card_fin] at hcode
  have ht₁ := block_tail_le D₁ p₁ δ hn hδ
  have ht₂ := block_tail_le D₂ p₂ δ hn hδ
  have ht₁₂ := block_tail_le W (productInput p₁ p₂) δ hn hδ
  have hvariance : (n : ℝ) * (V₁ + V₂ + V₁₂) / ((n : ℝ) * δ) ^ 2 =
      (n : ℝ) * V₁ / ((n : ℝ) * δ) ^ 2 +
      (n : ℝ) * V₂ / ((n : ℝ) * δ) ^ 2 +
      (n : ℝ) * V₁₂ / ((n : ℝ) * δ) ^ 2 := by ring
  rw [hvariance]
  exact hcode.trans (by
    dsimp [t₁, t₂, t₁₂, V₁, V₂, V₁₂, D₁, D₂] at *
    linarith)

end CapacityAtlas.MultipleAccess
