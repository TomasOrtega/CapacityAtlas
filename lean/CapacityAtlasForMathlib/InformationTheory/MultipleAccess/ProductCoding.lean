/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.

Adapted from TomasOrtega/CapacityAtlasMAC, commit ec5be554b9644df94dd58190963793f3f1d1da52,
CapacityAtlasMAC/ProductCoding.lean. Reuses shared random-coding estimates.
-/

import CapacityAtlasForMathlib.InformationTheory.MultipleAccess.ProductTails

open scoped BigOperators

namespace CapacityAtlas.MultipleAccess

private theorem messageDifference_le (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    ((FiniteChannel.messageCountAtRate s n - 1 : ℕ) : ℝ) ≤
      2 * Real.exp ((n : ℝ) * s * Real.log 2) := by
  have hcount : ((FiniteChannel.messageCountAtRate s n - 1 : ℕ) : ℝ) ≤
      (FiniteChannel.messageCountAtRate s n : ℝ) := by
    exact_mod_cast Nat.sub_le (FiniteChannel.messageCountAtRate s n) 1
  exact hcount.trans (FiniteChannel.natCeil_exp_le_two_mul_exp (by positivity))

private theorem rival_bound (s information δ : ℝ) (hs : 0 ≤ s)
    (hgap : s = 0 ∨ s * Real.log 2 + 2 * δ ≤ information) (n : ℕ) :
    ((FiniteChannel.messageCountAtRate s n - 1 : ℕ) : ℝ) *
        Real.exp (-((n : ℝ) * information - (n : ℝ) * δ)) ≤
      2 * Real.exp (-((n : ℝ) * δ)) := by
  rcases hgap with rfl | hgap
  · simp [FiniteChannel.messageCountAtRate, Real.exp_nonneg]
  have hcount : ((FiniteChannel.messageCountAtRate s n - 1 : ℕ) : ℝ) ≤
      (FiniteChannel.messageCountAtRate s n : ℝ) := by
    exact_mod_cast Nat.sub_le (FiniteChannel.messageCountAtRate s n) 1
  exact (mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le).trans
    (FiniteChannel.messageCountAtRate_mul_exp_neg_le s δ hs n (by
      have h := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) n)
      nlinarith))

private theorem joint_rival_bound (s₁ s₂ information δ : ℝ)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hgap : s₁ = 0 ∨ s₂ = 0 ∨ (s₁ + s₂) * Real.log 2 + 2 * δ ≤ information)
    (n : ℕ) :
    ((FiniteChannel.messageCountAtRate s₁ n - 1 : ℕ) : ℝ) *
        ((FiniteChannel.messageCountAtRate s₂ n - 1 : ℕ) : ℝ) *
        Real.exp (-((n : ℝ) * information - (n : ℝ) * δ)) ≤
      4 * Real.exp (-((n : ℝ) * δ)) := by
  rcases hgap with rfl | rfl | hgap
  · simp [FiniteChannel.messageCountAtRate, Real.exp_nonneg]
  · simp [FiniteChannel.messageCountAtRate, Real.exp_nonneg]
  calc
    _ ≤ ((2 * Real.exp ((n : ℝ) * s₁ * Real.log 2)) *
        (2 * Real.exp ((n : ℝ) * s₂ * Real.log 2))) *
        Real.exp (-((n : ℝ) * information - (n : ℝ) * δ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul (messageDifference_le s₁ hs₁ n) (messageDifference_le s₂ hs₂ n)
        (Nat.cast_nonneg _) (by positivity)
    _ = 4 * Real.exp ((n : ℝ) * (s₁ + s₂) * Real.log 2 -
        ((n : ℝ) * information - (n : ℝ) * δ)) := by
      rw [show (n : ℝ) * (s₁ + s₂) * Real.log 2 -
          ((n : ℝ) * information - (n : ℝ) * δ) =
          (n : ℝ) * s₁ * Real.log 2 + (n : ℝ) * s₂ * Real.log 2 +
            -((n : ℝ) * information - (n : ℝ) * δ) by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
      have h := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) n)
      nlinarith

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

private def ProductRandomCodingBound (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) (V : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ n M₁ M₂ : ℕ, 0 < n → 0 < M₁ → 0 < M₂ →
    ∃ code : BlockCode W n,
      code.messageCount₁ = M₁ ∧ code.messageCount₂ = M₂ ∧
      code.averageErrorProbability ≤
        (n : ℝ) * V / ((n : ℝ) * δ) ^ 2 +
        ((M₁ - 1 : ℕ) : ℝ) * Real.exp (-((n : ℝ) *
          (leftInformation W p₁ p₂ * Real.log 2) - (n : ℝ) * δ)) +
        ((M₂ - 1 : ℕ) : ℝ) * Real.exp (-((n : ℝ) *
          (rightInformation W p₁ p₂ * Real.log 2) - (n : ℝ) * δ)) +
        ((M₁ - 1 : ℕ) : ℝ) * ((M₂ - 1 : ℕ) : ℝ) * Real.exp (-((n : ℝ) *
          (jointInformation W p₁ p₂ * Real.log 2) - (n : ℝ) * δ))

private theorem codes_of_strict_productInput (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) (V : ℝ)
    (randomCoding : ProductRandomCodingBound W p₁ p₂ V) (s : RatePair)
    (hs₁ : 0 ≤ s.1) (hs₂ : 0 ≤ s.2)
    (hleft : 0 < s.1 → s.1 < leftInformation W p₁ p₂)
    (hright : 0 < s.2 → s.2 < rightInformation W p₁ p₂)
    (hjoint : 0 < s.1 → 0 < s.2 → s.1 + s.2 < jointInformation W p₁ p₂) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ code : BlockCode W n, code.averageErrorProbability ≤ ε ∧
        s.1 ≤ code.rate₁ ∧ s.2 ≤ code.rate₂ := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let g₁ := if s.1 = 0 then 1 else
    leftInformation W p₁ p₂ * Real.log 2 - s.1 * Real.log 2
  let g₂ := if s.2 = 0 then 1 else
    rightInformation W p₁ p₂ * Real.log 2 - s.2 * Real.log 2
  let g₁₂ := if s.1 = 0 ∨ s.2 = 0 then 1 else
    jointInformation W p₁ p₂ * Real.log 2 - (s.1 + s.2) * Real.log 2
  have hg₁ : 0 < g₁ := by
    dsimp [g₁]
    split_ifs with h
    · norm_num
    · exact sub_pos.mpr (mul_lt_mul_of_pos_right (hleft (lt_of_le_of_ne hs₁ (Ne.symm h))) hlog)
  have hg₂ : 0 < g₂ := by
    dsimp [g₂]
    split_ifs with h
    · norm_num
    · exact sub_pos.mpr (mul_lt_mul_of_pos_right (hright (lt_of_le_of_ne hs₂ (Ne.symm h))) hlog)
  have hg₁₂ : 0 < g₁₂ := by
    dsimp [g₁₂]
    split_ifs with h
    · norm_num
    · have h₁ : 0 < s.1 := lt_of_le_of_ne hs₁ (Ne.symm (fun hz ↦ h (Or.inl hz)))
      have h₂ : 0 < s.2 := lt_of_le_of_ne hs₂ (Ne.symm (fun hz ↦ h (Or.inr hz)))
      exact sub_pos.mpr (mul_lt_mul_of_pos_right (hjoint h₁ h₂) hlog)
  let δ := min g₁ (min g₂ g₁₂) / 2
  have hδ : 0 < δ := div_pos (lt_min hg₁ (lt_min hg₂ hg₁₂)) (by norm_num)
  have hδ₁ : 2 * δ ≤ g₁ := by dsimp [δ]; linarith [min_le_left g₁ (min g₂ g₁₂)]
  have hδ₂ : 2 * δ ≤ g₂ := by
    have h := (min_le_right g₁ (min g₂ g₁₂)).trans (min_le_left g₂ g₁₂)
    dsimp [δ]
    linarith
  have hδ₁₂ : 2 * δ ≤ g₁₂ := by
    have h := (min_le_right g₁ (min g₂ g₁₂)).trans (min_le_right g₂ g₁₂)
    dsimp [δ]
    linarith
  have hgap₁ : s.1 = 0 ∨ s.1 * Real.log 2 + 2 * δ ≤
      leftInformation W p₁ p₂ * Real.log 2 := by
    by_cases h : s.1 = 0
    · exact Or.inl h
    · right
      simp only [g₁, if_neg h] at hδ₁
      linarith
  have hgap₂ : s.2 = 0 ∨ s.2 * Real.log 2 + 2 * δ ≤
      rightInformation W p₁ p₂ * Real.log 2 := by
    by_cases h : s.2 = 0
    · exact Or.inl h
    · right
      simp only [g₂, if_neg h] at hδ₂
      linarith
  have hgap₁₂ : s.1 = 0 ∨ s.2 = 0 ∨ (s.1 + s.2) * Real.log 2 + 2 * δ ≤
      jointInformation W p₁ p₂ * Real.log 2 := by
    by_cases h₁ : s.1 = 0
    · exact Or.inl h₁
    by_cases h₂ : s.2 = 0
    · exact Or.inr (Or.inl h₂)
    right; right
    simp only [g₁₂, h₁, h₂, or_self, if_false] at hδ₁₂
    linarith
  intro ε hε
  have hbound := FiniteChannel.weightedRandomCodingBound_tendsto_zero V δ 8 hδ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hbound).2 ε hε)
  refine ⟨max 1 N, by omega, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  obtain ⟨code, hc₁, hc₂, herror⟩ := randomCoding δ hδ n
    (FiniteChannel.messageCountAtRate s.1 n) (FiniteChannel.messageCountAtRate s.2 n)
    hnpos (FiniteChannel.messageCountAtRate_pos _ _) (FiniteChannel.messageCountAtRate_pos _ _)
  refine ⟨code, ?_, ?_, ?_⟩
  · have h₁ := rival_bound s.1 (leftInformation W p₁ p₂ * Real.log 2) δ hs₁ hgap₁ n
    have h₂ := rival_bound s.2 (rightInformation W p₁ p₂ * Real.log 2) δ hs₂ hgap₂ n
    have h₁₂ := joint_rival_bound s.1 s.2 (jointInformation W p₁ p₂ * Real.log 2)
      δ hs₁ hs₂ hgap₁₂ n
    have hlimit := hN n (by omega)
    linarith
  · rw [BlockCode.rate₁, hc₁]
    simpa only [Real.logb, div_div, mul_comm (Real.log 2)] using
      FiniteChannel.targetRate_le_rateOfMessageCountAtRate s.1 hnpos
  · rw [BlockCode.rate₂, hc₂]
    simpa only [Real.logb, div_div, mul_comm (Real.log 2)] using
      FiniteChannel.targetRate_le_rateOfMessageCountAtRate s.2 hnpos

private theorem achievableRate_of_productInput_of_randomCodingBound
    (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) (V : ℝ)
    (randomCoding : ProductRandomCodingBound W p₁ p₂ V) (r : RatePair)
    (hr₁ : 0 ≤ r.1) (hr₂ : 0 ≤ r.2)
    (ha : r.1 ≤ leftInformation W p₁ p₂)
    (hb : r.2 ≤ rightInformation W p₁ p₂)
    (hc : r.1 + r.2 ≤ jointInformation W p₁ p₂) : AchievableRate W r := by
  refine ⟨hr₁, hr₂, ?_⟩
  intro ε hε
  let s : RatePair := (max 0 (r.1 - ε / 2), max 0 (r.2 - ε / 2))
  have hs₁ : 0 ≤ s.1 := le_max_left _ _
  have hs₂ : 0 ≤ s.2 := le_max_left _ _
  have hs₁le : s.1 ≤ r.1 := max_le hr₁ (by linarith)
  have hs₂le : s.2 ≤ r.2 := max_le hr₂ (by linarith)
  have hs₁lt (hs : 0 < s.1) : s.1 < r.1 :=
    max_lt (hs.trans_le hs₁le) (by linarith)
  have hs₂lt (hs : 0 < s.2) : s.2 < r.2 :=
    max_lt (hs.trans_le hs₂le) (by linarith)
  have hleft (hs : 0 < s.1) : s.1 < leftInformation W p₁ p₂ := (hs₁lt hs).trans_le ha
  have hright (hs : 0 < s.2) : s.2 < rightInformation W p₁ p₂ := (hs₂lt hs).trans_le hb
  have hjoint (hs : 0 < s.1) (_ : 0 < s.2) :
      s.1 + s.2 < jointInformation W p₁ p₂ := by
    linarith [hs₁lt hs]
  obtain ⟨N, hN, hcodes⟩ := codes_of_strict_productInput W p₁ p₂ V randomCoding s
    hs₁ hs₂ hleft hright hjoint ε hε
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨code, herror, hrate₁, hrate₂⟩ := hcodes n hn
  refine ⟨code, herror, ?_, ?_⟩
  · have hslack : r.1 - ε / 2 ≤ s.1 := le_max_right _ _
    linarith
  · have hslack : r.2 - ε / 2 ≤ s.2 := le_max_right _ _
    linarith

/-- Every weak product-input pentagon rate is achievable, including its axes and boundary. -/
theorem achievableRate_of_productInput (W : FiniteChannel (X₁ × X₂) Y)
    (p₁ : FiniteDistribution X₁) (p₂ : FiniteDistribution X₂) (r : RatePair)
    (hr₁ : 0 ≤ r.1) (hr₂ : 0 ≤ r.2)
    (ha : r.1 ≤ leftInformation W p₁ p₂)
    (hb : r.2 ≤ rightInformation W p₁ p₂)
    (hc : r.1 + r.2 ≤ jointInformation W p₁ p₂) : AchievableRate W r := by
  obtain ⟨V, _, hbound⟩ := hasProductRandomCodingBound W p₁ p₂
  exact achievableRate_of_productInput_of_randomCodingBound W p₁ p₂ V hbound r hr₁ hr₂ ha hb hc

end CapacityAtlas.MultipleAccess
