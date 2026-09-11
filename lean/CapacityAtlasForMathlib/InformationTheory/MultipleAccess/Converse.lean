/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.

Adapted from TomasOrtega/CapacityAtlasMAC, commit ec5be554b9644df94dd58190963793f3f1d1da52,
CapacityAtlasMAC/Converse.lean. Local imports, shared Fano normalization, and sender-swap reuse for the second converse.
-/

import CapacityAtlasForMathlib.InformationTheory.MultipleAccess.RegionGeometry
import CapacityAtlasForMathlib.InformationTheory.MultipleAccess
import CapacityAtlasForMathlib.InformationTheory.BlockInputInformation
import CapacityAtlasForMathlib.InformationTheory.FiniteProductDistribution

open scoped BigOperators

namespace CapacityAtlas.MultipleAccess

attribute [local instance] Classical.propDecidable

variable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]

private theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    FiniteDistribution.uniform (A × B) =
      productInput (FiniteDistribution.uniform A) (FiniteDistribution.uniform B) := by
  ext pair
  simp [productInput, FiniteDistribution.uniform_apply, Fintype.card_prod,
    Nat.cast_mul, mul_inv_rev, mul_comm]

private theorem averageError_eq_sum_uniform {A B M : Type*}
    [Fintype A] [Fintype B] [Fintype M] [Nonempty M] [DecidableEq M]
    {channel : FiniteChannel A B} (code : CapacityAtlas.OneShotCode channel M) :
    code.averageErrorProbability =
      ∑ m, FiniteDistribution.uniform M m * code.errorProbability m := by
  rw [CapacityAtlas.OneShotCode.averageErrorProbability_eq]
  simp only [FiniteDistribution.uniform_apply, Finset.mul_sum]

private theorem mutualInformation_eq_bits_mul {A B : Type*} [Fintype A] [Fintype B]
    (channel : FiniteChannel A B) (input : FiniteDistribution A) :
    channel.mutualInformation input = channel.mutualInformationBits input * Real.log 2 := by
  simp [FiniteChannel.mutualInformationBits, Real.log_ne_zero_of_pos_of_ne_one
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]

namespace BlockCode

variable {W : FiniteChannel (X₁ × X₂) Y} {n : ℕ}

/-- The first encoder's input law at a fixed coordinate under its uniform message. -/
noncomputable def coordinateInput₁ (code : BlockCode W n) (i : Fin n) : FiniteDistribution X₁ :=
  (FiniteDistribution.uniform (Fin code.messageCount₁)).map (fun m ↦ code.encode₁ m i)

/-- The second encoder's input law at the same coordinate. -/
noncomputable def coordinateInput₂ (code : BlockCode W n) (i : Fin n) : FiniteDistribution X₂ :=
  (FiniteDistribution.uniform (Fin code.messageCount₂)).map (fun m ↦ code.encode₂ m i)

private def conditionalFirstCode (code : BlockCode W n) (m₂ : Fin code.messageCount₂) :
    CapacityAtlas.OneShotCode (W.block n) (Fin code.messageCount₁) where
  encode m₁ i := (code.encode₁ m₁ i, code.encode₂ m₂ i)
  decode output := (code.decode output).1

private theorem conditionalFirst_error_le (code : BlockCode W n)
    (m₁ : Fin code.messageCount₁) (m₂ : Fin code.messageCount₂) :
    (conditionalFirstCode code m₂).errorProbability m₁ ≤
      code.toOneShotCode.errorProbability (m₁, m₂) := by
  rw [CapacityAtlas.OneShotCode.errorProbability_eq_sum_decode_ne,
    CapacityAtlas.OneShotCode.errorProbability_eq_sum_decode_ne]
  apply Finset.sum_le_sum
  intro output _
  change (if (code.decode output).1 ≠ m₁ then _ else 0) ≤
    if code.decode output ≠ (m₁, m₂) then _ else 0
  by_cases hpair : code.decode output = (m₁, m₂)
  · simp [hpair]
  · simp only [if_pos hpair]
    split_ifs
    · exact le_rfl
    · exact (W.block n).nonnegative _ _

private theorem average_conditionalFirst_error_le (code : BlockCode W n) :
    (∑ m₂, FiniteDistribution.uniform (Fin code.messageCount₂) m₂ *
      (conditionalFirstCode code m₂).averageErrorProbability) ≤ code.averageErrorProbability := by
  let u₁ := FiniteDistribution.uniform (Fin code.messageCount₁)
  let u₂ := FiniteDistribution.uniform (Fin code.messageCount₂)
  simp_rw [averageError_eq_sum_uniform, Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ m₁, ∑ m₂, u₂ m₂ * (u₁ m₁ *
    (conditionalFirstCode code m₂).errorProbability m₁)) ≤ _
  calc
    _ ≤ ∑ m₁, ∑ m₂, u₁ m₁ * u₂ m₂ * code.toOneShotCode.errorProbability (m₁, m₂) := by
      apply Finset.sum_le_sum
      intro m₁ _
      apply Finset.sum_le_sum
      intro m₂ _
      have hw : 0 ≤ u₁ m₁ * u₂ m₂ := mul_nonneg (u₁.nonnegative m₁) (u₂.nonnegative m₂)
      calc
        _ = u₁ m₁ * u₂ m₂ * (conditionalFirstCode code m₂).errorProbability m₁ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (conditionalFirst_error_le code m₁ m₂) hw
    _ = code.averageErrorProbability := by
      unfold averageErrorProbability
      rw [averageError_eq_sum_uniform, uniform_product]
      simp only [Fintype.sum_prod_type, productInput, FiniteDistribution.joint_apply]
      rfl

private theorem conditionalFirst_log_bound (code : BlockCode W n)
    (m₂ : Fin code.messageCount₂) :
    Real.log code.messageCount₁ ≤
      (∑ i, (leftSlice W (code.encode₂ m₂ i)).mutualInformation (code.coordinateInput₁ i)) +
        Real.log 2 + (conditionalFirstCode code m₂).averageErrorProbability *
          Real.log code.messageCount₁ := by
  let input := FiniteDistribution.uniform (Fin code.messageCount₁)
  let encode := (conditionalFirstCode code m₂).encode
  let channel := (W.block n).encoded encode
  have hfano := channel.fano_uniform (conditionalFirstCode code m₂).decode
  change Real.log (Fintype.card (Fin code.messageCount₁)) ≤
    channel.mutualInformation input + Real.log 2 +
      (conditionalFirstCode code m₂).averageErrorProbability *
        Real.log (Fintype.card (Fin code.messageCount₁)) at hfano
  simp only [Fintype.card_fin] at hfano
  have hinfo := W.encoded_block_mutualInformation_le_sum n encode input
  have hi (i : Fin n) : (W.encoded (fun m ↦ encode m i)).mutualInformation input =
      (leftSlice W (code.encode₂ m₂ i)).mutualInformation (code.coordinateInput₁ i) := by
    change ((leftSlice W (code.encode₂ m₂ i)).encoded (fun m ↦ code.encode₁ m i)).mutualInformation
      input = _
    rw [FiniteChannel.encoded_mutualInformation]
    rfl
  simp_rw [hi] at hinfo
  exact hfano.trans (by dsimp [channel]; linarith)

/-- Conditional Fano for the first message, averaged over the second message. -/
theorem log_messageCount₁_bound (code : BlockCode W n) :
    (1 - code.averageErrorProbability) * Real.log code.messageCount₁ ≤
      (∑ i, leftInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i)) *
        Real.log 2 + Real.log 2 := by
  let u₂ := FiniteDistribution.uniform (Fin code.messageCount₂)
  have haverage : (∑ m₂, u₂ m₂ * Real.log code.messageCount₁) ≤
      ∑ m₂, u₂ m₂ * ((∑ i,
        (leftSlice W (code.encode₂ m₂ i)).mutualInformation (code.coordinateInput₁ i)) +
          Real.log 2 + (conditionalFirstCode code m₂).averageErrorProbability *
            Real.log code.messageCount₁) := by
    apply Finset.sum_le_sum
    intro m₂ _
    exact mul_le_mul_of_nonneg_left (conditionalFirst_log_bound code m₂) (u₂.nonnegative m₂)
  have hinfo :
      (∑ m₂, u₂ m₂ * ∑ i,
        (leftSlice W (code.encode₂ m₂ i)).mutualInformation (code.coordinateInput₁ i)) =
      (∑ i, leftInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i)) *
        Real.log 2 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [leftInformation, Finset.sum_mul]
    simp_rw [mul_assoc, ← mutualInformation_eq_bits_mul]
    exact (u₂.sum_map_mul (fun m ↦ code.encode₂ m i)
      (fun x₂ ↦ (leftSlice W x₂).mutualInformation (code.coordinateInput₁ i))).symm
  have herror := average_conditionalFirst_error_le code
  have hlog : 0 ≤ Real.log (code.messageCount₁ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast code.messageCount₁_pos)
  have herrormul := mul_le_mul_of_nonneg_right herror hlog
  simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib, ← Finset.sum_mul,
    u₂.sum_probability_eq_one, one_mul] at haverage
  rw [hinfo] at haverage
  change (∑ m₂, u₂ m₂ * (conditionalFirstCode code m₂).averageErrorProbability) *
    Real.log code.messageCount₁ ≤ code.averageErrorProbability * Real.log code.messageCount₁
      at herrormul
  linarith

/-- Conditional Fano for the second message, averaged over the first message. -/
theorem log_messageCount₂_bound (code : BlockCode W n) :
    (1 - code.averageErrorProbability) * Real.log code.messageCount₂ ≤
      (∑ i, rightInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i)) *
        Real.log 2 + Real.log 2 := by
  have bound := code.swap.log_messageCount₁_bound
  rw [averageErrorProbability_swap] at bound
  have h₁ (i : Fin n) : code.swap.coordinateInput₁ i = code.coordinateInput₂ i := rfl
  have h₂ (i : Fin n) : code.swap.coordinateInput₂ i = code.coordinateInput₁ i := rfl
  simp only [leftInformation_swap, h₁, h₂] at bound
  exact bound

/-- Joint Fano retains the same pair of coordinate marginals used in the conditional bounds. -/
theorem log_messageCount_sum_bound (code : BlockCode W n) :
    (1 - code.averageErrorProbability) *
        (Real.log code.messageCount₁ + Real.log code.messageCount₂) ≤
      (∑ i, jointInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i)) *
        Real.log 2 + Real.log 2 := by
  let input := FiniteDistribution.uniform (Fin code.messageCount₁ × Fin code.messageCount₂)
  let channel := (W.block n).encoded code.toOneShotCode.encode
  have hfano := channel.fano_uniform code.decode
  change Real.log (Fintype.card (Fin code.messageCount₁ × Fin code.messageCount₂)) ≤
    channel.mutualInformation input + Real.log 2 + code.averageErrorProbability *
      Real.log (Fintype.card (Fin code.messageCount₁ × Fin code.messageCount₂)) at hfano
  have hcount₁ : (code.messageCount₁ : ℝ) ≠ 0 := by exact_mod_cast code.messageCount₁_pos.ne'
  have hcount₂ : (code.messageCount₂ : ℝ) ≠ 0 := by exact_mod_cast code.messageCount₂_pos.ne'
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Real.log_mul hcount₁ hcount₂] at hfano
  have hinfo := W.encoded_block_mutualInformation_le_sum n code.toOneShotCode.encode input
  have hi (i : Fin n) :
      (W.encoded (fun m ↦ code.toOneShotCode.encode m i)).mutualInformation input =
        jointInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i) * Real.log 2 := by
    rw [FiniteChannel.encoded_mutualInformation, mutualInformation_eq_bits_mul]
    congr 1
    unfold input
    rw [uniform_product]
    unfold jointInformation productInput coordinateInput₁ coordinateInput₂
    congr 1
    exact FiniteDistribution.map_joint_independent
      (FiniteDistribution.uniform (Fin code.messageCount₁))
      (FiniteDistribution.uniform (Fin code.messageCount₂))
      (fun m ↦ code.encode₁ m i) (fun m ↦ code.encode₂ m i)
  simp_rw [hi] at hinfo
  rw [← Finset.sum_mul] at hinfo
  change channel.mutualInformation input ≤ _ at hinfo
  linarith


/-- All three finite-block bounds use a single family of product coordinate laws. -/
theorem rate_bounds (code : BlockCode W n) (hn : 0 < n) :
    (1 - code.averageErrorProbability) * code.rate₁ ≤
      (n : ℝ)⁻¹ * ∑ i, leftInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i) +
        (n : ℝ)⁻¹ ∧
    (1 - code.averageErrorProbability) * code.rate₂ ≤
      (n : ℝ)⁻¹ * ∑ i, rightInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i) +
        (n : ℝ)⁻¹ ∧
    (1 - code.averageErrorProbability) * (code.rate₁ + code.rate₂) ≤
      (n : ℝ)⁻¹ * ∑ i, jointInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i) +
        (n : ℝ)⁻¹ := by
  refine ⟨fano_normalized_log_bound hn code.log_messageCount₁_bound,
    fano_normalized_log_bound hn code.log_messageCount₂_bound, ?_⟩
  simpa only [rate₁, rate₂, add_div] using
    fano_normalized_log_bound hn code.log_messageCount_sum_bound

/-- Positive message counts give nonnegative rates. -/
theorem rates_nonnegative (code : BlockCode W n) : 0 ≤ code.rate₁ ∧ 0 ≤ code.rate₂ := by
  have hdenom : 0 ≤ (n : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (by norm_num))
  exact ⟨div_nonneg (Real.log_nonneg (by exact_mod_cast code.messageCount₁_pos)) hdenom,
    div_nonneg (Real.log_nonneg (by exact_mod_cast code.messageCount₂_pos)) hdenom⟩

end BlockCode

/-- Every achievable rate pair satisfies the single-letter inequalities with finite time sharing. -/
theorem achievableRate_mem_informationRegion (W : FiniteChannel (X₁ × X₂) Y)
    {r : RatePair} (hr : AchievableRate W r) : r ∈ informationRegion W := by
  obtain ⟨hr₁, hr₂, hcodes⟩ := hr
  apply mem_informationRegion_of_approx W r hr₁ hr₂
  intro δ hδ
  let K := r.1 + r.2 + 3
  have hK : 0 < K := by dsimp [K]; linarith
  let ε := min (1 / 2 : ℝ) (δ / (2 * K))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hbudget : ε * (2 * K) ≤ δ :=
    (le_div_iff₀ (by positivity : 0 < 2 * K)).mp (min_le_right _ _)
  obtain ⟨N, hN, hcodesN⟩ := hcodes ε hε
  obtain ⟨n, hnlarge⟩ := exists_nat_gt (max (N : ℝ) (1 / ε))
  have hNn : N ≤ n := by exact_mod_cast (le_max_left (N : ℝ) (1 / ε)).trans hnlarge.le
  have hn : 0 < n := hN.trans_le hNn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hinv : (n : ℝ)⁻¹ < ε := by
    rw [← one_div]
    apply (div_lt_iff₀ hnreal).mpr
    have hlarge : 1 / ε < (n : ℝ) := (le_max_right _ _).trans_lt hnlarge
    have hmul := (div_lt_iff₀ hε).mp hlarge
    nlinarith
  obtain ⟨code, he, hrate₁, hrate₂⟩ := hcodesN n hNn
  obtain ⟨ha, hb, hc⟩ := code.rate_bounds hn
  obtain ⟨hnonneg₁, hnonneg₂⟩ := code.rates_nonnegative
  have hfactor : 0 ≤ 1 - ε := by linarith
  have hscale₁ := mul_le_mul_of_nonneg_left hrate₁ hfactor
  have hscale₂ := mul_le_mul_of_nonneg_left hrate₂ hfactor
  have hscaleSum := mul_le_mul_of_nonneg_left (add_le_add hrate₁ hrate₂) hfactor
  have he₁ := mul_le_mul_of_nonneg_right (sub_le_sub_left he 1) hnonneg₁
  have he₂ := mul_le_mul_of_nonneg_right (sub_le_sub_left he 1) hnonneg₂
  have heSum := mul_le_mul_of_nonneg_right (sub_le_sub_left he 1)
    (add_nonneg hnonneg₁ hnonneg₂)
  have hbound₁ := (hscale₁.trans he₁).trans ha
  have hbound₂ := (hscale₂.trans he₂).trans hb
  have hboundSum := (hscaleSum.trans heSum).trans hc
  have hfinal₁ : r.1 ≤ (n : ℝ)⁻¹ * ∑ i,
      leftInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i) + δ := by
    dsimp [K] at hbudget
    nlinarith [sq_nonneg ε, mul_nonneg hε.le hr₁, mul_nonneg hε.le hr₂]
  have hfinal₂ : r.2 ≤ (n : ℝ)⁻¹ * ∑ i,
      rightInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i) + δ := by
    dsimp [K] at hbudget
    nlinarith [sq_nonneg ε, mul_nonneg hε.le hr₁, mul_nonneg hε.le hr₂]
  have hfinalSum : r.1 + r.2 ≤ (n : ℝ)⁻¹ * ∑ i,
      jointInformation W (code.coordinateInput₁ i) (code.coordinateInput₂ i) + δ := by
    dsimp [K] at hbudget
    nlinarith [sq_nonneg ε, mul_nonneg hε.le hr₁, mul_nonneg hε.le hr₂]
  letI : NeZero n := ⟨hn.ne'⟩
  refine ⟨n, FiniteDistribution.uniform (Fin n), code.coordinateInput₁,
    code.coordinateInput₂, ?_, ?_, ?_⟩
  · simpa only [FiniteDistribution.uniform_apply, Fintype.card_fin, ← Finset.mul_sum]
      using hfinal₁
  · simpa only [FiniteDistribution.uniform_apply, Fintype.card_fin, ← Finset.mul_sum]
      using hfinal₂
  · simpa only [FiniteDistribution.uniform_apply, Fintype.card_fin, ← Finset.mul_sum]
      using hfinalSum

/-- The MAC converse for deterministic independent encoders and average joint error. -/
theorem operationalRegion_subset_informationRegion (W : FiniteChannel (X₁ × X₂) Y) :
    operationalRegion W ⊆ informationRegion W := by
  intro r hr
  exact achievableRate_mem_informationRegion W hr

end CapacityAtlas.MultipleAccess
