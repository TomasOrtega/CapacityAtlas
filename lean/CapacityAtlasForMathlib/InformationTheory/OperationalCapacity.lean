/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.Code
import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Ring

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The memoryless `n`-fold extension of a finite channel. -/
@[capacity_shared_api]
def block (channel : FiniteChannel X Y) (n : ℕ) :
    FiniteChannel (Fin n → X) (Fin n → Y) where
  transition input output := ∏ i, channel.transition (input i) (output i)
  nonnegative input output := Finset.prod_nonneg fun i _ ↦
    channel.nonnegative (input i) (output i)
  row_sum input := by
    rw [← Fintype.prod_sum]
    simp

@[simp, capacity_shared_api]
theorem block_transition (channel : FiniteChannel X Y) (n : ℕ)
    (input : Fin n → X) (output : Fin n → Y) :
    (channel.block n).transition input output =
      ∏ i, channel.transition (input i) (output i) :=
  rfl

/-- A deterministic block code with a positive finite message set. -/
@[capacity_shared_api]
structure BlockCode (channel : FiniteChannel X Y) (blocklength : ℕ) where
  messageCount : ℕ
  messageCount_pos : 0 < messageCount
  encode : Fin messageCount → Fin blocklength → X
  decode : (Fin blocklength → Y) → Fin messageCount

namespace BlockCode

variable {channel : FiniteChannel X Y} {blocklength : ℕ}

/-- The block code with one message, encoded as a constant input word. -/
@[capacity_shared_api]
noncomputable def oneMessage [Nonempty X] (channel : FiniteChannel X Y) (blocklength : ℕ) :
    BlockCode channel blocklength where
  messageCount := 1
  messageCount_pos := by simp
  encode _ _ := Classical.choice inferInstance
  decode _ := 0

@[simp, capacity_shared_api]
theorem oneMessage_messageCount [Nonempty X] (channel : FiniteChannel X Y) (blocklength : ℕ) :
    (oneMessage channel blocklength).messageCount = 1 :=
  rfl

/-- A block code viewed as a one-shot code for the product channel. -/
@[capacity_shared_api]
def toOneShotCode (code : BlockCode channel blocklength) :
    OneShotCode (channel.block blocklength) (Fin code.messageCount) where
  encode := code.encode
  decode := code.decode

/-- Average decoding error under the uniform message distribution. -/
@[capacity_shared_api]
noncomputable def averageErrorProbability (code : BlockCode channel blocklength) : ℝ :=
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  code.toOneShotCode.averageErrorProbability

/-- Code rate in bits per channel use. -/
@[capacity_shared_api]
noncomputable def rate (code : BlockCode channel blocklength) : ℝ :=
  Real.logb 2 code.messageCount / blocklength

@[simp, capacity_shared_api]
theorem oneMessage_averageErrorProbability [Nonempty X]
    (channel : FiniteChannel X Y) (blocklength : ℕ) :
    (oneMessage channel blocklength).averageErrorProbability = 0 := by
  simp [averageErrorProbability, toOneShotCode, OneShotCode.averageErrorProbability,
    OneShotCode.averageSuccessProbability, OneShotCode.successProbability, oneMessage]
  rw [sub_eq_zero]
  symm
  exact (channel.block blocklength).row_sum _

@[simp, capacity_shared_api]
theorem oneMessage_rate [Nonempty X] (channel : FiniteChannel X Y) (blocklength : ℕ) :
    (oneMessage channel blocklength).rate = 0 := by
  simp [rate]

end BlockCode

/-- A rate achievable by deterministic block codes with vanishing average error. -/
@[capacity_shared_api]
def AchievableRate (channel : FiniteChannel X Y) (rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ firstBlocklength : ℕ, 0 < firstBlocklength ∧
    ∀ blocklength, firstBlocklength ≤ blocklength →
      ∃ code : BlockCode channel blocklength,
        code.averageErrorProbability ≤ ε ∧ rate ≤ code.rate

/-- Operational average-error capacity in bits per channel use. -/
@[capacity_shared_api]
noncomputable def operationalCapacityBits (channel : FiniteChannel X Y) : ℝ :=
  sSup {rate | channel.AchievableRate rate}

/-- The finite-channel coding theorem for a particular channel. -/
@[capacity_shared_api]
def SatisfiesCodingTheorem (channel : FiniteChannel X Y) : Prop :=
  channel.operationalCapacityBits = channel.informationCapacityBits

/-- Every nonpositive rate is achievable using a one-message code. -/
@[capacity_shared_api]
theorem achievableRate_of_nonpos [Nonempty X] (channel : FiniteChannel X Y)
    {rate : ℝ} (hrate : rate ≤ 0) : channel.AchievableRate rate := by
  intro ε hε
  refine ⟨1, by simp, ?_⟩
  intro blocklength _
  refine ⟨BlockCode.oneMessage channel blocklength, ?_, ?_⟩
  · simpa using hε.le
  · simpa using hrate

/-- A message count whose associated block-code rate is at least `rate`. -/
@[capacity_shared_api]
noncomputable def messageCountAtRate (rate : ℝ) (blocklength : ℕ) : ℕ :=
  Nat.ceil (Real.exp ((blocklength : ℝ) * rate * Real.log 2))

@[capacity_shared_api]
theorem messageCountAtRate_pos (rate : ℝ) (blocklength : ℕ) :
    0 < messageCountAtRate rate blocklength := by
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

/-- Rounding the exponential message count upward preserves the target rate. -/
@[capacity_shared_api]
theorem targetRate_le_rateOfMessageCountAtRate (rate : ℝ) {blocklength : ℕ}
    (hblocklength : 0 < blocklength) :
    rate ≤ Real.logb 2 (messageCountAtRate rate blocklength : ℝ) / blocklength := by
  have hblocklengthReal : 0 < (blocklength : ℝ) := by exact_mod_cast hblocklength
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil :
      Real.exp ((blocklength : ℝ) * rate * Real.log 2) ≤
        (messageCountAtRate rate blocklength : ℝ) := by
    exact Nat.le_ceil _
  have hlog :
      (blocklength : ℝ) * rate * Real.log 2 ≤
        Real.log (messageCountAtRate rate blocklength : ℝ) := by
    rw [← Real.log_exp ((blocklength : ℝ) * rate * Real.log 2)]
    exact Real.log_le_log (Real.exp_pos _) hceil
  rw [Real.logb, div_div]
  apply (le_div_iff₀ (mul_pos hlogTwo hblocklengthReal)).2
  calc
    rate * (Real.log 2 * (blocklength : ℝ)) =
        (blocklength : ℝ) * rate * Real.log 2 := by ring
    _ ≤ Real.log (messageCountAtRate rate blocklength : ℝ) := hlog

/-- The ceiling of `exp t` costs at most a factor of two when `t` is nonnegative. -/
@[capacity_shared_api]
theorem natCeil_exp_le_two_mul_exp {t : ℝ} (ht : 0 ≤ t) :
    (Nat.ceil (Real.exp t) : ℝ) ≤ 2 * Real.exp t := by
  have hceil : (Nat.ceil (Real.exp t) : ℝ) < Real.exp t + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos t).le
  have hone : 1 ≤ Real.exp t := by simpa using Real.exp_monotone ht
  linarith

/-- The polynomial and exponential terms in the random-coding estimate vanish. -/
@[capacity_shared_api]
theorem randomCodingAsymptoticBound_tendsto_zero (variance δ : ℝ) (hδ : 0 < δ) :
    Filter.Tendsto
      (fun blocklength : ℕ ↦
        ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2) +
          2 * Real.exp (-((blocklength : ℝ) * δ)))
      Filter.atTop
      (nhds 0) := by
  have hfirstBase :
      Filter.Tendsto (fun blocklength : ℕ ↦ (variance / δ ^ 2) / (blocklength : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop (variance / δ ^ 2)
  have hfirst :
      Filter.Tendsto
        (fun blocklength : ℕ ↦
          ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2))
        Filter.atTop (nhds 0) := by
    apply hfirstBase.congr'
    filter_upwards [Filter.eventually_ne_atTop 0] with blocklength hblocklength
    have hblocklengthReal : (blocklength : ℝ) ≠ 0 := by exact_mod_cast hblocklength
    field_simp [hblocklengthReal, hδ.ne']
  have hscaled :
      Filter.Tendsto (fun blocklength : ℕ ↦ (blocklength : ℝ) * δ)
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hδ
  have hexponential :
      Filter.Tendsto (fun blocklength : ℕ ↦ Real.exp (-((blocklength : ℝ) * δ)))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      ((Filter.tendsto_neg_atTop_atBot :
        Filter.Tendsto (fun value : ℝ ↦ -value) Filter.atTop Filter.atBot).comp hscaled)
  simpa using hfirst.add (Filter.Tendsto.const_mul 2 hexponential)

/-- The finite-block estimate needed to derive direct achievability for a fixed input. -/
@[capacity_shared_api]
def HasRandomCodingBound (channel : FiniteChannel X Y) (input : FiniteDistribution X)
    (variance : ℝ) : Prop :=
  ∀ (δ : ℝ) {blocklength messageCount : ℕ}, 0 < blocklength → 0 < messageCount → 0 < δ →
    ∃ code : BlockCode channel blocklength,
      code.messageCount = messageCount ∧
        code.averageErrorProbability ≤
          ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2) +
            (messageCount : ℝ) * Real.exp
              (-((blocklength : ℝ) * channel.mutualInformation input -
                (blocklength : ℝ) * δ))

/-- A finite-block random-coding estimate makes every rate below a fixed input's
mutual information achievable. -/
@[capacity_shared_api]
theorem achievableRate_of_lt_mutualInformationBits_of_randomCodingBound [Nonempty X]
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) (variance : ℝ)
    (randomCoding : HasRandomCodingBound channel input variance)
    {rate : ℝ} (hrate : rate < channel.mutualInformationBits input) :
    channel.AchievableRate rate := by
  by_cases hrateNonpos : rate ≤ 0
  · exact achievableRate_of_nonpos channel hrateNonpos
  have hratePos : 0 < rate := lt_of_not_ge hrateNonpos
  let information := channel.mutualInformation input
  let logTwo := Real.log 2
  let gap := information - rate * logTwo
  let δ := gap / 2
  have hlogTwo : 0 < logTwo := Real.log_pos (by norm_num)
  have hrateNats : rate * logTwo < information := by
    apply (lt_div_iff₀ hlogTwo).mp
    simpa [FiniteChannel.mutualInformationBits, information, logTwo] using hrate
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  intro ε hε
  have hbound := randomCodingAsymptoticBound_tendsto_zero variance δ hδ
  have heventually :
      ∀ᶠ blocklength : ℕ in Filter.atTop,
        ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2) +
            2 * Real.exp (-((blocklength : ℝ) * δ)) < ε :=
    (tendsto_order.1 hbound).2 ε hε
  obtain ⟨firstBound, hfirstBound⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨max 1 firstBound, by omega, ?_⟩
  intro blocklength hblocklength
  have hblocklengthPos : 0 < blocklength := lt_of_lt_of_le (by omega) hblocklength
  let messageCount := messageCountAtRate rate blocklength
  have hmessageCount : 0 < messageCount := messageCountAtRate_pos rate blocklength
  obtain ⟨code, hcodeCount, hcodeError⟩ :=
    randomCoding δ hblocklengthPos hmessageCount hδ
  refine ⟨code, ?_, ?_⟩
  · have hmessageExponent :
        0 ≤ (blocklength : ℝ) * rate * Real.log 2 := by positivity
    have hmessageUpper :
        (messageCount : ℝ) ≤
          2 * Real.exp ((blocklength : ℝ) * rate * Real.log 2) := by
      exact natCeil_exp_le_two_mul_exp hmessageExponent
    have hexponential :
        (messageCount : ℝ) * Real.exp
            (-((blocklength : ℝ) * channel.mutualInformation input -
              (blocklength : ℝ) * δ)) ≤
          2 * Real.exp (-((blocklength : ℝ) * δ)) := by
      calc
        (messageCount : ℝ) * Real.exp
              (-((blocklength : ℝ) * channel.mutualInformation input -
                (blocklength : ℝ) * δ)) ≤
            (2 * Real.exp ((blocklength : ℝ) * rate * Real.log 2)) *
              Real.exp
                (-((blocklength : ℝ) * channel.mutualInformation input -
                  (blocklength : ℝ) * δ)) :=
          mul_le_mul_of_nonneg_right hmessageUpper (Real.exp_pos _).le
        _ = 2 * Real.exp
              ((blocklength : ℝ) * rate * Real.log 2 +
                -((blocklength : ℝ) * channel.mutualInformation input -
                  (blocklength : ℝ) * δ)) := by
          rw [mul_assoc, ← Real.exp_add]
        _ = 2 * Real.exp (-((blocklength : ℝ) * δ)) := by
          congr 2
          dsimp [δ, gap, information, logTwo]
          ring
    have herrorBound :
        ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2) +
            (messageCount : ℝ) * Real.exp
              (-((blocklength : ℝ) * channel.mutualInformation input -
                (blocklength : ℝ) * δ)) ≤
          ((blocklength : ℝ) * variance) / (((blocklength : ℝ) * δ) ^ 2) +
            2 * Real.exp (-((blocklength : ℝ) * δ)) :=
      add_le_add_right hexponential _
    exact hcodeError.trans
      (herrorBound.trans
        (hfirstBound blocklength (le_trans (Nat.le_max_right _ _) hblocklength)).le)
  · rw [BlockCode.rate, hcodeCount]
    exact targetRate_le_rateOfMessageCountAtRate rate hblocklengthPos

/-- Finite-block random-coding bounds for every input distribution. -/
@[capacity_shared_api]
def HasRandomCodingBounds (channel : FiniteChannel X Y) : Prop :=
  ∀ input : FiniteDistribution X,
    ∃ variance : ℝ, HasRandomCodingBound channel input variance

/-- The pointwise random-coding estimates prove direct achievability below information capacity. -/
@[capacity_shared_api]
theorem achievableRate_of_lt_informationCapacityBits_of_randomCodingBounds [Nonempty X]
    (channel : FiniteChannel X Y) (randomCoding : HasRandomCodingBounds channel)
    {rate : ℝ} (hrate : rate < channel.informationCapacityBits) :
    channel.AchievableRate rate := by
  obtain ⟨input, hinput⟩ := channel.exists_input_of_lt_informationCapacityBits hrate
  obtain ⟨variance, hvariance⟩ := randomCoding input
  exact achievableRate_of_lt_mutualInformationBits_of_randomCodingBound
    channel input variance hvariance hinput

/-- The pointwise operational converse for achievable rates. -/
@[capacity_shared_api]
def HasAchievableRateConverse (channel : FiniteChannel X Y) : Prop :=
  ∀ {rate : ℝ}, channel.AchievableRate rate → rate ≤ channel.informationCapacityBits

/-- The converse bounds the supremum of achievable rates by information capacity. -/
@[capacity_shared_api]
theorem operationalCapacityBits_le_informationCapacityBits_of_converse [Nonempty X]
    (channel : FiniteChannel X Y)
    (converse : ∀ {rate : ℝ}, channel.AchievableRate rate →
      rate ≤ channel.informationCapacityBits) :
    channel.operationalCapacityBits ≤ channel.informationCapacityBits := by
  unfold operationalCapacityBits
  apply csSup_le
  · exact ⟨0, achievableRate_of_nonpos channel le_rfl⟩
  · intro rate hrate
    exact converse hrate

/-- Direct achievability and the converse put information capacity below operational capacity. -/
@[capacity_shared_api]
theorem informationCapacityBits_le_operationalCapacityBits_of_direct_converse
    (channel : FiniteChannel X Y)
    (direct : ∀ {rate : ℝ}, rate < channel.informationCapacityBits →
      channel.AchievableRate rate)
    (converse : ∀ {rate : ℝ}, channel.AchievableRate rate →
      rate ≤ channel.informationCapacityBits) :
    channel.informationCapacityBits ≤ channel.operationalCapacityBits := by
  let achievableRates : Set ℝ := {rate | channel.AchievableRate rate}
  have hbounded : BddAbove achievableRates := by
    refine ⟨channel.informationCapacityBits, ?_⟩
    intro rate hrate
    exact converse hrate
  by_contra hcapacity
  have hstrict : channel.operationalCapacityBits < channel.informationCapacityBits :=
    lt_of_not_ge hcapacity
  let rate := (channel.operationalCapacityBits + channel.informationCapacityBits) / 2
  have hop_lt_rate : channel.operationalCapacityBits < rate := by
    dsimp [rate]
    linarith
  have hrate_lt_info : rate < channel.informationCapacityBits := by
    dsimp [rate]
    linarith
  have hrate_le_op : rate ≤ channel.operationalCapacityBits := by
    unfold operationalCapacityBits
    exact le_csSup hbounded (direct hrate_lt_info)
  exact (not_lt_of_ge hrate_le_op) hop_lt_rate

/-- Direct achievability and the converse imply the finite-channel coding theorem. -/
@[capacity_shared_api]
theorem satisfiesCodingTheorem_of_direct_converse [Nonempty X]
    (channel : FiniteChannel X Y)
    (direct : ∀ {rate : ℝ}, rate < channel.informationCapacityBits →
      channel.AchievableRate rate)
    (converse : ∀ {rate : ℝ}, channel.AchievableRate rate →
      rate ≤ channel.informationCapacityBits) :
    channel.SatisfiesCodingTheorem := by
  apply le_antisymm
  · exact operationalCapacityBits_le_informationCapacityBits_of_converse channel converse
  · exact informationCapacityBits_le_operationalCapacityBits_of_direct_converse
      channel direct converse

/-- Random-coding bounds and the pointwise converse imply the finite-channel coding theorem. -/
@[capacity_shared_api]
theorem satisfiesCodingTheorem_of_randomCodingBounds_converse [Nonempty X]
    (channel : FiniteChannel X Y) (randomCoding : HasRandomCodingBounds channel)
    (converse : HasAchievableRateConverse channel) :
    channel.SatisfiesCodingTheorem :=
  satisfiesCodingTheorem_of_direct_converse channel
    (achievableRate_of_lt_informationCapacityBits_of_randomCodingBounds channel randomCoding)
    converse

/-- No positive-blocklength code exists when the input alphabet is empty. -/
@[capacity_shared_api]
theorem not_achievableRate_of_isEmpty [IsEmpty X]
    (channel : FiniteChannel X Y) (rate : ℝ) : ¬channel.AchievableRate rate := by
  intro hrate
  obtain ⟨firstBlocklength, hfirst, hcodes⟩ := hrate 1 zero_lt_one
  obtain ⟨code, _⟩ := hcodes firstBlocklength le_rfl
  exact isEmptyElim
    (code.encode ⟨0, code.messageCount_pos⟩ ⟨0, hfirst⟩)

/-- An empty input alphabet has no achievable rates, hence zero operational capacity. -/
@[capacity_shared_api]
theorem operationalCapacityBits_eq_zero_of_isEmpty [IsEmpty X]
    (channel : FiniteChannel X Y) : channel.operationalCapacityBits = 0 := by
  have hrates : {rate : ℝ | channel.AchievableRate rate} = ∅ := by
    ext rate
    constructor
    · intro hrate
      exact (not_achievableRate_of_isEmpty channel rate hrate).elim
    · intro hfalse
      exact hfalse.elim
  unfold operationalCapacityBits
  rw [hrates, Real.sSup_empty]

/-- The degenerate empty-input channel satisfies the coding theorem. -/
@[capacity_shared_api]
theorem satisfiesCodingTheorem_emptyInput [IsEmpty X]
    (channel : FiniteChannel X Y) : channel.SatisfiesCodingTheorem := by
  rw [SatisfiesCodingTheorem, operationalCapacityBits_eq_zero_of_isEmpty,
    informationCapacityBits_eq_zero_of_isEmpty]

/-- A total finite-channel wrapper, including the degenerate empty-input case. -/
@[capacity_shared_api]
theorem finiteDMCSatisfiesCodingTheorem_of_bounds
    (channel : FiniteChannel X Y) (randomCoding : HasRandomCodingBounds channel)
    (converse : HasAchievableRateConverse channel) :
    channel.SatisfiesCodingTheorem := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI : IsEmpty X := hX
      exact satisfiesCodingTheorem_emptyInput channel
  | inr hX =>
      letI : Nonempty X := hX
      exact satisfiesCodingTheorem_of_randomCodingBounds_converse
        channel randomCoding converse

@[capacity_shared_api]
theorem operationalCapacityBits_eq_of_satisfiesCodingTheorem
    (channel : FiniteChannel X Y) (capacity : ℝ)
    (codingTheorem : channel.SatisfiesCodingTheorem)
    (informationCapacity : channel.informationCapacityBits = capacity) :
    channel.operationalCapacityBits = capacity :=
  codingTheorem.trans informationCapacity

end FiniteChannel

end CapacityAtlas
