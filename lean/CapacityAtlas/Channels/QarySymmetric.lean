/-
Copyright 2026 The Capacity Atlas Authors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import CapacityAtlas.Channels.AdditiveNoise
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

namespace CapacityAtlas.Channel

open CapacityAtlas

private theorem sum_ite_zero (q : ℕ) [NeZero q] (a b : ℝ) :
    (∑ z : ZMod q, if z = 0 then a else b) =
      a + ((q - 1 : ℕ) : ℝ) * b := by
  classical
  have hcard : (Finset.univ.erase (0 : ZMod q)).card = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod q)), Finset.card_univ,
      ZMod.card]
  calc
    (∑ z : ZMod q, if z = 0 then a else b) =
        (∑ z ∈ (Finset.univ.erase (0 : ZMod q)), if z = 0 then a else b) +
          (if (0 : ZMod q) = 0 then a else b) := by
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q))).symm
    _ = a + ((q - 1 : ℕ) : ℝ) * b := by
      rw [show (∑ z ∈ (Finset.univ.erase (0 : ZMod q)), if z = 0 then a else b) =
        ∑ _z ∈ (Finset.univ.erase (0 : ZMod q)), b by
          apply Finset.sum_congr rfl
          intro z hz
          simp [Finset.ne_of_mem_erase hz]]
      rw [Finset.sum_const, hcard]
      simp only [nsmul_eq_mul, if_true]
      ring

/-- The atlas q-ary noise range is contained in the probability interval. -/
theorem qarySymmetric_p_le_one (q : ℕ) (hq : 2 ≤ q) {p : ℝ}
    (hp : p ≤ ((q - 1 : ℕ) : ℝ) / q) : p ≤ 1 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hq)
  have hsuble : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
  exact hp.trans ((div_le_one hqpos).2 hsuble)

/-- The q-ary symmetric noise distribution on the cyclic group with `q` elements. -/
@[capacity_problem "q-ary-symmetric-channel", capacity_definition]
noncomputable def qarySymmetricNoise (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteDistribution (ZMod q) where
  probability z := if z = 0 then 1 - p else p / ((q - 1 : ℕ) : ℝ)
  nonnegative z := by
    have hdpos : (0 : ℝ) < (q - 1 : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) hq)
    split
    · linarith
    · exact div_nonneg hp0 hdpos.le
  sum_probability := by
    change (∑ z : ZMod q,
      if z = 0 then 1 - p else p / ((q - 1 : ℕ) : ℝ)) = 1
    rw [sum_ite_zero]
    have hdpos : (0 : ℝ) < (q - 1 : ℕ) := by
      exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) hq)
    have hd : (((q - 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hdpos
    field_simp [hd]
    ring

/-- The q-ary symmetric channel as additive noise on `ZMod q`. -/
@[capacity_problem "q-ary-symmetric-channel", capacity_definition]
noncomputable def qarySymmetric (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteChannel (ZMod q) (ZMod q) :=
  additiveNoise (qarySymmetricNoise q hq p hp0 hp1)

/-- The additive construction has the q-ary symmetric transition law. -/
@[capacity_problem "q-ary-symmetric-channel", capacity_short_proof]
theorem qarySymmetric_transition (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (input output : ZMod q) :
    (qarySymmetric q hq p hp0 hp1).transition input output =
      if input = output then 1 - p else p / ((q - 1 : ℕ) : ℝ) := by
  change (if -input + output = 0 then 1 - p else p / ((q - 1 : ℕ) : ℝ)) = _
  by_cases h : input = output
  · subst output
    simp
  · have hn : -input + output ≠ 0 := by
      intro hn
      apply h
      calc
        input = input + 0 := (add_zero input).symm
        _ = input + (-input + output) := congrArg (input + ·) hn.symm
        _ = output := by rw [← add_assoc, add_neg_cancel, zero_add]
    simp [h, hn]

/-- Entropy of q-ary symmetric noise in nats. -/
theorem qarySymmetricNoise_entropy (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (qarySymmetricNoise q hq p hp0 hp1).entropy =
      Real.binEntropy p + p * Real.log ((q - 1 : ℕ) : ℝ) := by
  unfold FiniteDistribution.entropy
  change (∑ z : ZMod q, Real.negMulLog
    (if z = 0 then 1 - p else p / ((q - 1 : ℕ) : ℝ))) = _
  simp_rw [apply_ite]
  rw [sum_ite_zero]
  have hdpos : (0 : ℝ) < (q - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) hq)
  have hd : (((q - 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hdpos
  have hscaled :
      ((q - 1 : ℕ) : ℝ) * Real.negMulLog (p / ((q - 1 : ℕ) : ℝ)) =
        Real.negMulLog p + p * Real.log ((q - 1 : ℕ) : ℝ) := by
    by_cases hpzero : p = 0
    · simp [hpzero]
    · unfold Real.negMulLog
      rw [Real.log_div hpzero hd]
      field_simp [hd]
      ring
  rw [hscaled, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- The single-letter information capacity of the q-ary symmetric channel. -/
@[capacity_problem "q-ary-symmetric-channel", capacity_statement]
theorem qarySymmetric_informationCapacity (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (qarySymmetric q hq p hp0 hp1).informationCapacityBits =
      Real.log q / Real.log 2 - Real.binEntropy p / Real.log 2 -
        p * Real.log ((q - 1 : ℕ) : ℝ) / Real.log 2 := by
  rw [qarySymmetric, additiveNoise_informationCapacity, ZMod.card,
    FiniteDistribution.entropyBits, qarySymmetricNoise_entropy]
  ring

/-- The operational q-ary symmetric capacity claim on the atlas parameter range. -/
@[capacity_problem "q-ary-symmetric-channel", capacity_statement]
def qarySymmetricCapacityStatement (q : ℕ) (hq : 2 ≤ q) (p : ℝ) (hp0 : 0 ≤ p)
    (hpMax : p ≤ ((q - 1 : ℕ) : ℝ) / q) : Prop :=
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hq)⟩
  let hp1 := qarySymmetric_p_le_one q hq hpMax
  (qarySymmetric q hq p hp0 hp1).operationalCapacityBits =
    Real.log q / Real.log 2 - Real.binEntropy p / Real.log 2 -
      p * Real.log ((q - 1 : ℕ) : ℝ) / Real.log 2

/-- The operational average-error capacity of the q-ary symmetric channel. -/
@[capacity_problem "q-ary-symmetric-channel", capacity_short_proof]
theorem qarySymmetric_operationalCapacity (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (qarySymmetric q hq p hp0 hp1).operationalCapacityBits =
      Real.log q / Real.log 2 - Real.binEntropy p / Real.log 2 -
        p * Real.log ((q - 1 : ℕ) : ℝ) / Real.log 2 := by
  calc
    (qarySymmetric q hq p hp0 hp1).operationalCapacityBits =
        (qarySymmetric q hq p hp0 hp1).informationCapacityBits :=
      FiniteChannel.codingTheorem (qarySymmetric q hq p hp0 hp1)
    _ = Real.log q / Real.log 2 - Real.binEntropy p / Real.log 2 -
        p * Real.log ((q - 1 : ℕ) : ℝ) / Real.log 2 :=
      qarySymmetric_informationCapacity q hq p hp0 hp1

/-- The registered q-ary symmetric capacity proposition holds unconditionally. -/
@[capacity_problem "q-ary-symmetric-channel", capacity_short_proof]
theorem qarySymmetricCapacityStatement_proof
    (q : ℕ) (hq : 2 ≤ q) (p : ℝ) (hp0 : 0 ≤ p)
    (hpMax : p ≤ ((q - 1 : ℕ) : ℝ) / q) :
    qarySymmetricCapacityStatement q hq p hp0 hpMax := by
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hq)⟩
  unfold qarySymmetricCapacityStatement
  exact qarySymmetric_operationalCapacity q hq p hp0
    (qarySymmetric_p_le_one q hq hpMax)

end CapacityAtlas.Channel
