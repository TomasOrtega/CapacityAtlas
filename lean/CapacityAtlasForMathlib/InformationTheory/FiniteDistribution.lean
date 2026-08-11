/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasUtil.Metadata
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

open scoped BigOperators

namespace CapacityAtlas

/-- A real-valued probability distribution on a finite type. -/
@[capacity_shared_api]
structure FiniteDistribution (X : Type*) [Fintype X] where
  probability : X → ℝ
  nonnegative : ∀ x, 0 ≤ probability x
  sum_probability : ∑ x, probability x = 1

namespace FiniteDistribution

variable {X Y : Type*} [Fintype X] [Fintype Y]

instance : FunLike (FiniteDistribution X) X ℝ where
  coe distribution := distribution.probability
  coe_injective left right h := by
    cases left
    cases right
    simp_all

@[ext, capacity_shared_api]
theorem ext {left right : FiniteDistribution X}
    (h : ∀ x, left x = right x) : left = right :=
  DFunLike.ext left right h

@[simp, capacity_shared_api]
theorem probability_nonnegative (distribution : FiniteDistribution X) (x : X) :
    0 ≤ distribution x :=
  distribution.nonnegative x

@[simp, capacity_shared_api]
theorem sum_probability_eq_one (distribution : FiniteDistribution X) :
    ∑ x, distribution x = 1 :=
  distribution.sum_probability

@[capacity_shared_api]
theorem probability_le_one (distribution : FiniteDistribution X) (x : X) :
    distribution x ≤ 1 := by
  rw [← distribution.sum_probability]
  exact Finset.single_le_sum (fun y _ ↦ distribution.nonnegative y) (Finset.mem_univ x)

/-- The carrier of a finite probability distribution is nonempty. -/
@[capacity_shared_api]
theorem nonempty (distribution : FiniteDistribution X) : Nonempty X := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI : IsEmpty X := hX
      have hsum := distribution.sum_probability
      simp at hsum
  | inr hX => exact hX

/-- The entropy of a finite distribution, measured in nats. -/
@[capacity_shared_api]
noncomputable def entropy (distribution : FiniteDistribution X) : ℝ :=
  ∑ x, Real.negMulLog (distribution x)

/-- The entropy of a finite distribution, measured in bits. -/
@[capacity_shared_api]
noncomputable def entropyBits (distribution : FiniteDistribution X) : ℝ :=
  distribution.entropy / Real.log 2

/-- Push a finite distribution forward along a function. -/
@[capacity_shared_api]
noncomputable def map [DecidableEq Y] (distribution : FiniteDistribution X) (f : X → Y) :
    FiniteDistribution Y where
  probability y := ∑ x with f x = y, distribution x
  nonnegative y := Finset.sum_nonneg fun _ _ ↦ distribution.nonnegative _
  sum_probability := by
    rw [Finset.sum_fiberwise]
    exact distribution.sum_probability

/-- The uniform distribution on a nonempty finite type. -/
@[capacity_shared_api]
noncomputable def uniform (X : Type*) [Fintype X] [Nonempty X] : FiniteDistribution X where
  probability _ := (Fintype.card X : ℝ)⁻¹
  nonnegative _ := by positivity
  sum_probability := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

@[simp, capacity_shared_api]
theorem uniform_apply (X : Type*) [Fintype X] [Nonempty X] (x : X) :
    uniform X x = (Fintype.card X : ℝ)⁻¹ :=
  rfl

/-- A Bernoulli distribution on `Bool`, with `true` having probability `q`. -/
@[capacity_shared_api]
def bernoulli (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : FiniteDistribution Bool where
  probability
    | false => 1 - q
    | true => q
  nonnegative x := by
    cases x <;> simp <;> linarith
  sum_probability := by
    simp

@[simp, capacity_shared_api]
theorem bernoulli_false (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    bernoulli q hq0 hq1 false = 1 - q :=
  rfl

@[simp, capacity_shared_api]
theorem bernoulli_true (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    bernoulli q hq0 hq1 true = q :=
  rfl

@[capacity_shared_api]
theorem bool_probability_false (distribution : FiniteDistribution Bool) :
    distribution false = 1 - distribution true := by
  change distribution.probability false = 1 - distribution.probability true
  have h := distribution.sum_probability
  simp only [Fintype.sum_bool] at h
  linarith

@[capacity_shared_api]
theorem eq_bernoulli (distribution : FiniteDistribution Bool) :
    distribution = bernoulli (distribution true) (distribution.nonnegative true)
      (distribution.probability_le_one true) := by
  ext x
  cases x
  · exact distribution.bool_probability_false
  · rfl

@[capacity_shared_api]
theorem entropy_bernoulli (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (bernoulli q hq0 hq1).entropy = Real.binEntropy q := by
  simp [entropy, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

@[capacity_shared_api]
theorem entropyBits_bernoulli (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (bernoulli q hq0 hq1).entropyBits = Real.binEntropy q / Real.log 2 := by
  rw [entropyBits, entropy_bernoulli]

end FiniteDistribution

end CapacityAtlas
