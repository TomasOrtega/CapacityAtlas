/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.InformationDensity

open scoped BigOperators

namespace CapacityAtlas

namespace FiniteDistribution

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Finite Gibbs inequality for two normalized nonnegative mass functions. -/
@[capacity_shared_api]
theorem sum_mul_log_div_nonnegative
    (p q : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpSum : ∑ a, p a = 1) (hqSum : ∑ a, q a = 1)
    (hsupport : ∀ a, p a ≠ 0 → q a ≠ 0) :
    0 ≤ ∑ a, p a * Real.log (p a / q a) := by
  have hpoint (a : A) : p a - q a ≤ p a * Real.log (p a / q a) := by
    by_cases hpZero : p a = 0
    · simp [hpZero, hq a]
    have hpPos : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm hpZero)
    have hqNe : q a ≠ 0 := hsupport a hpZero
    have hqPos : 0 < q a := lt_of_le_of_ne (hq a) (Ne.symm hqNe)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hqPos hpPos)
    have hscaled := mul_le_mul_of_nonneg_left hlog hpPos.le
    have hratio : p a * (q a / p a - 1) = q a - p a := by
      field_simp [hpZero]
    rw [hratio] at hscaled
    have hswap : Real.log (p a / q a) = -Real.log (q a / p a) := by
      rw [Real.log_div hpZero hqNe, Real.log_div hqNe hpZero]
      ring
    rw [hswap]
    linarith
  calc
    0 = ∑ a, (p a - q a) := by rw [Finset.sum_sub_distrib, hpSum, hqSum]; ring
    _ ≤ ∑ a, p a * Real.log (p a / q a) :=
      Finset.sum_le_sum fun a _ ↦ hpoint a

/-- Entropy of a finite probability distribution is nonnegative. -/
@[capacity_shared_api]
theorem entropy_nonnegative (distribution : FiniteDistribution A) :
    0 ≤ distribution.entropy := by
  unfold entropy
  exact Finset.sum_nonneg fun a _ ↦
    Real.negMulLog_nonneg (distribution.nonnegative a) (distribution.probability_le_one a)

@[capacity_shared_api]
theorem entropy_eq_neg_sum_mul_log (distribution : FiniteDistribution A) :
    distribution.entropy = -(∑ a, distribution a * Real.log (distribution a)) := by
  unfold entropy
  simp only [Real.negMulLog_def]
  rw [← Finset.sum_neg_distrib]
  apply Fintype.sum_congr
  intro a
  ring

/-- A finite distribution has entropy at most the logarithm of its alphabet size. -/
@[capacity_shared_api]
theorem entropy_le_log_card [Nonempty A] (distribution : FiniteDistribution A) :
    distribution.entropy ≤ Real.log (Fintype.card A) := by
  let card : ℝ := Fintype.card A
  have hcard : 0 < card := by
    dsimp [card]
    exact_mod_cast Fintype.card_pos
  let uniformMass : A → ℝ := fun _ ↦ card⁻¹
  have huniformNonnegative : ∀ a, 0 ≤ uniformMass a := fun _ ↦ by
    dsimp [uniformMass]
    positivity
  have huniformSum : ∑ a, uniformMass a = 1 := by
    simp only [uniformMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp [card]
    field_simp
  have hkl := sum_mul_log_div_nonnegative distribution uniformMass
    distribution.nonnegative huniformNonnegative distribution.sum_probability huniformSum
    (fun _ _ ↦ by dsimp [uniformMass]; positivity)
  have hidentity :
      (∑ a, distribution a * Real.log (distribution a / uniformMass a)) =
        Real.log card - distribution.entropy := by
    calc
      ∑ a, distribution a * Real.log (distribution a / uniformMass a) =
          ∑ a, (distribution a * Real.log (distribution a) +
            distribution a * Real.log card) := by
        apply Fintype.sum_congr
        intro a
        by_cases ha : distribution a = 0
        · simp [ha]
        · have huniformNe : uniformMass a ≠ 0 := by
            dsimp [uniformMass]
            positivity
          rw [Real.log_div ha huniformNe]
          have hlogUniform : Real.log (uniformMass a) = -Real.log card := by
            dsimp [uniformMass]
            exact Real.log_inv card
          rw [hlogUniform]
          ring
      _ = Real.log card - distribution.entropy := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul,
          show (∑ a, distribution a) = 1 from distribution.sum_probability]
        unfold entropy
        simp only [Real.negMulLog_def]
        have hneg :
            (∑ a, -distribution a * Real.log (distribution a)) =
              -(∑ a, distribution a * Real.log (distribution a)) := by
          rw [← Finset.sum_neg_distrib]
          apply Fintype.sum_congr
          intro a
          ring
        rw [hneg]
        ring
  rw [hidentity] at hkl
  dsimp [card] at hkl ⊢
  linarith

/-- The uniform distribution has entropy equal to the logarithm of the alphabet size. -/
@[capacity_shared_api]
theorem entropy_uniform (A : Type*) [Fintype A] [Nonempty A] :
    (uniform A).entropy = Real.log (Fintype.card A) := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change (∑ _a : A, Real.negMulLog ((Fintype.card A : ℝ)⁻¹)) = _
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold Real.negMulLog
  rw [Real.log_inv]
  field_simp

/-- Entropy bound for a nonnegative finite mass function of arbitrary total mass. -/
@[capacity_shared_api]
theorem sum_negMulLog_le_negMulLog_sum_add_mul_log_card [Nonempty A]
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a) :
    (∑ a, Real.negMulLog (weight a)) ≤
      Real.negMulLog (∑ a, weight a) +
        (∑ a, weight a) * Real.log (Fintype.card A) := by
  let total := ∑ a, weight a
  have htotal : 0 ≤ total := Finset.sum_nonneg fun a _ ↦ hweight a
  by_cases htotalZero : total = 0
  · have hweightZero (a : A) : weight a = 0 := by
      apply le_antisymm
      · calc
          weight a ≤ ∑ other, weight other :=
            Finset.single_le_sum (fun other _ ↦ hweight other) (Finset.mem_univ a)
          _ = 0 := htotalZero
      · exact hweight a
    simp [hweightZero]
  have htotalPositive : 0 < total := lt_of_le_of_ne htotal (Ne.symm htotalZero)
  let normalized : FiniteDistribution A :=
    { probability := fun a ↦ weight a / total
      nonnegative := fun a ↦ div_nonneg (hweight a) htotal
      sum_probability := by
        rw [← Finset.sum_div, show (∑ a, weight a) = total by rfl]
        exact div_self htotalZero }
  have hdecomposition :
      (∑ a, Real.negMulLog (weight a)) =
        Real.negMulLog total + total * normalized.entropy := by
    calc
      ∑ a, Real.negMulLog (weight a) =
          ∑ a, Real.negMulLog (total * normalized a) := by
        apply Fintype.sum_congr
        intro a
        congr 1
        change weight a = total * (weight a / total)
        field_simp
      _ = ∑ a, (normalized a * Real.negMulLog total +
          total * Real.negMulLog (normalized a)) := by
        apply Fintype.sum_congr
        intro a
        exact Real.negMulLog_mul total (normalized a)
      _ = Real.negMulLog total + total * normalized.entropy := by
        have hnormalizedSum : ∑ a, normalized a = 1 := normalized.sum_probability
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hnormalizedSum,
          one_mul, ← Finset.mul_sum]
        rfl
  rw [hdecomposition]
  change Real.negMulLog total + total * normalized.entropy ≤
    Real.negMulLog total + total * Real.log (Fintype.card A)
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left normalized.entropy_le_log_card htotal) _

/-- Finite expectation is preserved by pushing a distribution forward. -/
@[capacity_shared_api]
theorem sum_map_mul [DecidableEq B] (distribution : FiniteDistribution A)
    (mapFunction : A → B) (observable : B → ℝ) :
    ∑ b, distribution.map mapFunction b * observable b =
      ∑ a, distribution a * observable (mapFunction a) := by
  change (∑ b, (∑ a with mapFunction a = b, distribution a) * observable b) = _
  simp_rw [Finset.sum_mul]
  calc
    ∑ b, ∑ a with mapFunction a = b, distribution a * observable b =
        ∑ b, ∑ a with mapFunction a = b,
          distribution a * observable (mapFunction a) := by
      apply Fintype.sum_congr
      intro b
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a, distribution a * observable (mapFunction a) := by
      rw [Finset.sum_fiberwise]

/-- A pushforward fiber contains the mass of each point mapped into it. -/
@[capacity_shared_api]
theorem le_map_apply [DecidableEq B] (distribution : FiniteDistribution A)
    (mapFunction : A → B) (a : A) :
    distribution a ≤ distribution.map mapFunction (mapFunction a) := by
  unfold map
  change distribution a ≤ ∑ other with mapFunction other = mapFunction a, distribution other
  exact Finset.single_le_sum (fun other _ ↦ distribution.nonnegative other) (by simp)

/-- Consecutive pushforwards agree with pushforward along the composite map. -/
@[simp, capacity_shared_api]
theorem map_map {C : Type*} [Fintype C] [DecidableEq B] [DecidableEq C]
    (distribution : FiniteDistribution A) (first : A → B) (second : B → C) :
    (distribution.map first).map second = distribution.map (second ∘ first) := by
  ext c
  change (∑ b with second b = c, distribution.map first b) =
    ∑ a with second (first a) = c, distribution a
  rw [Finset.sum_filter, Finset.sum_filter]
  simpa only [mul_ite, mul_one, mul_zero] using
    distribution.sum_map_mul first (fun b ↦ if second b = c then 1 else 0)

private theorem negMulLog_sum_le_sum_negMulLog
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a) (set : Finset A) :
    Real.negMulLog (∑ a ∈ set, weight a) ≤ ∑ a ∈ set, Real.negMulLog (weight a) := by
  classical
  let total := ∑ a ∈ set, weight a
  have htotal : 0 ≤ total := Finset.sum_nonneg fun a ha ↦ hweight a
  by_cases htotalZero : total = 0
  · have hweightZero {a : A} (ha : a ∈ set) : weight a = 0 := by
      apply le_antisymm
      · calc
          weight a ≤ ∑ other ∈ set, weight other := by
            exact Finset.single_le_sum (fun other hother ↦ hweight other) ha
          _ = 0 := htotalZero
      · exact hweight a
    simp only [show (∑ a ∈ set, weight a) = 0 from htotalZero, Real.negMulLog_zero]
    exact Finset.sum_nonneg fun a ha ↦ by simp [hweightZero ha]
  · have htotalPositive : 0 < total := lt_of_le_of_ne htotal (Ne.symm htotalZero)
    let normalized : FiniteDistribution A :=
      { probability := fun a ↦ if a ∈ set then weight a / total else 0
        nonnegative := fun a ↦ by
          split_ifs
          · exact div_nonneg (hweight a) htotal
          · exact le_rfl
        sum_probability := by
          change (∑ a, if a ∈ set then weight a / total else 0) = 1
          rw [← Finset.sum_filter, ← Finset.sum_div]
          have hfiltered : (∑ i with i ∈ set, weight i) = total := by
            rw [show Finset.univ.filter (fun i ↦ i ∈ set) = set by ext; simp]
          rw [hfiltered]
          exact div_self htotalZero }
    have hnormalizedSet : ∑ a ∈ set, normalized a = 1 := by
      rw [← normalized.sum_probability]
      change (∑ a ∈ set, if a ∈ set then weight a / total else 0) =
        ∑ a, if a ∈ set then weight a / total else 0
      simp
    have hnormalizedEntropy :
        ∑ a ∈ set, Real.negMulLog (normalized a) = normalized.entropy := by
      unfold entropy
      calc
        ∑ a ∈ set, Real.negMulLog (normalized a) =
            ∑ a ∈ set, Real.negMulLog (weight a / total) := by
          apply Finset.sum_congr rfl
          intro a ha
          change Real.negMulLog (if a ∈ set then weight a / total else 0) = _
          simp [ha]
        _ = ∑ a, if a ∈ set then Real.negMulLog (weight a / total) else 0 := by
          rw [← Finset.sum_filter]
          rw [show Finset.univ.filter (fun a ↦ a ∈ set) = set by ext; simp]
        _ = ∑ a, Real.negMulLog (normalized a) := by
          apply Fintype.sum_congr
          intro a
          change (if a ∈ set then Real.negMulLog (weight a / total) else 0) =
            Real.negMulLog (if a ∈ set then weight a / total else 0)
          split_ifs <;> simp
    have hdecomposition :
        (∑ a ∈ set, Real.negMulLog (weight a)) =
          Real.negMulLog total + total * normalized.entropy := by
      calc
        ∑ a ∈ set, Real.negMulLog (weight a) =
            ∑ a ∈ set, Real.negMulLog (total * normalized a) := by
          apply Finset.sum_congr rfl
          intro a ha
          congr 1
          change weight a = total * (if a ∈ set then weight a / total else 0)
          simp only [ha, if_true]
          field_simp
        _ = ∑ a ∈ set, (normalized a * Real.negMulLog total +
            total * Real.negMulLog (normalized a)) := by
          apply Finset.sum_congr rfl
          intro a _
          exact Real.negMulLog_mul total (normalized a)
        _ = Real.negMulLog total + total * normalized.entropy := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hnormalizedSet,
            one_mul, ← Finset.mul_sum, hnormalizedEntropy]
    rw [hdecomposition]
    exact le_add_of_nonneg_right (mul_nonneg htotal normalized.entropy_nonnegative)

/-- A deterministic observation cannot have more entropy than its source. -/
@[capacity_shared_api]
theorem entropy_map_le [DecidableEq B] (distribution : FiniteDistribution A)
    (mapFunction : A → B) :
    (distribution.map mapFunction).entropy ≤ distribution.entropy := by
  unfold entropy map
  calc
    ∑ b, Real.negMulLog (∑ a with mapFunction a = b, distribution a) ≤
        ∑ b, ∑ a with mapFunction a = b, Real.negMulLog (distribution a) := by
      apply Finset.sum_le_sum
      intro b _
      simpa only [Finset.sum_filter] using
        negMulLog_sum_le_sum_negMulLog distribution distribution.nonnegative
          (Finset.univ.filter fun a ↦ mapFunction a = b)
    _ = ∑ a, Real.negMulLog (distribution a) := by
      rw [Finset.sum_fiberwise]

private theorem sum_prod_fiber_snd {C : Type*} [Fintype C] [DecidableEq C]
    (mass : A × C → ℝ) (c : C) :
    (∑ a, mass (a, c)) = ∑ pair with pair.2 = c, mass pair := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp

/-- Strong subadditivity of entropy for three finite random variables. -/
@[capacity_shared_api]
theorem entropy_strong_subadditivity {C : Type*} [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (distribution : FiniteDistribution (A × (B × C))) :
    distribution.entropy + (distribution.map fun x ↦ x.2.2).entropy ≤
      (distribution.map fun x ↦ (x.1, x.2.2)).entropy +
        (distribution.map fun x ↦ (x.2.1, x.2.2)).entropy := by
  let acMap : A × (B × C) → A × C := fun x ↦ (x.1, x.2.2)
  let bcMap : A × (B × C) → B × C := fun x ↦ (x.2.1, x.2.2)
  let cMap : A × (B × C) → C := fun x ↦ x.2.2
  let ac := distribution.map acMap
  let bc := distribution.map bcMap
  let cDistribution := distribution.map cMap
  have hacMap : ac.map Prod.snd = cDistribution := by
    calc
      ac.map Prod.snd = distribution.map (Prod.snd ∘ acMap) :=
        distribution.map_map acMap Prod.snd
      _ = cDistribution := by rfl
  have hbcMap : bc.map Prod.snd = cDistribution := by
    calc
      bc.map Prod.snd = distribution.map (Prod.snd ∘ bcMap) :=
        distribution.map_map bcMap Prod.snd
      _ = cDistribution := by rfl
  have hacSum (c : C) : ∑ a, ac (a, c) = cDistribution c := by
    calc
      ∑ a, ac (a, c) = ∑ pair with pair.2 = c, ac pair :=
        sum_prod_fiber_snd ac c
      _ = ac.map Prod.snd c := rfl
      _ = cDistribution c := by rw [hacMap]
  have hbcSum (c : C) : ∑ b, bc (b, c) = cDistribution c := by
    calc
      ∑ b, bc (b, c) = ∑ pair with pair.2 = c, bc pair :=
        sum_prod_fiber_snd bc c
      _ = bc.map Prod.snd c := rfl
      _ = cDistribution c := by rw [hbcMap]
  let productMass : A × (B × C) → ℝ := fun x ↦
    if cDistribution x.2.2 = 0 then 0
    else ac (x.1, x.2.2) * bc (x.2.1, x.2.2) / cDistribution x.2.2
  have hproductNonnegative : ∀ x, 0 ≤ productMass x := by
    intro x
    dsimp [productMass]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (ac.nonnegative _) (bc.nonnegative _))
        (cDistribution.nonnegative _)
  have hproductSum : ∑ x, productMass x = 1 := by
    calc
      ∑ x : A × (B × C), productMass x =
          ∑ a : A, ∑ b : B, ∑ c : C, productMass (a, (b, c)) := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
      _ = ∑ a : A, ∑ c : C, ∑ b : B, productMass (a, (b, c)) := by
        apply Fintype.sum_congr
        intro a
        rw [Finset.sum_comm]
      _ = ∑ c : C, ∑ a : A, ∑ b : B, productMass (a, (b, c)) := by
        rw [Finset.sum_comm]
      _ = ∑ c : C, cDistribution c := by
        apply Fintype.sum_congr
        intro c
        by_cases hc : cDistribution c = 0
        · simp [productMass, hc]
        · calc
            ∑ a : A, ∑ b : B, productMass (a, (b, c)) =
                ∑ a : A, ∑ b : B,
                  ac (a, c) * bc (b, c) / cDistribution c := by
              simp only [productMass, hc, if_false]
            _ = ∑ a : A,
                ac (a, c) * (∑ b : B, bc (b, c)) / cDistribution c := by
              apply Fintype.sum_congr
              intro a
              rw [← Finset.sum_div, ← Finset.mul_sum]
            _ = (∑ a : A, ac (a, c)) * (∑ b : B, bc (b, c)) /
                cDistribution c := by
              rw [← Finset.sum_div, ← Finset.sum_mul]
            _ = cDistribution c * cDistribution c / cDistribution c := by
              rw [hacSum, hbcSum]
            _ = cDistribution c := by field_simp
      _ = 1 := cDistribution.sum_probability
  have hacPositive {x : A × (B × C)} (hx : distribution x ≠ 0) :
      0 < ac (x.1, x.2.2) := by
    have hxPositive : 0 < distribution x :=
      lt_of_le_of_ne (distribution.nonnegative x) (Ne.symm hx)
    exact hxPositive.trans_le (distribution.le_map_apply acMap x)
  have hbcPositive {x : A × (B × C)} (hx : distribution x ≠ 0) :
      0 < bc (x.2.1, x.2.2) := by
    have hxPositive : 0 < distribution x :=
      lt_of_le_of_ne (distribution.nonnegative x) (Ne.symm hx)
    exact hxPositive.trans_le (distribution.le_map_apply bcMap x)
  have hcPositive {x : A × (B × C)} (hx : distribution x ≠ 0) :
      0 < cDistribution x.2.2 := by
    have hxPositive : 0 < distribution x :=
      lt_of_le_of_ne (distribution.nonnegative x) (Ne.symm hx)
    exact hxPositive.trans_le (distribution.le_map_apply cMap x)
  have hsupport : ∀ x, distribution x ≠ 0 → productMass x ≠ 0 := by
    intro x hx
    have hac := hacPositive hx
    have hbc := hbcPositive hx
    have hc := hcPositive hx
    dsimp [productMass]
    rw [if_neg hc.ne']
    exact (div_pos (mul_pos hac hbc) hc).ne'
  have hkl := sum_mul_log_div_nonnegative distribution productMass
    distribution.nonnegative hproductNonnegative distribution.sum_probability hproductSum hsupport
  have hpoint (x : A × (B × C)) :
      distribution x * Real.log (distribution x / productMass x) =
        ((distribution x * Real.log (distribution x) +
          distribution x * Real.log (cDistribution x.2.2)) -
          distribution x * Real.log (ac (x.1, x.2.2))) -
          distribution x * Real.log (bc (x.2.1, x.2.2)) := by
    by_cases hx : distribution x = 0
    · simp [hx]
    have hac := hacPositive hx
    have hbc := hbcPositive hx
    have hc := hcPositive hx
    have hproduct : productMass x ≠ 0 := hsupport x hx
    have hproductFormula : productMass x =
        ac (x.1, x.2.2) * bc (x.2.1, x.2.2) / cDistribution x.2.2 := by
      simp [productMass, hc.ne']
    rw [Real.log_div hx hproduct, hproductFormula,
      Real.log_div (mul_ne_zero hac.ne' hbc.ne') hc.ne',
      Real.log_mul hac.ne' hbc.ne']
    ring
  have hacExpectation :
      (∑ x : A × (B × C),
        distribution x * Real.log (ac (x.1, x.2.2))) =
        ∑ pair : A × C, ac pair * Real.log (ac pair) := by
    simpa [acMap, ac] using
      (distribution.sum_map_mul acMap (fun pair ↦ Real.log (ac pair))).symm
  have hbcExpectation :
      (∑ x : A × (B × C),
        distribution x * Real.log (bc (x.2.1, x.2.2))) =
        ∑ pair : B × C, bc pair * Real.log (bc pair) := by
    simpa [bcMap, bc] using
      (distribution.sum_map_mul bcMap (fun pair ↦ Real.log (bc pair))).symm
  have hcExpectation :
      (∑ x : A × (B × C),
        distribution x * Real.log (cDistribution x.2.2)) =
        ∑ c : C, cDistribution c * Real.log (cDistribution c) := by
    simpa [cMap, cDistribution] using
      (distribution.sum_map_mul cMap (fun c ↦ Real.log (cDistribution c))).symm
  have hidentity :
      (∑ x : A × (B × C),
        distribution x * Real.log (distribution x / productMass x)) =
        -distribution.entropy - cDistribution.entropy + ac.entropy + bc.entropy := by
    calc
      ∑ x : A × (B × C),
          distribution x * Real.log (distribution x / productMass x) =
          ∑ x : A × (B × C),
            (((distribution x * Real.log (distribution x) +
              distribution x * Real.log (cDistribution x.2.2)) -
              distribution x * Real.log (ac (x.1, x.2.2))) -
              distribution x * Real.log (bc (x.2.1, x.2.2))) := by
        apply Fintype.sum_congr
        exact hpoint
      _ = ( ∑ x : A × (B × C), distribution x * Real.log (distribution x)) +
          (∑ x : A × (B × C),
            distribution x * Real.log (cDistribution x.2.2)) -
          (∑ x : A × (B × C),
            distribution x * Real.log (ac (x.1, x.2.2))) -
          (∑ x : A × (B × C),
            distribution x * Real.log (bc (x.2.1, x.2.2))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = -distribution.entropy - cDistribution.entropy + ac.entropy + bc.entropy := by
        rw [hacExpectation, hbcExpectation, hcExpectation,
          distribution.entropy_eq_neg_sum_mul_log,
          cDistribution.entropy_eq_neg_sum_mul_log,
          ac.entropy_eq_neg_sum_mul_log, bc.entropy_eq_neg_sum_mul_log]
        ring
  rw [hidentity] at hkl
  simpa [ac, bc, cDistribution, acMap, bcMap, cMap] using
    (show distribution.entropy + cDistribution.entropy ≤ ac.entropy + bc.entropy by linarith)

/-- Strong subadditivity for three deterministic observations of a common source. -/
@[capacity_shared_api]
theorem entropy_map_strong_subadditivity {X C : Type*} [Fintype X] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (distribution : FiniteDistribution X) (first : X → A) (second : X → B)
    (third : X → C) :
    (distribution.map fun x ↦ (first x, (second x, third x))).entropy +
        (distribution.map third).entropy ≤
      (distribution.map fun x ↦ (first x, third x)).entropy +
        (distribution.map fun x ↦ (second x, third x)).entropy := by
  let joint := distribution.map fun x ↦ (first x, (second x, third x))
  simpa [joint, Function.comp_def] using
    joint.entropy_strong_subadditivity

/-- The marginal distribution of one coordinate of a finite random vector. -/
@[capacity_shared_api]
noncomputable def coordinateMarginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (distribution : FiniteDistribution (ι → A)) (coordinate : ι) :
    FiniteDistribution A := by
  classical
  exact distribution.map (fun word ↦ word coordinate)

/-- Entropy of a finite random vector is at most the sum of its marginal entropies. -/
@[capacity_shared_api]
theorem entropy_pi_le_sum_coordinateEntropy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (distribution : FiniteDistribution (ι → A)) :
    distribution.entropy ≤
      ∑ coordinate : ι, (distribution.coordinateMarginal coordinate).entropy := by
  classical
  let marginal : ι → FiniteDistribution A := fun coordinate ↦
    distribution.coordinateMarginal coordinate
  let productMass : (ι → A) → ℝ := fun word ↦
    ∏ coordinate, marginal coordinate (word coordinate)
  have hproductNonnegative : ∀ word, 0 ≤ productMass word := by
    intro word
    exact Finset.prod_nonneg fun coordinate _ ↦
      (marginal coordinate).nonnegative (word coordinate)
  have hproductSum : ∑ word, productMass word = 1 := by
    calc
      ∑ word : ι → A, productMass word =
          ∏ coordinate : ι, ∑ symbol : A, marginal coordinate symbol := by
        unfold productMass
        simpa only using
          (Fintype.prod_sum (fun coordinate symbol ↦ marginal coordinate symbol)).symm
      _ = 1 := by simp
  have hmarginalPositive {word : ι → A} (hword : distribution word ≠ 0)
      (coordinate : ι) : 0 < marginal coordinate (word coordinate) := by
    have hwordPositive : 0 < distribution word :=
      lt_of_le_of_ne (distribution.nonnegative word) (Ne.symm hword)
    apply hwordPositive.trans_le
    simpa [marginal, coordinateMarginal] using
      (distribution.le_map_apply (fun other : ι → A ↦ other coordinate) word)
  have hsupport : ∀ word, distribution word ≠ 0 → productMass word ≠ 0 := by
    intro word hword
    exact (Finset.prod_pos fun coordinate _ ↦ hmarginalPositive hword coordinate).ne'
  have hkl := sum_mul_log_div_nonnegative distribution productMass
    distribution.nonnegative hproductNonnegative distribution.sum_probability hproductSum hsupport
  have hpoint (word : ι → A) :
      distribution word * Real.log (distribution word / productMass word) =
        distribution word * Real.log (distribution word) -
          distribution word * ∑ coordinate : ι,
            Real.log (marginal coordinate (word coordinate)) := by
    by_cases hword : distribution word = 0
    · simp [hword]
    have hproduct : productMass word ≠ 0 := hsupport word hword
    have hlogProduct :
        Real.log (productMass word) =
          ∑ coordinate : ι, Real.log (marginal coordinate (word coordinate)) := by
      unfold productMass
      rw [Real.log_prod]
      intro coordinate _
      exact (hmarginalPositive hword coordinate).ne'
    rw [Real.log_div hword hproduct, hlogProduct]
    ring
  have hexpectation (coordinate : ι) :
      (∑ word : ι → A,
        distribution word * Real.log (marginal coordinate (word coordinate))) =
        ∑ symbol : A, marginal coordinate symbol *
          Real.log (marginal coordinate symbol) := by
    simpa [marginal, coordinateMarginal] using
      (distribution.sum_map_mul (fun word : ι → A ↦ word coordinate)
        (fun symbol ↦ Real.log (marginal coordinate symbol))).symm
  have hidentity :
      (∑ word : ι → A,
        distribution word * Real.log (distribution word / productMass word)) =
        -distribution.entropy + ∑ coordinate : ι, (marginal coordinate).entropy := by
    calc
      ∑ word : ι → A,
          distribution word * Real.log (distribution word / productMass word) =
          ∑ word : ι → A,
            (distribution word * Real.log (distribution word) -
              distribution word * ∑ coordinate : ι,
                Real.log (marginal coordinate (word coordinate))) := by
        apply Fintype.sum_congr
        exact hpoint
      _ = (∑ word : ι → A,
            distribution word * Real.log (distribution word)) -
          ∑ coordinate : ι, ∑ word : ι → A,
            distribution word * Real.log (marginal coordinate (word coordinate)) := by
        rw [Finset.sum_sub_distrib]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = (∑ word : ι → A,
            distribution word * Real.log (distribution word)) -
          ∑ coordinate : ι, ∑ symbol : A,
            marginal coordinate symbol * Real.log (marginal coordinate symbol) := by
        congr 1
        apply Fintype.sum_congr
        exact hexpectation
      _ = -distribution.entropy +
          ∑ coordinate : ι, (marginal coordinate).entropy := by
        rw [distribution.entropy_eq_neg_sum_mul_log]
        simp_rw [entropy_eq_neg_sum_mul_log]
        have hmarginalNeg :
            (∑ coordinate : ι,
              -(∑ symbol : A, marginal coordinate symbol *
                Real.log (marginal coordinate symbol))) =
              -(∑ coordinate : ι, ∑ symbol : A,
                marginal coordinate symbol * Real.log (marginal coordinate symbol)) := by
          rw [Finset.sum_neg_distrib]
        rw [hmarginalNeg]
        ring
  rw [hidentity] at hkl
  simpa [marginal] using (show distribution.entropy ≤
    ∑ coordinate : ι, (marginal coordinate).entropy by linarith)

end FiniteDistribution

namespace FiniteChannel

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Mutual information of a finite channel is nonnegative. -/
@[capacity_shared_api]
theorem mutualInformation_nonnegative
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) :
    0 ≤ channel.mutualInformation input := by
  rw [← channel.sum_jointMass_mul_informationDensity input]
  have hpoint (x : X) (y : Y) :
      input x * (channel.transition x y - channel.outputDistribution input y) ≤
        channel.jointMass input (x, y) * channel.informationDensity input (x, y) := by
    by_cases hinputZero : input x = 0
    · simp [hinputZero, jointMass]
    by_cases htransitionZero : channel.transition x y = 0
    · unfold jointMass informationDensity
      rw [htransitionZero]
      simp only [zero_div, Real.log_zero, mul_zero, zero_sub]
      exact mul_nonpos_of_nonneg_of_nonpos (input.nonnegative x)
        (neg_nonpos.mpr ((channel.outputDistribution input).nonnegative y))
    have hinput : 0 < input x :=
      lt_of_le_of_ne (input.nonnegative x) (Ne.symm hinputZero)
    have htransition : 0 < channel.transition x y :=
      lt_of_le_of_ne (channel.nonnegative x y) (Ne.symm htransitionZero)
    have houtput : 0 < channel.outputDistribution input y := by
      apply (mul_pos hinput htransition).trans_le
      exact Finset.single_le_sum
        (fun symbol _ ↦ mul_nonneg (input.nonnegative symbol)
          (channel.nonnegative symbol y))
        (Finset.mem_univ x)
    have hlog := Real.log_le_sub_one_of_pos
      (div_pos houtput htransition)
    have hscaled := mul_le_mul_of_nonneg_left hlog htransition.le
    have hratio :
        channel.transition x y *
            (channel.outputDistribution input y / channel.transition x y - 1) =
          channel.outputDistribution input y - channel.transition x y := by
      field_simp [htransitionZero]
    rw [hratio] at hscaled
    have hswap :
        Real.log (channel.transition x y / channel.outputDistribution input y) =
          -Real.log (channel.outputDistribution input y / channel.transition x y) := by
      rw [Real.log_div htransitionZero houtput.ne',
        Real.log_div houtput.ne' htransitionZero]
      ring
    unfold jointMass informationDensity
    rw [hswap]
    nlinarith
  calc
    0 = ∑ x : X, ∑ y : Y,
        input x * (channel.transition x y - channel.outputDistribution input y) := by
      symm
      calc
        ∑ x : X, ∑ y : Y,
            input x * (channel.transition x y - channel.outputDistribution input y) =
            ∑ x : X, input x *
              ((∑ y : Y, channel.transition x y) -
                ∑ y : Y, channel.outputDistribution input y) := by
          apply Fintype.sum_congr
          intro x
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = 0 := by
          have houtputSum : ∑ y, channel.outputDistribution input y = 1 :=
            (channel.outputDistribution input).sum_probability
          apply Finset.sum_eq_zero
          intro x _
          rw [channel.row_sum x, houtputSum, sub_self, mul_zero]
    _ ≤ ∑ x : X, ∑ y : Y,
        channel.jointMass input (x, y) *
          channel.informationDensity input (x, y) := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_le_sum fun y _ ↦ hpoint x y
    _ = ∑ pair : X × Y,
        channel.jointMass input pair * channel.informationDensity input pair := by
      rw [Fintype.sum_prod_type]

/-- Mutual information is bounded by the output-alphabet logarithm. -/
@[capacity_shared_api]
theorem mutualInformation_le_log_card_output
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) :
    channel.mutualInformation input ≤ Real.log (Fintype.card Y) := by
  letI : Nonempty X := input.nonempty
  letI : Nonempty Y := channel.output_nonempty
  have hconditional : 0 ≤ channel.conditionalOutputEntropy input := by
    unfold conditionalOutputEntropy
    exact Finset.sum_nonneg fun x _ ↦
      mul_nonneg (input.nonnegative x) (channel.rowDistribution x).entropy_nonnegative
  unfold mutualInformation
  linarith [((channel.outputDistribution input).entropy_le_log_card)]

/-- Every input's information value is below the channel information capacity. -/
@[capacity_shared_api]
theorem mutualInformationBits_le_informationCapacityBits
    (channel : FiniteChannel X Y) (input : FiniteDistribution X) :
    channel.mutualInformationBits input ≤ channel.informationCapacityBits := by
  letI : Nonempty X := input.nonempty
  letI : Nonempty Y := channel.output_nonempty
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbdd : BddAbove (Set.range channel.mutualInformationBits) := by
    refine ⟨Real.log (Fintype.card Y) / Real.log 2, ?_⟩
    rintro value ⟨otherInput, rfl⟩
    unfold mutualInformationBits
    exact div_le_div_of_nonneg_right
      (channel.mutualInformation_le_log_card_output otherInput) hlogTwo.le
  unfold informationCapacityBits
  exact le_csSup hbdd (Set.mem_range_self input)

/-- A finite channel with a nonempty input alphabet has nonnegative information capacity. -/
@[capacity_shared_api]
theorem informationCapacityBits_nonnegative [Nonempty X]
    (channel : FiniteChannel X Y) : 0 ≤ channel.informationCapacityBits := by
  let input := FiniteDistribution.uniform X
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmutualBits : 0 ≤ channel.mutualInformationBits input := by
    unfold mutualInformationBits
    exact div_nonneg (channel.mutualInformation_nonnegative input) hlogTwo.le
  exact hmutualBits.trans (channel.mutualInformationBits_le_informationCapacityBits input)

/-- A coordinate marginal of a memoryless block output is the corresponding one-use output. -/
@[capacity_shared_api]
theorem block_output_coordinateMarginal
    (channel : FiniteChannel X Y) (n : ℕ)
    (input : FiniteDistribution (Fin n → X)) (coordinate : Fin n) :
    ((channel.block n).outputDistribution input).coordinateMarginal coordinate =
      channel.outputDistribution (input.coordinateMarginal coordinate) := by
  classical
  apply FiniteDistribution.ext
  intro output
  let indicator : Y → ℝ := fun symbol ↦ if symbol = output then 1 else 0
  have houtputMap :=
    ((channel.block n).outputDistribution input).sum_map_mul
      (fun word : Fin n → Y ↦ word coordinate) indicator
  have hinputMap := input.sum_map_mul
    (fun word : Fin n → X ↦ word coordinate)
    (fun symbol ↦ channel.transition symbol output)
  have hrow (inputWord : Fin n → X) :
      (∑ outputWord : Fin n → Y,
        (channel.block n).transition inputWord outputWord * indicator (outputWord coordinate)) =
        channel.transition (inputWord coordinate) output := by
    rw [show (fun outputWord : Fin n → Y ↦
        (channel.block n).transition inputWord outputWord * indicator (outputWord coordinate)) =
        (fun outputWord ↦
          (∏ i, channel.transition (inputWord i) (outputWord i)) *
            indicator (outputWord coordinate)) by rfl]
    rw [FiniteProductProbability.sum_prod_mul_apply
      (fun i symbol ↦ channel.transition (inputWord i) symbol) indicator
      (fun i ↦ channel.row_sum (inputWord i)) coordinate]
    simp [indicator]
  calc
    (((channel.block n).outputDistribution input).coordinateMarginal coordinate) output =
        ∑ outputWord : Fin n → Y,
          (channel.block n).outputDistribution input outputWord *
            indicator (outputWord coordinate) := by
      simpa [indicator, FiniteDistribution.coordinateMarginal] using houtputMap
    _ = ∑ inputWord : Fin n → X, input inputWord *
        ∑ outputWord : Fin n → Y,
          (channel.block n).transition inputWord outputWord *
            indicator (outputWord coordinate) := by
      change
        (∑ outputWord : Fin n → Y,
          (∑ inputWord : Fin n → X,
            input inputWord * (channel.block n).transition inputWord outputWord) *
              indicator (outputWord coordinate)) = _
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro inputWord
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro outputWord
      ring
    _ = ∑ inputWord : Fin n → X, input inputWord *
        channel.transition (inputWord coordinate) output := by
      apply Fintype.sum_congr
      intro inputWord
      rw [hrow]
    _ = ∑ symbol : X, input.coordinateMarginal coordinate symbol *
        channel.transition symbol output := by
      simpa [FiniteDistribution.coordinateMarginal] using hinputMap.symm
    _ = channel.outputDistribution (input.coordinateMarginal coordinate) output := rfl

/-- A memoryless channel row has additive entropy across a finite block. -/
@[capacity_shared_api]
theorem block_rowDistribution_entropy
    (channel : FiniteChannel X Y) (n : ℕ) (inputWord : Fin n → X) :
    ((channel.block n).rowDistribution inputWord).entropy =
      ∑ coordinate : Fin n, (channel.rowDistribution (inputWord coordinate)).entropy := by
  classical
  have hpoint (outputWord : Fin n → Y) :
      Real.negMulLog ((channel.block n).transition inputWord outputWord) =
        -(∏ coordinate, channel.transition (inputWord coordinate) (outputWord coordinate)) *
          ∑ coordinate, Real.log (channel.transition (inputWord coordinate) (outputWord coordinate)) := by
    by_cases hproduct :
        (∏ coordinate, channel.transition (inputWord coordinate) (outputWord coordinate)) = 0
    · simp [block_transition, hproduct]
    · rw [block_transition, Real.negMulLog_def]
      change
        -(∏ coordinate, channel.transition (inputWord coordinate) (outputWord coordinate)) *
            Real.log
              (∏ coordinate, channel.transition (inputWord coordinate) (outputWord coordinate)) = _
      rw [Real.log_prod (Finset.prod_ne_zero_iff.mp hproduct)]
  unfold FiniteDistribution.entropy
  simp only [rowDistribution_apply]
  calc
    ∑ outputWord : Fin n → Y,
        Real.negMulLog ((channel.block n).transition inputWord outputWord) =
        ∑ outputWord : Fin n → Y,
          -(∏ coordinate, channel.transition (inputWord coordinate) (outputWord coordinate)) *
            ∑ coordinate,
              Real.log (channel.transition (inputWord coordinate) (outputWord coordinate)) := by
      apply Fintype.sum_congr
      exact hpoint
    _ = ∑ coordinate : Fin n, ∑ outputWord : Fin n → Y,
        (∏ i, channel.transition (inputWord i) (outputWord i)) *
          (-Real.log (channel.transition (inputWord coordinate) (outputWord coordinate))) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro coordinate
      apply Fintype.sum_congr
      intro outputWord
      ring
    _ = ∑ coordinate : Fin n, ∑ output : Y,
        channel.transition (inputWord coordinate) output *
          (-Real.log (channel.transition (inputWord coordinate) output)) := by
      apply Fintype.sum_congr
      intro coordinate
      rw [FiniteProductProbability.sum_prod_mul_apply
        (fun i symbol ↦ channel.transition (inputWord i) symbol)
        (fun symbol ↦ -Real.log (channel.transition (inputWord coordinate) symbol))
        (fun i ↦ channel.row_sum (inputWord i)) coordinate]
    _ = ∑ coordinate : Fin n,
        (channel.rowDistribution (inputWord coordinate)).entropy := by
      apply Fintype.sum_congr
      intro coordinate
      unfold FiniteDistribution.entropy
      simp only [rowDistribution_apply, Real.negMulLog_def]
      apply Fintype.sum_congr
      intro output
      ring

/-- Conditional output entropy of a memoryless block is the sum of one-use terms. -/
@[capacity_shared_api]
theorem block_conditionalOutputEntropy
    (channel : FiniteChannel X Y) (n : ℕ)
    (input : FiniteDistribution (Fin n → X)) :
    (channel.block n).conditionalOutputEntropy input =
      ∑ coordinate : Fin n,
        channel.conditionalOutputEntropy (input.coordinateMarginal coordinate) := by
  classical
  unfold conditionalOutputEntropy
  simp_rw [channel.block_rowDistribution_entropy n]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro coordinate
  simpa [FiniteDistribution.coordinateMarginal] using
    (input.sum_map_mul (fun word : Fin n → X ↦ word coordinate)
      (fun symbol ↦ (channel.rowDistribution symbol).entropy)).symm

/-- Block mutual information is at most blocklength times single-letter capacity. -/
@[capacity_shared_api]
theorem block_mutualInformation_le_informationCapacityBits_mul_log_two
    (channel : FiniteChannel X Y) (n : ℕ)
    (input : FiniteDistribution (Fin n → X)) :
    (channel.block n).mutualInformation input ≤
      (n : ℝ) * channel.informationCapacityBits * Real.log 2 := by
  classical
  let output := (channel.block n).outputDistribution input
  have houtputEntropy :
      output.entropy ≤
        ∑ coordinate : Fin n,
          (channel.outputDistribution (input.coordinateMarginal coordinate)).entropy := by
    calc
      output.entropy ≤
          ∑ coordinate : Fin n, (output.coordinateMarginal coordinate).entropy :=
        output.entropy_pi_le_sum_coordinateEntropy
      _ = ∑ coordinate : Fin n,
          (channel.outputDistribution (input.coordinateMarginal coordinate)).entropy := by
        apply Fintype.sum_congr
        intro coordinate
        rw [show output.coordinateMarginal coordinate =
            channel.outputDistribution (input.coordinateMarginal coordinate) by
          exact channel.block_output_coordinateMarginal n input coordinate]
  have hsumInformation :
      (channel.block n).mutualInformation input ≤
        ∑ coordinate : Fin n,
          channel.mutualInformation (input.coordinateMarginal coordinate) := by
    unfold mutualInformation
    rw [channel.block_conditionalOutputEntropy n input]
    calc
      output.entropy -
          ∑ coordinate : Fin n,
            channel.conditionalOutputEntropy (input.coordinateMarginal coordinate) ≤
          (∑ coordinate : Fin n,
            (channel.outputDistribution (input.coordinateMarginal coordinate)).entropy) -
            ∑ coordinate : Fin n,
              channel.conditionalOutputEntropy (input.coordinateMarginal coordinate) :=
        sub_le_sub_right houtputEntropy _
      _ = ∑ coordinate : Fin n,
          ((channel.outputDistribution (input.coordinateMarginal coordinate)).entropy -
            channel.conditionalOutputEntropy (input.coordinateMarginal coordinate)) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ coordinate : Fin n,
          channel.mutualInformation (input.coordinateMarginal coordinate) := by rfl
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (channel.block n).mutualInformation input ≤
        ∑ coordinate : Fin n,
          channel.mutualInformation (input.coordinateMarginal coordinate) := hsumInformation
    _ ≤ ∑ _coordinate : Fin n,
        channel.informationCapacityBits * Real.log 2 := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact (div_le_iff₀ hlogTwo).mp
        (channel.mutualInformationBits_le_informationCapacityBits
          (input.coordinateMarginal coordinate))
    _ = (n : ℝ) * channel.informationCapacityBits * Real.log 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end FiniteChannel

end CapacityAtlas
