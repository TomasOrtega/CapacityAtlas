/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.

Adapted from TomasOrtega/CapacityAtlasMAC, commit ec5be554b9644df94dd58190963793f3f1d1da52,
CapacityAtlasMAC/RandomCoding.lean. Imports and certificate types use the monorepo modules.
-/

import CapacityAtlasForMathlib.InformationTheory.MultipleAccess
import CapacityAtlasForMathlib.InformationTheory.RandomCoding

open scoped BigOperators

namespace CapacityAtlas.MultipleAccess

attribute [local instance] Classical.propDecidable

private def indicator (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

private theorem indicator_nonnegative (p : Prop) [Decidable p] : 0 ≤ indicator p := by
  unfold indicator
  split_ifs <;> norm_num

section Ensemble

variable {A B I J K : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J] [Fintype K]
variable [DecidableEq I] [DecidableEq J]

private noncomputable def ensembleMean (p : FiniteDistribution A) (q : FiniteDistribution B)
    (f : (I → A) → (J → B) → ℝ) : ℝ :=
  ∑ c, FiniteProductProbability.mass p c * ∑ d, FiniteProductProbability.mass q d * f c d

private theorem ensembleMean_mono (p : FiniteDistribution A) (q : FiniteDistribution B)
    {f g : (I → A) → (J → B) → ℝ} (h : ∀ c d, f c d ≤ g c d) :
    ensembleMean p q f ≤ ensembleMean p q g := by
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (FiniteProductProbability.mass_nonnegative p p.nonnegative c)
  apply Finset.sum_le_sum
  intro d _
  exact mul_le_mul_of_nonneg_left (h c d)
    (FiniteProductProbability.mass_nonnegative q q.nonnegative d)

private theorem ensembleMean_add (p : FiniteDistribution A) (q : FiniteDistribution B)
    (f g : (I → A) → (J → B) → ℝ) :
    ensembleMean p q (fun c d ↦ f c d + g c d) =
      ensembleMean p q f + ensembleMean p q g := by
  simp only [ensembleMean, mul_add, Finset.sum_add_distrib]

omit [Fintype K] in
private theorem ensembleMean_sum (p : FiniteDistribution A) (q : FiniteDistribution B)
    (s : Finset K) (f : K → (I → A) → (J → B) → ℝ) :
    ensembleMean p q (fun c d ↦ ∑ k ∈ s, f k c d) =
      ∑ k ∈ s, ensembleMean p q (f k) := by
  simp only [ensembleMean, Finset.mul_sum]
  calc
    _ = ∑ c, ∑ k ∈ s, ∑ d,
        FiniteProductProbability.mass p c * (FiniteProductProbability.mass q d * f k c d) := by
      apply Fintype.sum_congr
      intro c
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

private theorem ensembleMean_comm (p : FiniteDistribution A) (q : FiniteDistribution B)
    (f : (I → A) → (J → B) → ℝ) :
    ensembleMean p q f = ensembleMean q p (fun d c ↦ f c d) := by
  simp only [ensembleMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro d
  apply Fintype.sum_congr
  intro c
  ring

private theorem ensembleMean_eval (p : FiniteDistribution A) (q : FiniteDistribution B)
    (i : I) (j : J) (f : A → B → ℝ) :
    ensembleMean p q (fun c d ↦ f (c i) (d j)) =
      ∑ a, p a * ∑ b, q b * f a b := by
  unfold ensembleMean
  simp_rw [FiniteProductProbability.sum_mass_mul_apply q _ q.sum_probability j]
  simpa only [FiniteProductProbability.mean] using
    (FiniteProductProbability.sum_mass_mul_apply p
      (fun a ↦ FiniteProductProbability.mean q (f a)) p.sum_probability i)

private theorem ensembleMean_two_left (p : FiniteDistribution A) (q : FiniteDistribution B)
    {i i' : I} (hii' : i ≠ i') (j : J) (f g : A → B → ℝ) :
    ensembleMean p q (fun c d ↦ f (c i) (d j) * g (c i') (d j)) =
      ∑ b, q b * ((∑ a, p a * f a b) * (∑ a, p a * g a b)) := by
  rw [ensembleMean_comm]
  unfold ensembleMean
  have hinner (d : J → B) :
      (∑ c : I → A, FiniteProductProbability.mass p c * (f (c i) (d j) * g (c i') (d j))) =
        (∑ a, p a * f a (d j)) * (∑ a, p a * g a (d j)) := by
    simpa only [FiniteProductProbability.mean] using
      FiniteProductProbability.sum_mass_mul_apply_mul_apply p
        (fun a ↦ f a (d j)) (fun a ↦ g a (d j)) p.sum_probability hii'
  simp_rw [hinner]
  simpa only [FiniteProductProbability.mean] using
    FiniteProductProbability.sum_mass_mul_apply q
      (fun b ↦ (∑ a, p a * f a b) * (∑ a, p a * g a b)) q.sum_probability j

private theorem ensembleMean_two_right (p : FiniteDistribution A) (q : FiniteDistribution B)
    (i : I) {j j' : J} (hjj' : j ≠ j') (f g : A → B → ℝ) :
    ensembleMean p q (fun c d ↦ f (c i) (d j) * g (c i) (d j')) =
      ∑ a, p a * ((∑ b, q b * f a b) * (∑ b, q b * g a b)) := by
  rw [ensembleMean_comm]
  exact ensembleMean_two_left q p hjj' i (fun b a ↦ f a b) (fun b a ↦ g a b)

private theorem ensembleMean_two_both (p : FiniteDistribution A) (q : FiniteDistribution B)
    {i i' : I} (hii' : i ≠ i') {j j' : J} (hjj' : j ≠ j') (f g : A → B → ℝ) :
    ensembleMean p q (fun c d ↦ f (c i) (d j) * g (c i') (d j')) =
      (∑ a, p a * ∑ b, q b * f a b) * (∑ a, p a * ∑ b, q b * g a b) := by
  rw [ensembleMean_comm]
  unfold ensembleMean
  have hinner (d : J → B) :
      (∑ c : I → A, FiniteProductProbability.mass p c * (f (c i) (d j) * g (c i') (d j'))) =
        (∑ a, p a * f a (d j)) * (∑ a, p a * g a (d j')) := by
    simpa only [FiniteProductProbability.mean] using
      FiniteProductProbability.sum_mass_mul_apply_mul_apply p
        (fun a ↦ f a (d j)) (fun a ↦ g a (d j')) p.sum_probability hii'
  simp_rw [hinner]
  rw [FiniteProductProbability.sum_mass_mul_apply_mul_apply q
    (fun b ↦ ∑ a, p a * f a b) (fun b ↦ ∑ a, p a * g a b) q.sum_probability hjj']
  simp only [FiniteProductProbability.mean]
  have hswap (h : A → B → ℝ) :
      (∑ b, q b * ∑ a, p a * h a b) = ∑ a, p a * ∑ b, q b * h a b := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro a
    apply Fintype.sum_congr
    intro b
    ring
  rw [hswap f, hswap g]

private theorem ensembleMean_const_mul (p : FiniteDistribution A) (q : FiniteDistribution B)
    (k : ℝ) (f : (I → A) → (J → B) → ℝ) :
    ensembleMean p q (fun c d ↦ k * f c d) = k * ensembleMean p q f := by
  simp only [ensembleMean, Finset.mul_sum]
  apply Fintype.sum_congr
  intro c
  apply Fintype.sum_congr
  intro d
  ring

end Ensemble

section Coding

variable {A B Y I J : Type*} [Fintype A] [Fintype B] [Fintype Y]
variable [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J]

private def IsJointCandidate (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t₁ t₂ t₁₂ : ℝ)
    (a : A) (b : B) (y : Y) : Prop :=
  (leftSlice W b).IsInformationDensityCandidate p t₁ a y ∧
  (rightSlice W a).IsInformationDensityCandidate q t₂ b y ∧
  W.IsInformationDensityCandidate (productInput p q) t₁₂ (a, b) y

private noncomputable def jointDecoder (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t₁ t₂ t₁₂ : ℝ)
    (c : I → A) (d : J → B) (y : Y) : I × J :=
  if h : ∃ m : I × J, IsJointCandidate W p q t₁ t₂ t₁₂ (c m.1) (d m.2) y then
    Classical.choose h else Classical.choice inferInstance

private noncomputable def jointThresholdCode (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t₁ t₂ t₁₂ : ℝ)
    (c : I → A) (d : J → B) : OneShotCode W I J where
  encode₁ := c
  encode₂ := d
  decode := jointDecoder W p q t₁ t₂ t₁₂ c d

omit [DecidableEq I] [DecidableEq J] in
private theorem jointDecoder_candidate (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t₁ t₂ t₁₂ : ℝ)
    (c : I → A) (d : J → B) (y : Y)
    (h : ∃ m : I × J, IsJointCandidate W p q t₁ t₂ t₁₂ (c m.1) (d m.2) y) :
    IsJointCandidate W p q t₁ t₂ t₁₂
      (c (jointDecoder W p q t₁ t₂ t₁₂ c d y).1)
      (d (jointDecoder W p q t₁ t₂ t₁₂ c d y).2) y := by
  rw [jointDecoder, dif_pos h]
  exact Classical.choose_spec h

private noncomputable def missMass (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t₁ t₂ t₁₂ : ℝ)
    (a : A) (b : B) (y : Y) : ℝ :=
  W.transition (a, b) y *
    (indicator ((leftSlice W b).informationDensity p (a, y) ≤ t₁) +
      indicator ((rightSlice W a).informationDensity q (b, y) ≤ t₂) +
      indicator (W.informationDensity (productInput p q) ((a, b), y) ≤ t₁₂))

private noncomputable def rival₁ (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (t : ℝ) (a b : A) (x : B) (y : Y) : ℝ :=
  W.transition (a, x) y * indicator ((leftSlice W x).IsInformationDensityCandidate p t b y)

private noncomputable def rival₂ (W : FiniteChannel (A × B) Y)
    (q : FiniteDistribution B) (t : ℝ) (a : A) (b x : B) (y : Y) : ℝ :=
  W.transition (a, b) y * indicator ((rightSlice W a).IsInformationDensityCandidate q t x y)

private noncomputable def rival₁₂ (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t : ℝ)
    (a a' : A) (b b' : B) (y : Y) : ℝ :=
  W.transition (a, b) y * indicator (W.IsInformationDensityCandidate (productInput p q) t (a', b') y)

private theorem errorSummand_le (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t₁ t₂ t₁₂ : ℝ)
    (c : I → A) (d : J → B) (m : I × J) (y : Y) :
    (if jointDecoder W p q t₁ t₂ t₁₂ c d y ≠ m then W.transition (c m.1, d m.2) y else 0) ≤
      missMass W p q t₁ t₂ t₁₂ (c m.1) (d m.2) y +
      (∑ i ∈ Finset.univ.erase m.1, rival₁ W p t₁ (c m.1) (c i) (d m.2) y) +
      (∑ j ∈ Finset.univ.erase m.2, rival₂ W q t₂ (c m.1) (d m.2) (d j) y) +
      ∑ i ∈ Finset.univ.erase m.1, ∑ j ∈ Finset.univ.erase m.2,
        rival₁₂ W p q t₁₂ (c m.1) (c i) (d m.2) (d j) y := by
  let z := W.transition (c m.1, d m.2) y
  have hz : 0 ≤ z := W.nonnegative _ _
  have hm : 0 ≤ missMass W p q t₁ t₂ t₁₂ (c m.1) (d m.2) y :=
    mul_nonneg hz (add_nonneg (add_nonneg (indicator_nonnegative _) (indicator_nonnegative _))
      (indicator_nonnegative _))
  have h₁ : ∀ i, 0 ≤ rival₁ W p t₁ (c m.1) (c i) (d m.2) y :=
    fun _ ↦ mul_nonneg hz (indicator_nonnegative _)
  have h₂ : ∀ j, 0 ≤ rival₂ W q t₂ (c m.1) (d m.2) (d j) y :=
    fun _ ↦ mul_nonneg hz (indicator_nonnegative _)
  have h₁₂ : ∀ i j, 0 ≤ rival₁₂ W p q t₁₂ (c m.1) (c i) (d m.2) (d j) y :=
    fun _ _ ↦ mul_nonneg hz (indicator_nonnegative _)
  have hs₁ := Finset.sum_nonneg (s := Finset.univ.erase m.1) (fun i _ ↦ h₁ i)
  have hs₂ := Finset.sum_nonneg (s := Finset.univ.erase m.2) (fun j _ ↦ h₂ j)
  have hs₁₂ := Finset.sum_nonneg (s := Finset.univ.erase m.1)
    (fun i _ ↦ Finset.sum_nonneg (s := Finset.univ.erase m.2) (fun j _ ↦ h₁₂ i j))
  by_cases hdecode : jointDecoder W p q t₁ t₂ t₁₂ c d y = m
  · simp only [hdecode, ne_eq, not_true_eq_false, if_false]
    linarith
  rw [if_pos hdecode]
  change z ≤ _
  by_cases hcand : IsJointCandidate W p q t₁ t₂ t₁₂ (c m.1) (d m.2) y
  · let decoded := jointDecoder W p q t₁ t₂ t₁₂ c d y
    have hd := jointDecoder_candidate W p q t₁ t₂ t₁₂ c d y ⟨m, hcand⟩
    change IsJointCandidate W p q t₁ t₂ t₁₂ (c decoded.1) (d decoded.2) y at hd
    by_cases hfirst : decoded.1 = m.1
    · have hsecond : decoded.2 ≠ m.2 := fun h ↦ hdecode (Prod.ext hfirst h)
      have hterm := Finset.single_le_sum (fun j _ ↦ h₂ j)
        (show decoded.2 ∈ Finset.univ.erase m.2 by simp [hsecond])
      have heq : rival₂ W q t₂ (c m.1) (d m.2) (d decoded.2) y = z := by
        have h := hd.2.1
        rw [hfirst] at h
        simp [rival₂, indicator, h, z]
      rw [heq] at hterm
      linarith
    · by_cases hsecond : decoded.2 = m.2
      · have hterm := Finset.single_le_sum (fun i _ ↦ h₁ i)
          (show decoded.1 ∈ Finset.univ.erase m.1 by simp [hfirst])
        have heq : rival₁ W p t₁ (c m.1) (c decoded.1) (d m.2) y = z := by
          have h := hd.1
          rw [hsecond] at h
          simp [rival₁, indicator, h, z]
        rw [heq] at hterm
        linarith
      · have hinner := Finset.single_le_sum (fun j _ ↦ h₁₂ decoded.1 j)
          (show decoded.2 ∈ Finset.univ.erase m.2 by simp [hsecond])
        have houter := Finset.single_le_sum
          (fun i _ ↦ Finset.sum_nonneg (s := Finset.univ.erase m.2) (fun j _ ↦ h₁₂ i j))
          (show decoded.1 ∈ Finset.univ.erase m.1 by simp [hfirst])
        have heq : rival₁₂ W p q t₁₂ (c m.1) (c decoded.1) (d m.2) (d decoded.2) y = z := by
          simp only [rival₁₂, indicator, if_pos hd.2.2, mul_one]
          rfl
        rw [heq] at hinner
        linarith
  · have hmiss : z ≤ missMass W p q t₁ t₂ t₁₂ (c m.1) (d m.2) y := by
      by_cases hzero : z = 0
      · simpa [hzero] using hm
      have hpositive : 0 < z := lt_of_le_of_ne hz (Ne.symm hzero)
      by_cases hleft : (leftSlice W (d m.2)).informationDensity p (c m.1, y) ≤ t₁
      · simp only [missMass, indicator, hleft, if_true]
        split_ifs
        all_goals dsimp [z] at *
        all_goals nlinarith
      by_cases hright : (rightSlice W (c m.1)).informationDensity q (d m.2, y) ≤ t₂
      · simp only [missMass, indicator, hright, if_true]
        split_ifs
        all_goals dsimp [z] at *
        all_goals nlinarith
      by_cases hjoint : W.informationDensity (productInput p q) ((c m.1, d m.2), y) ≤ t₁₂
      · simp only [missMass, indicator, hjoint, if_true]
        split_ifs
        all_goals dsimp [z] at *
        all_goals nlinarith
      exact False.elim (hcand ⟨⟨hpositive, lt_of_not_ge hleft⟩,
        ⟨hpositive, lt_of_not_ge hright⟩, ⟨hpositive, lt_of_not_ge hjoint⟩⟩)
    linarith

omit [Nonempty I] [Nonempty J] in
private theorem ensembleMean_miss (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t₁ t₂ t₁₂ : ℝ) (i : I) (j : J) :
    ensembleMean p q (fun c d ↦ ∑ y, missMass W p q t₁ t₂ t₁₂ (c i) (d j) y) =
      (∑ b, q b * (leftSlice W b).informationDensityLowerTailMass p t₁) +
      (∑ a, p a * (rightSlice W a).informationDensityLowerTailMass q t₂) +
      W.informationDensityLowerTailMass (productInput p q) t₁₂ := by
  rw [ensembleMean_sum]
  have heval (y : Y) :
      ensembleMean p q (fun c d ↦ missMass W p q t₁ t₂ t₁₂ (c i) (d j) y) =
        ∑ a, p a * ∑ b, q b * missMass W p q t₁ t₂ t₁₂ a b y :=
    ensembleMean_eval p q i j (fun a b ↦ missMass W p q t₁ t₂ t₁₂ a b y)
  simp_rw [heval]
  simp only [missMass, mul_add, Finset.sum_add_distrib]
  simp only [FiniteChannel.informationDensityLowerTailMass, FiniteChannel.jointMass,
    productInput, FiniteDistribution.joint_apply, Fintype.sum_prod_type, Finset.mul_sum]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · calc
      _ = ∑ a : A, ∑ b : B, ∑ y : Y,
          p a * (q b * (W.transition (a, b) y *
            indicator ((leftSlice W b).informationDensity p (a, y) ≤ t₁))) := by
        rw [Finset.sum_comm]
        apply Fintype.sum_congr
        intro a
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Fintype.sum_congr
        intro b
        rw [Finset.sum_comm]
        apply Fintype.sum_congr
        intro y
        apply Fintype.sum_congr
        intro a
        unfold indicator
        split_ifs <;> simp [leftSlice, FiniteChannel.encoded_transition, mul_assoc, mul_left_comm, mul_comm]
  · rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro a
    apply Fintype.sum_congr
    intro y
    apply Fintype.sum_congr
    intro b
    unfold indicator
    split_ifs <;> simp [rightSlice, FiniteChannel.encoded_transition]
  · apply Fintype.sum_congr
    intro y
    apply Fintype.sum_congr
    intro a
    apply Fintype.sum_congr
    intro b
    unfold indicator
    split_ifs <;> simp [mul_assoc]

omit [Nonempty I] [Nonempty J] in
private theorem ensembleMean_rival₁_le (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t : ℝ)
    {i i' : I} (hii' : i ≠ i') (j : J) :
    ensembleMean p q (fun c d ↦ ∑ y, rival₁ W p t (c i) (c i') (d j) y) ≤ Real.exp (-t) := by
  rw [ensembleMean_sum]
  have heval (y : Y) :
      ensembleMean p q (fun c d ↦ rival₁ W p t (c i) (c i') (d j) y) =
        ∑ b, q b * ((∑ a, p a * W.transition (a, b) y) *
          ∑ a, p a * indicator ((leftSlice W b).IsInformationDensityCandidate p t a y)) :=
    ensembleMean_two_left p q hii' j (fun a b ↦ W.transition (a, b) y)
      (fun a b ↦ indicator ((leftSlice W b).IsInformationDensityCandidate p t a y))
  simp_rw [heval]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b, q b * ∑ y, (leftSlice W b).outputDistribution p y *
        ∑ a, p a * indicator ((leftSlice W b).IsInformationDensityCandidate p t a y) := by
      apply Fintype.sum_congr
      intro b
      rw [Finset.mul_sum]
      rfl
    _ ≤ ∑ b, q b * Real.exp (-t) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left
        ((leftSlice W b).falseAlarmMass_le_exp_neg p t) (q.nonnegative b)
    _ = _ := by rw [← Finset.sum_mul, q.sum_probability_eq_one, one_mul]

omit [Nonempty I] [Nonempty J] in
private theorem ensembleMean_rival₂_le (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t : ℝ)
    (i : I) {j j' : J} (hjj' : j ≠ j') :
    ensembleMean p q (fun c d ↦ ∑ y, rival₂ W q t (c i) (d j) (d j') y) ≤ Real.exp (-t) := by
  rw [ensembleMean_sum]
  have heval (y : Y) :
      ensembleMean p q (fun c d ↦ rival₂ W q t (c i) (d j) (d j') y) =
        ∑ a, p a * ((∑ b, q b * W.transition (a, b) y) *
          ∑ b, q b * indicator ((rightSlice W a).IsInformationDensityCandidate q t b y)) :=
    ensembleMean_two_right p q i hjj' (fun a b ↦ W.transition (a, b) y)
      (fun a b ↦ indicator ((rightSlice W a).IsInformationDensityCandidate q t b y))
  simp_rw [heval]
  rw [Finset.sum_comm]
  calc
    _ = ∑ a, p a * ∑ y, (rightSlice W a).outputDistribution q y *
        ∑ b, q b * indicator ((rightSlice W a).IsInformationDensityCandidate q t b y) := by
      apply Fintype.sum_congr
      intro a
      rw [Finset.mul_sum]
      rfl
    _ ≤ ∑ a, p a * Real.exp (-t) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        ((rightSlice W a).falseAlarmMass_le_exp_neg q t) (p.nonnegative a)
    _ = _ := by rw [← Finset.sum_mul, p.sum_probability_eq_one, one_mul]

omit [Nonempty I] [Nonempty J] in
private theorem ensembleMean_rival₁₂_le (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t : ℝ)
    {i i' : I} (hii' : i ≠ i') {j j' : J} (hjj' : j ≠ j') :
    ensembleMean p q (fun c d ↦ ∑ y, rival₁₂ W p q t (c i) (c i') (d j) (d j') y) ≤
      Real.exp (-t) := by
  rw [ensembleMean_sum]
  have heval (y : Y) :
      ensembleMean p q (fun c d ↦ rival₁₂ W p q t (c i) (c i') (d j) (d j') y) =
        (∑ a, p a * ∑ b, q b * W.transition (a, b) y) *
          ∑ a, p a * ∑ b, q b *
            indicator (W.IsInformationDensityCandidate (productInput p q) t (a, b) y) :=
    ensembleMean_two_both p q hii' hjj' (fun a b ↦ W.transition (a, b) y)
      (fun a b ↦ indicator (W.IsInformationDensityCandidate (productInput p q) t (a, b) y))
  simp_rw [heval]
  have hmean (f : A × B → ℝ) :
      (∑ a, p a * ∑ b, q b * f (a, b)) = ∑ x, productInput p q x * f x := by
    simp only [Fintype.sum_prod_type, productInput, FiniteDistribution.joint_apply,
      Finset.mul_sum, mul_assoc]
  have hout (y : Y) := hmean (fun x ↦ W.transition x y)
  have hcand (y : Y) := hmean
    (fun x ↦ indicator (W.IsInformationDensityCandidate (productInput p q) t x y))
  simp_rw [hout, hcand]
  exact W.falseAlarmMass_le_exp_neg (productInput p q) t

private noncomputable def packingBound (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t₁ t₂ t₁₂ : ℝ)
    (count₁ count₂ : ℕ) : ℝ :=
  (∑ b, q b * (leftSlice W b).informationDensityLowerTailMass p t₁) +
    (∑ a, p a * (rightSlice W a).informationDensityLowerTailMass q t₂) +
    W.informationDensityLowerTailMass (productInput p q) t₁₂ +
    (count₁ - 1 : ℕ) * Real.exp (-t₁) +
    (count₂ - 1 : ℕ) * Real.exp (-t₂) +
    (count₁ - 1 : ℕ) * (count₂ - 1 : ℕ) * Real.exp (-t₁₂)

private theorem expected_errorProbability_le (W : FiniteChannel (A × B) Y)
    (p : FiniteDistribution A) (q : FiniteDistribution B) (t₁ t₂ t₁₂ : ℝ) (m : I × J) :
    ensembleMean p q (fun c d ↦
      (jointThresholdCode W p q t₁ t₂ t₁₂ c d).toOneShotCode.errorProbability m) ≤
      packingBound W p q t₁ t₂ t₁₂ (Fintype.card I) (Fintype.card J) := by
  have hpoint (c : I → A) (d : J → B) :
      (jointThresholdCode W p q t₁ t₂ t₁₂ c d).toOneShotCode.errorProbability m ≤
        (∑ y, missMass W p q t₁ t₂ t₁₂ (c m.1) (d m.2) y) +
        (∑ i ∈ Finset.univ.erase m.1, ∑ y, rival₁ W p t₁ (c m.1) (c i) (d m.2) y) +
        (∑ j ∈ Finset.univ.erase m.2, ∑ y, rival₂ W q t₂ (c m.1) (d m.2) (d j) y) +
        ∑ i ∈ Finset.univ.erase m.1, ∑ j ∈ Finset.univ.erase m.2, ∑ y,
          rival₁₂ W p q t₁₂ (c m.1) (c i) (d m.2) (d j) y := by
    rw [CapacityAtlas.OneShotCode.errorProbability_eq_sum_decode_ne]
    calc
      _ ≤ ∑ y,
          (missMass W p q t₁ t₂ t₁₂ (c m.1) (d m.2) y +
          (∑ i ∈ Finset.univ.erase m.1, rival₁ W p t₁ (c m.1) (c i) (d m.2) y) +
          (∑ j ∈ Finset.univ.erase m.2, rival₂ W q t₂ (c m.1) (d m.2) (d j) y) +
          ∑ i ∈ Finset.univ.erase m.1, ∑ j ∈ Finset.univ.erase m.2,
            rival₁₂ W p q t₁₂ (c m.1) (c i) (d m.2) (d j) y) :=
        Finset.sum_le_sum fun y _ ↦ errorSummand_le W p q t₁ t₂ t₁₂ c d m y
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_) ?_
        · rw [Finset.sum_comm]
        · rw [Finset.sum_comm]
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
  have h₁ :
      (∑ i ∈ Finset.univ.erase m.1, ensembleMean p q
        (fun c d ↦ ∑ y, rival₁ W p t₁ (c m.1) (c i) (d m.2) y)) ≤
      (Fintype.card I - 1 : ℕ) * Real.exp (-t₁) := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.erase m.1, Real.exp (-t₁) := by
        apply Finset.sum_le_sum
        intro i hi
        exact ensembleMean_rival₁_le W p q t₁
          (Ne.symm (Finset.mem_erase.mp hi).1) m.2
      _ = _ := by simp [Finset.card_erase_of_mem, Finset.mem_univ, nsmul_eq_mul]
  have h₂ :
      (∑ j ∈ Finset.univ.erase m.2, ensembleMean p q
        (fun c d ↦ ∑ y, rival₂ W q t₂ (c m.1) (d m.2) (d j) y)) ≤
      (Fintype.card J - 1 : ℕ) * Real.exp (-t₂) := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase m.2, Real.exp (-t₂) := by
        apply Finset.sum_le_sum
        intro j hj
        exact ensembleMean_rival₂_le W p q t₂ m.1
          (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = _ := by simp [Finset.card_erase_of_mem, Finset.mem_univ, nsmul_eq_mul]
  have h₁₂ :
      (∑ i ∈ Finset.univ.erase m.1, ∑ j ∈ Finset.univ.erase m.2, ensembleMean p q
        (fun c d ↦ ∑ y, rival₁₂ W p q t₁₂ (c m.1) (c i) (d m.2) (d j) y)) ≤
      (Fintype.card I - 1 : ℕ) * (Fintype.card J - 1 : ℕ) * Real.exp (-t₁₂) := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.erase m.1, ∑ _j ∈ Finset.univ.erase m.2, Real.exp (-t₁₂) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact ensembleMean_rival₁₂_le W p q t₁₂
          (Ne.symm (Finset.mem_erase.mp hi).1) (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = _ := by simp [Finset.card_erase_of_mem, Finset.mem_univ, nsmul_eq_mul, mul_assoc]
  have h := ensembleMean_mono p q hpoint
  simp only [ensembleMean_add, ensembleMean_miss,
    ensembleMean_sum p q (Finset.univ.erase m.1),
    ensembleMean_sum p q (Finset.univ.erase m.2)] at h
  unfold packingBound
  linarith

/-- Independent random codebooks admit one joint decoder with all three MAC packing bounds.
The exact rival counts retain singleton-message and zero-rate cases. -/
theorem exists_oneShotCode_averageErrorProbability_le
    (W : FiniteChannel (A × B) Y) (p : FiniteDistribution A) (q : FiniteDistribution B)
    (t₁ t₂ t₁₂ : ℝ) :
    ∃ code : OneShotCode W I J,
      code.averageErrorProbability ≤
        (∑ b, q b * (leftSlice W b).informationDensityLowerTailMass p t₁) +
        (∑ a, p a * (rightSlice W a).informationDensityLowerTailMass q t₂) +
        W.informationDensityLowerTailMass (productInput p q) t₁₂ +
        (Fintype.card I - 1 : ℕ) * Real.exp (-t₁) +
        (Fintype.card J - 1 : ℕ) * Real.exp (-t₂) +
        (Fintype.card I - 1 : ℕ) * (Fintype.card J - 1 : ℕ) * Real.exp (-t₁₂) := by
  letI : Nonempty A := p.nonempty
  letI : Nonempty B := q.nonempty
  let codeOf : (I → A) → (J → B) → OneShotCode W I J := jointThresholdCode W p q t₁ t₂ t₁₂
  let bound := packingBound W p q t₁ t₂ t₁₂ (Fintype.card I) (Fintype.card J)
  have hensemble : ensembleMean p q (fun c d ↦ (codeOf c d).averageErrorProbability) ≤ bound := by
    simp only [OneShotCode.averageErrorProbability, CapacityAtlas.OneShotCode.averageErrorProbability_eq]
    rw [ensembleMean_const_mul, ensembleMean_sum]
    calc
      _ ≤ (Fintype.card (I × J) : ℝ)⁻¹ * ∑ _m : I × J, bound := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro m _
        exact expected_errorProbability_le W p q t₁ t₂ t₁₂ m
      _ = bound := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard : (Fintype.card (I × J) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        field_simp
  let weights : ((I → A) × (J → B)) → ℝ := fun books ↦
    FiniteProductProbability.mass p books.1 * FiniteProductProbability.mass q books.2
  have hnonnegative (books : (I → A) × (J → B)) : 0 ≤ weights books :=
    mul_nonneg (FiniteProductProbability.mass_nonnegative p p.nonnegative books.1)
      (FiniteProductProbability.mass_nonnegative q q.nonnegative books.2)
  have hsum : ∑ books, weights books = 1 := by
    simp only [weights, Fintype.sum_prod_type, ← Finset.mul_sum,
      FiniteProductProbability.sum_mass q q.sum_probability, mul_one,
      FiniteProductProbability.sum_mass p p.sum_probability]
  obtain ⟨books, hbooks⟩ := FiniteProductProbability.exists_value_le_weighted_mean
    weights (fun books ↦ (codeOf books.1 books.2).averageErrorProbability) hnonnegative hsum
  refine ⟨codeOf books.1 books.2, ?_⟩
  have heq : (∑ books, weights books * (codeOf books.1 books.2).averageErrorProbability) =
      ensembleMean p q (fun c d ↦ (codeOf c d).averageErrorProbability) := by
    simp only [weights, ensembleMean, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  rw [heq] at hbooks
  exact hbooks.trans hensemble

end Coding

end CapacityAtlas.MultipleAccess
