/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteInformation
import CapacityAtlasForMathlib.InformationTheory.SequentialInformation

open scoped BigOperators

namespace CapacityAtlas.FiniteInformation

variable {Ω A B C D : Type*} [Fintype Ω] [Fintype A] [Fintype B]
  [Fintype C] [Fintype D]

@[capacity_shared_api]
theorem entropy_eq_map [DecidableEq A] (p : FiniteDistribution Ω) (f : Ω → A) :
    entropy p f = (p.map f).entropyBits := by
  exact congrArg (fun eq : DecidableEq A ↦
    (@FiniteDistribution.map Ω A _ _ eq p f).entropyBits) (Subsingleton.elim _ _)

@[capacity_shared_api]
theorem entropy_map (p : FiniteDistribution Ω) (f : Ω → A) (g : A → B)
    [DecidableEq A] : entropy (p.map f) g = entropy p (g ∘ f) := by
  classical
  simp only [entropy, FiniteDistribution.map_map]

@[capacity_shared_api]
theorem information_map (p : FiniteDistribution Ω) (f : Ω → A)
    (g : A → B) (h : A → C) [DecidableEq A] :
    information (p.map f) g h = information p (g ∘ f) (h ∘ f) := by
  simp only [information, entropy_map, Function.comp_def]

@[capacity_shared_api]
theorem conditional_map (p : FiniteDistribution Ω) (f : Ω → A)
    (g : A → B) (h : A → C) (k : A → D) [DecidableEq A] :
    conditional (p.map f) g h k = conditional p (g ∘ f) (h ∘ f) (k ∘ f) := by
  simp only [conditional, entropy_map, Function.comp_def]

@[capacity_shared_api]
theorem entropy_comp_injective (p : FiniteDistribution Ω) (f : Ω → A)
    (g : A → B) (hg : Function.Injective g) :
    entropy p (g ∘ f) = entropy p f := by
  classical
  simp only [entropy, FiniteDistribution.entropyBits,
    ← FiniteDistribution.map_map, FiniteDistribution.entropy_map_of_injective _ g hg]

@[capacity_shared_api]
theorem entropy_comp_le (p : FiniteDistribution Ω) (f : Ω → A) (g : A → B) :
    entropy p (g ∘ f) ≤ entropy p f := by
  classical
  unfold entropy FiniteDistribution.entropyBits
  rw [← FiniteDistribution.map_map]
  exact div_le_div_of_nonneg_right ((p.map f).entropy_map_le g)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- Observations that determine each other have the same entropy. -/
@[capacity_shared_api]
theorem entropy_eq_of_mutual (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B)
    (fg : A → B) (gf : B → A) (hfg : fg ∘ f = g) (hgf : gf ∘ g = f) :
    entropy p f = entropy p g := by
  apply le_antisymm
  · simpa only [hgf] using entropy_comp_le p g gf
  · simpa only [hfg] using entropy_comp_le p f fg

@[capacity_shared_api]
theorem entropy_pair_swap (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) :
    entropy p (fun ω ↦ (f ω, g ω)) = entropy p (fun ω ↦ (g ω, f ω)) := by
  exact (entropy_comp_injective p (fun ω ↦ (f ω, g ω))
    Prod.swap Prod.swap_injective).symm

@[capacity_shared_api]
theorem entropy_pair_assoc (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B)
    (h : Ω → C) :
    entropy p (fun ω ↦ ((f ω, g ω), h ω)) =
      entropy p (fun ω ↦ (f ω, g ω, h ω)) := by
  exact (entropy_comp_injective p (fun ω ↦ ((f ω, g ω), h ω))
    (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C).injective).symm

@[capacity_shared_api]
theorem entropy_nonneg (p : FiniteDistribution Ω) (f : Ω → A) :
    0 ≤ entropy p f := by
  classical
  exact div_nonneg (p.map f).entropy_nonnegative
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

@[capacity_shared_api]
theorem entropy_const (p : FiniteDistribution Ω) (a : A) :
    entropy p (fun _ ↦ a) = 0 := by
  have h := entropy_comp_injective p (fun _ ↦ ()) (fun _ : Unit ↦ a)
    (fun _ _ _ ↦ Subsingleton.elim _ _)
  classical
  simpa [entropy, FiniteDistribution.entropyBits,
    FiniteDistribution.entropy_of_subsingleton, Function.comp_def] using h

@[capacity_shared_api]
theorem conditionalEntropy_nonneg (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) : 0 ≤ conditionalEntropy p f g := by
  have h := entropy_comp_le p (fun ω ↦ (f ω, g ω)) Prod.snd
  unfold conditionalEntropy
  exact sub_nonneg.mpr h

@[capacity_shared_api]
theorem conditional_nonneg (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) : 0 ≤ conditional p f g h := by
  classical
  have hssa := p.entropy_map_strong_subadditivity f g h
  have hd := div_le_div_of_nonneg_right hssa
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simp only [add_div] at hd
  unfold conditional entropy FiniteDistribution.entropyBits
  have hd' : entropy p (fun ω ↦ (f ω, g ω, h ω)) + entropy p h ≤
      entropy p (fun ω ↦ (f ω, h ω)) + entropy p (fun ω ↦ (g ω, h ω)) := by
    simpa only [entropy_eq_map, FiniteDistribution.entropyBits] using hd
  change 0 ≤ entropy p (fun ω ↦ (f ω, h ω)) + entropy p (fun ω ↦ (g ω, h ω)) -
    entropy p h - entropy p (fun ω ↦ (f ω, g ω, h ω))
  linarith only [hd']

@[capacity_shared_api]
theorem conditionalEntropy_conditioning_le (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    conditionalEntropy p f (fun ω ↦ (g ω, h ω)) ≤ conditionalEntropy p f h := by
  have hnonneg := conditional_nonneg p f g h
  unfold conditional conditionalEntropy at *
  linarith

@[capacity_shared_api]
theorem information_comm (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) :
    information p f g = information p g f := by
  unfold information
  rw [entropy_pair_swap p f g]
  ring

@[capacity_shared_api]
theorem information_chain_rule (p : FiniteDistribution Ω) (f : Ω → A)
    (g : Ω → B) (h : Ω → C) :
    information p f (fun ω ↦ (g ω, h ω)) =
      information p f h + conditional p f g h := by
  unfold information conditional
  ring

@[capacity_shared_api]
theorem conditional_comm (p : FiniteDistribution Ω) (f : Ω → A)
    (g : Ω → B) (h : Ω → C) :
    conditional p f g h = conditional p g f h := by
  have hswap : entropy p (fun ω ↦ (f ω, g ω, h ω)) =
      entropy p (fun ω ↦ (g ω, f ω, h ω)) := by
    rw [← entropy_pair_assoc, ← entropy_pair_assoc]
    exact (entropy_comp_injective p (fun ω ↦ ((f ω, g ω), h ω))
      (fun z ↦ ((z.1.2, z.1.1), z.2)) (by
        intro a b hab
        rcases a with ⟨⟨a₁, a₂⟩, a₃⟩
        rcases b with ⟨⟨b₁, b₂⟩, b₃⟩
        simpa only [Prod.mk.injEq, and_comm, and_left_comm, and_assoc] using hab)).symm
  unfold conditional
  rw [hswap]
  ring

@[capacity_shared_api]
theorem conditional_chain_rule (p : FiniteDistribution Ω) (f : Ω → A)
    (g : Ω → B) (h : Ω → C) (k : Ω → D) :
    conditional p f (fun ω ↦ (g ω, h ω)) k =
      conditional p f h k + conditional p f g (fun ω ↦ (h ω, k ω)) := by
  unfold conditional
  rw [entropy_pair_assoc p g h k]
  have heq : entropy p (fun ω ↦ (f ω, (g ω, h ω), k ω)) =
      entropy p (fun ω ↦ (f ω, g ω, h ω, k ω)) := by
    exact (entropy_comp_injective p (fun ω ↦ (f ω, (g ω, h ω), k ω))
      (fun z ↦ (z.1, z.2.1.1, z.2.1.2, z.2.2)) (by
        intro a b hab
        rcases a with ⟨a₁, ⟨a₂, a₃⟩, a₄⟩
        rcases b with ⟨b₁, ⟨b₂, b₃⟩, b₄⟩
        simpa only [Prod.mk.injEq, and_assoc] using hab)).symm
  rw [heq]
  ring

@[capacity_shared_api]
theorem information_joint_fst_snd (p : FiniteDistribution A) (W : FiniteChannel A B) :
    information (joint p W) Prod.fst Prod.snd = W.mutualInformationBits p := by
  classical
  have hid : (p.joint W.rowDistribution).map (fun ω ↦ ω) = p.joint W.rowDistribution := by
    ext x
    change (∑ y with y = x, (p.joint W.rowDistribution) y) = _
    rw [Finset.sum_filter]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [information, entropy_eq_map, joint, FiniteDistribution.map_fst_joint,
    FiniteDistribution.map_snd_joint, Prod.mk.eta, hid,
    FiniteDistribution.entropyBits, FiniteDistribution.entropy_joint,
    FiniteChannel.mutualInformationBits, FiniteChannel.mutualInformation,
    FiniteChannel.conditionalOutputEntropy]
  change p.entropy / Real.log 2 + (W.outputDistribution p).entropy / Real.log 2 -
    (p.entropy + ∑ a, p a * (W.rowDistribution a).entropy) / Real.log 2 = _
  ring

@[capacity_shared_api]
theorem information_independent (p : FiniteDistribution A) (q : FiniteDistribution B) :
    information (independent p q) Prod.fst Prod.snd = 0 := by
  rw [independent, information_joint_fst_snd]
  have hout : (FiniteChannel.ofRows (fun _ : A ↦ q)).outputDistribution p = q :=
    p.mixture_const q
  rw [FiniteChannel.mutualInformationBits, FiniteChannel.mutualInformation, hout]
  simp only [FiniteChannel.conditionalOutputEntropy, FiniteChannel.rowDistribution_ofRows]
  rw [← Finset.sum_mul]
  change (q.entropy - (∑ a, p.probability a) * q.entropy) / Real.log 2 = 0
  rw [p.sum_probability, one_mul, sub_self, zero_div]

@[capacity_shared_api]
theorem conditional_eq_conditionalEntropy_sub (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    conditional p f g h = conditionalEntropy p f h -
      conditionalEntropy p f (fun ω ↦ (g ω, h ω)) := by
  unfold conditional conditionalEntropy
  ring

@[capacity_shared_api]
theorem conditional_le_conditionalEntropy (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    conditional p f g h ≤ conditionalEntropy p f h := by
  rw [conditional_eq_conditionalEntropy_sub]
  exact sub_le_self _ (conditionalEntropy_nonneg p f _)

@[capacity_shared_api]
theorem conditional_information_difference (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) :
    conditional p f g h - information p f g =
      conditional p f h g - information p f h := by
  have heq : entropy p (fun ω ↦ (f ω, g ω, h ω)) =
      entropy p (fun ω ↦ (f ω, h ω, g ω)) := by
    exact (entropy_comp_injective p (fun ω ↦ (f ω, g ω, h ω))
      (fun z ↦ (z.1, z.2.2, z.2.1)) (by
        intro a b hab
        rcases a with ⟨a₁, a₂, a₃⟩
        rcases b with ⟨b₁, b₂, b₃⟩
        simpa only [Prod.mk.injEq, and_comm, and_left_comm, and_assoc] using hab)).symm
  unfold conditional information
  rw [entropy_pair_swap p g h, heq]
  ring

/-- Decodability of the public message controls the extra conditional leakage. -/
@[capacity_shared_api]
theorem conditional_le_information_add_conditionalEntropy
    (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) (h : Ω → C)
    (hindependent : information p f h = 0) :
    conditional p f g h ≤ information p f g + conditionalEntropy p h g := by
  have heq := conditional_information_difference p f g h
  have hle := conditional_le_conditionalEntropy p h f g
  rw [conditional_comm p h f g] at hle
  rw [hindependent, sub_zero] at heq
  linarith

@[capacity_shared_api]
theorem information_le_conditional_of_independent (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) (h : Ω → C) (hindependent : information p f h = 0) :
    information p f g ≤ conditional p f g h := by
  have heq := conditional_information_difference p f g h
  have hnonneg := conditional_nonneg p f h g
  rw [hindependent, sub_zero] at heq
  linarith

@[capacity_shared_api]
theorem information_le_entropy_right (p : FiniteDistribution Ω)
    (f : Ω → A) (g : Ω → B) : information p f g ≤ entropy p g := by
  have h := conditionalEntropy_nonneg p g f
  unfold conditionalEntropy at h
  rw [entropy_pair_swap p g f] at h
  unfold information
  linarith

@[capacity_shared_api]
theorem entropy_le_log_card (p : FiniteDistribution Ω) (f : Ω → A) :
    entropy p f ≤ Real.log (Fintype.card A) / Real.log 2 := by
  classical
  letI : Nonempty A := (p.map f).nonempty
  rw [entropy_eq_map, FiniteDistribution.entropyBits]
  exact div_le_div_of_nonneg_right (p.map f).entropy_le_log_card
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

@[capacity_shared_api]
theorem conditional_right_eq_of_mutual (p : FiniteDistribution Ω) (f : Ω → A)
    (g : Ω → B) (h : Ω → C) (k : Ω → D)
    (gh : B → C) (hg : C → B) (hgh : gh ∘ g = h) (hhg : hg ∘ h = g) :
    conditional p f g k = conditional p f h k := by
  have hpair : entropy p (fun ω ↦ (g ω, k ω)) =
      entropy p (fun ω ↦ (h ω, k ω)) := by
    apply entropy_eq_of_mutual p _ _ (fun z ↦ (gh z.1, z.2))
      (fun z ↦ (hg z.1, z.2))
    · funext ω
      exact Prod.ext (congrFun hgh ω) rfl
    · funext ω
      exact Prod.ext (congrFun hhg ω) rfl
  have htriple : entropy p (fun ω ↦ (f ω, g ω, k ω)) =
      entropy p (fun ω ↦ (f ω, h ω, k ω)) := by
    apply entropy_eq_of_mutual p _ _ (fun z ↦ (z.1, gh z.2.1, z.2.2))
      (fun z ↦ (z.1, hg z.2.1, z.2.2))
    · funext ω
      exact Prod.ext rfl (Prod.ext (congrFun hgh ω) rfl)
    · funext ω
      exact Prod.ext rfl (Prod.ext (congrFun hhg ω) rfl)
  simp only [conditional, hpair, htriple]

@[capacity_shared_api]
theorem conditional_comp_right_injective (p : FiniteDistribution Ω) (f : Ω → A)
    (g : Ω → B) (h : Ω → C) (k : B → D) (hk : Function.Injective k) :
    conditional p f (k ∘ g) h = conditional p f g h := by
  have hpair := entropy_comp_injective p (fun ω ↦ (g ω, h ω))
    (fun z ↦ (k z.1, z.2)) (by
      intro a b hab
      exact Prod.ext (hk (Prod.mk.inj hab).1) (Prod.mk.inj hab).2)
  have htriple := entropy_comp_injective p (fun ω ↦ (f ω, g ω, h ω))
    (fun z ↦ (z.1, k z.2.1, z.2.2)) (by
      intro a b hab
      exact Prod.ext (Prod.mk.inj hab).1
        (Prod.ext (hk (Prod.mk.inj (Prod.mk.inj hab).2).1)
          (Prod.mk.inj (Prod.mk.inj hab).2).2))
  simp only [Function.comp_def] at hpair htriple ⊢
  simp only [conditional, hpair, htriple]

/-- The entries strictly before a cut; `none` hides every other coordinate. -/
@[capacity_shared_api]
def sequencePrefix {n : ℕ} (f : Ω → Fin n → A) (i : ℕ) (ω : Ω) (j : Fin n) : Option A :=
  if j.val < i then some (f ω j) else none

/-- The entries at or after a cut. -/
@[capacity_shared_api]
def sequenceSuffix {n : ℕ} (f : Ω → Fin n → A) (i : ℕ) (ω : Ω) (j : Fin n) : Option A :=
  if i ≤ j.val then some (f ω j) else none

private def pastFuture {n : ℕ} (f : Ω → Fin n → A) (g : Ω → Fin n → B)
    (i : ℕ) (ω : Ω) := (sequencePrefix f i ω, sequenceSuffix g i ω)

private def cutContext {n : ℕ} (f : Ω → Fin n → A) (g : Ω → Fin n → B)
    (i : ℕ) (ω : Ω) := (sequencePrefix f i ω, sequenceSuffix g (i + 1) ω)

private theorem pastFuture_next_equiv {n : ℕ} (p : FiniteDistribution Ω)
    (m : Ω → C) (h : Ω → D) (f : Ω → Fin n → A) (g : Ω → Fin n → B)
    (i : Fin n) :
    conditional p m (pastFuture f g (i.val + 1)) h =
      conditional p m (fun ω ↦ (some (f ω i), cutContext f g i.val ω)) h := by
  apply conditional_right_eq_of_mutual p _ _ _ _
    (fun z ↦ (z.1 i, (fun j ↦ if j.val < i.val then z.1 j else none), z.2))
    (fun z ↦ (Function.update z.2.1 i z.1, z.2.2))
  · funext ω
    apply Prod.ext
    · simp [pastFuture, sequencePrefix]
    · apply Prod.ext
      · funext j
        dsimp [pastFuture, cutContext, sequencePrefix]
        split_ifs <;> simp_all
        omega
      · rfl
  · funext ω
    apply Prod.ext
    · funext j
      dsimp [pastFuture, cutContext, sequencePrefix]
      by_cases hji : j = i
      · subst j
        simp
      · rw [Function.update_of_ne hji]
        have hne : j.val ≠ i.val := fun heq ↦ hji (Fin.ext heq)
        have hcut : (j.val < i.val) ↔ j.val < i.val + 1 := by omega
        simp only [sequencePrefix, hcut]
    · rfl

private theorem pastFuture_prev_equiv {n : ℕ} (p : FiniteDistribution Ω)
    (m : Ω → C) (h : Ω → D) (f : Ω → Fin n → A) (g : Ω → Fin n → B)
    (i : Fin n) :
    conditional p m (pastFuture f g i.val) h =
      conditional p m (fun ω ↦ (some (g ω i), cutContext f g i.val ω)) h := by
  apply conditional_right_eq_of_mutual p _ _ _ _
    (fun z ↦ (z.2 i, z.1, (fun j ↦ if i.val + 1 ≤ j.val then z.2 j else none)))
    (fun z ↦ (z.2.1, Function.update z.2.2 i z.1))
  · funext ω
    apply Prod.ext
    · simp [pastFuture, sequenceSuffix]
    · apply Prod.ext
      · rfl
      · funext j
        dsimp [pastFuture, cutContext, sequenceSuffix]
        split_ifs <;> simp_all
        omega
  · funext ω
    apply Prod.ext
    · rfl
    · funext j
      dsimp [pastFuture, cutContext, sequenceSuffix]
      by_cases hji : j = i
      · subst j
        simp
      · rw [Function.update_of_ne hji]
        have hne : j.val ≠ i.val := fun heq ↦ hji (Fin.ext heq)
        have hcut : (i.val + 1 ≤ j.val) ↔ i.val ≤ j.val := by omega
        simp only [sequenceSuffix, hcut]

/-- Csiszár's telescoping identity for finite observations, conditioned on a public variable. -/
@[capacity_shared_api]
theorem csiszar_sum_identity {n : ℕ} (p : FiniteDistribution Ω)
    (m : Ω → C) (h : Ω → D) (f : Ω → Fin n → A) (g : Ω → Fin n → B) :
    conditional p m f h - conditional p m g h =
      ∑ i : Fin n,
        (conditional p m (fun ω ↦ f ω i)
          (fun ω ↦ ((sequencePrefix f i.val ω, sequenceSuffix g (i.val + 1) ω), h ω)) -
        conditional p m (fun ω ↦ g ω i)
          (fun ω ↦ ((sequencePrefix f i.val ω, sequenceSuffix g (i.val + 1) ω), h ω))) := by
  have hstep (i : Fin n) :
      conditional p m (pastFuture f g (i.val + 1)) h -
        conditional p m (pastFuture f g i.val) h =
      conditional p m (fun ω ↦ f ω i) (fun ω ↦ (cutContext f g i.val ω, h ω)) -
        conditional p m (fun ω ↦ g ω i) (fun ω ↦ (cutContext f g i.val ω, h ω)) := by
    rw [pastFuture_next_equiv, pastFuture_prev_equiv,
      conditional_chain_rule p m (fun ω ↦ some (f ω i)) (cutContext f g i.val) h,
      conditional_chain_rule p m (fun ω ↦ some (g ω i)) (cutContext f g i.val) h]
    have hf := conditional_comp_right_injective p m (fun ω ↦ f ω i)
      (fun ω ↦ (cutContext f g i.val ω, h ω)) some (Option.some_injective _)
    have hg := conditional_comp_right_injective p m (fun ω ↦ g ω i)
      (fun ω ↦ (cutContext f g i.val ω, h ω)) some (Option.some_injective _)
    simp only [Function.comp_def] at hf hg
    rw [hf, hg]
    ring
  have hzero : conditional p m (pastFuture f g 0) h = conditional p m g h := by
    have hinj : Function.Injective
        (fun z : Fin n → B ↦ ((fun _ : Fin n ↦ (none : Option A)), fun i ↦ some (z i))) := by
      intro a b hab
      funext i
      exact Option.some.inj (congrFun (Prod.mk.inj hab).2 i)
    have heq : pastFuture f g 0 =
        fun ω ↦ ((fun _ : Fin n ↦ (none : Option A)), fun i ↦ some (g ω i)) := by
      funext ω
      apply Prod.ext <;> funext j <;> simp [pastFuture, sequencePrefix, sequenceSuffix]
    rw [heq]
    exact conditional_comp_right_injective p m g h
      (fun z : Fin n → B ↦ ((fun _ : Fin n ↦ (none : Option A)), fun i ↦ some (z i))) hinj
  have hn : conditional p m (pastFuture f g n) h = conditional p m f h := by
    have hinj : Function.Injective
        (fun z : Fin n → A ↦ ((fun i ↦ some (z i)), fun _ : Fin n ↦ (none : Option B))) := by
      intro a b hab
      funext i
      exact Option.some.inj (congrFun (Prod.mk.inj hab).1 i)
    have heq : pastFuture f g n =
        fun ω ↦ ((fun i ↦ some (f ω i)), fun _ : Fin n ↦ (none : Option B)) := by
      funext ω
      apply Prod.ext <;> funext j <;>
        simp [pastFuture, sequencePrefix, sequenceSuffix, Nat.not_le_of_lt]
    rw [heq]
    exact conditional_comp_right_injective p m f h
      (fun z : Fin n → A ↦ ((fun i ↦ some (z i)), fun _ : Fin n ↦ (none : Option B))) hinj
  calc
    _ = conditional p m (pastFuture f g n) h - conditional p m (pastFuture f g 0) h :=
      by rw [hn, hzero]
    _ = ∑ i : Fin n, (conditional p m (pastFuture f g (i.val + 1)) h -
        conditional p m (pastFuture f g i.val) h) := by
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ conditional p m (pastFuture f g (i + 1)) h -
        conditional p m (pastFuture f g i) h)]
      exact (Finset.sum_range_sub (fun i ↦ conditional p m (pastFuture f g i) h) n).symm
    _ = _ := Finset.sum_congr rfl fun i _ ↦ hstep i

end CapacityAtlas.FiniteInformation
