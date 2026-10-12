/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.SequencePacking
import Mathlib.Probability.ProductMeasure

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical BigOperators

namespace CapacityAtlas.MeasureBinning

theorem sequenceSuccess_readback {S : Type*} {V : ℕ → Type*}
    (initial : S) (next : (i : ℕ) → S × V i → S) (A : (i : ℕ) → Set (S × V i))
    (P : (i : ℕ) → S → V i → Prop) (n : ℕ)
    (hOwn : ∀ i, i < n → ∀ s v, (s, v) ∈ A i → P i (next i (s, v)) v)
    (hLater : ∀ i j, i < j → j < n → ∀ s v w, P i s v → P i (next j (s, w)) v)
    (samples : SequenceSamples V n) (hs : samples ∈ sequenceSuccess initial next A n) :
    ∀ i : Fin n, P i.val (sequenceState initial next n samples) (sequenceSampleAt n samples i) := by
  induction n with
  | zero => exact fun i ↦ Fin.elim0 i
  | succ n ih =>
      intro i
      induction i using Fin.lastCases with
      | last =>
          simp only [sequenceSampleAt_last, Fin.val_last, sequenceState]
          exact hOwn n (Nat.lt_succ_self n) _ _ hs.2
      | cast i =>
          simp only [sequenceSampleAt_castSucc, Fin.val_castSucc, sequenceState]
          exact hLater i.val n i.isLt (Nat.lt_succ_self n) _ _ _
            (ih (fun j hj ↦ hOwn j (Nat.lt_succ_of_lt hj))
              (fun j k hjk hk ↦ hLater j k hjk (Nat.lt_succ_of_lt hk)) samples.1 hs.1 i)

theorem updateKernel_comp_apply {S U : Type*} [MeasurableSpace S] [MeasurableSpace U]
    (σ : Measure S) [SFinite σ] (η : Kernel S U) [IsSFiniteKernel η]
    {update : S × U → S} (hu : Measurable update) {E : Set S} (hE : MeasurableSet E) :
    (updateKernel η hu ∘ₘ σ) E = (σ ⊗ₘ η) (update ⁻¹' E) := by
  rw [Measure.bind_apply hE (Kernel.aemeasurable _), Measure.compProd_apply (hu hE)]
  apply lintegral_congr
  intro s
  rw [updateKernel_apply, Measure.map_apply
    (show Measurable (fun u ↦ update (s, u)) from hu.comp measurable_prodMk_left) hE]
  rfl

theorem sampledKernel_univ_apply_invariant {S V : Type*}
    [MeasurableSpace S] [MeasurableSpace V] (ν : Measure V) [IsProbabilityMeasure ν]
    {next : S × V → S} (hn : Measurable next) {E : Set S} (hE : MeasurableSet E)
    (hInv : ∀ s v, next (s, v) ∈ E ↔ s ∈ E) (s : S) :
    sampledKernel ν MeasurableSet.univ hn s E = E.indicator (fun _ ↦ 1) s := by
  rw [sampledKernel_apply ν MeasurableSet.univ hn s hE]
  simp only [Set.mem_univ, true_and, hInv]
  by_cases hs : s ∈ E <;> simp [hs]

theorem sequenceReferenceLaw_apply_eq_of_invariant {S : Type*} [MeasurableSpace S]
    (κ : ℕ → Kernel S S) (initial : S) {E : Set S} (hE : MeasurableSet E)
    {m n : ℕ} (hmn : m ≤ n)
    (hInv : ∀ i, m ≤ i → i < n → ∀ s, κ i s E = E.indicator (fun _ ↦ 1) s) :
    sequenceReferenceLaw κ initial n E = sequenceReferenceLaw κ initial m E := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [sequenceReferenceLaw, Measure.bind_apply hE (Kernel.aemeasurable _)]
      simp_rw [hInv n hmn (Nat.lt_succ_self n), lintegral_indicator hE]
      simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
      exact ih (fun i hmi hin ↦ hInv i hmi (Nat.lt_succ_of_lt hin))

theorem measurePreserving_pi_transpose {I J V : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace V] (μ : I → J → Measure V) [∀ i j, IsProbabilityMeasure (μ i j)] :
    MeasurePreserving (fun x : I → J → V ↦ fun j i ↦ x i j)
      (Measure.pi (fun i ↦ Measure.pi (μ i)))
      (Measure.pi (fun j ↦ Measure.pi (fun i ↦ μ i j))) := by
  have h₁ : MeasurePreserving (MeasurableEquiv.curry I J V).symm
      (Measure.pi (fun i ↦ Measure.pi (μ i)))
      (Measure.pi (fun p : I × J ↦ μ p.1 p.2)) :=
    ⟨by fun_prop, by simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry_symm μ⟩
  have h₂ := measurePreserving_piCongrLeft (fun p : J × I ↦ μ p.2 p.1)
    (Equiv.prodComm I J)
  have h₃ : MeasurePreserving (MeasurableEquiv.curry J I V)
      (Measure.pi (fun p : J × I ↦ μ p.2 p.1))
      (Measure.pi (fun j ↦ Measure.pi (fun i ↦ μ i j))) :=
    ⟨by fun_prop, by simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun j i ↦ μ i j)⟩
  exact h₃.comp (h₂.comp h₁)

theorem measurePreserving_sequenceSampleTuple {V : Type*} [MeasurableSpace V]
    (ν : ℕ → Measure V) [∀ n, IsProbabilityMeasure (ν n)] (n : ℕ) :
    MeasurePreserving (sequenceSampleAt (V := fun _ ↦ V) n) (sequenceSampleLaw ν n)
      (Measure.pi (fun i : Fin n ↦ ν i.val)) := by
  refine ⟨measurable_pi_lambda _ (measurable_sequenceSampleAt n), ?_⟩
  induction n with
  | zero =>
      apply (Measure.pi_eq _).symm
      intro E hE
      have heq : univ.pi E = univ := by ext x; simp
      rw [heq, Measure.map_apply (measurable_pi_lambda _ (measurable_sequenceSampleAt 0))
        MeasurableSet.univ]
      simp [sequenceSampleLaw]
  | succ n ih =>
      apply (Measure.pi_eq _).symm
      intro E hE
      have hrect : sequenceSampleAt (V := fun _ ↦ V) (n + 1) ⁻¹' univ.pi E =
          (sequenceSampleAt n ⁻¹' univ.pi (fun i : Fin n ↦ E i.castSucc)) ×ˢ E (Fin.last n) := by
        ext samples
        rcases samples with ⟨prior, latest⟩
        simp only [mem_preimage, mem_univ_pi, mem_prod, Fin.forall_iff_castSucc,
          sequenceSampleAt_last, sequenceSampleAt_castSucc, and_comm]
      rw [Measure.map_apply (measurable_pi_lambda _ (measurable_sequenceSampleAt (n + 1)))
        (MeasurableSet.univ_pi hE), hrect]
      change ((sequenceSampleLaw ν n).prod (ν n)) _ = _
      rw [Measure.prod_prod,
        ← Measure.map_apply (measurable_pi_lambda _ (measurable_sequenceSampleAt n))
          (MeasurableSet.univ_pi (fun i ↦ hE i.castSucc)), ih, Measure.pi_pi,
        Fin.prod_univ_castSucc]
      rfl

variable {S : Type*} [MeasurableSpace S]

omit [MeasurableSpace S] in
theorem sequenceSuccess_univ {V : ℕ → Type*} (initial : S)
    (next : (n : ℕ) → S × V n → S) (n : ℕ) :
    sequenceSuccess initial next (fun _ ↦ univ) n = univ := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sequenceSuccess, ih]

theorem sequenceReferenceLaw_sampled {V : ℕ → Type*} [∀ n, MeasurableSpace (V n)]
    (ν : (n : ℕ) → Measure (V n)) [∀ n, IsProbabilityMeasure (ν n)]
    (initial : S) {next : (n : ℕ) → S × V n → S} (hnext : ∀ n, Measurable (next n)) (n : ℕ) :
    sequenceReferenceLaw (fun i ↦ sampledKernel (ν i) MeasurableSet.univ (hnext i)) initial n =
      (sequenceSampleLaw ν n).map (sequenceState initial next n) := by
  have heq : ∀ n, sequenceReferenceLaw
        (fun i ↦ sampledKernel (ν i) MeasurableSet.univ (hnext i)) initial n =
          sequenceSuccessLaw ν initial next (fun _ ↦ univ) n := by
    intro n
    induction n with
    | zero => rw [sequenceSuccessLaw_zero]; rfl
    | succ n ih =>
        rw [sequenceReferenceLaw, ih, sequenceSuccessLaw_succ ν initial hnext
          (fun _ ↦ MeasurableSet.univ)]
  rw [heq, sequenceSuccessLaw, sequenceSuccess_univ, Measure.restrict_univ]

omit [MeasurableSpace S] in
theorem sequenceState_update_coordinate {I V : Type*} [DecidableEq I]
    (initial : I → V) (order : ℕ → I) (n : ℕ)
    (hinj : Function.Injective (fun i : Fin n ↦ order i.val))
    (samples : SequenceSamples (fun _ ↦ V) n) (i : Fin n) :
    sequenceState initial (fun k p ↦ Function.update p.1 (order k) p.2) n samples (order i.val) =
      sequenceSampleAt n samples i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      induction i using Fin.lastCases with
      | last => simp [sequenceState]
      | cast i =>
          have hne : order i.val ≠ order n := by
            intro h
            have heq := congrArg Fin.val (hinj (a₁ := i.castSucc) (a₂ := Fin.last n) h)
            simp only [Fin.val_castSucc, Fin.val_last] at heq
            exact (Nat.ne_of_lt i.isLt) heq
          simp only [sequenceState, Fin.val_castSucc, Function.update_of_ne hne,
            sequenceSampleAt_castSucc]
          apply ih
          intro a b hab
          exact Fin.castSucc_injective n (hinj (a₁ := a.castSucc) (a₂ := b.castSucc) hab)

theorem sequenceState_update_map_pi {I V : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace V] (initial : I → V) (order : ℕ → I)
    (ν : ℕ → Measure V) [∀ i, IsProbabilityMeasure (ν i)]
    (μ : I → Measure V) [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ) (e : Fin n ≃ I)
    (horder : ∀ i : Fin n, order i.val = e i) (hν : ∀ i : Fin n, ν i.val = μ (e i)) :
    (sequenceSampleLaw ν n).map
      (sequenceState initial (fun k p ↦ Function.update p.1 (order k) p.2) n) = Measure.pi μ := by
  have hinj : Function.Injective (fun i : Fin n ↦ order i.val) := by
    intro i j h
    apply e.injective
    simpa only [horder] using h
  have heq : sequenceState initial (fun k p ↦ Function.update p.1 (order k) p.2) n =
      (MeasurableEquiv.piCongrLeft (fun _ : I ↦ V) e) ∘ sequenceSampleAt n := by
    funext samples j
    obtain ⟨i, rfl⟩ := e.surjective j
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
    simpa only [horder] using sequenceState_update_coordinate initial order n hinj samples i
  rw [heq, ← Measure.map_map (MeasurableEquiv.piCongrLeft (fun _ : I ↦ V) e).measurable
    (measurable_pi_lambda _ (measurable_sequenceSampleAt n)),
    (measurePreserving_sequenceSampleTuple ν n).map_eq]
  have hmeasures : (fun i : Fin n ↦ ν i.val) = (fun i : Fin n ↦ μ (e i)) := funext hν
  rw [hmeasures]
  exact (measurePreserving_piCongrLeft μ e).map_eq

end CapacityAtlas.MeasureBinning
