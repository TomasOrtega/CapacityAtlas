/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.BlockScheme

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference.BlockScheme

variable {μ : Measure ℂ} [IsProbabilityMeasure μ] {K L : ℕ} {P : ℝ} {A : Type*}
variable [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
variable (S : BlockScheme μ K L P A)

omit [IsProbabilityMeasure μ] in
theorem concat_energy {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (m : (i : Fin K) → Fin (c i).messageCount) (H : StateBlock K n) :
    energy (S.concat h c) m H =
      ∑ s, ∑ t, ∑ i,
        ‖S.encode i ((c i).encode (m i) s) (takeStateBlocks h H s) t‖ ^ 2 := by
  classical
  let f : Fin n → ℝ := fun t => ∑ i, ‖S.concatEncode h c i (m i) H t‖ ^ 2
  have hs : ∑ t ∈ Finset.univ.image (blockPosition h), f t = ∑ t, f t := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have ht' : ¬∃ p, blockPosition h p = t := by simpa only [Finset.mem_image,
      Finset.mem_univ, true_and] using ht
    simp [f, S.concatEncode_outside h c _ _ _ t ht']
  change (∑ t, f t) = _
  rw [← hs, Finset.sum_image (fun _ _ _ _ hp => blockPosition_injective h hp)]
  simp only [f, S.concatEncode_at, Fintype.sum_prod_type]

theorem concat_ae_energy_le {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (m : (i : Fin K) → Fin (c i).messageCount) :
    ∀ᵐ H ∂stateLaw μ K n, energy (S.concat h c) m H ≤ (b * L : ℕ) * P := by
  have hblock : ∀ s : Fin b, ∀ᵐ H ∂stateLaw μ K n,
      (∑ t, ∑ i, ‖S.encode i ((c i).encode (m i) s) (takeStateBlocks h H s) t‖ ^ 2)
        ≤ (L : ℝ) * P := by
    intro s
    exact ((measurePreserving_eval (fun _ : Fin b => stateLaw μ K L) s).comp
      (measurePreserving_takeStateBlocks μ h)).quasiMeasurePreserving.ae
        (S.power (fun i => (c i).encode (m i) s))
  filter_upwards [ae_all_iff.mpr hblock] with H hH
  rw [S.concat_energy]
  calc
    _ ≤ ∑ _ : Fin b, (L : ℝ) * P := Finset.sum_le_sum fun s _ => hH s
    _ = (b * L : ℕ) * P := by simp [mul_assoc]

theorem concat_powerAdmissible {b n : ℕ} (h : b * L ≤ n) (hP : 0 ≤ P)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b) :
    PowerAdmissible μ P (S.concat h c) := by
  classical
  have hbound (m : (S.concat h c).Message) :
      ∀ᵐ H ∂stateLaw μ K n, energy (S.concat h c) m H ≤ (n : ℝ) * P :=
    (S.concat_ae_energy_le h c m).mono fun _ hm => hm.trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hP)
  have hint (m : (S.concat h c).Message) : Integrable (energy (S.concat h c) m)
      (stateLaw μ K n) := by
    refine (integrable_const ((n : ℝ) * P)).mono_nonneg ?_ ?_ (hbound m)
    · apply Measurable.aestronglyMeasurable
      unfold energy
      fun_prop
    · exact Filter.Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨hint, ?_⟩
  have hp : 0 < ∏ i, ((S.concat h c).messages i : ℝ) :=
    Finset.prod_pos fun i _ => Nat.cast_pos.mpr ((S.concat h c).messages_pos i)
  calc
    _ ≤ (∏ i, ((S.concat h c).messages i : ℝ))⁻¹ *
        ∑ _ : (S.concat h c).Message, (n : ℝ) * P := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp.le)
      apply Finset.sum_le_sum
      intro m _
      simpa only [integral_const, probReal_univ, one_smul] using
        integral_mono_ae (hint m) (integrable_const ((n : ℝ) * P)) (hbound m)
    _ = (n : ℝ) * P := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : (Fintype.card (S.concat h c).Message : ℝ) =
          ∏ i, ((S.concat h c).messages i : ℝ) := by simp [Code.Message, Fintype.card_pi]
      rw [hc, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

omit [IsProbabilityMeasure μ] in
theorem concat_observe {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (m : (i : Fin K) → Fin (c i).messageCount) (H : StateBlock K n) (z : Noise K n)
    (i : Fin K) :
    ((S.concat h c).decode i).apply (H, Interference.output (S.concat h c) m H z i) =
      (c i).decode (fun s => S.observe (fun j => (c j).encode (m j) s) i
        (takeStateBlocks h H s, takeNoiseBlocks h z s)) := by
  apply congrArg (c i).decode
  funext s
  congr 2
  funext t
  simp only [Interference.output, concat, concatEncode_at, output, takeNoiseBlocks,
    takeStateBlocks]

theorem concat_word_law {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (m : (i : Fin K) → Fin (c i).messageCount) (i : Fin K) :
    MeasurePreserving (fun hz : StateBlock K n × Noise K n =>
      fun s => S.observe (fun j => (c j).encode (m j) s) i
        (takeStateBlocks h hz.1 s, takeNoiseBlocks h hz.2 s))
      ((stateLaw μ K n).prod (blockNoise K n))
      (((S.channel i).block b).toPMF ((c i).encode (m i))).toMeasure := by
  have hrows := (measurePreserving_pi _ _ (fun s : Fin b =>
    S.observe_law (fun j => (c j).encode (m j) s) i)).comp
      (measurePreserving_takeBlocks μ h)
  have heq : (Measure.pi fun s : Fin b =>
      ((S.channel i).toPMF ((c i).encode (m i) s)).toMeasure) =
        (((S.channel i).block b).toPMF ((c i).encode (m i))).toMeasure := by
    classical
    apply Measure.ext_of_singleton
    intro y
    simp only [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _
      (measurableSet_singleton _), FiniteChannel.toPMF_apply,
      FiniteChannel.block_transition]
    exact (ENNReal.ofReal_prod_of_nonneg fun s _ => (S.channel i).nonnegative _ _).symm
  rw [← heq]
  exact hrows

theorem concat_receiver_error {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (m : (i : Fin K) → Fin (c i).messageCount) (i : Fin K) :
    (((stateLaw μ K n).prod (blockNoise K n))
      {hz | ((S.concat h c).decode i).apply
        (hz.1, Interference.output (S.concat h c) m hz.1 hz.2 i) ≠ m i}).toReal =
      (c i).toOneShotCode.errorProbability (m i) := by
  classical
  simp_rw [S.concat_observe]
  change (((stateLaw μ K n).prod (blockNoise K n))
    {hz | (c i).decode (fun s => S.observe (fun j => (c j).encode (m j) s) i
      (takeStateBlocks h hz.1 s, takeNoiseBlocks h hz.2 s)) ≠ m i}).toReal = _
  have hm := S.concat_word_law h c m i
  have he := hm.measure_preimage (s := {y | (c i).decode y ≠ m i}) (by measurability)
  change (((stateLaw μ K n).prod (blockNoise K n))
    ((fun hz => fun s => S.observe (fun j => (c j).encode (m j) s) i
      (takeStateBlocks h hz.1 s, takeNoiseBlocks h hz.2 s)) ⁻¹'
        {y | (c i).decode y ≠ m i})).toReal = _
  rw [he]
  rw [PMF.toMeasure_apply_fintype]
  rw [CapacityAtlas.OneShotCode.errorProbability_eq_sum_decode_ne]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, FiniteChannel.toPMF_apply]
  rw [ENNReal.toReal_sum (fun _ _ => by split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro y _
  change (if (c i).decode y ≠ m i then
      ENNReal.ofReal (((S.channel i).block b).transition ((c i).encode (m i)) y) else 0).toReal =
    if (c i).decode y ≠ m i then
      ((S.channel i).block b).transition ((c i).encode (m i)) y else 0
  split_ifs
  · exact ENNReal.toReal_ofReal (((S.channel i).block b).nonnegative _ _)
  · rfl

private theorem average_pi_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (M : I → Type*) [∀ i, Fintype (M i)] [∀ i, Nonempty (M i)]
    (i : I) (f : M i → ℝ) :
    (∏ j, (Fintype.card (M j) : ℝ))⁻¹ * (∑ m : (j : I) → M j, f (m i)) =
      (Fintype.card (M i) : ℝ)⁻¹ * ∑ a, f a := by
  classical
  let e := Equiv.piSplitAt i M
  have hc : (∏ j, (Fintype.card (M j) : ℝ)) =
      (Fintype.card (M i) : ℝ) *
        (Fintype.card ((j : {j // j ≠ i}) → M j) : ℝ) := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_pi, Fintype.card_prod, Nat.cast_mul, Nat.cast_prod] using
      congrArg (fun n : ℕ => (n : ℝ)) h
  have hs : (∑ m : (j : I) → M j, f (m i)) =
      (Fintype.card ((j : {j // j ≠ i}) → M j) : ℝ) * ∑ a, f a := by
    rw [← e.symm.sum_comp (fun m => f (m i)), Fintype.sum_prod_type]
    simp [e, Equiv.piSplitAt, Finset.mul_sum]
  rw [hc, hs]
  have hn : (Fintype.card ((j : {j // j ≠ i}) → M j) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem concat_error_le {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b) :
    error μ (S.concat h c) ≤ ∑ i, (c i).averageErrorProbability := by
  classical
  letI (i : Fin K) : Nonempty (Fin (c i).messageCount) :=
    Fin.pos_iff_nonempty.mp (c i).messageCount_pos
  have hmsg (m : (S.concat h c).Message) :
      (((stateLaw μ K n).prod (blockNoise K n)) (errorEvent (S.concat h c) m)).toReal ≤
        ∑ i, (c i).toOneShotCode.errorProbability (m i) := by
    unfold errorEvent
    simp only [Set.setOf_exists]
    exact (measureReal_iUnion_fintype_le _).trans_eq
      (Finset.sum_congr rfl fun i _ => S.concat_receiver_error h c m i)
  unfold error
  calc
    _ ≤ (∏ i, ((S.concat h c).messages i : ℝ))⁻¹ *
        ∑ m : (S.concat h c).Message, ∑ i, (c i).toOneShotCode.errorProbability (m i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hmsg m) (by positivity)
    _ = ∑ i, (c i).averageErrorProbability := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (∏ j, ((c j).messageCount : ℝ))⁻¹ *
        (∑ m : (j : Fin K) → Fin (c j).messageCount,
          (c i).toOneShotCode.errorProbability (m i)) = _
      have havg := average_pi_coordinate (fun j => Fin (c j).messageCount) i
        (c i).toOneShotCode.errorProbability
      simp only [Fintype.card_fin] at havg
      rw [havg]
      simpa only [Fintype.card_fin, FiniteChannel.BlockCode.averageErrorProbability] using
        (CapacityAtlas.OneShotCode.averageErrorProbability_eq (c i).toOneShotCode).symm

omit [IsProbabilityMeasure μ] in
theorem concat_rates {b n : ℕ} (h : b * L ≤ n) (hb : 0 < b)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b) (i : Fin K) :
    rates (S.concat h c) i = (b : ℝ) / n * (c i).rate := by
  unfold rates Operational.messageRate FiniteChannel.BlockCode.rate
  change Real.logb 2 ((c i).messageCount : ℝ) / n = _
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp


end CapacityAtlas.Gaussian.Interference.BlockScheme
