/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.BlockSampling
import CapacityAtlasForMathlib.InformationTheory.FiniteChannel.PMF
import CapacityAtlasForMathlib.InformationTheory.RandomCoding

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference

structure BlockScheme (μ : Measure ℂ) (K L : ℕ) (P : ℝ) (A : Type*)
    [Fintype A] [MeasurableSpace A] where
  encode : Fin K → A → StateBlock K L → Fin L → ℂ
  encode_measurable : ∀ i a t, Measurable fun H => encode i a H t
  encode_causal : ∀ i a t H H', (∀ s, s ≤ t → H s = H' s) →
    encode i a H t = encode i a H' t
  decode : Fin K → (StateBlock K L × (Fin L → ℂ)) → A
  decode_measurable : ∀ i, Measurable (decode i)
  channel : Fin K → FiniteChannel A A
  row_law : ∀ (a : Fin K → A) i b,
    ((stateLaw μ K L).prod (blockNoise K L))
      {hz | decode i (hz.1, fun t =>
        (∑ j, hz.1 t i j * encode j (a j) hz.1 t) + complexNoise (hz.2 i t)) = b} =
      ENNReal.ofReal ((channel i).transition (a i) b)
  power : ∀ a : Fin K → A, ∀ᵐ H ∂stateLaw μ K L,
    (∑ t, ∑ i, ‖encode i (a i) H t‖ ^ 2) ≤ (L : ℝ) * P

namespace BlockScheme

variable {μ : Measure ℂ} {K L : ℕ} {P : ℝ} {A : Type*}
variable [Fintype A] [MeasurableSpace A]
variable (S : BlockScheme μ K L P A)

def output (a : Fin K → A) (H : StateBlock K L) (z : Noise K L)
    (i : Fin K) : Fin L → ℂ :=
  fun t => (∑ j, H t i j * S.encode j (a j) H t) + complexNoise (z i t)

@[fun_prop]
theorem measurable_output (a : Fin K → A) (i : Fin K) :
    Measurable fun hz : StateBlock K L × Noise K L => S.output a hz.1 hz.2 i := by
  apply measurable_pi_lambda
  intro t
  apply Measurable.add
  · apply Finset.measurable_sum
    intro j _
    exact (by fun_prop : Measurable fun hz : StateBlock K L × Noise K L => hz.1 t i j).mul
      ((S.encode_measurable j (a j) t).comp measurable_fst)
  · unfold complexNoise
    fun_prop

def observe (a : Fin K → A) (i : Fin K) (hz : StateBlock K L × Noise K L) : A :=
  S.decode i (hz.1, S.output a hz.1 hz.2 i)

@[fun_prop]
theorem measurable_observe (a : Fin K → A) (i : Fin K) : Measurable (S.observe a i) :=
  (S.decode_measurable i).comp (measurable_fst.prodMk (S.measurable_output a i))

theorem observe_law [MeasurableSingletonClass A] (a : Fin K → A) (i : Fin K) :
    MeasurePreserving (S.observe a i) ((stateLaw μ K L).prod (blockNoise K L))
      ((S.channel i).toPMF (a i)).toMeasure := by
  classical
  refine ⟨S.measurable_observe a i, ?_⟩
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (S.measurable_observe a i) (measurableSet_singleton b)]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  exact S.row_law a i b

noncomputable def concatEncode {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (i : Fin K) (m : Fin (c i).messageCount) (H : StateBlock K n) : Fin n → ℂ :=
  Function.extend (blockPosition h)
    (fun p => S.encode i ((c i).encode m p.1) (takeStateBlocks h H p.1) p.2) 0

theorem concatEncode_at {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (i : Fin K) (m : Fin (c i).messageCount) (H : StateBlock K n) (p : Fin b × Fin L) :
    S.concatEncode h c i m H (blockPosition h p) =
      S.encode i ((c i).encode m p.1) (takeStateBlocks h H p.1) p.2 :=
  (blockPosition_injective h).extend_apply _ _ _

theorem concatEncode_outside {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (i : Fin K) (m : Fin (c i).messageCount) (H : StateBlock K n) (t : Fin n)
    (ht : ¬∃ p, blockPosition h p = t) : S.concatEncode h c i m H t = 0 :=
  Function.extend_apply' _ _ _ ht

@[fun_prop]
theorem measurable_concatEncode {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (i : Fin K) (m : Fin (c i).messageCount) (t : Fin n) :
    Measurable fun H => S.concatEncode h c i m H t := by
  by_cases ht : ∃ p, blockPosition h p = t
  · obtain ⟨p, rfl⟩ := ht
    simp only [S.concatEncode_at]
    exact (S.encode_measurable i ((c i).encode m p.1) p.2).comp (by
      unfold takeStateBlocks
      fun_prop)
  · simp only [S.concatEncode_outside h c i m _ t ht]
    exact measurable_const

theorem concatEncode_causal {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b)
    (i : Fin K) (m : Fin (c i).messageCount) (t : Fin n) (H H' : StateBlock K n)
    (hh : ∀ s, s ≤ t → H s = H' s) :
    S.concatEncode h c i m H t = S.concatEncode h c i m H' t := by
  by_cases ht : ∃ p, blockPosition h p = t
  · obtain ⟨p, rfl⟩ := ht
    simp only [S.concatEncode_at]
    apply S.encode_causal
    intro s hs
    apply hh
    change s.val + L * p.1.val ≤ p.2.val + L * p.1.val
    exact Nat.add_le_add_right hs _
  · rw [S.concatEncode_outside h c i m H t ht, S.concatEncode_outside h c i m H' t ht]

noncomputable def concat [MeasurableSingletonClass A] {b n : ℕ} (h : b * L ≤ n)
    (c : ∀ i, FiniteChannel.BlockCode (S.channel i) b) : Code K n where
  messages i := (c i).messageCount
  messages_pos i := (c i).messageCount_pos
  encode := S.concatEncode h c
  encode_measurable := S.measurable_concatEncode h c
  encode_causal := S.concatEncode_causal h c
  decode i :=
    { apply := fun hy => (c i).decode fun s => S.decode i
        (takeStateBlocks h hy.1 s, fun t => hy.2 (blockPosition h (s, t)))
      measurable_fiber := fun m => by
        apply (measurableSet_singleton m).preimage
        apply (measurable_of_countable (c i).decode).comp
        apply measurable_pi_lambda
        intro s
        apply (S.decode_measurable i).comp
        unfold takeStateBlocks
        fun_prop }

end BlockScheme

end CapacityAtlas.Gaussian.Interference
