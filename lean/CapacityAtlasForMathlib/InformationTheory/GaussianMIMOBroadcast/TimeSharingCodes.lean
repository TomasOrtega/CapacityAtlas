/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Information
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MeasureTheory

lemma measurePreserving_pi_precomp_injective {I J E : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (f : I → J) (hf : Function.Injective f) :
    MeasurePreserving (fun x : J → E ↦ x ∘ f)
      (Measure.pi (fun _ : J ↦ μ)) (Measure.pi (fun _ : I ↦ μ)) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  have hi : iIndepFun (fun j (x : J → E) ↦ x j) (Measure.pi (fun _ : J ↦ μ)) :=
    iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)
  have hp := (hi.precomp hf).map_fun_eq_pi_map (fun i ↦ (measurable_pi_apply (f i)).aemeasurable)
  simpa only [Function.comp_def, (measurePreserving_eval (fun _ : J ↦ μ) (f _)).map_eq] using hp

end MeasureTheory

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n q : ℕ} {rx : Fin K → ℕ}

/-- Splitting every receiver's product message preserves the full uniform tuple. -/
def concatMessageEquiv (c : Code K tx rx n) (d : Code K tx rx q) :
    ((i : Fin K) → Fin (c.messages i * d.messages i)) ≃ MessageTuple c × MessageTuple d where
  toFun m := (fun i ↦ (finProdFinEquiv.symm (m i)).1, fun i ↦ (finProdFinEquiv.symm (m i)).2)
  invFun p i := finProdFinEquiv (p.1 i, p.2 i)
  left_inv m := by
    funext i
    exact finProdFinEquiv.apply_symm_apply (m i)
  right_inv p := by
    apply Prod.ext <;> funext i <;> simp

noncomputable def Code.concat (c : Code K tx rx n) (d : Code K tx rx q) : Code K tx rx (n + q) where
  messages i := c.messages i * d.messages i
  messages_pos i := Nat.mul_pos (c.messages_pos i) (d.messages_pos i)
  encode m := Fin.append (c.encode ((concatMessageEquiv c d m).1))
    (d.encode ((concatMessageEquiv c d m).2))
  decode i := {
    apply := fun y ↦ finProdFinEquiv ((c.decode i).apply (fun s ↦ y (Fin.castAdd q s)),
      (d.decode i).apply (fun s ↦ y (Fin.natAdd n s)))
    measurable_fiber := fun a ↦ by
      have hm : Measurable (fun y : Fin (n + q) → EuclideanSpace ℝ (Fin (rx i)) ↦
          finProdFinEquiv ((c.decode i).apply (fun s ↦ y (Fin.castAdd q s)),
            (d.decode i).apply (fun s ↦ y (Fin.natAdd n s)))) :=
        (measurable_of_finite finProdFinEquiv).comp
          (((decoder_measurable (c.decode i)).comp (by fun_prop)).prodMk
            ((decoder_measurable (d.decode i)).comp (by fun_prop)))
      exact hm (measurableSet_singleton a) }

lemma blockNoise_precomp
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (f : Fin n → Fin q) (hf : Function.Injective f) :
    MeasurePreserving (fun z : (i : Fin K) → Fin q → EuclideanSpace ℝ (Fin (rx i)) ↦
      fun i s ↦ z i (f s)) (blockNoise N q) (blockNoise N n) := by
  exact measurePreserving_pi _ _ (fun i ↦
    measurePreserving_pi_precomp_injective (multivariateGaussian 0 (N i)) f hf)

lemma concat_output_left
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (c : Code K tx rx n) (d : Code K tx rx q) (m : MessageTuple (c.concat d))
    (z : (i : Fin K) → Fin (n + q) → EuclideanSpace ℝ (Fin (rx i))) (i : Fin K) :
    (fun s ↦ output H ((c.concat d).encode m) z i (Fin.castAdd q s)) =
      output H (c.encode (concatMessageEquiv c d m).1)
        (fun i s ↦ z i (Fin.castAdd q s)) i := by
  funext s
  simp only [output, Code.concat, Fin.append_left]

lemma concat_output_right
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (c : Code K tx rx n) (d : Code K tx rx q) (m : MessageTuple (c.concat d))
    (z : (i : Fin K) → Fin (n + q) → EuclideanSpace ℝ (Fin (rx i))) (i : Fin K) :
    (fun s ↦ output H ((c.concat d).encode m) z i (Fin.natAdd n s)) =
      output H (d.encode (concatMessageEquiv c d m).2)
        (fun i s ↦ z i (Fin.natAdd n s)) i := by
  funext s
  simp only [output, Code.concat, Fin.append_right]

lemma sum_concat_messages (c : Code K tx rx n) (d : Code K tx rx q)
    (f : MessageTuple c × MessageTuple d → ℝ) :
    (∑ m : MessageTuple (c.concat d), f (concatMessageEquiv c d m)) = ∑ p, f p :=
  (concatMessageEquiv c d).sum_comp f

lemma average_concat_messages_add (c : Code K tx rx n) (d : Code K tx rx q)
    (f : MessageTuple c → ℝ) (g : MessageTuple d → ℝ) :
    (∏ i, ((c.concat d).messages i : ℝ))⁻¹ *
      ∑ m : MessageTuple (c.concat d), (f (concatMessageEquiv c d m).1 + g (concatMessageEquiv c d m).2) =
      (∏ i, (c.messages i : ℝ))⁻¹ * ∑ m, f m +
        (∏ i, (d.messages i : ℝ))⁻¹ * ∑ m, g m := by
  rw [sum_concat_messages c d (fun p ↦ f p.1 + g p.2), Fintype.sum_prod_type]
  simp only [Code.concat, Nat.cast_mul, Finset.prod_mul_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_messages]
  rw [← Finset.mul_sum]
  field_simp [(messageCountProduct_pos c).ne', (messageCountProduct_pos d).ne']

lemma concat_energy (c : Code K tx rx n) (d : Code K tx rx q) (m : MessageTuple (c.concat d)) :
    (∑ s, ∑ a, ((c.concat d).encode m s a) ^ 2) =
      (∑ s, ∑ a, (c.encode (concatMessageEquiv c d m).1 s a) ^ 2) +
        ∑ s, ∑ a, (d.encode (concatMessageEquiv c d m).2 s a) ^ 2 := by
  rw [Fin.sum_univ_add]
  simp only [Code.concat, Fin.append_left, Fin.append_right]

theorem Code.concat_powerAdmissible (c : Code K tx rx n) (d : Code K tx rx q) {P : ℝ}
    (hc : PowerAdmissible P c) (hd : PowerAdmissible P d) : PowerAdmissible P (c.concat d) := by
  unfold PowerAdmissible at hc hd ⊢
  simp_rw [concat_energy]
  have havg := average_concat_messages_add c d
    (fun m ↦ ∑ s, ∑ a, (c.encode m s a) ^ 2) (fun m ↦ ∑ s, ∑ a, (d.encode m s a) ^ 2)
  rw [havg, Nat.cast_add, add_mul]
  exact add_le_add hc hd

lemma concat_errorEvent_subset
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (c : Code K tx rx n) (d : Code K tx rx q) (m : MessageTuple (c.concat d)) :
    errorEvent H (c.concat d) m ⊆
      (fun z i s ↦ z i (Fin.castAdd q s)) ⁻¹' errorEvent H c (concatMessageEquiv c d m).1 ∪
      (fun z i s ↦ z i (Fin.natAdd n s)) ⁻¹' errorEvent H d (concatMessageEquiv c d m).2 := by
  intro z hz
  by_contra h
  have hleft : ∀ i, (c.decode i).apply
      (output H (c.encode (concatMessageEquiv c d m).1) (fun i s ↦ z i (Fin.castAdd q s)) i) =
        (concatMessageEquiv c d m).1 i := by
    simpa only [Set.mem_union, Set.mem_preimage, not_or, errorEvent, Set.mem_setOf_eq,
      not_exists, not_not] using (not_or.mp h).1
  have hright : ∀ i, (d.decode i).apply
      (output H (d.encode (concatMessageEquiv c d m).2) (fun i s ↦ z i (Fin.natAdd n s)) i) =
        (concatMessageEquiv c d m).2 i := by
    simpa only [Set.mem_preimage, errorEvent, Set.mem_setOf_eq, not_exists, not_not] using (not_or.mp h).2
  obtain ⟨i, hi⟩ := hz
  apply hi
  change finProdFinEquiv ((c.decode i).apply _, (d.decode i).apply _) = m i
  rw [concat_output_left, concat_output_right, hleft, hright]
  exact finProdFinEquiv.apply_symm_apply (m i)

lemma concat_conditional_error_le
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (d : Code K tx rx q) (m : MessageTuple (c.concat d)) :
    (blockNoise N (n + q)).real (errorEvent H (c.concat d) m) ≤
      (blockNoise N n).real (errorEvent H c (concatMessageEquiv c d m).1) +
        (blockNoise N q).real (errorEvent H d (concatMessageEquiv c d m).2) := by
  have hl := blockNoise_precomp N (Fin.castAdd q) (Fin.castAdd_injective n q)
  have hr := blockNoise_precomp N (Fin.natAdd n : Fin q → Fin (n + q)) (by
    intro a b h
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)))
  have hml : (blockNoise N (n + q)).real
      ((fun z i s ↦ z i (Fin.castAdd q s)) ⁻¹' errorEvent H c (concatMessageEquiv c d m).1) =
        (blockNoise N n).real (errorEvent H c (concatMessageEquiv c d m).1) := by
    simp only [Measure.real]
    rw [← hl.map_eq, Measure.map_apply hl.measurable
      (measurableSet_errorEvent H c (concatMessageEquiv c d m).1)]
  have hmr : (blockNoise N (n + q)).real
      ((fun z i s ↦ z i (Fin.natAdd n s)) ⁻¹' errorEvent H d (concatMessageEquiv c d m).2) =
        (blockNoise N q).real (errorEvent H d (concatMessageEquiv c d m).2) := by
    simp only [Measure.real]
    rw [← hr.map_eq, Measure.map_apply hr.measurable
      (measurableSet_errorEvent H d (concatMessageEquiv c d m).2)]
  exact (measureReal_mono (concat_errorEvent_subset H c d m)).trans
    ((measureReal_union_le _ _).trans_eq (congrArg₂ (· + ·) hml hmr))

theorem Code.concat_error_le
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (d : Code K tx rx q) :
    error H N (c.concat d) ≤ error H N c + error H N d := by
  unfold error
  calc
    _ ≤ (∏ i, ((c.concat d).messages i : ℝ))⁻¹ * ∑ m : MessageTuple (c.concat d),
        ((blockNoise N n).real (errorEvent H c (concatMessageEquiv c d m).1) +
          (blockNoise N q).real (errorEvent H d (concatMessageEquiv c d m).2)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (messageCountProduct_pos (c.concat d)).le)
      exact Finset.sum_le_sum (fun m _ ↦ concat_conditional_error_le H N c d m)
    _ = _ := average_concat_messages_add c d
      (fun m ↦ (blockNoise N n).real (errorEvent H c m))
      (fun m ↦ (blockNoise N q).real (errorEvent H d m))

theorem Code.concat_rates (c : Code K tx rx n) (d : Code K tx rx q)
    (hn : 0 < n) (hq : 0 < q) (i : Fin K) :
    rates (c.concat d) i = (n : ℝ) / (n + q) * rates c i + (q : ℝ) / (n + q) * rates d i := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  unfold rates Operational.messageRate Real.logb
  simp only [Code.concat, Nat.cast_mul, Nat.cast_add]
  rw [Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (c.messages_pos i)))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (d.messages_pos i)))]
  field_simp

end CapacityAtlas.Gaussian.MIMOBroadcast
