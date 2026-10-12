/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Basic
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.AlignmentBounds
import Mathlib.Probability.ProductMeasure

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference

def extensionLength (K n : ℕ) : ℕ := Fintype.card (Columns (Fin K) n)

theorem extensionLength_pos (K n : ℕ) : 0 < extensionLength K n := by
  rw [extensionLength, card_columns]
  have hp : 0 < (n + 1) ^ Fintype.card (Cross (Fin K)) := Nat.pow_pos (by omega)
  omega

noncomputable def slotEquiv (K n : ℕ) : Columns (Fin K) n ≃ Fin (extensionLength K n) :=
  Fintype.equivFin _

noncomputable def stateFading {K n : ℕ} (H : StateBlock K (extensionLength K n)) :
    FadingBlock (Fin K) n ℂ := fun c p ↦ H (slotEquiv K n c) p.1 p.2

noncomputable def flatState {K n : ℕ} (H : StateBlock K (extensionLength K n)) :
    Columns (Fin K) n × (Fin K × Fin K) → ℂ := fun p ↦ stateFading H p.1 p.2

theorem measurePreserving_flatState (μ : Measure ℂ) [IsProbabilityMeasure μ] (K n : ℕ) :
    MeasurePreserving (flatState (K := K) (n := n)) (stateLaw μ K (extensionLength K n))
      (Measure.pi fun _ ↦ μ) := by
  let U := Fin K
  let C := Columns U n
  have h₁ := measurePreserving_piCongrLeft
    (fun _ : Fin (extensionLength K n) ↦ Measure.pi fun _ : U ↦ Measure.pi fun _ : U ↦ μ)
    (slotEquiv K n)
  have h₂ : MeasurePreserving (MeasurableEquiv.curry U U ℂ).symm
      (Measure.pi fun _ : U ↦ Measure.pi fun _ : U ↦ μ)
      (Measure.pi fun _ : U × U ↦ μ) :=
    ⟨by fun_prop, by simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry_symm (fun _ : U ↦ fun _ : U ↦ μ)⟩
  have h₃ := measurePreserving_pi
    (fun _ : C ↦ Measure.pi fun _ : U ↦ Measure.pi fun _ : U ↦ μ)
    (fun _ : C ↦ Measure.pi fun _ : U × U ↦ μ) (fun _ ↦ h₂)
  have h₄ : MeasurePreserving (MeasurableEquiv.curry C (U × U) ℂ).symm
      (Measure.pi fun _ : C ↦ Measure.pi fun _ : U × U ↦ μ)
      (Measure.pi fun _ : C × (U × U) ↦ μ) :=
    ⟨by fun_prop, by simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry_symm (fun _ : C ↦ fun _ : U × U ↦ μ)⟩
  exact h₄.comp (h₃.comp h₁.symm)

theorem ae_stateFading_nonsingular (μ : Measure ℂ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (K n : ℕ) :
    ∀ᵐ H ∂stateLaw μ K (extensionLength K n), ∀ i : Fin K,
      (decodingMatrix (stateFading H) i).det ≠ 0 :=
  (measurePreserving_flatState μ K n).quasiMeasurePreserving.ae
    (ae_decodingMatrix_nonsingular (fun _ ↦ μ))

noncomputable def alignedTransmit {K n : ℕ} (H : StateBlock K (extensionLength K n))
    (x : Box (Fin K) n → ℂ) (t : Fin (extensionLength K n)) : ℂ :=
  transmitted (stateFading H) x ((slotEquiv K n).symm t)

theorem alignedTransmit_current {K n : ℕ} (H : StateBlock K (extensionLength K n))
    (x : Box (Fin K) n → ℂ) (t : Fin (extensionLength K n)) :
    alignedTransmit H x t = ∑ a, beam (fun p : Fin K × Fin K ↦ H t p.1 p.2) a * x a := by
  unfold alignedTransmit transmitted stateFading
  simp only [Equiv.apply_symm_apply]

theorem alignedTransmit_causal {K n : ℕ} (H H' : StateBlock K (extensionLength K n))
    (x : Box (Fin K) n → ℂ) (t : Fin (extensionLength K n)) (hh : H t = H' t) :
    alignedTransmit H x t = alignedTransmit H' x t := by
  simp only [alignedTransmit_current, hh]

theorem measurable_alignedTransmit {K n : ℕ} (x : Box (Fin K) n → ℂ)
    (t : Fin (extensionLength K n)) :
    Measurable (fun H : StateBlock K (extensionLength K n) ↦ alignedTransmit H x t) := by
  simp only [alignedTransmit_current, beam]
  fun_prop

theorem norm_alignedTransmit_le {K n : ℕ} (H : StateBlock K (extensionLength K n))
    (M Q : ℝ) (hh : ∀ t i j, ‖H t i j‖ ≤ M) (x : Box (Fin K) n → ℂ)
    (hx : ∀ a, ‖x a‖ ≤ Q) (t : Fin (extensionLength K n)) :
    ‖alignedTransmit H x t‖ ≤ Fintype.card (Box (Fin K) n) * beamBound (Fin K) n M * Q :=
  norm_transmitted_le (stateFading H) M Q (fun _ _ ↦ hh _ _ _) x hx _

noncomputable def alignedDecode {K n : ℕ} (H : StateBlock K (extensionLength K n))
    (i : Fin K) (y : Fin (extensionLength K n) → ℂ) : Box (Fin K) n → ℂ :=
  decoder (stateFading H) i (fun c ↦ y (slotEquiv K n c))

theorem measurable_alignedDecode {K n : ℕ} (i : Fin K) (a : Box (Fin K) n) :
    Measurable (fun hy : StateBlock K (extensionLength K n) ×
      (Fin (extensionLength K n) → ℂ) ↦ alignedDecode hy.1 i hy.2 a) := by
  unfold alignedDecode
  have hm : Measurable (fun hy : StateBlock K (extensionLength K n) ×
      (Fin (extensionLength K n) → ℂ) ↦
      (stateFading hy.1, fun c ↦ hy.2 (slotEquiv K n c))) := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro c
      apply measurable_pi_lambda
      intro p
      exact (measurable_pi_apply p.2).comp ((measurable_pi_apply p.1).comp
        ((measurable_pi_apply (slotEquiv K n c)).comp measurable_fst))
    · apply measurable_pi_lambda
      intro c
      exact (measurable_pi_apply (slotEquiv K n c)).comp measurable_snd
  have hc := (measurable_decoder_apply (U := Fin K) (n := n) i a).comp hm
  exact hc

theorem alignedDecode_signal_add_noise {K n : ℕ} (H : StateBlock K (extensionLength K n))
    (i : Fin K) (hi : (decodingMatrix (stateFading H) i).det ≠ 0)
    (x : Fin K → Box (Fin K) n → ℂ) (z : Fin (extensionLength K n) → ℂ) :
    alignedDecode H i (fun t ↦ (∑ j, H t i j * alignedTransmit H (x j) t) + z t) =
      x i + alignedDecode H i z := by
  unfold alignedDecode
  have he : (fun c ↦ (∑ j, H (slotEquiv K n c) i j *
      alignedTransmit H (x j) (slotEquiv K n c)) + z (slotEquiv K n c)) =
      received (stateFading H) x i + fun c ↦ z (slotEquiv K n c) := by
    ext c
    simp [received, stateFading, alignedTransmit]
  rw [he]
  exact decoder_received_add_noise _ i hi x _

end CapacityAtlas.Gaussian.Interference
