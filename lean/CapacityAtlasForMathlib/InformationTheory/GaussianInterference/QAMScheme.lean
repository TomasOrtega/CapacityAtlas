/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.AlignmentChannel
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.BlockScheme
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.FiniteObservation
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.NoiseTail

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference

noncomputable section

abbrev StreamAlphabet (K n q : ℕ) := Box (Fin K) n → QAM q

abbrev Environment (K n : ℕ) :=
  StateBlock K (extensionLength K n) × Noise K (extensionLength K n)

def environmentLaw (μ : Measure ℂ) (K n : ℕ) : Measure (Environment K n) :=
  (stateLaw μ K (extensionLength K n)).prod (blockNoise K (extensionLength K n))

instance environmentLaw_probability (μ : Measure ℂ) [IsProbabilityMeasure μ] (K n : ℕ) :
    IsProbabilityMeasure (environmentLaw μ K n) := by
  unfold environmentLaw
  infer_instance

def effectiveNoise {K n : ℕ} (i : Fin K) (hz : Environment K n) : Box (Fin K) n → ℂ :=
  alignedDecode hz.1 i (fun t => complexNoise (hz.2 i t))

theorem measurable_effectiveNoise {K n : ℕ} (i : Fin K) (a : Box (Fin K) n) :
    Measurable fun hz : Environment K n => effectiveNoise i hz a := by
  unfold effectiveNoise
  have hn : Measurable fun z : Noise K (extensionLength K n) =>
      fun t => complexNoise (z i t) := by
    unfold complexNoise
    fun_prop
  have hc := (measurable_alignedDecode i a).comp
    (measurable_fst.prodMk (hn.comp measurable_snd))
  exact hc

def qamStreams {K n q : ℕ} (δ : ℝ) (a : StreamAlphabet K n q) : Box (Fin K) n → ℂ :=
  fun s => (δ : ℂ) * qamValue (a s)

def qamObserve {K n q : ℕ} (hq : 0 < q) (δ : ℝ) (i : Fin K)
    (a : StreamAlphabet K n q) (hz : Environment K n) : StreamAlphabet K n q :=
  fun s => quantizeComplex q hq δ (qamStreams δ a s + effectiveNoise i hz s)

theorem measurable_qamObserve {K n q : ℕ} (hq : 0 < q) (δ : ℝ) (i : Fin K)
    (a : StreamAlphabet K n q) : Measurable (qamObserve hq δ i a) := by
  apply measurable_pi_lambda
  intro s
  exact (measurable_quantizeComplex q hq δ).comp
    (measurable_const.add (measurable_effectiveNoise i s))

def qamChannel (μ : Measure ℂ) [IsProbabilityMeasure μ] {K n q : ℕ}
    (hq : 0 < q) (δ : ℝ) (i : Fin K) : FiniteChannel (StreamAlphabet K n q)
      (StreamAlphabet K n q) :=
  observedChannel (environmentLaw μ K n) (qamObserve hq δ i)
    (measurable_qamObserve hq δ i)

def qamDecode {K n q : ℕ} (hq : 0 < q) (δ : ℝ) (i : Fin K)
    (hy : StateBlock K (extensionLength K n) × (Fin (extensionLength K n) → ℂ)) :
    StreamAlphabet K n q := fun s => quantizeComplex q hq δ (alignedDecode hy.1 i hy.2 s)

theorem measurable_qamDecode {K n q : ℕ} (hq : 0 < q) (δ : ℝ) (i : Fin K) :
    Measurable (qamDecode (n := n) hq δ i) := by
  apply measurable_pi_lambda
  intro s
  exact (measurable_quantizeComplex q hq δ).comp (measurable_alignedDecode i s)

def qamPowerFactor (K n : ℕ) (M δ : ℝ) : ℝ :=
  K * (2 * Fintype.card (Box (Fin K) n) * beamBound (Fin K) n M * δ) ^ 2

theorem ae_state_norm_le (μ : Measure ℂ) [IsProbabilityMeasure μ] {K L : ℕ} {M : ℝ}
    (hM : ∀ᵐ h ∂μ, ‖h‖ ≤ M) :
    ∀ᵐ H ∂stateLaw μ K L, ∀ t i j, ‖H t i j‖ ≤ M := by
  unfold stateLaw
  have hrow : ∀ᵐ h ∂Measure.pi (fun _ : Fin K ↦ μ), ∀ j, ‖h j‖ ≤ M := by
    rw [ae_all_iff]
    intro j
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin K ↦ μ) j).ae hM
  have hmatrix : ∀ᵐ H ∂Measure.pi (fun _ : Fin K ↦ Measure.pi (fun _ : Fin K ↦ μ)),
      ∀ i j, ‖H i j‖ ≤ M := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin K ↦ Measure.pi (fun _ : Fin K ↦ μ)) i).ae hrow
  rw [ae_all_iff]
  intro t
  exact (Measure.quasiMeasurePreserving_eval
    (fun _ : Fin L ↦ Measure.pi (fun _ : Fin K ↦ Measure.pi (fun _ : Fin K ↦ μ))) t).ae hmatrix

theorem qam_power_le {K n q : ℕ} (δ : ℝ) (hδ : 0 < δ) (M : ℝ)
    (a : Fin K → StreamAlphabet K n q) (H : StateBlock K (extensionLength K n))
    (hH : ∀ t i j, ‖H t i j‖ ≤ M) :
    (∑ t, ∑ i, ‖alignedTransmit H (qamStreams δ (a i)) t‖ ^ 2) ≤
      (extensionLength K n : ℝ) * (qamPowerFactor K n M δ * (q : ℝ) ^ 2) := by
  have hb (i : Fin K) (t : Fin (extensionLength K n)) :
      ‖alignedTransmit H (qamStreams δ (a i)) t‖ ≤
        Fintype.card (Box (Fin K) n) * beamBound (Fin K) n M * (δ * (2 * q)) := by
    apply norm_transmitted_le
    · intro r p
      exact hH _ _ _
    · intro s
      dsimp [qamStreams]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
      exact mul_le_mul_of_nonneg_left (qamValue_norm_le _) hδ.le
  calc
    _ ≤ ∑ _ : Fin (extensionLength K n), ∑ _ : Fin K,
        (Fintype.card (Box (Fin K) n) * beamBound (Fin K) n M * (δ * (2 * q))) ^ 2 := by
      gcongr with t i
      exact hb i t
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        qamPowerFactor]
      ring

def qamScheme (μ : Measure ℂ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {K n q : ℕ} (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ) (M : ℝ)
    (hM : ∀ᵐ h ∂μ, ‖h‖ ≤ M) :
    BlockScheme μ K (extensionLength K n) (qamPowerFactor K n M δ * (q : ℝ) ^ 2)
      (StreamAlphabet K n q) where
  encode _ a H := alignedTransmit H (qamStreams δ a)
  encode_measurable _ a t := measurable_alignedTransmit (qamStreams δ a) t
  encode_causal _ a t H H' hh := alignedTransmit_causal H H' (qamStreams δ a) t (hh t le_rfl)
  decode := qamDecode hq δ
  decode_measurable := measurable_qamDecode hq δ
  channel := qamChannel μ hq δ
  row_law a i b := by
    rw [qamChannel, observedChannel_transition, Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    apply measure_congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_stateFading_nonsingular μ K n)] with hz hhz
    apply propext
    change qamDecode hq δ i (hz.1, _) = b ↔ qamObserve hq δ i (a i) hz = b
    have hd := alignedDecode_signal_add_noise hz.1 i (hhz i)
      (fun j => qamStreams δ (a j)) (fun t => complexNoise (hz.2 i t))
    have he : qamDecode hq δ i
        (hz.1, fun t ↦ (∑ j, hz.1 t i j * alignedTransmit hz.1 (qamStreams δ (a j)) t) +
          complexNoise (hz.2 i t)) = qamObserve hq δ i (a i) hz := by
      funext s
      exact congrArg (quantizeComplex q hq δ) (congrFun hd s)
    rw [he]
  power a := by
    filter_upwards [ae_state_norm_le μ hM] with H hH
    exact qam_power_le δ hδ M a H hH

end

end CapacityAtlas.Gaussian.Interference
