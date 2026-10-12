/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.QAMScheme

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference

noncomputable section

def noiseBad {K n : ℕ} (δ : ℝ) : Set (Environment K n) :=
  {hz | ∃ i s, δ / 2 ≤ ‖effectiveNoise i hz s‖}

theorem exists_qam_spacing (μ : Measure ℂ) [IsProbabilityMeasure μ] (K n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (environmentLaw μ K n).real (noiseBad δ) < ε := by
  obtain ⟨b, hb, he⟩ := exists_noise_bound (environmentLaw μ K n)
    (fun hz (p : Fin K × Box (Fin K) n) => effectiveNoise p.1 hz p.2)
    (fun p => measurable_effectiveNoise p.1 p.2) hε
  refine ⟨2 * b, by positivity, ?_⟩
  simpa only [noiseBad, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    Prod.exists] using he

theorem qam_error_le_noise (μ : Measure ℂ) [IsProbabilityMeasure μ] {K n q : ℕ}
    (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ) (i : Fin K) (a : StreamAlphabet K n q) :
    1 - (qamChannel μ hq δ i).transition a a ≤
      (environmentLaw μ K n).real (noiseBad δ) := by
  classical
  rw [qamChannel, observedChannel_transition]
  have hm : MeasurableSet {hz : Environment K n | qamObserve hq δ i a hz = a} :=
    (measurable_qamObserve hq δ i a) (measurableSet_singleton a)
  rw [← probReal_univ (μ := environmentLaw μ K n), ← measureReal_compl hm]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro hz hhz
  by_contra hn
  apply hhz
  funext s
  apply quantizeComplex_correct hq hδ
  exact lt_of_not_ge fun hs => hn ⟨i, s, hs⟩

theorem log_card_streamAlphabet {K n q : ℕ} (hq : 0 < q) :
    Real.log (Fintype.card (StreamAlphabet K n q)) =
      2 * Fintype.card (Box (Fin K) n) * Real.log q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [StreamAlphabet, QAM, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul hq0 hq0]
  ring

theorem qam_information_lower (μ : Measure ℂ) [IsProbabilityMeasure μ] {K n q : ℕ}
    (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ) {ε : ℝ}
    (hε : (environmentLaw μ K n).real (noiseBad δ) ≤ ε) (i : Fin K) :
    ((1 - ε) * (2 * Fintype.card (Box (Fin K) n) * Real.log q) - Real.log 2) /
      Real.log 2 ≤ (qamChannel μ (n := n) hq δ i).informationCapacityBits := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hf := finite_fano_lower (qamChannel μ (n := n) hq δ i)
    (fun a => (qam_error_le_noise μ hq δ hδ i a).trans hε)
  rw [log_card_streamAlphabet hq] at hf
  exact (div_le_div_of_nonneg_right hf (Real.log_nonneg (by norm_num))).trans
    ((qamChannel μ hq δ i).mutualInformationBits_le_informationCapacityBits
      (FiniteDistribution.uniform _))

theorem qamPowerFactor_pos {K n : ℕ} (hK : 0 < K) (hn : 0 < n) (M δ : ℝ)
    (hδ : 0 < δ) : 0 < qamPowerFactor K n M δ := by
  have hc : 0 < Fintype.card (Box (Fin K) n) := by
    rw [card_box]
    positivity
  have hb := beamBound_pos (U := Fin K) (n := n) M
  unfold qamPowerFactor
  positivity

end

end CapacityAtlas.Gaussian.Interference
