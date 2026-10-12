/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteChannel.PMF
import CapacityAtlasForMathlib.InformationTheory.CodingConverse
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference

noncomputable section

def observedChannel {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : A → Ω → A)
    (hf : ∀ a, Measurable (f a)) : FiniteChannel A A :=
  FiniteChannel.ofRows fun a =>
    letI : IsProbabilityMeasure (ν.map (f a)) :=
      Measure.isProbabilityMeasure_map (hf a).aemeasurable
    FiniteDistribution.ofPMF (ν.map (f a)).toPMF

theorem observedChannel_transition {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : A → Ω → A)
    (hf : ∀ a, Measurable (f a)) (a b : A) :
    (observedChannel ν f hf).transition a b = ν.real {ω | f a ω = b} := by
  simp only [observedChannel, FiniteChannel.ofRows_transition,
    FiniteDistribution.ofPMF_apply, Measure.toPMF_apply, Measure.real]
  rw [Measure.map_apply (hf a) (measurableSet_singleton b)]
  rfl

theorem finite_fano_lower {A : Type*} [Fintype A] [Nonempty A]
    (W : FiniteChannel A A) {ε : ℝ} (hε : ∀ a, 1 - W.transition a a ≤ ε) :
    (1 - ε) * Real.log (Fintype.card A) - Real.log 2 ≤
      W.mutualInformation (FiniteDistribution.uniform A) := by
  classical
  let c : OneShotCode W A := ⟨id, id⟩
  have hc : c.averageErrorProbability ≤ ε := by
    rw [OneShotCode.averageErrorProbability_eq]
    have hcard : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    calc
      _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _ : A, ε := by
        gcongr with a
        simpa [c, OneShotCode.errorProbability, OneShotCode.successProbability] using hε a
      _ = ε := by simp [hcard.ne']
  have hf := FiniteChannel.fano_uniform W id
  change Real.log (Fintype.card A) ≤
    W.mutualInformation (FiniteDistribution.uniform A) + Real.log 2 +
      c.averageErrorProbability * Real.log (Fintype.card A) at hf
  have hlog : 0 ≤ Real.log (Fintype.card A) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := A))
  nlinarith [mul_le_mul_of_nonneg_right hc hlog]

end

end CapacityAtlas.Gaussian.Interference
