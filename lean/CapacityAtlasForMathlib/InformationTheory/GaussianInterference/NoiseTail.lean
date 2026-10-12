/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Quantization
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

open MeasureTheory Filter
open scoped BigOperators Topology

namespace CapacityAtlas.Gaussian.Interference

/-- Finite-valued measurable noise has arbitrarily small tails; no moment bound is needed. -/
theorem exists_noise_bound {Ω A : Type*} [MeasurableSpace Ω] [Fintype A]
    (ν : Measure Ω) [IsFiniteMeasure ν] (ξ : Ω → A → ℂ)
    (hξ : ∀ a, Measurable fun ω => ξ ω a) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ν.real {ω | ∃ a, b ≤ ‖ξ ω a‖} < ε := by
  classical
  let f : Ω → ℝ := fun ω => ∑ a, ‖ξ ω a‖
  have hf : Measurable f := Finset.measurable_sum _ fun a _ => (hξ a).norm
  let s : ℕ → Set Ω := fun n => {ω | (n : ℝ) ≤ f ω}
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_le measurable_const hf
  have hmono : Antitone s := by
    intro n m hnm ω hω
    exact (show (n : ℝ) ≤ m by exact_mod_cast hnm).trans hω
  have hempty : ⋂ n, s n = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    obtain ⟨n, hn⟩ := exists_nat_gt (f ω)
    exact (not_le_of_gt hn) (Set.mem_iInter.mp hω n)
  have ht : Tendsto (fun n => ν (s n)) atTop (𝓝 0) := by
    simpa only [hempty, measure_empty, Function.comp_def] using
      tendsto_measure_iInter_atTop (fun n => (hs n).nullMeasurableSet)
        hmono ⟨0, measure_ne_top _ _⟩
  have hreal : Tendsto (fun n => ν.real (s n)) atTop (𝓝 0) := by
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  obtain ⟨n, hn⟩ := (hreal.eventually (gt_mem_nhds hε)).exists
  refine ⟨n + 1, by positivity, lt_of_le_of_lt ?_ hn⟩
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨a, ha⟩
  have hsum : ‖ξ ω a‖ ≤ f ω :=
    Finset.single_le_sum (fun a _ => norm_nonneg (ξ ω a)) (Finset.mem_univ a)
  change (n : ℝ) ≤ f ω
  linarith

end CapacityAtlas.Gaussian.Interference
