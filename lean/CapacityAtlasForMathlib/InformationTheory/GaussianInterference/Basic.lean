/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianOperational
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Complex.Basic
import CapacityAtlasUtil

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference

abbrev State (K : ℕ) := Fin K → Fin K → ℂ
abbrev StateBlock (K n : ℕ) := Fin n → State K
abbrev Noise (K n : ℕ) := Fin K → Fin n → EuclideanSpace ℝ (Fin 2)

/-- All directed channel coefficients, including direct links, are sampled independently. -/
noncomputable def stateLaw (μ : Measure ℂ) (K n : ℕ) : Measure (StateBlock K n) :=
  Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin K => μ

instance (μ : Measure ℂ) [IsProbabilityMeasure μ] (K n : ℕ) :
    IsProbabilityMeasure (stateLaw μ K n) := by unfold stateLaw; infer_instance

def complexNoise (z : EuclideanSpace ℝ (Fin 2)) : ℂ := z 0 + z 1 * Complex.I

/-- Independent real and imaginary noise coordinates each have variance one half. -/
noncomputable def blockNoise (K n : ℕ) : Measure (Noise K n) :=
  Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin n =>
    multivariateGaussian 0 ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))

instance (K n : ℕ) : IsProbabilityMeasure (blockNoise K n) := by
  unfold blockNoise
  infer_instance

/-- Encoders know their own messages and the channel history through the current use. -/
@[capacity_problem "k-user-gaussian-interference-channel", capacity_definition]
structure Code (K n : ℕ) where
  messages : Fin K → ℕ
  messages_pos : ∀ i, 0 < messages i
  encode : (i : Fin K) → Fin (messages i) → StateBlock K n → Fin n → ℂ
  encode_measurable : ∀ i m t, Measurable fun H => encode i m H t
  encode_causal : ∀ i m t H H', (∀ s, s ≤ t → H s = H' s) →
    encode i m H t = encode i m H' t
  decode : (i : Fin K) → Decoder (StateBlock K n × (Fin n → ℂ)) (messages i)

variable {K n : ℕ}

abbrev Code.Message (c : Code K n) := (i : Fin K) → Fin (c.messages i)

def output (c : Code K n) (m : c.Message) (H : StateBlock K n) (z : Noise K n)
    (i : Fin K) : Fin n → ℂ :=
  fun t => (∑ j, H t i j * c.encode j (m j) H t) + complexNoise (z i t)

@[fun_prop]
theorem measurable_output (c : Code K n) (m : c.Message) (i : Fin K) :
    Measurable fun hz : StateBlock K n × Noise K n => output c m hz.1 hz.2 i := by
  unfold output complexNoise
  apply measurable_pi_lambda
  intro t
  apply Measurable.add
  · apply Finset.measurable_sum
    intro j _
    have hcoef : Measurable fun hz : StateBlock K n × Noise K n => hz.1 t i j := by
      fun_prop
    exact hcoef.mul ((c.encode_measurable j (m j) t).comp measurable_fst)
  · fun_prop

noncomputable def energy (c : Code K n) (m : c.Message) (H : StateBlock K n) : ℝ :=
  ∑ t, ∑ i, ‖c.encode i (m i) H t‖ ^ 2

/-- One power budget, averaged over the independent uniform messages and fading. -/
def PowerAdmissible (μ : Measure ℂ) (P : ℝ) (c : Code K n) : Prop :=
  (∀ m, Integrable (energy c m) (stateLaw μ K n)) ∧
    (∏ i, (c.messages i : ℝ))⁻¹ *
      (∑ m, ∫ H, energy c m H ∂stateLaw μ K n) ≤ (n : ℝ) * P

def errorEvent (c : Code K n) (m : c.Message) : Set (StateBlock K n × Noise K n) :=
  {hz | ∃ i, (c.decode i).apply (hz.1, output c m hz.1 hz.2 i) ≠ m i}

theorem measurableSet_errorEvent (c : Code K n) (m : c.Message) :
    MeasurableSet (errorEvent c m) := by
  unfold errorEvent
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  exact (((c.decode i).measurable_fiber (m i)).preimage
    (measurable_fst.prodMk (measurable_output c m i))).compl

noncomputable def error (μ : Measure ℂ) (c : Code K n) : ℝ :=
  (∏ i, (c.messages i : ℝ))⁻¹ * ∑ m,
    (((stateLaw μ K n).prod (blockNoise K n)) (errorEvent c m)).toReal

noncomputable def rates (c : Code K n) (i : Fin K) : ℝ :=
  Operational.messageRate (c.messages i) n

@[capacity_problem "k-user-gaussian-interference-channel", capacity_definition]
noncomputable def capacityRegion (μ : Measure ℂ) (K : ℕ) (P : ℝ) : Set (Fin K → ℝ) :=
  Operational.achievableVectorRegion (Code K) (fun _ c => PowerAdmissible μ P c)
    (fun _ c => error μ c) (fun _ c => rates c)

@[capacity_problem "k-user-gaussian-interference-channel", capacity_definition]
noncomputable def sumCapacity (μ : Measure ℂ) (K : ℕ) (P : ℝ) : ℝ :=
  sSup {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i}

theorem error_nonneg (μ : Measure ℂ) (c : Code K n) : 0 ≤ error μ c := by
  unfold error
  positivity

theorem error_le_one (μ : Measure ℂ) [IsProbabilityMeasure μ] (c : Code K n) :
    error μ c ≤ 1 := by
  have hpos : 0 < ∏ i, (c.messages i : ℝ) :=
    Finset.prod_pos fun i _ => Nat.cast_pos.mpr (c.messages_pos i)
  unfold error
  calc
    _ ≤ (∏ i, (c.messages i : ℝ))⁻¹ * ∑ _ : c.Message, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos.le)
      exact Finset.sum_le_sum fun _ _ => measureReal_le_one
    _ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hc : (Fintype.card c.Message : ℝ) = ∏ i, (c.messages i : ℝ) := by
        simp [Code.Message, Fintype.card_pi]
      rw [hc, inv_mul_cancel₀ hpos.ne']

end CapacityAtlas.Gaussian.Interference
