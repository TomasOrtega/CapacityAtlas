/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Basic
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Realification
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal BigOperators

namespace CapacityAtlas.Gaussian.Interference

noncomputable def uniformFinLaw (m : ℕ) (hm : 0 < m) : Measure (Fin m) :=
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  (PMF.uniformOfFintype (Fin m)).toMeasure

instance (m : ℕ) (hm : 0 < m) : IsProbabilityMeasure (uniformFinLaw m hm) := by
  unfold uniformFinLaw
  infer_instance

theorem uniformFinLaw_singleton (m : ℕ) (hm : 0 < m) (a : Fin m) :
    uniformFinLaw m hm {a} = (m : ℝ≥0∞)⁻¹ := by
  simp [uniformFinLaw]

variable {K n : ℕ}

noncomputable def messageLaw (c : Code K n) : Measure c.Message :=
  Measure.pi fun i ↦ uniformFinLaw (c.messages i) (c.messages_pos i)

instance (c : Code K n) : IsProbabilityMeasure (messageLaw c) := by
  unfold messageLaw
  infer_instance

theorem messageLaw_real_singleton (c : Code K n) (m : c.Message) :
    (messageLaw c).real {m} = (∏ i, (c.messages i : ℝ))⁻¹ := by
  simp only [Measure.real, messageLaw, Measure.pi_singleton, uniformFinLaw_singleton,
    ENNReal.toReal_prod, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.prod_inv_distrib]

theorem integral_messageLaw (c : Code K n) (f : c.Message → ℝ) :
    (∫ m, f m ∂messageLaw c) = (∏ i, (c.messages i : ℝ))⁻¹ * ∑ m, f m := by
  rw [integral_fintype Integrable.of_finite]
  simp only [messageLaw_real_singleton, smul_eq_mul, ← Finset.mul_sum]

noncomputable def receiverMean (c : Code K n) (m : c.Message) (H : StateBlock K n)
    (i : Fin K) : EuclideanSpace ℝ (Fin 2 × Fin n) :=
  realBlock fun t ↦ ∑ j, H t i j * c.encode j (m j) H t

def receiverEvent (c : Code K n) (m : c.Message) (i : Fin K) :
    Set (StateBlock K n × Noise K n) :=
  {hz | (c.decode i).apply (hz.1, output c m hz.1 hz.2 i) ≠ m i}

theorem measurableSet_receiverEvent (c : Code K n) (m : c.Message) (i : Fin K) :
    MeasurableSet (receiverEvent c m i) :=
  (((c.decode i).measurable_fiber (m i)).preimage
    (measurable_fst.prodMk (measurable_output c m i))).compl

noncomputable def receiverErrorAt (c : Code K n) (m : c.Message) (H : StateBlock K n)
    (i : Fin K) : ℝ :=
  (blockNoise K n).real (Prod.mk H ⁻¹' receiverEvent c m i)

theorem measurable_receiverErrorAt (c : Code K n) (m : c.Message) (i : Fin K) :
    Measurable fun H ↦ receiverErrorAt c m H i :=
  (measurable_measure_prodMk_left (measurableSet_receiverEvent c m i)).ennreal_toReal

theorem integrable_receiverErrorAt (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : Code K n) (m : c.Message) (i : Fin K) :
    Integrable (fun H ↦ receiverErrorAt c m H i) (stateLaw μ K n) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_receiverErrorAt c m i).aestronglyMeasurable
  filter_upwards with H
  unfold receiverErrorAt
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

theorem integral_receiverErrorAt (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : Code K n) (m : c.Message) (i : Fin K) :
    (∫ H, receiverErrorAt c m H i ∂stateLaw μ K n) =
      ((stateLaw μ K n).prod (blockNoise K n)).real (receiverEvent c m i) := by
  rw [Measure.real, Measure.prod_apply (measurableSet_receiverEvent c m i)]
  exact integral_toReal
    (measurable_measure_prodMk_left (measurableSet_receiverEvent c m i)).aemeasurable
    (Filter.Eventually.of_forall fun _ ↦ measure_lt_top _ _)

theorem average_receiverErrorAt_le_error (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (c : Code K n) (i : Fin K) :
    (∫ m, ∫ H, receiverErrorAt c m H i ∂stateLaw μ K n ∂messageLaw c) ≤ error μ c := by
  rw [integral_messageLaw]
  unfold error
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro m _
  rw [integral_receiverErrorAt]
  exact measureReal_mono (fun _ hh ↦ ⟨i, hh⟩) (measure_ne_top _ _)

theorem blockNoise_map_flatten_receiver (i : Fin K) :
    (blockNoise K n).map (fun z ↦ flattenGaussianBlock (z i)) =
      multivariateGaussian 0 ((1 / 2 : ℝ) •
        (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℝ)) := by
  change (blockNoise K n).map (flattenGaussianBlock ∘ fun z ↦ z i) = _
  rw [← Measure.map_map measurable_flattenGaussianBlock (measurable_pi_apply i)]
  have hproj : (blockNoise K n).map (fun z ↦ z i) =
      Measure.pi fun _ : Fin n ↦ multivariateGaussian 0
        ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
    (measurePreserving_eval (fun _ : Fin K ↦ Measure.pi fun _ : Fin n ↦
      multivariateGaussian 0 ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) i).map_eq
  rw [hproj,
    map_flatten_pi_multivariateGaussian_zero _
      (fun _ ↦ (PosDef.one.smul (by norm_num : (0 : ℝ) < 1 / 2)).posSemidef)]
  congr 1
  change blockDiagonal ((1 / 2 : ℝ) • (1 : Fin n → Matrix (Fin 2) (Fin 2) ℝ)) = _
  rw [blockDiagonal_smul, blockDiagonal_one]

theorem realBlock_output (c : Code K n) (m : c.Message) (H : StateBlock K n)
    (z : Noise K n) (i : Fin K) :
    realBlock (output c m H z i) = receiverMean c m H i + flattenGaussianBlock (z i) := by
  change realBlock ((fun t ↦ ∑ j, H t i j * c.encode j (m j) H t) +
    fun t ↦ complexNoise (z i t)) = _
  rw [realBlock_add]
  congr 1
  change realBlock (fun t ↦ Complex.orthonormalBasisOneI.repr.symm (z i t)) = _
  unfold realBlock
  simp only [LinearIsometryEquiv.apply_symm_apply]

theorem blockNoise_map_realBlock_output (c : Code K n) (m : c.Message)
    (H : StateBlock K n) (i : Fin K) :
    (blockNoise K n).map (fun z ↦ realBlock (output c m H z i)) =
      multivariateGaussian (receiverMean c m H i) ((1 / 2 : ℝ) •
        (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℝ)) := by
  simp_rw [realBlock_output]
  change (blockNoise K n).map ((fun y ↦ receiverMean c m H i + y) ∘
    fun z ↦ flattenGaussianBlock (z i)) = _
  rw [← Measure.map_map (by fun_prop)
      (show Measurable (fun z : Noise K n ↦ flattenGaussianBlock (z i)) from
        measurable_flattenGaussianBlock.comp (measurable_pi_apply i)),
    blockNoise_map_flatten_receiver, multivariateGaussian_map_const_add, add_zero]

theorem receiverErrorAt_eq_gaussian (c : Code K n) (m : c.Message)
    (H : StateBlock K n) (i : Fin K) :
    receiverErrorAt c m H i =
      (multivariateGaussian (receiverMean c m H i) ((1 / 2 : ℝ) •
        (1 : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℝ))).real
          {y | (c.decode i).apply (H, complexBlock y) ≠ m i} := by
  rw [← blockNoise_map_realBlock_output]
  have hm : Measurable fun z : Noise K n ↦ realBlock (output c m H z i) :=
    measurable_realBlock.comp ((measurable_output c m i).comp measurable_prodMk_left)
  have hs : MeasurableSet {y : EuclideanSpace ℝ (Fin 2 × Fin n) |
      (c.decode i).apply (H, complexBlock y) ≠ m i} :=
    (((c.decode i).measurable_fiber (m i)).preimage
      (measurable_const.prodMk measurable_complexBlock)).compl
  rw [Measure.real, Measure.map_apply hm hs]
  simp only [Set.preimage_setOf_eq, complexBlock_realBlock]
  rfl

end CapacityAtlas.Gaussian.Interference
