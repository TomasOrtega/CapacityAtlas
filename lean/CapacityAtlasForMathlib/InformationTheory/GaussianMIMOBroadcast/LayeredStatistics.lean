/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredCoding

open MeasureTheory ProbabilityTheory Matrix Filter CapacityAtlas.MeasureChannel CapacityAtlas.MeasureBinning
  CapacityAtlas.MeasureInformation
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ}

theorem measurePreserving_blockLayerTranspose
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) (n : ℕ) :
    MeasurePreserving (fun x : LayerBlocks K tx n ↦ fun t j ↦ x j t)
      (blockLayerLaw Q π n) (Measure.pi (fun _ : Fin n ↦ layerLaw Q π)) :=
  measurePreserving_pi_transpose (fun j _ ↦ multivariateGaussian 0 (Q (π j)))

def blockLayerSource {r : ℕ} (n : ℕ)
    (p : LayerBlocks K tx n × (Fin n → EuclideanSpace ℝ (Fin r))) :
    Fin n → (Fin K → EuclideanSpace ℝ (Fin tx)) × EuclideanSpace ℝ (Fin r) :=
  fun t ↦ ((fun j ↦ p.1 j t), p.2 t)

@[fun_prop]
theorem measurable_blockLayerSource {r : ℕ} (n : ℕ) :
    Measurable (blockLayerSource (K := K) (tx := tx) (r := r) n) := by
  unfold blockLayerSource
  fun_prop

theorem measurePreserving_blockLayerSource {r : ℕ}
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K))
    (N : Matrix (Fin r) (Fin r) ℝ) (n : ℕ) :
    MeasurePreserving (blockLayerSource n)
      ((blockLayerLaw Q π n).prod (DirtyPaper.blockStateLaw N n))
      (Measure.pi (fun _ : Fin n ↦ layerSourceLaw Q π N)) := by
  have h₁ := (measurePreserving_blockLayerTranspose Q π n).prod
    (MeasurePreserving.id (DirtyPaper.blockStateLaw N n))
  have h₂ := (measurePreserving_arrowProdEquivProdArrow
    (Fin K → EuclideanSpace ℝ (Fin tx)) (EuclideanSpace ℝ (Fin r)) (Fin n)
      (fun _ ↦ layerLaw Q π) (fun _ ↦ multivariateGaussian 0 N)).symm
        (MeasurableEquiv.arrowProdEquivProdArrow _ _ _)
  exact h₂.comp h₁

theorem blockLayerState_upperTail_tendsto_zero {r : ℕ}
    (H : Matrix (Fin r) (Fin tx) ℝ) (N : Matrix (Fin r) (Fin r) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (hN : N.PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K) (hk : (Q (π k)).PosDef)
    {a : ℝ} (ha : (∫ p, layerStateStatistic H N Q π k p ∂layerSourceLaw Q π N) < a) :
    Tendsto (fun n ↦ (blockLayerLaw Q π n)
      {x | ENNReal.ofReal (Real.exp ((n : ℝ) * a)) <
        blockLayerDensity H N Q π k n (x, blockLayerAuxiliary H N Q π k n x)})
      atTop (𝓝 0) := by
  have heq (n : ℕ) : (blockLayerLaw Q π n)
      {x | ENNReal.ofReal (Real.exp ((n : ℝ) * a)) <
        blockLayerDensity H N Q π k n (x, blockLayerAuxiliary H N Q π k n x)} =
      (Measure.pi (fun _ : Fin n ↦ layerSourceLaw Q π N))
        {z | (n : ℝ) * a < iidSum (layerStateStatistic H N Q π k) n z} := by
    have hs : Measurable (iidSum (layerStateStatistic H N Q π k) n) := by
      unfold iidSum
      fun_prop
    rw [← (measurePreserving_blockLayerSource Q π N n).map_eq,
      Measure.map_apply (measurable_blockLayerSource n) (measurableSet_lt measurable_const hs)]
    have hevent : MeasurableSet {x : LayerBlocks K tx n |
        ENNReal.ofReal (Real.exp ((n : ℝ) * a)) <
          blockLayerDensity H N Q π k n (x, blockLayerAuxiliary H N Q π k n x)} :=
      measurableSet_lt measurable_const
        ((measurable_blockLayerDensity H N Q π k n).comp
          (measurable_id.prodMk (measurable_blockLayerAuxiliary H N Q π k n)))
    conv_lhs => rw [← (measurePreserving_fst (μ := blockLayerLaw Q π n)
      (ν := DirtyPaper.blockStateLaw N n)).map_eq,
      Measure.map_apply measurable_fst hevent]
    congr 1
    ext p
    change (ENNReal.ofReal (Real.exp ((n : ℝ) * a)) <
      ENNReal.ofReal (Real.exp (iidSum (layerStateStatistic H N Q π k) n
        (blockLayerSource n p)))) ↔ _
    simp only [ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _), Real.exp_lt_exp]
    rfl
  simp_rw [heq]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (iidSum_upperTail_tendsto_zero (layerSourceLaw Q π N)
      (memLp_two_layerStateStatistic H N Q hQ hN π k hk) ha) (fun _ ↦ zero_le)
  intro n
  apply measure_mono
  intro z hz
  exact (show (n : ℝ) * a < iidSum (layerStateStatistic H N Q π k) n z from hz).le

noncomputable def blockLayerObservation {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ) (n : ℕ)
    (p : LayerBlocks K tx n × (Fin n → EuclideanSpace ℝ (Fin r))) :
    Fin n → EuclideanSpace ℝ (Fin r) := fun t ↦ layerObservation H (blockLayerSource n p t)

@[fun_prop]
theorem measurable_blockLayerObservation {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ) (n : ℕ) :
    Measurable (blockLayerObservation (K := K) H n) := by
  unfold blockLayerObservation
  fun_prop

theorem blockLayerObservation_lowerTail_tendsto_zero {r : ℕ}
    (H : Matrix (Fin r) (Fin tx) ℝ) (N : Matrix (Fin r) (Fin r) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (hN : N.PosDef) (π : Equiv.Perm (Fin K)) (k : Fin K) (hk : (Q (π k)).PosDef)
    {d : ℝ} (hd : d < ∫ p, layerObservationStatistic H N Q π k p ∂layerSourceLaw Q π N) :
    Tendsto (fun n ↦ ((blockLayerLaw Q π n).prod (DirtyPaper.blockStateLaw N n))
      {p | DirtyPaper.blockObservationLikelihood H (Q (π k)) (suffixCovariance Q π k)
        (layerNoiseCovariance H N Q π k) n
          (blockLayerAuxiliary H N Q π k n p.1, blockLayerObservation H n p) ≤
            ENNReal.ofReal (Real.exp ((n : ℝ) * d))}) atTop (𝓝 0) := by
  have heq (n : ℕ) : ((blockLayerLaw Q π n).prod (DirtyPaper.blockStateLaw N n))
      {p | DirtyPaper.blockObservationLikelihood H (Q (π k)) (suffixCovariance Q π k)
        (layerNoiseCovariance H N Q π k) n
          (blockLayerAuxiliary H N Q π k n p.1, blockLayerObservation H n p) ≤
            ENNReal.ofReal (Real.exp ((n : ℝ) * d))} =
      (Measure.pi (fun _ : Fin n ↦ layerSourceLaw Q π N))
        {z | ENNReal.ofReal (Real.exp (iidSum (layerObservationStatistic H N Q π k) n z)) ≤
          ENNReal.ofReal (Real.exp ((n : ℝ) * d))} := by
    have hs : Measurable (iidSum (layerObservationStatistic H N Q π k) n) := by
      unfold iidSum
      fun_prop
    rw [← (measurePreserving_blockLayerSource Q π N n).map_eq,
      Measure.map_apply (measurable_blockLayerSource n)
        (measurableSet_le hs.exp.ennreal_ofReal measurable_const)]
    rfl
  simp_rw [heq]
  exact iidLikelihood_lowerTail_tendsto_zero (layerSourceLaw Q π N)
    (memLp_two_layerObservationStatistic H N Q hQ hN π k hk) hd

noncomputable def layerTotalCost (x : Fin K → EuclideanSpace ℝ (Fin tx)) : ℝ :=
  ‖∑ j, x j‖ ^ 2

@[fun_prop]
theorem measurable_layerTotalCost : Measurable (layerTotalCost (K := K) (tx := tx)) := by
  unfold layerTotalCost
  fun_prop

theorem layerLaw_map_totalInput
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (π : Equiv.Perm (Fin K)) :
    (layerLaw Q π).map (fun x ↦ ∑ j, x j) = multivariateGaussian 0 (∑ j, Q (π j)) :=
  map_finsetSum_pi_multivariateGaussian (fun j ↦ Q (π j)) (fun j ↦ hQ (π j)) Finset.univ

theorem memLp_two_layerTotalCost
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (π : Equiv.Perm (Fin K)) : MemLp layerTotalCost 2 (layerLaw Q π) := by
  have hG : HasGaussianLaw (id : EuclideanSpace ℝ (Fin tx) → EuclideanSpace ℝ (Fin tx))
      (multivariateGaussian 0 (∑ j, Q (π j))) := IsGaussian.hasGaussianLaw_id
  have h := memLp_two_covarianceQuadratic (id : EuclideanSpace ℝ (Fin tx) → _)
    (fun i ↦ (hG.map (EuclideanSpace.proj i)).memLp (by norm_num)) 0
      (1 : Matrix (Fin tx) (Fin tx) ℝ)
  have hn : MemLp (fun x : EuclideanSpace ℝ (Fin tx) ↦ ‖x‖ ^ 2) 2
      (multivariateGaussian 0 (∑ j, Q (π j))) := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    simpa [dotProduct, pow_two] using h
  exact hn.comp_measurePreserving ⟨by fun_prop, layerLaw_map_totalInput Q hQ π⟩

theorem integral_layerTotalCost
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (π : Equiv.Perm (Fin K)) :
    (∫ x, layerTotalCost x ∂layerLaw Q π) = (∑ j, Q j).trace := by
  have hm := integral_map (μ := layerLaw Q π)
    (by fun_prop : AEMeasurable (fun x : Fin K → EuclideanSpace ℝ (Fin tx) ↦ ∑ j, x j) _)
    (by fun_prop : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin tx) ↦ ‖x‖ ^ 2) _)
  rw [layerLaw_map_totalInput Q hQ π] at hm
  change (∫ x, ‖∑ j, x j‖ ^ 2 ∂layerLaw Q π) = _
  rw [← hm]
  have heq : (∑ j, Q (π j)) = ∑ j, Q j := Equiv.sum_comp π Q
  rw [heq]
  simp only [EuclideanSpace.real_norm_sq_eq]
  simpa [dotProduct, pow_two] using integral_quadratic_multivariateGaussian
    (0 : EuclideanSpace ℝ (Fin tx)) 0 (∑ j, Q j) (1 : Matrix (Fin tx) (Fin tx) ℝ)
      (posSemidef_sum _ (fun j _ ↦ hQ j))

noncomputable def blockTotalInput (n : ℕ) (x : LayerBlocks K tx n) :
    Fin n → EuclideanSpace ℝ (Fin tx) := fun t ↦ ∑ j, x j t

@[fun_prop]
theorem measurable_blockTotalInput (n : ℕ) :
    Measurable (blockTotalInput (K := K) (tx := tx) n) := by
  unfold blockTotalInput
  fun_prop

theorem blockLayerTotalCost_upperTail_tendsto_zero
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (π : Equiv.Perm (Fin K)) {P : ℝ} (hP : (∑ j, Q j).trace < P) :
    Tendsto (fun n ↦ (blockLayerLaw Q π n)
      {x | ¬DirtyPaper.blockEnergy n (blockTotalInput n x) ≤ (n : ℝ) * P}) atTop (𝓝 0) := by
  have heq (n : ℕ) : (blockLayerLaw Q π n)
      {x | ¬DirtyPaper.blockEnergy n (blockTotalInput n x) ≤ (n : ℝ) * P} =
      (Measure.pi (fun _ : Fin n ↦ layerLaw Q π))
        {z | iidSum layerTotalCost n z ≤ (n : ℝ) * P}ᶜ := by
    have hs : Measurable (iidSum (layerTotalCost (K := K) (tx := tx)) n) := by
      unfold iidSum
      fun_prop
    rw [← (measurePreserving_blockLayerTranspose Q π n).map_eq,
      Measure.map_apply (by fun_prop) (measurableSet_le hs measurable_const).compl]
    rfl
  simp_rw [heq]
  exact iidCost_rejection_tendsto_zero (layerLaw Q π) (memLp_two_layerTotalCost Q hQ π)
    (by rwa [integral_layerTotalCost Q hQ π])

end CapacityAtlas.Gaussian.MIMOBroadcast
