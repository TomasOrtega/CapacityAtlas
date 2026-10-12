/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianDirtyPaper.InformationDensity
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcastRegion
import CapacityAtlasForMathlib.Probability.GaussianFiniteSum

open MeasureTheory ProbabilityTheory Matrix CapacityAtlas.MeasureInformation
open scoped BigOperators

namespace MeasureTheory.Measure

theorem map_prod_prod_prod_regroup {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (τ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    (((μ.prod ν).prod ρ).prod τ).map (fun p ↦ ((p.1.1.1, (p.1.1.2, p.2)), p.1.2)) =
      (μ.prod (ν.prod τ)).prod ρ := by
  have h₁ := measurePreserving_prodAssoc (μ.prod ν) ρ τ
  have h₂ := (MeasurePreserving.id (μ.prod ν)).prod
    (Measure.measurePreserving_swap (μ := ρ) (ν := τ))
  have h₃ := (measurePreserving_prodAssoc (μ.prod ν) τ ρ).symm MeasurableEquiv.prodAssoc
  have h₄ := (measurePreserving_prodAssoc μ ν τ).prod (MeasurePreserving.id ρ)
  exact (h₄.comp (h₃.comp (h₂.comp h₁))).map_eq

end MeasureTheory.Measure

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

noncomputable def layerLaw (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) : Measure (Fin K → EuclideanSpace ℝ (Fin tx)) :=
  Measure.pi (fun j ↦ multivariateGaussian 0 (Q (π j)))

instance layerLaw_isProbabilityMeasure (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) : IsProbabilityMeasure (layerLaw Q π) := by
  unfold layerLaw
  infer_instance

noncomputable def prefixInput (k : Fin K) (x : Fin K → EuclideanSpace ℝ (Fin tx)) :
    EuclideanSpace ℝ (Fin tx) := ∑ j ∈ Finset.univ.filter (fun j ↦ j < k), x j

noncomputable def suffixInput (k : Fin K) (x : Fin K → EuclideanSpace ℝ (Fin tx)) :
    EuclideanSpace ℝ (Fin tx) := ∑ j ∈ Finset.univ.filter (fun j ↦ k < j), x j

def suffixCovariance (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) : Matrix (Fin tx) (Fin tx) ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j ↦ k < j), Q (π j)

@[fun_prop]
theorem measurable_prefixInput (k : Fin K) : Measurable (prefixInput (tx := tx) k) := by
  unfold prefixInput
  fun_prop

@[fun_prop]
theorem measurable_suffixInput (k : Fin K) : Measurable (suffixInput (tx := tx) k) := by
  unfold suffixInput
  fun_prop

theorem suffixCovariance_posSemidef (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    (suffixCovariance Q π k).PosSemidef := posSemidef_sum _ (fun _ _ ↦ hQ _)

theorem layerLaw_map_groups (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    (layerLaw Q π).map (fun x ↦ ((x k, prefixInput k x), suffixInput k x)) =
      ((multivariateGaussian 0 (Q (π k))).prod
        (multivariateGaussian 0 (prefixCovariance Q π k))).prod
          (multivariateGaussian 0 (suffixCovariance Q π k)) := by
  apply map_coordinate_sum_sum_pi_multivariateGaussian (fun j ↦ Q (π j)) (fun j ↦ hQ (π j))
  · apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    exact (lt_asymm hj hj')
  · simp
  · simp

noncomputable def layerSourceLaw (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) {r : ℕ} (N : Matrix (Fin r) (Fin r) ℝ) :=
  (layerLaw Q π).prod (multivariateGaussian 0 N)

instance layerSourceLaw_isProbabilityMeasure (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) {r : ℕ} (N : Matrix (Fin r) (Fin r) ℝ) :
    IsProbabilityMeasure (layerSourceLaw Q π N) := by unfold layerSourceLaw; infer_instance

noncomputable def layerSource {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ) (k : Fin K)
    (p : (Fin K → EuclideanSpace ℝ (Fin tx)) × EuclideanSpace ℝ (Fin r)) :
    DirtyPaper.SourceSpace (Fin tx) (Fin r) :=
  ((p.1 k, H.toEuclideanLin (prefixInput k p.1) + p.2), suffixInput k p.1)

@[fun_prop]
theorem measurable_layerSource {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ) (k : Fin K) :
    Measurable (layerSource H k) := by unfold layerSource; fun_prop

theorem layerSourceLaw_map_layerSource {r : ℕ}
    (H : Matrix (Fin r) (Fin tx) ℝ) (N : Matrix (Fin r) (Fin r) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosSemidef)
    (hN : N.PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    (layerSourceLaw Q π N).map (layerSource H k) =
      DirtyPaper.sourceLaw (Q (π k)) (suffixCovariance Q π k)
        (receivedCovariance H N (prefixCovariance Q π k)) := by
  let μX := multivariateGaussian 0 (Q (π k))
  let μP := multivariateGaussian 0 (prefixCovariance Q π k)
  let μS := multivariateGaussian 0 (suffixCovariance Q π k)
  let μZ := multivariateGaussian 0 N
  let group := fun x : Fin K → EuclideanSpace ℝ (Fin tx) ↦
    ((x k, prefixInput k x), suffixInput k x)
  have hgroup : Measurable group := by unfold group; fun_prop
  have hgroupLaw : ((layerLaw Q π).map group).prod μZ = ((μX.prod μP).prod μS).prod μZ := by
    rw [layerLaw_map_groups Q hQ π k]
  have hprod := Measure.map_prod_map (layerLaw Q π) μZ hgroup measurable_id
  rw [Measure.map_id] at hprod
  have hgroupLaw' := hprod.symm.trans hgroupLaw
  let reorder := fun p : ((EuclideanSpace ℝ (Fin tx) × EuclideanSpace ℝ (Fin tx)) ×
      EuclideanSpace ℝ (Fin tx)) × EuclideanSpace ℝ (Fin r) ↦
    ((p.1.1.1, (p.1.1.2, p.2)), p.1.2)
  have hreorder := congrArg (fun μ ↦ μ.map reorder) hgroupLaw'
  rw [Measure.map_map (by unfold reorder; fun_prop) (hgroup.prodMap measurable_id),
    Measure.map_prod_prod_prod_regroup] at hreorder
  let receive := fun p : (EuclideanSpace ℝ (Fin tx) ×
      (EuclideanSpace ℝ (Fin tx) × EuclideanSpace ℝ (Fin r))) × EuclideanSpace ℝ (Fin tx) ↦
    ((p.1.1, H.toEuclideanLin p.1.2.1 + p.1.2.2), p.2)
  have hreceive := congrArg (fun μ ↦ μ.map receive) hreorder
  rw [Measure.map_map (by unfold receive; fun_prop) (by unfold reorder group; fun_prop)] at hreceive
  have hnoise : (μP.prod μZ).map (fun p ↦ H.toEuclideanLin p.1 + p.2) =
      multivariateGaussian 0 (receivedCovariance H N (prefixCovariance Q π k)) := by
    rw [← gaussianChannel_comp_eq_map, gaussianChannel_comp_multivariateGaussian H N hN 0 _
      (prefixCovariance_posSemidef Q hQ π k), map_zero]
    rfl
  have ht : ((μX.prod (μP.prod μZ)).prod μS).map receive =
      (μX.prod (multivariateGaussian 0 (receivedCovariance H N (prefixCovariance Q π k)))).prod μS := by
    change ((μX.prod (μP.prod μZ)).prod μS).map
      (Prod.map (Prod.map id (fun p ↦ H.toEuclideanLin p.1 + p.2)) id) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
      ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, Measure.map_id, hnoise]
  exact hreceive.trans ht

theorem prefix_add_current_add_suffix (k : Fin K) (x : Fin K → EuclideanSpace ℝ (Fin tx)) :
    prefixInput k x + x k + suffixInput k x = ∑ j, x j := by
  have hx : x k = ∑ j : Fin K, if j = k then x j else 0 := by simp
  rw [hx]
  simp only [prefixInput, suffixInput, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy j k with hj | rfl | hj
  · simp [hj, ne_of_lt hj, not_lt_of_gt hj]
  · simp
  · simp [hj, ne_of_gt hj, not_lt_of_gt hj]

noncomputable def layerObservation {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (p : (Fin K → EuclideanSpace ℝ (Fin tx)) × EuclideanSpace ℝ (Fin r)) :
    EuclideanSpace ℝ (Fin r) := H.toEuclideanLin (∑ j, p.1 j) + p.2

@[fun_prop]
theorem measurable_layerObservation {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ) :
    Measurable (layerObservation (K := K) H) := by unfold layerObservation; fun_prop

theorem observation_layerSource {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ) (k : Fin K)
    (p : (Fin K → EuclideanSpace ℝ (Fin tx)) × EuclideanSpace ℝ (Fin r)) :
    DirtyPaper.observation H (layerSource H k p) = layerObservation H p := by
  rw [DirtyPaper.observation_apply]
  change H.toEuclideanLin (p.1 k + suffixInput k p.1) +
    (H.toEuclideanLin (prefixInput k p.1) + p.2) = H.toEuclideanLin (∑ j, p.1 j) + p.2
  rw [← prefix_add_current_add_suffix k p.1, map_add, map_add, map_add]
  abel

def layerNoiseCovariance {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) : Matrix (Fin r) (Fin r) ℝ :=
  receivedCovariance H N (prefixCovariance Q π k)

theorem layerNoiseCovariance_posDef {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (hN : N.PosDef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    (layerNoiseCovariance H N Q π k).PosDef :=
  receivedCovariance_posDef H N _ hN (prefixCovariance_posSemidef Q hQ π k)

noncomputable def layerAuxiliary {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (x : Fin K → EuclideanSpace ℝ (Fin tx)) :
    EuclideanSpace ℝ (Fin tx) :=
  x k + (DirtyPaper.costaCoefficient H (Q (π k))
    (layerNoiseCovariance H N Q π k) * H).toEuclideanLin (suffixInput k x)

@[fun_prop]
theorem measurable_layerAuxiliary {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) : Measurable (layerAuxiliary H N Q π k) := by
  unfold layerAuxiliary
  fun_prop

theorem auxiliary_layerSource {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K)
    (p : (Fin K → EuclideanSpace ℝ (Fin tx)) × EuclideanSpace ℝ (Fin r)) :
    DirtyPaper.auxiliary H (Q (π k)) (layerNoiseCovariance H N Q π k) (layerSource H k p) =
      layerAuxiliary H N Q π k p.1 := rfl

noncomputable def layerStateStatistic {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K)
    (p : (Fin K → EuclideanSpace ℝ (Fin tx)) × EuclideanSpace ℝ (Fin r)) : ℝ :=
  DirtyPaper.stateInformationDensity H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) (suffixInput k p.1) (layerAuxiliary H N Q π k p.1)

noncomputable def layerObservationStatistic {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K)
    (p : (Fin K → EuclideanSpace ℝ (Fin tx)) × EuclideanSpace ℝ (Fin r)) : ℝ :=
  DirtyPaper.observationInformationDensity H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) (layerObservation H p) (layerAuxiliary H N Q π k p.1)

@[fun_prop]
theorem measurable_layerStateStatistic {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) : Measurable (layerStateStatistic H N Q π k) := by
  unfold layerStateStatistic
  simpa only [Function.comp_def] using
    (DirtyPaper.measurable_stateInformationDensity H (Q (π k)) (suffixCovariance Q π k)
      (layerNoiseCovariance H N Q π k)).comp
        (((measurable_suffixInput k).comp (measurable_fst (β := EuclideanSpace ℝ (Fin r)))).prodMk
          ((measurable_layerAuxiliary H N Q π k).comp measurable_fst))

@[fun_prop]
theorem measurable_layerObservationStatistic {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) : Measurable (layerObservationStatistic H N Q π k) := by
  unfold layerObservationStatistic
  simpa only [Function.comp_def] using
    (DirtyPaper.measurable_observationInformationDensity H (Q (π k)) (suffixCovariance Q π k)
      (layerNoiseCovariance H N Q π k)).comp
        ((measurable_layerObservation H).prodMk
          ((measurable_layerAuxiliary H N Q π k).comp measurable_fst))

theorem memLp_two_layerStateStatistic {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (hN : N.PosSemidef) (π : Equiv.Perm (Fin K))
    (k : Fin K) (hk : (Q (π k)).PosDef) :
    MemLp (layerStateStatistic H N Q π k) 2 (layerSourceLaw Q π N) := by
  have h := (DirtyPaper.memLp_two_stateInformationDensity H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) hk (suffixCovariance_posSemidef Q hQ π k)).comp_measurePreserving
      ⟨measurable_layerSource H k, layerSourceLaw_map_layerSource H N Q hQ hN π k⟩
  refine MemLp.ae_eq ?_ h
  exact Filter.Eventually.of_forall (fun _ ↦ rfl)

theorem memLp_two_layerObservationStatistic {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (hN : N.PosDef) (π : Equiv.Perm (Fin K))
    (k : Fin K) (hk : (Q (π k)).PosDef) :
    MemLp (layerObservationStatistic H N Q π k) 2 (layerSourceLaw Q π N) := by
  have h := (DirtyPaper.memLp_two_observationInformationDensity H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) hk (suffixCovariance_posSemidef Q hQ π k)
      (layerNoiseCovariance_posDef H N Q hQ hN π k)).comp_measurePreserving
        ⟨measurable_layerSource H k, layerSourceLaw_map_layerSource H N Q hQ hN.posSemidef π k⟩
  refine MemLp.ae_eq ?_ h
  apply Filter.Eventually.of_forall
  intro p
  dsimp only [Function.comp_def]
  rw [observation_layerSource, auxiliary_layerSource]
  rfl

theorem integral_layerStateStatistic {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (hN : N.PosSemidef) (π : Equiv.Perm (Fin K))
    (k : Fin K) (hk : (Q (π k)).PosDef) :
    (∫ p, layerStateStatistic H N Q π k p ∂layerSourceLaw Q π N) =
      (mutualInfoRV (DirtyPaper.auxiliary H (Q (π k)) (layerNoiseCovariance H N Q π k))
        Prod.snd (DirtyPaper.sourceLaw (Q (π k)) (suffixCovariance Q π k)
          (layerNoiseCovariance H N Q π k))).toReal := by
  let f := fun p : DirtyPaper.SourceSpace (Fin tx) (Fin r) ↦
    DirtyPaper.stateInformationDensity H (Q (π k)) (suffixCovariance Q π k)
      (layerNoiseCovariance H N Q π k) p.2
        (DirtyPaper.auxiliary H (Q (π k)) (layerNoiseCovariance H N Q π k) p)
  have hf : Measurable f := by
    simpa only [f, Function.comp_def] using
      (DirtyPaper.measurable_stateInformationDensity H (Q (π k)) (suffixCovariance Q π k)
        (layerNoiseCovariance H N Q π k)).comp
          (show Measurable (fun p : DirtyPaper.SourceSpace (Fin tx) (Fin r) ↦
            (p.2, DirtyPaper.auxiliary H (Q (π k)) (layerNoiseCovariance H N Q π k) p)) by fun_prop)
  have hmap := integral_map (μ := layerSourceLaw Q π N)
    (measurable_layerSource H k).aemeasurable hf.aestronglyMeasurable
  rw [layerSourceLaw_map_layerSource H N Q hQ hN π k] at hmap
  have heq : (∫ p, layerStateStatistic H N Q π k p ∂layerSourceLaw Q π N) =
      ∫ p, f p ∂DirtyPaper.sourceLaw (Q (π k)) (suffixCovariance Q π k)
        (layerNoiseCovariance H N Q π k) := by
    exact hmap.symm
  rw [heq]
  exact DirtyPaper.integral_stateInformationDensity H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) hk (suffixCovariance_posSemidef Q hQ π k)

theorem integral_layerObservationStatistic {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (hN : N.PosDef) (π : Equiv.Perm (Fin K))
    (k : Fin K) (hk : (Q (π k)).PosDef) :
    (∫ p, layerObservationStatistic H N Q π k p ∂layerSourceLaw Q π N) =
      (mutualInfoRV (DirtyPaper.auxiliary H (Q (π k)) (layerNoiseCovariance H N Q π k))
        (DirtyPaper.observation H) (DirtyPaper.sourceLaw (Q (π k)) (suffixCovariance Q π k)
          (layerNoiseCovariance H N Q π k))).toReal := by
  let f := fun p : DirtyPaper.SourceSpace (Fin tx) (Fin r) ↦
    DirtyPaper.observationInformationDensity H (Q (π k)) (suffixCovariance Q π k)
      (layerNoiseCovariance H N Q π k) (DirtyPaper.observation H p)
        (DirtyPaper.auxiliary H (Q (π k)) (layerNoiseCovariance H N Q π k) p)
  have hf : Measurable f := by
    simpa only [f, Function.comp_def] using
      (DirtyPaper.measurable_observationInformationDensity H (Q (π k)) (suffixCovariance Q π k)
        (layerNoiseCovariance H N Q π k)).comp
          (show Measurable (fun p : DirtyPaper.SourceSpace (Fin tx) (Fin r) ↦
            (DirtyPaper.observation H p,
              DirtyPaper.auxiliary H (Q (π k)) (layerNoiseCovariance H N Q π k) p)) by fun_prop)
  have hmap := integral_map (μ := layerSourceLaw Q π N)
    (measurable_layerSource H k).aemeasurable hf.aestronglyMeasurable
  rw [layerSourceLaw_map_layerSource H N Q hQ hN.posSemidef π k] at hmap
  have heq : (∫ p, layerObservationStatistic H N Q π k p ∂layerSourceLaw Q π N) =
      ∫ p, f p ∂DirtyPaper.sourceLaw (Q (π k)) (suffixCovariance Q π k)
        (layerNoiseCovariance H N Q π k) := by
    calc
      _ = ∫ p, f (layerSource H k p) ∂layerSourceLaw Q π N := by
        apply integral_congr_ae
        filter_upwards [] with p
        dsimp only [f]
        rw [observation_layerSource, auxiliary_layerSource]
        rfl
      _ = _ := hmap.symm
  rw [heq]
  exact DirtyPaper.integral_observationInformationDensity H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) hk (suffixCovariance_posSemidef Q hQ π k)
      (layerNoiseCovariance_posDef H N Q hQ hN π k)

theorem layerInformationDifference_eq_dpcRate
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K))
    (k : Fin K) (hk : (Q (π k)).PosDef) :
    (∫ p, layerObservationStatistic (H (π k)) (N (π k)) Q π k p ∂layerSourceLaw Q π (N (π k))) -
      (∫ p, layerStateStatistic (H (π k)) (N (π k)) Q π k p ∂layerSourceLaw Q π (N (π k))) =
        dpcRate H N Q π k * Real.log 2 := by
  rw [integral_layerObservationStatistic _ _ Q hQ (hN (π k)) π k hk,
    integral_layerStateStatistic _ _ Q hQ (hN (π k)).posSemidef π k hk,
    DirtyPaper.costa_information_difference _ _ _ _ hk (suffixCovariance_posSemidef Q hQ π k)
      (layerNoiseCovariance_posDef _ _ Q hQ (hN (π k)) π k)]
  have hnum : DirtyPaper.outputCovariance (H (π k)) (Q (π k))
      (layerNoiseCovariance (H (π k)) (N (π k)) Q π k) =
      receivedCovariance (H (π k)) (N (π k)) (prefixCovariance Q π k + Q (π k)) := by
    simp only [DirtyPaper.outputCovariance, layerNoiseCovariance, receivedCovariance,
      Matrix.mul_add, Matrix.add_mul, add_assoc]
  rw [hnum]
  unfold dpcRate Real.logb
  rw [Real.log_div (dpcRate_numerator_pos H N Q hN hQ π k).ne'
    (dpcRate_denominator_pos H N Q hN hQ π k).ne']
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  change (_ - _) / 2 = (1 / 2 : ℝ) * ((_ - _) / Real.log 2) * Real.log 2
  field_simp
  rfl

noncomputable def layerAuxiliaryKernel {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) :
    Kernel (Fin K → EuclideanSpace ℝ (Fin tx)) (EuclideanSpace ℝ (Fin tx)) :=
  (gaussianChannel (DirtyPaper.costaCoefficient H (Q (π k)) (layerNoiseCovariance H N Q π k) * H)
    (Q (π k))).comap (suffixInput k) (measurable_suffixInput k)

instance layerAuxiliaryKernel_isMarkovKernel {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) : IsMarkovKernel (layerAuxiliaryKernel H N Q π k) := by
  unfold layerAuxiliaryKernel
  infer_instance

theorem layerAuxiliaryKernel_eq_withDensity {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K)
    (hk : (Q (π k)).PosDef) (x : Fin K → EuclideanSpace ℝ (Fin tx)) :
    layerAuxiliaryKernel H N Q π k x =
      (multivariateGaussian 0 (DirtyPaper.auxiliaryCovariance H (Q (π k)) (suffixCovariance Q π k)
        (layerNoiseCovariance H N Q π k))).withDensity (fun u ↦ ENNReal.ofReal (Real.exp
          (DirtyPaper.stateInformationDensity H (Q (π k)) (suffixCovariance Q π k)
            (layerNoiseCovariance H N Q π k) (suffixInput k x) u))) :=
  DirtyPaper.stateKernel_eq_withDensity H (Q (π k)) (suffixCovariance Q π k)
    (layerNoiseCovariance H N Q π k) hk (suffixCovariance_posSemidef Q hQ π k) (suffixInput k x)

theorem layerAuxiliaryKernel_map_encoderInput {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) (x : Fin K → EuclideanSpace ℝ (Fin tx)) :
    (layerAuxiliaryKernel H N Q π k x).map
      (fun u ↦ DirtyPaper.encoderInput H (Q (π k)) (layerNoiseCovariance H N Q π k)
        (suffixInput k x) u) = multivariateGaussian 0 (Q (π k)) := by
  rw [layerAuxiliaryKernel, Kernel.comap_apply, gaussianChannel_apply_eq_map,
    Measure.map_map (by unfold DirtyPaper.encoderInput; fun_prop) (by fun_prop)]
  have heq : (fun u ↦ DirtyPaper.encoderInput H (Q (π k)) (layerNoiseCovariance H N Q π k)
      (suffixInput k x) ((DirtyPaper.costaCoefficient H (Q (π k))
        (layerNoiseCovariance H N Q π k) * H).toEuclideanLin (suffixInput k x) + u)) = id := by
    funext u
    simp [DirtyPaper.encoderInput]
  simp only [Function.comp_def, heq, Measure.map_id]

end CapacityAtlas.Gaussian.MIMOBroadcast
