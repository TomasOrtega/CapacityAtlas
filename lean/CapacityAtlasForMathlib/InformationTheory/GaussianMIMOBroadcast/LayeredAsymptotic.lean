/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredBounds
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Asymptotic

open MeasureTheory ProbabilityTheory Filter CapacityAtlas.MeasureBinning
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

theorem layeredFailureBound_tendsto_zero
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K)
    (a b : Fin K → ℝ)
    (ha : ∀ k, (∫ p, layerStateStatistic (H (π k)) (N (π k)) Q π k p
      ∂layerSourceLaw Q π (N (π k))) < a k)
    (hab : ∀ k, a k < b k) :
    Tendsto (fun n ↦ layeredFailureBound H N Q π order n
      (fun j ↦ binCount (b (order j)) n) (fun j ↦ Real.exp ((n : ℝ) * a (order j))))
      atTop (𝓝 0) := by
  have hterm (i : Fin K) : Tendsto (fun n ↦ (2 : ℝ≥0∞) ^ i.val *
      (2 * layeredStateTail H N Q π (order i.val) n (Real.exp ((n : ℝ) * a (order i.val))) +
        ENNReal.ofReal (Real.exp (-((binCount (b (order i.val)) n : ℝ) *
          ((1 / 2) / Real.exp ((n : ℝ) * a (order i.val)))))))) atTop (𝓝 0) := by
    have hstate := blockLayerState_upperTail_tendsto_zero
      (H (π (order i.val))) (N (π (order i.val))) Q (fun j ↦ (hQ j).posSemidef)
      (hN (π (order i.val))).posSemidef π (order i.val) (hQ _) (ha _)
    have hstate₂ := ENNReal.Tendsto.const_mul hstate (a := (2 : ℝ≥0∞)) (Or.inr (by finiteness))
    have hsum := hstate₂.add (coveringTerm_tendsto_zero (hab (order i.val)))
    simpa only [layeredStateTail, mul_zero, zero_add] using
      ENNReal.Tendsto.const_mul hsum (a := (2 : ℝ≥0∞) ^ i.val) (Or.inr (by finiteness))
  simpa only [layeredFailureBound, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ ↦ hterm i)

/-- Every term in the actual shared-codebook error bound vanishes at strict rates. -/
theorem layeredErrorBound_tendsto_zero
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K)
    {P : ℝ} (hP : (∑ j, Q j).trace < P) (R : Fin K → ℝ) (hR : ∀ i, 0 ≤ R i)
    (a b d : Fin K → ℝ) (active : Finset (Fin K))
    (ha : ∀ k, (∫ p, layerStateStatistic (H (π k)) (N (π k)) Q π k p
      ∂layerSourceLaw Q π (N (π k))) < a k)
    (hab : ∀ k, a k < b k) (hb : ∀ k, 0 ≤ b k)
    (hgap : ∀ i ∈ active, R (π (order i.val)) * Real.log 2 + b (order i.val) < d (order i.val))
    (hd : ∀ i ∈ active, d (order i.val) <
      ∫ p, layerObservationStatistic (H (π (order i.val))) (N (π (order i.val))) Q π
        (order i.val) p ∂layerSourceLaw Q π (N (π (order i.val)))) :
    Tendsto (fun n ↦ layeredErrorBound H N Q π order n
      (fun j ↦ binCount (b (order j)) n) (fun j ↦ Real.exp ((n : ℝ) * a (order j)))
      (fun r ↦ FiniteChannel.messageCountAtRate (R r) n) P
      (fun i ↦ ENNReal.ofReal (Real.exp ((n : ℝ) * d (order i.val)))) active) atTop (𝓝 0) := by
  have hfail := layeredFailureBound_tendsto_zero H N Q hQ hN π order a b ha hab
  have hcost := blockLayerTotalCost_upperTail_tendsto_zero Q (fun j ↦ (hQ j).posSemidef) π hP
  have hcost₂ := ENNReal.Tendsto.const_mul hcost (a := (2 : ℝ≥0∞) ^ K) (Or.inr (by finiteness))
  have hterm (i : Fin K) (hi : i ∈ active) : Tendsto (fun n ↦
      layeredFailureBound H N Q π order n
        (fun j ↦ binCount (b (order j)) n) (fun j ↦ Real.exp ((n : ℝ) * a (order j))) +
      2 ^ K * layeredCostTail Q π n P +
      2 ^ K * layeredMissTail H N Q π (order i.val) n
        (ENNReal.ofReal (Real.exp ((n : ℝ) * d (order i.val)))) +
      (FiniteChannel.messageCountAtRate (R (π (order i.val))) n - 1 : ℕ) *
        binCount (b (order i.val)) n *
          (ENNReal.ofReal (Real.exp ((n : ℝ) * d (order i.val))))⁻¹) atTop (𝓝 0) := by
    have hmiss := blockLayerObservation_lowerTail_tendsto_zero
      (H (π (order i.val))) (N (π (order i.val))) Q (fun j ↦ (hQ j).posSemidef)
      (hN (π (order i.val))) π (order i.val) (hQ _) (hd i hi)
    have hmiss₂ := ENNReal.Tendsto.const_mul hmiss (a := (2 : ℝ≥0∞) ^ K) (Or.inr (by finiteness))
    have hpacking := binningPackingTerm_tendsto_zero (hR (π (order i.val)))
      (hb (order i.val)) (hgap i hi)
    simpa only [layeredCostTail, layeredMissTail, mul_zero, add_zero] using
      ((hfail.add hcost₂).add hmiss₂).add hpacking
  simpa only [layeredErrorBound, Finset.sum_const_zero] using
    tendsto_finsetSum active hterm

end CapacityAtlas.Gaussian.MIMOBroadcast
