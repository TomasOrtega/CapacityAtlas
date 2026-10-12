/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredAsymptotic
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredOneShot
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredThresholds
import Mathlib.Data.Fin.Rev

open MeasureTheory ProbabilityTheory Filter CapacityAtlas.MeasureBinning
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

/-- Native layered Gaussian codes achieve every strict DPC rate with strict total power slack. -/
theorem strict_dpc_mem_capacityRegion (hK : 0 < K)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K))
    {P : ℝ} (htrace : (∑ i, (Q i).trace) < P) (R : Fin K → ℝ)
    (hR : ∀ i, 0 ≤ R i)
    (hstrict : ∀ k, R (π k) = 0 ∨ R (π k) < dpcRate H N Q π k) :
    R ∈ capacityRegion H N P := by
  let order : ℕ → Fin K := fun j ↦ Fin.rev ⟨j % K, Nat.mod_lt j hK⟩
  have horder (i : Fin K) : order i.val = Fin.revPerm i := by
    dsimp only [order, Fin.revPerm, Function.Involutive.toPerm]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hdesc (i j : Fin K) (hij : i < j) : order j.val < order i.val := by
    rw [horder, horder]
    exact Fin.rev_lt_rev.mpr hij
  have hP : 0 ≤ P := (Finset.sum_nonneg (fun i _ ↦ (hQ i).posSemidef.trace_nonneg)).trans htrace.le
  have htrace' : (∑ i, Q i).trace < P := by rwa [Matrix.trace_sum]
  obtain ⟨a, b, d, ha, hab, hb, hactive⟩ := exists_layered_thresholds H N Q hQ hN π R hstrict
  let active := layeredActiveStages π order R
  have hlim := layeredErrorBound_tendsto_zero H N Q hQ hN π order htrace' R hR a b d active
    ha hab hb (fun i hi ↦ (hactive (order i.val) ((mem_layeredActiveStages π order R i).mp hi)).1)
    (fun i hi ↦ (hactive (order i.val) ((mem_layeredActiveStages π order R i).mp hi)).2)
  rw [capacityRegion_eq_achievableVectorRegion]
  refine ⟨hR, fun ε hε ↦ ?_⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε)))
  refine ⟨max n₀ 1, by omega, fun n hn ↦ ?_⟩
  have hnpos : 0 < n := by omega
  obtain ⟨c, hmessages, hpower, herror⟩ := exists_layeredCode_error_le H N Q hQ hN π
    order Fin.revPerm horder hdesc n
    (fun j ↦ binCount (b (order j)) n) (fun j ↦ binCount_pos _ n)
    (fun j ↦ Real.exp ((n : ℝ) * a (order j))) (fun _ ↦ Real.exp_pos _)
    (fun r ↦ FiniteChannel.messageCountAtRate (R r) n)
    (fun r ↦ FiniteChannel.messageCountAtRate_pos (R r) n) P hP
    (fun i ↦ ENNReal.ofReal (Real.exp ((n : ℝ) * d (order i.val))))
    (fun _ ↦ ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    (fun _ ↦ ENNReal.ofReal_ne_top) active
    (fun i hi ↦ messageCountAtRate_inactive π order R hR n i hi) hε.le
    (hn₀ n (by omega)).le
  refine ⟨c, hpower, herror, fun i ↦ ?_⟩
  change R i - ε ≤ Real.logb 2 (c.messages i : ℝ) / n
  rw [hmessages]
  exact (sub_le_self _ hε.le).trans (FiniteChannel.targetRate_le_rateOfMessageCountAtRate (R i) hnpos)

end CapacityAtlas.Gaussian.MIMOBroadcast
