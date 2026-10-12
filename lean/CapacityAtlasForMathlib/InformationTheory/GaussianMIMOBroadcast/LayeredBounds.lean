/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredReadback

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

noncomputable def layeredStateTail
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K))
    (k : Fin K) (n : ℕ) (T : ℝ) : ℝ≥0∞ :=
  (blockLayerLaw Q π n) {x | ENNReal.ofReal T <
    blockLayerDensity (H (π k)) (N (π k)) Q π k n
      (x, blockLayerAuxiliary (H (π k)) (N (π k)) Q π k n x)}

noncomputable def layeredCostTail (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (n : ℕ) (P : ℝ) : ℝ≥0∞ :=
  (blockLayerLaw Q π n) {x | ¬DirtyPaper.blockEnergy n (blockTotalInput n x) ≤ (n : ℝ) * P}

noncomputable def layeredMissTail
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K))
    (k : Fin K) (n : ℕ) (F : ℝ≥0∞) : ℝ≥0∞ :=
  ((blockLayerLaw Q π n).prod (DirtyPaper.blockStateLaw (N (π k)) n))
    {p | DirtyPaper.blockObservationLikelihood (H (π k)) (Q (π k)) (suffixCovariance Q π k)
      (layerNoiseCovariance (H (π k)) (N (π k)) Q π k) n
        (blockLayerAuxiliary (H (π k)) (N (π k)) Q π k n p.1,
          blockLayerObservation (H (π k)) n p) ≤ F}

noncomputable def layeredFailureBound
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K))
    (order : ℕ → Fin K) (n : ℕ) (L : ℕ → ℕ) (T : ℕ → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin K, 2 ^ j.val * (2 * layeredStateTail H N Q π (order j.val) n (T j.val) +
    ENNReal.ofReal (Real.exp (-((L j.val : ℝ) * ((1 / 2) / T j.val)))))

noncomputable def layeredErrorBound
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K))
    (order : ℕ → Fin K) (n : ℕ) (L : ℕ → ℕ) (T : ℕ → ℝ)
    (M : Fin K → ℕ) (P : ℝ) (F : Fin K → ℝ≥0∞) (active : Finset (Fin K)) : ℝ≥0∞ :=
  ∑ i ∈ active, (layeredFailureBound H N Q π order n L T +
    2 ^ K * layeredCostTail Q π n P + 2 ^ K * layeredMissTail H N Q π (order i.val) n (F i) +
    (M (π (order i.val)) - 1 : ℕ) * L i.val * (F i)⁻¹)

end CapacityAtlas.Gaussian.MIMOBroadcast
