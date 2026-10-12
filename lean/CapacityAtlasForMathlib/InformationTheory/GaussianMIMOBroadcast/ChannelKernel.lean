/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast
import CapacityAtlasForMathlib.Probability.GaussianChannel

open MeasureTheory ProbabilityTheory

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n : ℕ} {rx : Fin K → ℕ}

theorem blockNoise_map_output
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin tx)) (i : Fin K) (s : Fin n) :
    (blockNoise N n).map (fun z ↦ output H x z i s) =
      gaussianChannel (H i) (N i) (x s) := by
  rw [gaussianChannel_apply_eq_map, ← (blockNoise_eval N i s).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem blockNoise_map_output_eq_multivariateGaussian
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin tx)) (i : Fin K) (s : Fin n) :
    (blockNoise N n).map (fun z ↦ output H x z i s) =
      multivariateGaussian ((H i).toEuclideanLin (x s)) (N i) := by
  rw [blockNoise_map_output, gaussianChannel_apply]

theorem blockNoise_map_output_eq_withDensity
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin tx)) (i : Fin K) (s : Fin n)
    (hN : (N i).PosDef) :
    (blockNoise N n).map (fun z ↦ output H x z i s) = volume.withDensity
      (fun y ↦ ENNReal.ofReal (multivariateGaussianPDFReal
        ((H i).toEuclideanLin (x s)) (N i) y)) := by
  rw [blockNoise_map_output, gaussianChannel_apply_eq_withDensity _ _ hN]

end CapacityAtlas.Gaussian.MIMOBroadcast
