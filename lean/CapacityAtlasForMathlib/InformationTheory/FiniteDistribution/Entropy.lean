/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution.PMF
import CapacityAtlasForMathlib.InformationTheory.Entropy.RandomVariable

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.FiniteDistribution

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Finite entropy agrees with random-variable entropy for its probability measure. -/
@[capacity_shared_api]
theorem entropy_eq_probabilityTheory [MeasurableSpace A] [MeasurableSingletonClass A]
    (distribution : FiniteDistribution A) :
    distribution.entropy = ProbabilityTheory.entropy id distribution.toPMF.toMeasure := by
  rw [ProbabilityTheory.entropy_eq_sum, Measure.map_id, tsum_fintype]
  unfold entropy
  apply Finset.sum_congr rfl
  intro x _
  rw [Measure.real, distribution.toPMF.toMeasure_apply_singleton x (measurableSet_singleton x),
    toPMF_apply_toReal]

/-- A finite pushforward has the entropy of the corresponding random variable. -/
@[capacity_shared_api]
theorem entropy_map_eq_probabilityTheory [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [DecidableEq B]
    (distribution : FiniteDistribution A) (f : A → B) :
    (distribution.map f).entropy = ProbabilityTheory.entropy f distribution.toPMF.toMeasure := by
  rw [ProbabilityTheory.entropy_def, PMF.toMeasure_map f distribution.toPMF (measurable_of_finite f),
    ← toPMF_map]
  simpa [ProbabilityTheory.entropy_def] using (distribution.map f).entropy_eq_probabilityTheory

end CapacityAtlas.FiniteDistribution
