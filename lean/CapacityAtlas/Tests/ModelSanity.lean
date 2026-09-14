/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.RemainingModels
import CapacityAtlas.Network.CycleIndexCoding

/-! Structural regression tests only. No capacity theorem is proved here. -/

open scoped BigOperators

namespace CapacityAtlas.Tests

/-- This fails if the real-channel factor one half is accidentally removed. -/
@[capacity_test]
theorem realAWGN_unit_snr : Gaussian.awgnFormula 1 1 = (1 / 2 : ℝ) := by
  norm_num [Gaussian.awgnFormula, Real.logb]

/-- A one-use code whose two codeword energies are zero and four. -/
noncomputable def unevenPowerCode : Gaussian.Code 1 where
  messages := 2
  messages_pos := by decide
  encode m _ := if m = 0 then 0 else 2
  decode := {
    apply := fun _ ↦ 0
    measurable_fiber := fun m ↦ by
      change MeasurableSet {_y : Fin 1 → ℝ | (0 : Fin 2) = m}
      by_cases hm : (0 : Fin 2) = m <;> simp [hm] }

/-- Expected power and maximum-codeword power really define different code classes. -/
@[capacity_test]
theorem messageAverage_not_codeword_power :
    Gaussian.MessageAveragePowerAdmissible 2 unevenPowerCode ∧
      ¬Gaussian.CodewordPowerAdmissible 2 unevenPowerCode := by
  unfold Gaussian.MessageAveragePowerAdmissible Gaussian.CodewordPowerAdmissible
  unfold unevenPowerCode
  constructor
  · norm_num [Fin.sum_univ_succ]
  · intro h
    have hbad := h (1 : Fin 2)
    norm_num at hbad

@[capacity_test]
theorem scalarMIMO_output {n : ℕ} (x z : Fin n → Fin 1 → ℝ) (t : Fin n) :
    Gaussian.vectorOutput (1 : Matrix (Fin 1) (Fin 1) ℝ) x z t 0 = x t 0 + z t 0 := by
  simp [Gaussian.vectorOutput]

@[capacity_test]
theorem scalarMIMO_codeword_power {n : ℕ} (P : ℝ) (c : Gaussian.VectorCode 1 1 n) :
    Gaussian.CodewordVectorPowerAdmissible P c ↔
      ∀ m, (∑ t, (c.encode m t 0) ^ 2) ≤ (n : ℝ) * P := by
  simp [Gaussian.CodewordVectorPowerAdmissible]

@[capacity_test]
theorem scalarMIMO_objective (P N : ℝ) :
    Gaussian.logDet (1 : Matrix (Fin 1) (Fin 1) ℝ) N (fun _ _ ↦ P) =
      Gaussian.awgnFormula P N := by
  simp [Gaussian.logDet, Gaussian.awgnFormula, Matrix.one_apply]

/-- Zero-gain modes do not consume power, including at zero noise in the total definition. -/
@[capacity_test]
theorem waterFilling_zero_gain (N level : ℝ) :
    Gaussian.waterFillingPower (fun _ : Fin 1 ↦ 0) N level 0 = 0 := by
  simp [Gaussian.waterFillingPower]

/-- Known two-mode allocation: thresholds 1/4 and 1, level 9/8, total power one. -/
@[capacity_test]
theorem waterFilling_two_modes :
    Gaussian.waterFillingPower ![4, 1] 1 (9 / 8) 0 = (7 / 8 : ℝ) ∧
      Gaussian.waterFillingPower ![4, 1] 1 (9 / 8) 1 = (1 / 8 : ℝ) := by
  norm_num [Gaussian.waterFillingPower]

/-- Actual normalized production output laws, not a parallel reference implementation. -/
@[capacity_test]
theorem finiteState_outputLaw_normalized {X S Y : Type*}
    [Fintype X] [Fintype S] [Fintype Y] {W : FiniteStateChannel X S Y}
    (initial : FiniteDistribution S) {n : ℕ} (c : FiniteStateOperational.FeedbackCode W n)
    (m : Fin c.messages) :
    (∑ y, FiniteStateOperational.outputLaw initial c m y) = 1 :=
  (FiniteStateOperational.outputLaw initial c m).sum_probability

/-- The path-sum model recovers a physical channel row in the memoryless one-use case. -/
@[capacity_test]
theorem finiteState_memoryless_one_step {X Y : Type*} [Fintype X] [Fintype Y]
    (W : FiniteChannel X Y) (x : X) (y : Y) :
    FiniteStateOperational.likelihood (FiniteStateOperational.memoryless W)
      (FiniteStateOperational.fixedInitial ()) (fun _ : Fin 1 ↦ x) (fun _ ↦ y) =
        W.transition x y := by
  simp [FiniteStateOperational.likelihood, FiniteStateOperational.memoryless,
    FiniteStateOperational.fixedInitial, FiniteChannel.deterministic,
    FiniteChannel.rowDistribution]
  change (1 : ℝ) * W.transition x y = W.transition x y
  exact one_mul _

/-- Different future noises give the same first output under the actual recursion. -/
@[capacity_test]
theorem causalRun_first_output_ignores_future (initial : ℝ)
    (step : (t : Fin 2) → (Fin t.val → ℝ) → ℝ → ℝ) :
    CausalHistories.run initial step ![0, 1] 0 =
      CausalHistories.run initial step ![0, 2] 0 := by
  rfl

@[capacity_test]
theorem directed_triangle_side_information :
    ∀ r : Fin 3, (IndexCoding.directedCycle 0).sideInformation r = {r + 1} := by
  decide

@[capacity_test]
theorem five_cycle_side_information :
    ∀ r : Fin 5, IndexCoding.undirectedFiveCycle.sideInformation r = {r - 1, r + 1} := by
  decide

end CapacityAtlas.Tests
