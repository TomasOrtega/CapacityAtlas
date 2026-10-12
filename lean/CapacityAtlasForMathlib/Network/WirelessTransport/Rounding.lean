/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace CapacityAtlas.WirelessTransport

/-- A square grid of pairs fits every node budget, including nonsquares. -/
theorem exists_grid_size {n : ℕ} (hn : 4 ≤ n) :
    ∃ m : ℕ, 0 < m ∧ 2 * (m * m) ≤ n ∧ Real.sqrt n ≤ 4 * (m : ℝ) := by
  let m := Nat.sqrt n / 2
  have hs : 2 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hm : 0 < m := by dsimp [m]; omega
  have hms : 2 * m ≤ Nat.sqrt n := by dsimp [m]; omega
  have hsm : Nat.sqrt n + 1 ≤ 4 * m := by dsimp [m]; omega
  have hsq := Nat.sqrt_le n
  have hnlt := Nat.lt_succ_sqrt n
  refine ⟨m, hm, by nlinarith, ?_⟩
  have hnreal : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    exact_mod_cast (show n < (Nat.sqrt n + 1) ^ 2 by simpa [pow_two] using hnlt)
  have hsmreal : (Nat.sqrt n : ℝ) + 1 ≤ 4 * (m : ℝ) := by exact_mod_cast hsm
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hn0 := Real.sqrt_nonneg (n : ℝ)
  have hm0 : (0 : ℝ) ≤ m := by positivity
  nlinarith

end CapacityAtlas.WirelessTransport
