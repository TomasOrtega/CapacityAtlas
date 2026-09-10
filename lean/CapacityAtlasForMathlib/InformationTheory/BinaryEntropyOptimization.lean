/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasUtil.Metadata
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

namespace Real

/-- The pointwise entropy bound underlying Gibbs' inequality, including zero mass. -/
@[capacity_shared_api]
theorem negMulLog_add_mul_log_le_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    negMulLog x + x * log y ≤ y - x := by
  have hscaled := mul_le_mul_of_nonneg_left
    (negMulLog_le_one_sub_self (div_nonneg hx hy.le)) hy.le
  have hmul := negMulLog_mul (x / y) y
  rw [div_mul_cancel₀ x hy.ne'] at hmul
  have hcancel : (x / y) * negMulLog y = -(x * log y) := by
    simp only [negMulLog_def]
    field_simp [hy.ne']
  rw [hcancel] at hmul
  have hright : y * (1 - x / y) = y - x := by
    field_simp [hy.ne']
  rw [hright] at hscaled
  linarith

/-- Binary entropy plus a linear log-weight is at most its log-partition value. -/
@[capacity_shared_api]
theorem binEntropy_add_mul_log_le_log_one_add {x t : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht : 0 < t) :
    binEntropy x + x * log t ≤ log (1 + t) := by
  have hdenominator : 0 < 1 + t := by linarith
  have hfirst := negMulLog_add_mul_log_le_sub hx0 (div_pos ht hdenominator)
  have hsecond := negMulLog_add_mul_log_le_sub (sub_nonneg.mpr hx1)
    (one_div_pos.mpr hdenominator)
  rw [log_div ht.ne' hdenominator.ne'] at hfirst
  rw [log_div one_ne_zero hdenominator.ne', log_one, zero_sub] at hsecond
  have hsum : t / (1 + t) + 1 / (1 + t) = 1 := by
    field_simp [hdenominator.ne']
    ring
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  linarith

/-- The normalized positive weight attains the binary log-partition bound. -/
@[capacity_shared_api]
theorem binEntropy_div_one_add_add_mul_log {t : ℝ} (ht : 0 < t) :
    binEntropy (t / (1 + t)) + (t / (1 + t)) * log t = log (1 + t) := by
  have hdenominator : 0 < 1 + t := by linarith
  have hcomplement : 1 - t / (1 + t) = 1 / (1 + t) := by
    field_simp [hdenominator.ne']
    ring
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, hcomplement]
  simp only [negMulLog_def]
  rw [log_div ht.ne' hdenominator.ne', log_div one_ne_zero hdenominator.ne', log_one]
  field_simp [hdenominator.ne']
  ring

end Real
