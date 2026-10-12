/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

open Filter Set Real
open scoped Topology

namespace CapacityAtlas.MeasureInformation

lemma tendsto_log_add_mul_sub_log (d a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ ↦ log (d + t * a) - log t) atTop (𝓝 (log a)) := by
  have h := (tendsto_log_comp_add_sub_log (d / a)).add_const (log a)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-(d / a))] with t ht ht'
  have hta : 0 < t + d / a := by linarith
  have heq : d + t * a = a * (t + d / a) := by field_simp; ring
  rw [heq, log_mul ha.ne' hta.ne']
  ring

/-- A scalar entropy lower bound obtained by integrating a rational derivative bound. -/
theorem entropy_power_mul_ge_of_heat_derivative_bound
    (H J : ℝ → ℝ) {d a c : ℝ} (hd : 0 < d) (ha : 0 < a)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt H (J t / 2) t)
    (hbound : ∀ t, 0 < t → J t ≤ d * a / (d + t * a))
    (hlimit : Tendsto (fun t : ℝ ↦ H t - d / 2 * log t) atTop (𝓝 (d / 2 * c))) :
    d ≤ exp (2 * H 0 / d - c) * a := by
  let F := fun t ↦ H t - d / 2 * log (d + t * a)
  have hF (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt F (J t / 2 - d / 2 * (a / (d + t * a))) t := by
    have hp : 0 < d + t * a := add_pos_of_pos_of_nonneg hd (mul_nonneg ht ha.le)
    have hh := (((hasDerivAt_id t).mul_const a).const_add d).log hp.ne'
    convert! (hderiv t ht).sub (hh.const_mul (d / 2)) using 1
    simp only [id_eq, one_mul]
  have hanti : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t ht ↦ (hF t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hF t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    have hb := hbound t ht'
    have heq : d / 2 * (a / (d + t * a)) = (d * a / (d + t * a)) / 2 := by ring
    rw [heq]
    linarith
  have hFbound (t : ℝ) (ht : 0 ≤ t) : F t ≤ F 0 := hanti (by simp) ht ht
  have hFlim : Tendsto F atTop (𝓝 (d / 2 * c - d / 2 * log a)) := by
    convert hlimit.sub ((tendsto_log_add_mul_sub_log d a ha).const_mul (d / 2)) using 1
    ext t
    dsimp only [F]
    ring
  have hle : d / 2 * c - d / 2 * log a ≤ H 0 - d / 2 * log d := by
    have hi := le_of_tendsto hFlim (eventually_atTop.2 ⟨0, hFbound⟩)
    simpa only [F, zero_mul, add_zero] using hi
  have hlog : log (d / a) ≤ 2 * H 0 / d - c := by
    rw [log_div hd.ne' ha.ne']
    have hi : log d - log a + c ≤ 2 * H 0 / d := (le_div_iff₀ hd).mpr (by nlinarith)
    linarith
  have hexp := exp_le_exp.mpr hlog
  rw [exp_log (div_pos hd ha)] at hexp
  exact (div_le_iff₀ ha).mp hexp

/-- The scalar Stam bound, with zero initial Fisher information covered by a positive limit. -/
theorem entropy_power_mul_fisher_ge_of_heat_flow
    (H J : ℝ → ℝ) {d c : ℝ} (hd : 0 < d) (hJ : 0 ≤ J 0)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt H (J t / 2) t)
    (hbound : ∀ t, 0 < t → J t ≤ d * J 0 / (d + t * J 0))
    (hlimit : Tendsto (fun t : ℝ ↦ H t - d / 2 * log t) atTop (𝓝 (d / 2 * c))) :
    d ≤ exp (2 * H 0 / d - c) * J 0 := by
  let P := exp (2 * H 0 / d - c)
  have hP : 0 < P := exp_pos _
  apply le_of_forall_pos_le_add
  intro ε hε
  let a := J 0 + ε / P
  have ha : 0 < a := add_pos_of_nonneg_of_pos hJ (div_pos hε hP)
  have hJa : J 0 ≤ a := le_add_of_nonneg_right (div_nonneg hε.le hP.le)
  have hb (t : ℝ) (ht : 0 < t) : J t ≤ d * a / (d + t * a) := by
    apply (hbound t ht).trans
    apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hd (mul_nonneg ht.le hJ))
      (add_pos_of_pos_of_nonneg hd (mul_nonneg ht.le ha.le))).mpr
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hJa)]
  have hi := entropy_power_mul_ge_of_heat_derivative_bound H J hd ha hderiv hb hlimit
  change d ≤ P * J 0 + ε
  change d ≤ P * (J 0 + ε / P) at hi
  have heq : P * (J 0 + ε / P) = P * J 0 + ε := by field_simp
  rwa [heq] at hi

/-- A pointwise Stam bound makes entropy power grow at least linearly. -/
theorem entropy_power_add_le_of_heat_flow
    (H J : ℝ → ℝ) {d c : ℝ} (hd : 0 < d)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt H (J t / 2) t)
    (hstam : ∀ t, 0 ≤ t → d ≤ exp (2 * H t / d - c) * J t)
    {t : ℝ} (ht : 0 ≤ t) :
    exp (2 * H 0 / d - c) + t ≤ exp (2 * H t / d - c) := by
  let P := fun s ↦ exp (2 * H s / d - c) - s
  have hP (s : ℝ) (hs : 0 ≤ s) :
      HasDerivAt P (exp (2 * H s / d - c) * J s / d - 1) s := by
    have h := ((((hderiv s hs).const_mul 2).div_const d).sub_const c).exp.sub (hasDerivAt_id s)
    apply h.congr_deriv
    ring
  have hmono : MonotoneOn P (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun s hs ↦ (hP s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (hP s (interior_subset hs)).hasDerivWithinAt)
    intro s hs
    have hs' : 0 ≤ s := le_of_lt (show 0 < s by simpa only [interior_Ici, mem_Ioi] using hs)
    exact sub_nonneg.mpr ((le_div_iff₀ hd).mpr (by simpa only [one_mul] using hstam s hs'))
  have hi := hmono (by simp) ht ht
  dsimp only [P] at hi
  linarith

lemma convexOn_log_exp_add {C : ℝ} (hC : 0 ≤ C) :
    ConvexOn ℝ univ (fun x : ℝ ↦ log (exp x + C)) := by
  have hderiv (x : ℝ) : HasDerivAt (fun y ↦ log (exp y + C)) (exp x / (exp x + C)) x :=
    ((hasDerivAt_exp x).add_const C).log (add_pos_of_pos_of_nonneg (exp_pos x) hC).ne'
  apply Monotone.convexOn_univ_of_deriv (fun x ↦ (hderiv x).differentiableAt)
  intro x y hxy
  rw [(hderiv x).deriv, (hderiv y).deriv]
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (exp_pos x) hC)
    (add_pos_of_pos_of_nonneg (exp_pos y) hC)).mpr
  nlinarith [mul_nonneg hC (sub_nonneg.mpr (exp_le_exp.mpr hxy))]

/-- Finite conditioning preserves an entropy-power inequality with a fixed added power. -/
theorem exp_weighted_sum_add_le {β : Type*} [Fintype β]
    (u : β → ℝ) (hu : ∀ j, 0 ≤ u j) (hu1 : ∑ j, u j = 1)
    (a b : β → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ j, exp (a j) + C ≤ exp (b j)) :
    exp (∑ j, u j * a j) + C ≤ exp (∑ j, u j * b j) := by
  have hj := (convexOn_log_exp_add hC).map_sum_le (t := Finset.univ)
    (fun j _ ↦ hu j) hu1 (fun j _ ↦ mem_univ (a j))
  simp only [smul_eq_mul] at hj
  have hlog : log (exp (∑ j, u j * a j) + C) ≤ ∑ j, u j * b j := by
    apply hj.trans
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hu j)
    simpa only [log_exp] using log_le_log
      (add_pos_of_pos_of_nonneg (exp_pos (a j)) hC) (hrow j)
  have hi := exp_le_exp.mpr hlog
  rwa [exp_log (add_pos_of_pos_of_nonneg (exp_pos _) hC)] at hi

end CapacityAtlas.MeasureInformation
