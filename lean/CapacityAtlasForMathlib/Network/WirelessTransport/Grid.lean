/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! A separated square grid of simultaneous protocol-model links. -/

noncomputable section

namespace CapacityAtlas.WirelessTransport

abbrev GridIndex (m : ℕ) := Fin m × Fin m

def gridStep (R : ℝ) (m : ℕ) : ℝ := R / (2 * (m : ℝ))

def gridHop (R Δ : ℝ) (m : ℕ) : ℝ := R / (8 * (1 + Δ) * (m : ℝ))

def gridTx (R _Δ : ℝ) (m : ℕ) (i : GridIndex m) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(i.1.val : ℝ) * gridStep R m, (i.2.val : ℝ) * gridStep R m]

def gridRx (R Δ : ℝ) (m : ℕ) (i : GridIndex m) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(i.1.val : ℝ) * gridStep R m + gridHop R Δ m,
    (i.2.val : ℝ) * gridStep R m]

theorem gridStep_pos {R : ℝ} {m : ℕ} (hR : 0 < R) (hm : 0 < m) :
    0 < gridStep R m := by
  unfold gridStep
  positivity

theorem gridHop_pos {R Δ : ℝ} {m : ℕ} (hR : 0 < R) (hΔ : 0 < Δ) (hm : 0 < m) :
    0 < gridHop R Δ m := by
  unfold gridHop
  positivity

theorem gridHop_mul {R Δ : ℝ} {m : ℕ} (hΔ : 0 < Δ) :
    (1 + Δ) * gridHop R Δ m = gridStep R m / 4 := by
  unfold gridHop gridStep
  have hd : 1 + Δ ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem gridHop_le_step {R Δ : ℝ} {m : ℕ}
    (hR : 0 < R) (hΔ : 0 < Δ) (hm : 0 < m) :
    gridHop R Δ m ≤ gridStep R m / 4 := by
  have hp := gridHop_pos hR hΔ hm
  have he := gridHop_mul (R := R) (m := m) hΔ
  nlinarith

theorem grid_hop_length {R Δ : ℝ} {m : ℕ}
    (hR : 0 < R) (hΔ : 0 < Δ) (hm : 0 < m) (i : GridIndex m) :
    dist (gridTx R Δ m i) (gridRx R Δ m i) = gridHop R Δ m := by
  have hp := gridHop_pos hR hΔ hm
  rw [EuclideanSpace.dist_eq]
  simp [gridTx, gridRx, Fin.sum_univ_two, Real.dist_eq, Real.sqrt_sq_eq_abs,
    abs_of_pos hp]

theorem grid_coord_bounds {R : ℝ} {m : ℕ} (hR : 0 < R) (hm : 0 < m) (i : Fin m) :
    0 ≤ (i.val : ℝ) * gridStep R m ∧
      (i.val : ℝ) * gridStep R m + gridStep R m ≤ R / 2 := by
  have hs := gridStep_pos hR hm
  have hi : (i.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast i.isLt
  have he : (m : ℝ) * gridStep R m = R / 2 := by
    unfold gridStep
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    field_simp
  constructor
  · positivity
  · nlinarith

theorem gridTx_norm_le {R Δ : ℝ} {m : ℕ}
    (hR : 0 < R) (hm : 0 < m) (i : GridIndex m) : ‖gridTx R Δ m i‖ ≤ R := by
  have hx := grid_coord_bounds hR hm i.1
  have hy := grid_coord_bounds hR hm i.2
  have hs := gridStep_pos hR hm
  have he : ‖gridTx R Δ m i‖ ^ 2 =
      ((i.1.val : ℝ) * gridStep R m) ^ 2 + ((i.2.val : ℝ) * gridStep R m) ^ 2 := by
    simpa [gridTx, Fin.sum_univ_two] using
      EuclideanSpace.real_norm_sq_eq (gridTx R Δ m i)
  have hxx := mul_nonneg hx.1 (show 0 ≤ R / 2 - (i.1.val : ℝ) * gridStep R m by linarith)
  have hyy := mul_nonneg hy.1 (show 0 ≤ R / 2 - (i.2.val : ℝ) * gridStep R m by linarith)
  nlinarith

theorem gridRx_norm_le {R Δ : ℝ} {m : ℕ}
    (hR : 0 < R) (hΔ : 0 < Δ) (hm : 0 < m) (i : GridIndex m) :
    ‖gridRx R Δ m i‖ ≤ R := by
  have hx := grid_coord_bounds hR hm i.1
  have hy := grid_coord_bounds hR hm i.2
  have hs := gridStep_pos hR hm
  have hp := gridHop_pos hR hΔ hm
  have hps := gridHop_le_step hR hΔ hm
  have he : ‖gridRx R Δ m i‖ ^ 2 =
      ((i.1.val : ℝ) * gridStep R m + gridHop R Δ m) ^ 2 +
      ((i.2.val : ℝ) * gridStep R m) ^ 2 := by
    simpa [gridRx, Fin.sum_univ_two] using
      EuclideanSpace.real_norm_sq_eq (gridRx R Δ m i)
  have hx' : 0 ≤ (i.1.val : ℝ) * gridStep R m + gridHop R Δ m ∧
      (i.1.val : ℝ) * gridStep R m + gridHop R Δ m ≤ R / 2 := by
    constructor <;> linarith
  have hxx := mul_nonneg hx'.1 (show 0 ≤ R / 2 -
      ((i.1.val : ℝ) * gridStep R m + gridHop R Δ m) by linarith)
  have hyy := mul_nonneg hy.1 (show 0 ≤ R / 2 - (i.2.val : ℝ) * gridStep R m by linarith)
  nlinarith

theorem grid_coord_separation {R : ℝ} {m : ℕ} (hR : 0 < R) (hm : 0 < m)
    {i j : Fin m} (hij : i ≠ j) :
    gridStep R m ≤ dist ((i.val : ℝ) * gridStep R m) ((j.val : ℝ) * gridStep R m) := by
  have hs := gridStep_pos hR hm
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rw [Real.dist_eq]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hlt
    have hp := mul_le_mul_of_nonneg_right h hs.le
    have ha := neg_le_abs ((i.val : ℝ) * gridStep R m - (j.val : ℝ) * gridStep R m)
    nlinarith
  · have h : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hgt
    have hp := mul_le_mul_of_nonneg_right h hs.le
    have ha := le_abs_self ((i.val : ℝ) * gridStep R m - (j.val : ℝ) * gridStep R m)
    nlinarith

theorem grid_tx_separation {R Δ : ℝ} {m : ℕ} (hR : 0 < R) (hm : 0 < m)
    {i j : GridIndex m} (hij : i ≠ j) :
    gridStep R m ≤ dist (gridTx R Δ m i) (gridTx R Δ m j) := by
  by_cases hfirst : i.1 = j.1
  · have hsecond : i.2 ≠ j.2 := fun h => hij (Prod.ext hfirst h)
    have hc := PiLp.dist_apply_le (gridTx R Δ m i) (gridTx R Δ m j) (1 : Fin 2)
    change dist ((i.2.val : ℝ) * gridStep R m) ((j.2.val : ℝ) * gridStep R m) ≤
      dist (gridTx R Δ m i) (gridTx R Δ m j) at hc
    exact (grid_coord_separation hR hm hsecond).trans hc
  · have hc := PiLp.dist_apply_le (gridTx R Δ m i) (gridTx R Δ m j) (0 : Fin 2)
    change dist ((i.1.val : ℝ) * gridStep R m) ((j.1.val : ℝ) * gridStep R m) ≤
      dist (gridTx R Δ m i) (gridTx R Δ m j) at hc
    exact (grid_coord_separation hR hm hfirst).trans hc

theorem grid_protocol {R Δ : ℝ} {m : ℕ}
    (hR : 0 < R) (hΔ : 0 < Δ) (hm : 0 < m) {i j : GridIndex m} (hij : i ≠ j) :
    (1 + Δ) * dist (gridTx R Δ m i) (gridRx R Δ m i) ≤
      dist (gridTx R Δ m j) (gridRx R Δ m i) := by
  have hs := gridStep_pos hR hm
  have hsep := grid_tx_separation (Δ := Δ) hR hm hij.symm
  have ht := dist_triangle (gridTx R Δ m j) (gridRx R Δ m i) (gridTx R Δ m i)
  rw [dist_comm (gridRx R Δ m i), grid_hop_length hR hΔ hm] at ht
  rw [grid_hop_length hR hΔ hm]
  have hp := gridHop_le_step hR hΔ hm
  have he := gridHop_mul (R := R) (m := m) hΔ
  nlinarith

theorem grid_total_length {R Δ : ℝ} {m : ℕ}
    (hR : 0 < R) (hΔ : 0 < Δ) (hm : 0 < m) :
    ∑ i : GridIndex m, dist (gridTx R Δ m i) (gridRx R Δ m i) =
      R * (m : ℝ) / (8 * (1 + Δ)) := by
  simp only [grid_hop_length hR hΔ hm, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hd : 1 + Δ ≠ 0 := ne_of_gt (by linarith)
  unfold gridHop
  field_simp

end CapacityAtlas.WirelessTransport
