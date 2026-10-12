/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic

open MeasureTheory

namespace CapacityAtlas.Gaussian.Interference

noncomputable section

abbrev QAM (q : ℕ) := Fin q × Fin q

def qamValue {q : ℕ} (a : QAM q) : ℂ := (a.1.val : ℂ) + (a.2.val : ℂ) * Complex.I

def quantizeReal (q : ℕ) (hq : 0 < q) (x : ℝ) : Fin q :=
  ⟨min ⌊x + 1 / 2⌋₊ (q - 1), lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩

@[fun_prop]
theorem measurable_quantizeReal (q : ℕ) (hq : 0 < q) : Measurable (quantizeReal q hq) := by
  let f : ℕ → Fin q := fun k => ⟨min k (q - 1),
    lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩
  exact (measurable_of_countable f).comp
    (measurable_id.add_const (1 / 2 : ℝ)).nat_floor

theorem quantizeReal_correct {q : ℕ} (hq : 0 < q) (a : Fin q) {z : ℝ}
    (hz : |z| < 1 / 2) : quantizeReal q hq ((a.val : ℝ) + z) = a := by
  apply Fin.ext
  have hh := abs_lt.mp hz
  have hf : ⌊(a.val : ℝ) + z + 1 / 2⌋₊ = a.val := by
    apply Nat.floor_eq_on_Ico
    constructor <;> linarith
  simp only [quantizeReal, hf]
  exact min_eq_left (by omega)

def quantizeComplex (q : ℕ) (hq : 0 < q) (δ : ℝ) (z : ℂ) : QAM q :=
  (quantizeReal q hq (z.re / δ), quantizeReal q hq (z.im / δ))

@[fun_prop]
theorem measurable_quantizeComplex (q : ℕ) (hq : 0 < q) (δ : ℝ) :
    Measurable (quantizeComplex q hq δ) := by
  unfold quantizeComplex
  apply Measurable.prodMk <;>
    exact (measurable_quantizeReal q hq).comp (by fun_prop)

theorem quantizeComplex_correct {q : ℕ} (hq : 0 < q) {δ : ℝ} (hδ : 0 < δ)
    (a : QAM q) {z : ℂ} (hz : ‖z‖ < δ / 2) :
    quantizeComplex q hq δ ((δ : ℂ) * qamValue a + z) = a := by
  have hre : |z.re / δ| < 1 / 2 := by
    rw [abs_div, abs_of_pos hδ, div_lt_iff₀ hδ]
    linarith [Complex.abs_re_le_norm z]
  have him : |z.im / δ| < 1 / 2 := by
    rw [abs_div, abs_of_pos hδ, div_lt_iff₀ hδ]
    linarith [Complex.abs_im_le_norm z]
  have hr : (((δ : ℂ) * qamValue a + z).re / δ) = (a.1.val : ℝ) + z.re / δ := by
    simp [qamValue, add_div, hδ.ne']
  have hi : (((δ : ℂ) * qamValue a + z).im / δ) = (a.2.val : ℝ) + z.im / δ := by
    simp [qamValue, add_div, hδ.ne']
  apply Prod.ext
  · simpa only [quantizeComplex, hr] using quantizeReal_correct hq a.1 hre
  · simpa only [quantizeComplex, hi] using quantizeReal_correct hq a.2 him

theorem qamValue_norm_le {q : ℕ} (a : QAM q) : ‖qamValue a‖ ≤ 2 * (q : ℝ) := by
  have ha : (a.1.val : ℝ) ≤ q := by exact_mod_cast a.1.isLt.le
  have hb : (a.2.val : ℝ) ≤ q := by exact_mod_cast a.2.isLt.le
  have h := norm_add_le (a.1.val : ℂ) ((a.2.val : ℂ) * Complex.I)
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_I, mul_one] at h
  exact h.trans (by linarith)

end

end CapacityAtlas.Gaussian.Interference
