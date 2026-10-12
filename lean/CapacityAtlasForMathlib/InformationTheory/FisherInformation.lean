/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open scoped BigOperators

namespace CapacityAtlas.MeasureInformation

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- The directional score is the density derivative divided by the density. -/
noncomputable def directionalScore (density : E → ℝ) (v x : E) : ℝ :=
  lineDeriv ℝ density x v / density x

/-- Directional Fisher information, computed from the density's actual line derivative. -/
noncomputable def directionalFisherWith (reference : Measure E) (density : E → ℝ) (v : E) : ℝ :=
  ∫ x, (lineDeriv ℝ density x v) ^ 2 / density x ∂reference

theorem directionalFisherWith_eq_integral_score_sq (reference : Measure E)
    (density : E → ℝ) (v : E) :
    directionalFisherWith reference density v =
      ∫ x, density x * directionalScore density v x ^ 2 ∂reference := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : density x = 0
  · simp [directionalScore, hx]
  · simp only [directionalScore]
    field_simp

theorem directionalFisherWith_nonneg (reference : Measure E) (density : E → ℝ) (v : E)
    (hpos : ∀ x, 0 ≤ density x) : 0 ≤ directionalFisherWith reference density v :=
  integral_nonneg (fun x ↦ div_nonneg (sq_nonneg _) (hpos x))

variable [Fintype ι]

omit [MeasurableSpace E] in
theorem hasLineDerivAt_weighted_sum (w : ι → ℝ) (density derivative : ι → E → ℝ)
    (x v : E) (hderiv : ∀ i, HasLineDerivAt ℝ (density i) (derivative i x) x v) :
    HasLineDerivAt ℝ (fun y ↦ ∑ i, w i * density i y)
      (∑ i, w i * derivative i x) x v := by
  exact HasDerivAt.fun_sum (fun i _ ↦ (hderiv i).const_mul (w i))

/-- Weighted Cauchy–Schwarz for the square of a mixture score. -/
theorem mixture_score_sq_le (w p d : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 < p i) :
    (∑ i, w i * d i) ^ 2 / (∑ i, w i * p i) ≤ ∑ i, w i * (d i ^ 2 / p i) := by
  apply div_le_of_le_mul₀
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i) (hp i).le))
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i) (div_nonneg (sq_nonneg _) (hp i).le)))
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (r := fun i ↦ w i * d i)
    (f := fun i ↦ w i * (d i ^ 2 / p i)) (g := fun i ↦ w i * p i)
  · intro i _
    exact mul_nonneg (hw i) (div_nonneg (sq_nonneg _) (hp i).le)
  · intro i _
    exact mul_nonneg (hw i) (hp i).le
  · intro i _
    apply le_of_eq
    field_simp [(hp i).ne']

section FiniteMixture

variable (reference : Measure E) (w : ι → ℝ) (density derivative : ι → E → ℝ) (v : E)
  (hw : ∀ i, 0 ≤ w i) (hpos : ∀ i x, 0 < density i x)
  (hmeas : ∀ i, Measurable (density i)) (hdmeas : ∀ i, Measurable (derivative i))
  (hderiv : ∀ i x, HasLineDerivAt ℝ (density i) (derivative i x) x v)
  (hint : ∀ i, Integrable (fun x ↦ derivative i x ^ 2 / density i x) reference)

include hw hpos hmeas hdmeas hderiv hint

theorem integrable_fisher_weighted_sum :
    Integrable (fun x ↦ (lineDeriv ℝ (fun y ↦ ∑ i, w i * density i y) x v) ^ 2 /
      (∑ i, w i * density i x)) reference := by
  have hline (x : E) : lineDeriv ℝ (fun y ↦ ∑ i, w i * density i y) x v =
      ∑ i, w i * derivative i x :=
    (hasLineDerivAt_weighted_sum w density derivative x v (fun i ↦ hderiv i x)).lineDeriv
  simp_rw [hline]
  have hupper : Integrable (fun x ↦ ∑ i, w i * (derivative i x ^ 2 / density i x)) reference :=
    integrable_finsetSum _ (fun i _ ↦ (hint i).const_mul (w i))
  apply hupper.mono' (Measurable.aestronglyMeasurable (by fun_prop))
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _)
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i) (hpos i x).le)))]
  exact mixture_score_sq_le w (fun i ↦ density i x) (fun i ↦ derivative i x) hw
    (fun i ↦ hpos i x)

/-- Fisher information is convex under finite mixtures of differentiable positive densities. -/
theorem directionalFisherWith_weighted_sum_le :
    directionalFisherWith reference (fun x ↦ ∑ i, w i * density i x) v ≤
      ∑ i, w i * directionalFisherWith reference (density i) v := by
  have hline (x : E) : lineDeriv ℝ (fun y ↦ ∑ i, w i * density i y) x v =
      ∑ i, w i * derivative i x :=
    (hasLineDerivAt_weighted_sum w density derivative x v (fun i ↦ hderiv i x)).lineDeriv
  have hupper : Integrable (fun x ↦ ∑ i, w i * (derivative i x ^ 2 / density i x)) reference :=
    integrable_finsetSum _ (fun i _ ↦ (hint i).const_mul (w i))
  calc
    directionalFisherWith reference (fun x ↦ ∑ i, w i * density i x) v ≤
        ∫ x, ∑ i, w i * (derivative i x ^ 2 / density i x) ∂reference := by
      apply integral_mono
        (integrable_fisher_weighted_sum reference w density derivative v hw hpos
          hmeas hdmeas hderiv hint) hupper
      intro x
      dsimp only
      rw [hline]
      exact mixture_score_sq_le w (fun i ↦ density i x) (fun i ↦ derivative i x) hw
        (fun i ↦ hpos i x)
    _ = ∑ i, w i * directionalFisherWith reference (density i) v := by
      rw [integral_finsetSum _ (fun i _ ↦ (hint i).const_mul (w i))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [(hderiv i x).lineDeriv]

end FiniteMixture

end CapacityAtlas.MeasureInformation
