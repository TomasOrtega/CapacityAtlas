/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace CapacityAtlas.Gaussian.Interference

private theorem polynomial_ae_eval_ne_zero (p : Polynomial ℂ) (hp : p ≠ 0)
    (μ : Measure ℂ) [NullSingletonClass μ] : ∀ᵐ x ∂μ, p.eval x ≠ 0 := by
  simpa only [Polynomial.IsRoot, Set.mem_setOf_eq] using
    (Polynomial.finite_setOf_isRoot hp).countable.ae_notMem μ

private theorem ae_eval_ne_zero_fin {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (hp : p ≠ 0)
    (μ : Fin n → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] :
    ∀ᵐ x ∂Measure.pi μ, MvPolynomial.eval x p ≠ 0 := by
  classical
  induction n with
  | zero =>
    filter_upwards [] with x hx
    apply hp
    apply MvPolynomial.funext
    intro y
    simpa only [Subsingleton.elim y x, map_zero] using hx
  | succ n ih =>
    let q := MvPolynomial.finSuccEquiv ℂ n p
    have hq : q ≠ 0 := by
      exact fun h => hp ((MvPolynomial.finSuccEquiv ℂ n).injective
        (h.trans (map_zero _).symm))
    let k := q.natDegree
    have hk : q.coeff k ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
    have htail := ih (q.coeff k) hk (fun i => μ i.succ)
    have hc : Continuous (fun z : ℂ × (Fin n → ℂ) =>
        (Fin.cons z.1 z.2 : Fin (n + 1) → ℂ)) := by
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_fst
      · exact (continuous_apply j).comp continuous_snd
    have hm : MeasurableSet {z : ℂ × (Fin n → ℂ) |
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0} := by
      exact (isClosed_eq ((MvPolynomial.continuous_eval p).comp hc)
        continuous_const).measurableSet.compl
    have hinner : ∀ᵐ x ∂Measure.pi (fun i => μ i.succ),
        ∀ᵐ y ∂μ 0, MvPolynomial.eval (Fin.cons y x) p ≠ 0 := by
      filter_upwards [htail] with x hx
      have hmap : q.map (MvPolynomial.eval x) ≠ 0 := by
        intro h
        have := congrArg (fun r : Polynomial ℂ => r.coeff k) h
        exact hx (by simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using this)
      simpa only [MvPolynomial.eval_eq_eval_mv_eval', q] using
        polynomial_ae_eval_ne_zero (q.map (MvPolynomial.eval x)) hmap (μ 0)
    have hprod : ∀ᵐ z ∂(μ 0).prod (Measure.pi (fun i => μ i.succ)),
        MvPolynomial.eval (Fin.cons z.1 z.2) p ≠ 0 := (Measure.ae_prod_iff_ae_ae hm).mpr
      ((Measure.ae_ae_comm hm).mpr hinner)
    have hmp := measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
    simp only [Fin.succAbove_zero] at hmp
    have h := hmp.quasiMeasurePreserving.ae hprod
    filter_upwards [h] with x hx
    change MvPolynomial.eval (Fin.cons (x 0) (fun j => x j.succ)) p ≠ 0 at hx
    have hcons : (Fin.cons (x 0) (fun j => x j.succ) : Fin (n + 1) → ℂ) = x := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    rwa [hcons] at hx

/-- Independent nonatomic coordinates avoid every nonzero complex polynomial almost surely. -/
theorem ae_eval_ne_zero {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℂ) (hp : p ≠ 0)
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] :
    ∀ᵐ x ∂Measure.pi μ, MvPolynomial.eval x p ≠ 0 := by
  classical
  let e := (Fintype.equivFin ι).symm
  let q := MvPolynomial.rename e.symm p
  have hq : q ≠ 0 := by
    intro h
    apply hp
    exact (MvPolynomial.rename_injective e.symm e.symm.injective)
      (h.trans (map_zero _).symm)
  have h := ae_eval_ne_zero_fin q hq (fun i => μ (e i))
  have h' := (measurePreserving_piCongrLeft μ e).symm.quasiMeasurePreserving.ae h
  simp only [q, MvPolynomial.eval_rename] at h'
  filter_upwards [h'] with x hx
  have heq : (MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) e).symm x ∘ e.symm = x := by
    funext j
    change x (e (e.symm j)) = x j
    rw [Equiv.apply_symm_apply]
  rwa [heq] at hx

end CapacityAtlas.Gaussian.Interference
