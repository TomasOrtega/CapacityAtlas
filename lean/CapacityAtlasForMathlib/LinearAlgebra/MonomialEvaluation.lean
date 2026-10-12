/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators

namespace CapacityAtlas.MonomialEvaluation

variable {C V R : Type*} [Fintype C] [Fintype V] [DecidableEq C]
  [CommRing R]

/-- The variables belonging to one row of a monomial evaluation matrix. -/
noncomputable def rowExponent (r : C) (e : V → ℕ) : C × V →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun p ↦ if p.1 = r then e p.2 else 0)

@[simp] theorem rowExponent_apply (r s : C) (e : V → ℕ) (v : V) :
    rowExponent r e (s, v) = if s = r then e v else 0 := rfl

/-- Distinct rows have separate indeterminates. -/
noncomputable def matrix (e : C → V → ℕ) : Matrix C C (MvPolynomial (C × V) R) :=
  fun r c ↦ MvPolynomial.monomial (rowExponent r (e c)) 1

noncomputable def permutationExponent (e : C → V → ℕ) (p : Equiv.Perm C) :
    C × V →₀ ℕ :=
  ∑ c, rowExponent (p c) (e c)

theorem permutationExponent_apply (e : C → V → ℕ) (p : Equiv.Perm C)
    (r : C) (v : V) : permutationExponent e p (r, v) = e (p.symm r) v := by
  classical
  simp only [permutationExponent, Finsupp.coe_finsetSum, Finset.sum_apply, rowExponent_apply]
  rw [Finset.sum_eq_single (p.symm r)]
  · simp
  · intro c _ hc
    have h : r ≠ p c := by
      intro h
      apply hc
      exact p.injective (by simpa using h.symm)
    simp [h]
  · simp

theorem permutationExponent_injective {e : C → V → ℕ} (he : Function.Injective e) :
    Function.Injective (permutationExponent e) := by
  intro p q hpq
  have h : p.symm = q.symm := by
    ext r
    apply he
    funext v
    simpa only [permutationExponent_apply] using congrArg (fun d ↦ d (r, v)) hpq
  exact inv_injective h

theorem product_entry (e : C → V → ℕ) (p : Equiv.Perm C) :
    (∏ c, matrix (R := R) e (p c) c) =
      MvPolynomial.monomial (permutationExponent e p) 1 := by
  classical
  simpa only [matrix, permutationExponent] using
    (MvPolynomial.monomial_sum_one (R := R) Finset.univ
      (fun c ↦ rowExponent (p c) (e c))).symm

/-- The identity permutation contributes a coefficient that no other permutation can cancel. -/
theorem coefficient_det (e : C → V → ℕ) (he : Function.Injective e) :
    MvPolynomial.coeff (permutationExponent e 1) (Matrix.det (matrix (R := R) e)) = 1 := by
  classical
  rw [Matrix.det_apply, MvPolynomial.coeff_sum]
  simp_rw [product_entry, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro p _ hp
    have h : permutationExponent e p ≠ permutationExponent e 1 :=
      fun h ↦ hp (permutationExponent_injective he h)
    simp [h]
  · simp

/-- A square matrix evaluating distinct monomials at independent rows has a nonzero
determinant polynomial. -/
theorem determinant_ne_zero [Nontrivial R] (e : C → V → ℕ)
    (he : Function.Injective e) : Matrix.det (matrix (R := R) e) ≠ 0 := by
  intro h
  have hc := coefficient_det (R := R) e he
  rw [h, MvPolynomial.coeff_zero] at hc
  exact zero_ne_one hc

theorem eval_matrix (e : C → V → ℕ) (x : C × V → R) (r c : C) :
    MvPolynomial.eval x (matrix (R := R) e r c) = ∏ v, x (r, v) ^ e c v := by
  classical
  simp only [matrix, MvPolynomial.eval_monomial, one_mul]
  rw [Finsupp.prod_fintype]
  · simp only [Fintype.prod_prod_type, rowExponent_apply]
    rw [Finset.prod_eq_single r]
    · simp
    · intro s _ hs
      simp [hs]
    · simp
  · simp

end CapacityAtlas.MonomialEvaluation
