/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

open scoped BigOperators

namespace CapacityAtlas.LinearMulticast

private theorem exists_eval_ne_zero {σ K : Type} [Finite σ] [Field K] [Fintype K]
    (p : MvPolynomial σ K) (hp : p ≠ 0) (hd : p.totalDegree < Fintype.card K) :
    ∃ x : σ → K, MvPolynomial.eval x p ≠ 0 := by
  classical
  by_contra! h
  apply hp
  apply MvPolynomial.eq_zero_of_eval_eq_zero σ K p h
  rw [MvPolynomial.mem_restrictDegree]
  intro s hs i
  have hi := MvPolynomial.monomial_le_degreeOf i hs
  have ht := MvPolynomial.degreeOf_le_totalDegree p i
  omega

private theorem totalDegree_map_le {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) : (p.map f).totalDegree ≤ p.totalDegree := by
  classical
  apply Finset.sup_le
  intro s hs
  exact MvPolynomial.le_totalDegree (MvPolynomial.support_map_subset f p hs)

/-- Finitely many nonzero polynomials can simultaneously avoid zero over a
sufficiently large finite binary extension field. -/
theorem exists_binary_specialization {σ T : Type} [Fintype σ] [Fintype T]
    (p : T → MvPolynomial σ (ZMod 2)) (hp : ∀ t, p t ≠ 0) :
    ∃ b : ℕ, 0 < b ∧ ∃ x : σ → GaloisField 2 b,
      ∀ t, MvPolynomial.eval₂ (algebraMap (ZMod 2) (GaloisField 2 b)) x (p t) ≠ 0 := by
  classical
  let P := ∏ t, p t
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun t _ ↦ hp t)
  let b := P.totalDegree + 1
  have hb : 0 < b := Nat.succ_pos _
  let K := GaloisField 2 b
  letI : Fintype K := Fintype.ofFinite K
  let f : ZMod 2 →+* K := algebraMap (ZMod 2) K
  have hf : Function.Injective f := f.injective
  have hmap : P.map f ≠ 0 := by
    exact fun h ↦ hP ((MvPolynomial.map_injective f hf) (h.trans (map_zero _).symm))
  have hcard : Fintype.card K = 2 ^ b := by
    simpa only [Nat.card_eq_fintype_card] using GaloisField.card 2 b (Nat.ne_of_gt hb)
  have hbound : (P.map f).totalDegree < Fintype.card K := by
    rw [hcard]
    exact lt_of_le_of_lt (totalDegree_map_le f P)
      (lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.lt_two_pow_self (n := b)).le)
  obtain ⟨x, hx⟩ := exists_eval_ne_zero (P.map f) hmap hbound
  refine ⟨b, hb, x, ?_⟩
  have hx' : MvPolynomial.eval₂ f x P ≠ 0 := by
    simpa only [MvPolynomial.eval_map] using hx
  have hall : ∏ t, MvPolynomial.eval₂ f x (p t) ≠ 0 := by
    change (∏ t, (MvPolynomial.eval₂Hom f x) (p t)) ≠ 0
    rw [← map_prod]
    exact hx'
  exact fun t ↦ Finset.prod_ne_zero_iff.mp hall t (Finset.mem_univ t)

end CapacityAtlas.LinearMulticast
