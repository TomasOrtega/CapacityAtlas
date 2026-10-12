/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.LinearAlgebra.MonomialEvaluation
import Mathlib.Data.Fintype.Card

open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference

variable (U : Type*) [Fintype U] [DecidableEq U]

abbrev Cross := {p : U × U // p.1 ≠ p.2}

abbrev Box (n : ℕ) := Cross U → Fin n

abbrev Columns (n : ℕ) := Box U n ⊕ Box U (n + 1)

variable {U}

def beamExponent {n : ℕ} (a : Box U n) (p : U × U) : ℕ :=
  if h : p.1 ≠ p.2 then (a ⟨p, h⟩).val else 0

omit [Fintype U] in
@[simp] theorem beamExponent_cross {n : ℕ} (a : Box U n) (p : Cross U) :
    beamExponent a p.val = (a p).val := by simp [beamExponent, p.property]

omit [Fintype U] in
@[simp] theorem beamExponent_diag {n : ℕ} (a : Box U n) (i : U) :
    beamExponent a (i, i) = 0 := by simp [beamExponent]

def columnExponent {n : ℕ} (i : U) : Columns U n → U × U → ℕ
  | Sum.inl a, p => beamExponent a p + if p = (i, i) then 1 else 0
  | Sum.inr a, p => beamExponent a p

omit [Fintype U] in
theorem columnExponent_injective {n : ℕ} (i : U) :
    Function.Injective (columnExponent (n := n) i) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr 1
      funext p
      apply Fin.ext
      have h := congrFun hab p.val
      have hp : p.val ≠ (i, i) := by intro hp; exact p.property (by rw [hp])
      simpa [columnExponent, hp] using h
    | inr b =>
      have h := congrFun hab (i, i)
      simp [columnExponent] at h
  | inr a =>
    cases b with
    | inl b =>
      have h := congrFun hab (i, i)
      simp [columnExponent] at h
    | inr b =>
      congr 1
      funext p
      apply Fin.ext
      have h := congrFun hab p.val
      simpa [columnExponent] using h

def shifted {n : ℕ} (a : Box U n) (p : Cross U) : Box U (n + 1) :=
  fun q ↦ ⟨(a q).val + if q = p then 1 else 0, by
    split_ifs <;> have := (a q).isLt <;> omega⟩

omit [Fintype U] in
theorem shifted_exponent {n : ℕ} (a : Box U n) (p : Cross U) (q : U × U) :
    beamExponent (shifted a p) q = beamExponent a q + if q = p.val then 1 else 0 := by
  by_cases hq : q.1 = q.2
  · have hp : q ≠ p.val := by intro hp; exact p.property (hp ▸ hq)
    simp [beamExponent, hq, hp]
  · simp only [beamExponent, dif_pos hq, shifted, Subtype.ext_iff]

variable {R : Type*} [CommRing R]

def beam {n : ℕ} (h : U × U → R) (a : Box U n) : R :=
  ∏ p, h p ^ beamExponent a p

theorem beam_shifted {n : ℕ} (h : U × U → R) (a : Box U n) (p : Cross U) :
    beam h (shifted a p) = h p.val * beam h a := by
  classical
  simp only [beam, shifted_exponent, pow_add, Finset.prod_mul_distrib]
  have ht : (∏ q, h q ^ (if q = p.val then 1 else 0 : ℕ)) = h p.val := by
    rw [Finset.prod_eq_single p.val]
    · simp
    · intro q _ hq
      simp [hq]
    · simp
  rw [ht, mul_comm]

theorem eval_column {n : ℕ} (h : U × U → R) (i : U) (a : Columns U n) :
    (∏ p, h p ^ columnExponent i a p) =
      Sum.elim (fun a ↦ h (i, i) * beam h a) (beam h) a := by
  classical
  cases a with
  | inl a =>
    simp only [columnExponent, pow_add, Finset.prod_mul_distrib, Sum.elim_inl]
    have ht : (∏ q, h q ^ (if q = (i, i) then 1 else 0 : ℕ)) = h (i, i) := by
      rw [Finset.prod_eq_single (i, i)]
      · simp
      · intro q _ hq
        simp [hq]
      · simp
    rw [ht, mul_comm]
    rfl
  | inr a => rfl

noncomputable def decodingPolynomial {n : ℕ} (i : U) :
    MvPolynomial (Columns U n × (U × U)) R :=
  Matrix.det (MonomialEvaluation.matrix (columnExponent (n := n) i))

theorem decodingPolynomial_ne_zero [Nontrivial R] {n : ℕ} (i : U) :
    decodingPolynomial (R := R) (n := n) i ≠ 0 :=
  MonomialEvaluation.determinant_ne_zero _ (columnExponent_injective i)

theorem card_cross : Fintype.card (Cross U) = Fintype.card U * (Fintype.card U - 1) := by
  classical
  let e : {p : U × U // p.1 = p.2} ≃ U :=
    { toFun := fun p ↦ p.val.1
      invFun := fun i ↦ ⟨(i, i), rfl⟩
      left_inv := by rintro ⟨⟨i, j⟩, hij⟩; cases hij; rfl
      right_inv := fun _ ↦ rfl }
  have he := Fintype.card_congr e
  change Fintype.card {p : U × U // ¬p.1 = p.2} = _
  rw [Fintype.card_subtype_compl, Fintype.card_prod, he, Nat.mul_sub_left_distrib,
    Nat.mul_one]

theorem card_box (n : ℕ) : Fintype.card (Box U n) = n ^ Fintype.card (Cross U) := by
  simp [Box]

theorem card_columns (n : ℕ) : Fintype.card (Columns U n) =
    n ^ Fintype.card (Cross U) + (n + 1) ^ Fintype.card (Cross U) := by
  simp [Columns]

end CapacityAtlas.Gaussian.Interference
