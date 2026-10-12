/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Monomials
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped BigOperators Matrix

namespace CapacityAtlas.Gaussian.Interference

variable {U R : Type*} [Fintype U] [DecidableEq U] [Field R] {n : ℕ}

abbrev FadingBlock (U : Type*) [DecidableEq U] (n : ℕ) (R : Type*) :=
  Columns U n → U × U → R

def decodingMatrix (h : FadingBlock U n R) (i : U) :
    Matrix (Columns U n) (Columns U n) R :=
  fun r ↦ Sum.elim (fun a ↦ h r (i, i) * beam (h r) a) (beam (h r))

theorem eval_decodingPolynomial (h : FadingBlock U n R) (i : U) :
    MvPolynomial.eval (fun p ↦ h p.1 p.2) (decodingPolynomial (n := n) i) =
      (decodingMatrix h i).det := by
  classical
  change (MvPolynomial.eval (fun p ↦ h p.1 p.2))
    (Matrix.det (MonomialEvaluation.matrix (columnExponent i))) = _
  rw [RingHom.map_det]
  congr 1
  ext r c
  exact (MonomialEvaluation.eval_matrix _ _ r c).trans (eval_column _ _ _)

noncomputable def decoder (h : FadingBlock U n R) (i : U) :
    (Columns U n → R) →ₗ[R] (Box U n → R) :=
  LinearMap.pi (fun a ↦ (LinearMap.proj (Sum.inl a)).comp
    (decodingMatrix h i)⁻¹.mulVecLin)

theorem decoder_column (h : FadingBlock U n R) (i : U)
    (hi : (decodingMatrix h i).det ≠ 0) (c : Columns U n) (a : Box U n) :
    decoder h i ((decodingMatrix h i).col c) a =
      (Pi.single c (1 : R) : Columns U n → R) (Sum.inl a) := by
  change ((decodingMatrix h i)⁻¹ *ᵥ (decodingMatrix h i).col c) (Sum.inl a) = _
  rw [← Matrix.mulVec_single_one, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hi), Matrix.one_mulVec]

def receivedColumn (h : FadingBlock U n R) (i u : U) (a : Box U n) :
    Columns U n → R := fun r ↦ h r (i, u) * beam (h r) a

theorem receivedColumn_self (h : FadingBlock U n R) (i : U) (a : Box U n) :
    receivedColumn h i i a = (decodingMatrix h i).col (Sum.inl a) := rfl

theorem receivedColumn_other (h : FadingBlock U n R) (i u : U) (hiu : i ≠ u)
    (a : Box U n) :
    receivedColumn h i u a =
      (decodingMatrix h i).col (Sum.inr (shifted a ⟨(i, u), hiu⟩)) := by
  funext r
  exact (beam_shifted (h r) a ⟨(i, u), hiu⟩).symm

theorem decoder_receivedColumn (h : FadingBlock U n R) (i : U)
    (hi : (decodingMatrix h i).det ≠ 0) (u : U) (a : Box U n) :
    decoder h i (receivedColumn h i u a) = if i = u then Pi.single a 1 else 0 := by
  ext b
  by_cases hiu : i = u
  · subst u
    rw [receivedColumn_self, decoder_column h i hi]
    simp [Pi.single_apply]
  · rw [receivedColumn_other h i u hiu, decoder_column h i hi]
    simp [hiu]

def transmitted (h : FadingBlock U n R) (x : Box U n → R) : Columns U n → R :=
  fun r ↦ ∑ a, beam (h r) a * x a

def received (h : FadingBlock U n R) (x : U → Box U n → R) (i : U) :
    Columns U n → R := fun r ↦ ∑ u, h r (i, u) * transmitted h (x u) r

theorem received_eq_sum (h : FadingBlock U n R) (x : U → Box U n → R) (i : U) :
    received h x i = ∑ u, ∑ a, x u a • receivedColumn h i u a := by
  ext r
  simp only [received, transmitted, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    receivedColumn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Every desired stream is recovered while every other transmitter is canceled. -/
theorem decoder_received (h : FadingBlock U n R) (i : U)
    (hi : (decodingMatrix h i).det ≠ 0) (x : U → Box U n → R) :
    decoder h i (received h x i) = x i := by
  classical
  rw [received_eq_sum]
  simp_rw [map_sum, map_smul, decoder_receivedColumn h i hi]
  ext a
  simp only [ite_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  simp [Pi.single_apply]

theorem decoder_received_add_noise (h : FadingBlock U n R) (i : U)
    (hi : (decodingMatrix h i).det ≠ 0) (x : U → Box U n → R)
    (z : Columns U n → R) :
    decoder h i (received h x i + z) = x i + decoder h i z := by
  rw [map_add, decoder_received h i hi]

end CapacityAtlas.Gaussian.Interference
