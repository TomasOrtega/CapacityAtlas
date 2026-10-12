/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.LinearMulticast.Polynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators Classical

namespace CapacityAtlas.LinearMulticast

/-- Each wire depends on locally available input symbols and earlier wires. -/
structure Circuit (Input Wire : Type) where
  height : Wire → ℕ
  input : Wire → Input → Prop
  parent : Wire → Wire → Prop
  parent_lt : ∀ e p, parent e p → height p < height e

namespace Circuit

variable {I W : Type} [Fintype W] (G : Circuit I W)

abbrev Variable (_G : Circuit I W) := W × (I ⊕ W)

noncomputable def transfer {R : Type*} [CommSemiring R]
    (c : G.Variable → R) (e : W) (i : I) : R := by
  classical
  exact (if G.input e i then c (e, Sum.inl i) else 0) +
    ∑ p : W, if h : G.parent e p then c (e, Sum.inr p) * transfer c p i else 0
termination_by G.height e
decreasing_by exact G.parent_lt _ _ h

theorem transfer_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (c : G.Variable → R) (e : W) (i : I) :
    f (G.transfer c e i) = G.transfer (f ∘ c) e i := by
  classical
  induction h : G.height e using Nat.strong_induction_on generalizing e with
  | h n ih =>
    rw [transfer, transfer, map_add, map_sum]
    congr 1
    · split_ifs <;> simp
    · apply Finset.sum_congr rfl
      intro p _
      split_ifs with hp
      · rw [map_mul, ih _ (h ▸ G.parent_lt e p hp) p rfl]
        rfl
      · simp

noncomputable def observed {R : Type*} [CommSemiring R]
    (c : G.Variable → R) (port : I ⊕ W) (i : I) : R := by
  classical
  exact match port with
    | Sum.inl j => if j = i then 1 else 0
    | Sum.inr e => G.transfer c e i

theorem observed_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (c : G.Variable → R) (port : I ⊕ W) (i : I) :
    f (G.observed c port i) = G.observed (f ∘ c) port i := by
  classical
  cases port with
  | inl j => simp [observed, apply_ite f]
  | inr e => exact G.transfer_map f c e i

/-- Rows are the receiver's chosen observable ports. -/
noncomputable def outputMatrix {R : Type*} [CommSemiring R]
    (c : G.Variable → R) (output : I → I ⊕ W) : Matrix I I R :=
  fun j i ↦ G.observed c (output j) i

theorem outputMatrix_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (c : G.Variable → R) (output : I → I ⊕ W) :
    (G.outputMatrix c output).map f = G.outputMatrix (f ∘ c) output := by
  ext j i
  exact G.observed_map f c (output j) i

/-- Per-receiver routing assignments imply one finite binary-field code
whose observations recover every input at every receiver. -/
theorem simultaneous [Fintype I] {T : Type} [Fintype T]
    (output : T → I → I ⊕ W)
    (route : ∀ t, ∃ c : G.Variable → ZMod 2, G.outputMatrix c (output t) = 1) :
    ∃ b : ℕ, 0 < b ∧ ∃ c : G.Variable → GaloisField 2 b,
      ∀ t, (G.outputMatrix c (output t)).det ≠ 0 := by
  classical
  let x : G.Variable → MvPolynomial G.Variable (ZMod 2) := MvPolynomial.X
  let p : T → MvPolynomial G.Variable (ZMod 2) :=
    fun t ↦ (G.outputMatrix x (output t)).det
  have hp : ∀ t, p t ≠ 0 := by
    intro t
    obtain ⟨c, hc⟩ := route t
    intro h
    have hh := congrArg (MvPolynomial.eval c) h
    have hm := G.outputMatrix_map (MvPolynomial.eval c) x (output t)
    have hx : (MvPolynomial.eval c) ∘ x = c := by ext v; simp [x]
    rw [hx] at hm
    change MvPolynomial.eval c ((G.outputMatrix x (output t)).det) = 0 at hh
    rw [RingHom.map_det] at hh
    change ((G.outputMatrix x (output t)).map (MvPolynomial.eval c)).det = 0 at hh
    rw [hm, hc, Matrix.det_one] at hh
    exact one_ne_zero hh
  obtain ⟨b, hb, c, hc⟩ := exists_binary_specialization p hp
  refine ⟨b, hb, c, fun t ↦ ?_⟩
  have hm := G.outputMatrix_map
    (MvPolynomial.eval₂Hom (algebraMap (ZMod 2) (GaloisField 2 b)) c) x (output t)
  have hx : (MvPolynomial.eval₂Hom (algebraMap (ZMod 2) (GaloisField 2 b)) c) ∘ x = c := by
    ext v
    simp [x]
  rw [hx] at hm
  have hh := hc t
  change (MvPolynomial.eval₂Hom (algebraMap (ZMod 2) (GaloisField 2 b)) c)
    ((G.outputMatrix x (output t)).det) ≠ 0 at hh
  rw [RingHom.map_det] at hh
  change ((G.outputMatrix x (output t)).map
    (MvPolynomial.eval₂Hom (algebraMap (ZMod 2) (GaloisField 2 b)) c)).det ≠ 0 at hh
  rwa [hm] at hh

end Circuit

end CapacityAtlas.LinearMulticast
