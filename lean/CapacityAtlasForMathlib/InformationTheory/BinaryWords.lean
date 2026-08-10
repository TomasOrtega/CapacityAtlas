/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasUtil.Metadata
import Mathlib.Data.Fintype.BigOperators
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

open scoped BigOperators

namespace CapacityAtlas

/-- Binary words of blocklength `n`. -/
abbrev BinaryWord (n : ℕ) := Fin n → Bool

namespace BinaryWord

/-- Coordinatewise addition in the Boolean cube. -/
@[capacity_shared_api]
def xor {n : ℕ} (x y : BinaryWord n) : BinaryWord n :=
  fun i => Bool.xor (x i) (y i)

@[simp, capacity_shared_api]
theorem xor_apply {n : ℕ} (x y : BinaryWord n) (i : Fin n) :
    xor x y i = Bool.xor (x i) (y i) :=
  rfl

@[simp, capacity_shared_api]
theorem xor_self {n : ℕ} (x : BinaryWord n) : xor x x = fun _ => false := by
  funext i
  cases x i <;> simp [xor]

@[simp, capacity_shared_api]
theorem xor_false_right {n : ℕ} (x : BinaryWord n) :
    xor x (fun _ => false) = x := by
  funext i
  cases x i <;> simp [xor]

@[simp, capacity_shared_api]
theorem xor_false_left {n : ℕ} (x : BinaryWord n) :
    xor (fun _ => false) x = x := by
  funext i
  cases x i <;> simp [xor]

@[capacity_shared_api]
theorem xor_comm {n : ℕ} (x y : BinaryWord n) : xor x y = xor y x := by
  funext i
  cases x i <;> cases y i <;> simp [xor]

@[capacity_shared_api]
theorem xor_assoc {n : ℕ} (x y z : BinaryWord n) :
    xor (xor x y) z = xor x (xor y z) := by
  funext i
  cases x i <;> cases y i <;> cases z i <;> simp [xor]

/-- Translation by a word is an involutive permutation of the Boolean cube. -/
@[capacity_shared_api]
def xorEquiv {n : ℕ} (x : BinaryWord n) : BinaryWord n ≃ BinaryWord n where
  toFun := xor x
  invFun := xor x
  left_inv y := by
    funext i
    cases x i <;> cases y i <;> simp [xor]
  right_inv y := by
    funext i
    cases x i <;> cases y i <;> simp [xor]

/-- Number of one-bits in a binary word. -/
@[capacity_shared_api]
def weight {n : ℕ} (x : BinaryWord n) : ℕ :=
  (Finset.univ.filter fun i => x i = true).card

@[simp, capacity_shared_api]
theorem weight_false {n : ℕ} : weight (fun _ : Fin n => false) = 0 := by
  simp [weight]

@[capacity_shared_api]
theorem weight_le {n : ℕ} (x : BinaryWord n) : weight x ≤ n := by
  calc
    weight x ≤ Finset.univ.card := by exact Finset.card_filter_le _ _
    _ = n := Fintype.card_fin n

/-- The Boolean cube has `2^n` words. -/
@[capacity_shared_api]
theorem card (n : ℕ) : Fintype.card (BinaryWord n) = 2 ^ n := by
  simp [BinaryWord]

/-- Mass of one Bernoulli noise bit. -/
@[capacity_shared_api]
def bitMass (p : ℝ) (b : Bool) : ℝ :=
  if b then p else 1 - p

/-- Product Bernoulli mass of a binary noise word. -/
@[capacity_shared_api]
def noiseMass {n : ℕ} (p : ℝ) (z : BinaryWord n) : ℝ :=
  ∏ i, bitMass p (z i)

@[capacity_shared_api]
theorem bitMass_nonnegative {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitMass p b := by
  cases b <;> simp [bitMass] <;> linarith

@[capacity_shared_api]
theorem noiseMass_nonnegative {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (z : BinaryWord n) : 0 ≤ noiseMass p z := by
  exact Finset.prod_nonneg fun i _ => bitMass_nonnegative hp0 hp1 (z i)

/-- Product Bernoulli masses sum to one. -/
@[capacity_shared_api]
theorem sum_noiseMass {n : ℕ} (p : ℝ) :
    ∑ z : BinaryWord n, noiseMass p z = 1 := by
  unfold noiseMass
  rw [← Fintype.prod_sum]
  simp [bitMass]

end BinaryWord

end CapacityAtlas
