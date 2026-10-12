/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.LinearMulticast.Circuit

open scoped BigOperators Classical

namespace CapacityAtlas.LinearMulticast.Circuit

variable {I W : Type} [Fintype I] [Fintype W] (G : Circuit I W)

noncomputable def value {R : Type*} [CommSemiring R]
    (c : G.Variable → R) (e : W) (m : I → R) : R :=
  ∑ i, G.transfer c e i * m i

/-- The global encoding vectors satisfy the local network operations. -/
theorem value_eq {R : Type*} [CommSemiring R]
    (c : G.Variable → R) (e : W) (m : I → R) :
    G.value c e m = (∑ i, if G.input e i then c (e, Sum.inl i) * m i else 0) +
      ∑ p, if G.parent e p then c (e, Sum.inr p) * G.value c p m else 0 := by
  unfold value
  conv_lhs => arg 2; ext i; rw [transfer]
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : G.parent e p
    · simp only [hp, ↓reduceDIte, ↓reduceIte, Finset.mul_sum, mul_assoc]
    · simp [hp]

noncomputable def portValue {R : Type*} [CommSemiring R]
    (c : G.Variable → R) (m : I → R) (port : I ⊕ W) : R :=
  match port with
  | Sum.inl i => m i
  | Sum.inr e => G.value c e m

theorem observed_mul_message {R : Type*} [CommSemiring R]
    (c : G.Variable → R) (m : I → R) (port : I ⊕ W) :
    ∑ i, G.observed c port i * m i = G.portValue c m port := by
  cases port with
  | inl j => simp [observed, portValue]
  | inr e => rfl

theorem outputMatrix_mulVec {R : Type*} [CommSemiring R]
    (c : G.Variable → R) (m : I → R) (output : I → I ⊕ W) :
    (G.outputMatrix c output).mulVec m = fun i ↦ G.portValue c m (output i) := by
  funext i
  exact G.observed_mul_message c m (output i)

noncomputable def decode {K : Type*} [Field K]
    (c : G.Variable → K) (output : I → I ⊕ W) (observations : I → K) : I → K :=
  (G.outputMatrix c output)⁻¹.mulVec observations

theorem decode_eq {K : Type*} [Field K]
    (c : G.Variable → K) (output : I → I ⊕ W)
    (hd : (G.outputMatrix c output).det ≠ 0) (m : I → K) :
    G.decode c output (fun i ↦ G.portValue c m (output i)) = m := by
  rw [decode, ← G.outputMatrix_mulVec c m output, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), Matrix.one_mulVec]

end CapacityAtlas.LinearMulticast.Circuit
