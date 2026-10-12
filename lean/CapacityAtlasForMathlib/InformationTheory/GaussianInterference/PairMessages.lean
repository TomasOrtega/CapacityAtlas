/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.CodeLaws
import CapacityAtlasForMathlib.MeasureTheory.PiResampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian.Interference

variable {K n : ℕ}

def pairMessage (c : Code K n) (m : c.Message) (i j : Fin K)
    (a : Fin (c.messages i)) (b : Fin (c.messages j)) : c.Message :=
  Function.update (Function.update m i a) j b

@[simp] theorem pairMessage_left (c : Code K n) (m : c.Message) (i j : Fin K)
    (hij : i ≠ j) (a : Fin (c.messages i)) (b : Fin (c.messages j)) :
    pairMessage c m i j a b i = a := by simp [pairMessage, hij]

@[simp] theorem pairMessage_right (c : Code K n) (m : c.Message) (i j : Fin K)
    (a : Fin (c.messages i)) (b : Fin (c.messages j)) :
    pairMessage c m i j a b j = b := by simp [pairMessage]

theorem integral_pairMessage (c : Code K n) (i j : Fin K) (f : c.Message → ℝ) :
    (∫ m, ∫ a, ∫ b, f (pairMessage c m i j a b)
      ∂uniformFinLaw (c.messages j) (c.messages_pos j)
      ∂uniformFinLaw (c.messages i) (c.messages_pos i) ∂messageLaw c) =
      ∫ m, f m ∂messageLaw c := by
  unfold pairMessage messageLaw
  rw [integral_integral_swap Integrable.of_finite]
  have hi := integral_updateProduct
    (fun k ↦ uniformFinLaw (c.messages k) (c.messages_pos k)) i
    (fun m ↦ ∫ b, f (Function.update m j b)
      ∂uniformFinLaw (c.messages j) (c.messages_pos j))
  rw [hi, integral_integral_swap Integrable.of_finite]
  exact integral_updateProduct
    (fun k ↦ uniformFinLaw (c.messages k) (c.messages_pos k)) j f

noncomputable def userSignal (c : Code K n) (H : StateBlock K n) (r i : Fin K)
    (a : Fin (c.messages i)) : EuclideanSpace ℝ (Fin 2 × Fin n) :=
  realBlock fun t ↦ H t r i * c.encode i a H t

noncomputable def pairBackground (c : Code K n) (m : c.Message) (H : StateBlock K n)
    (r i j : Fin K) : EuclideanSpace ℝ (Fin 2 × Fin n) :=
  realBlock fun t ↦ ∑ k, if k = i ∨ k = j then 0 else H t r k * c.encode k (m k) H t

theorem receiverMean_pairMessage (c : Code K n) (m : c.Message) (H : StateBlock K n)
    (r i j : Fin K) (hij : i ≠ j) (a : Fin (c.messages i)) (b : Fin (c.messages j)) :
    receiverMean c (pairMessage c m i j a b) H r =
      userSignal c H r i a + userSignal c H r j b + pairBackground c m H r i j := by
  unfold receiverMean userSignal pairBackground
  rw [← realBlock_add, ← realBlock_add]
  congr 1
  ext t
  have hs : (∑ k, H t r k * c.encode k (pairMessage c m i j a b k) H t) =
      ∑ k, ((if k = i then H t r i * c.encode i a H t else 0) +
        (if k = j then H t r j * c.encode j b H t else 0) +
        (if k = i ∨ k = j then 0 else H t r k * c.encode k (m k) H t)) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hij.symm]
      · simp [pairMessage, hki, hkj]
  rw [hs]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Pi.add_apply]

theorem userSignal_transfer (c : Code K n) (H : StateBlock K n) (r s i : Fin K)
    (hH : ∀ t, H t r i ≠ 0) (a : Fin (c.messages i)) :
    (complexBlockMatrix (fun t ↦ H t s i / H t r i)).toEuclideanLin (userSignal c H r i a) =
      userSignal c H s i a := by
  unfold userSignal
  rw [complexBlockMatrix_apply]
  congr 1
  ext t
  field_simp [hH t]

end CapacityAtlas.Gaussian.Interference
