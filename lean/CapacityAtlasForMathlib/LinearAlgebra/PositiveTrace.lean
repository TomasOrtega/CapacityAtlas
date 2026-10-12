/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

open scoped MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_eq_trace_sqrt_gram {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (A * B) = trace ((CFC.sqrt A * CFC.sqrt B).conjTranspose *
      (CFC.sqrt A * CFC.sqrt B)) := by
  have hsa := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hsb := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian
  rw [conjTranspose_mul, hsa, hsb]
  calc
    _ = trace (A * (CFC.sqrt B * CFC.sqrt B)) := by
      rw [CFC.sqrt_mul_sqrt_self B hB.nonneg]
    _ = trace (CFC.sqrt B * A * CFC.sqrt B) := by
      rw [← Matrix.mul_assoc, trace_mul_cycle]
    _ = _ := by
      nth_rw 1 [← CFC.sqrt_mul_sqrt_self A hA.nonneg]
      simp only [Matrix.mul_assoc]

lemma PosSemidef.trace_mul_nonneg {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ trace (A * B) := by
  rw [trace_mul_eq_trace_sqrt_gram hA hB]
  exact (posSemidef_conjTranspose_mul_self _).trace_nonneg

lemma PosSemidef.trace_mul_eq_zero_iff {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : trace (A * B) = 0 ↔ A * B = 0 := by
  constructor
  · intro h
    rw [trace_mul_eq_trace_sqrt_gram hA hB, trace_conjTranspose_mul_self_eq_zero_iff] at h
    calc
      A * B = CFC.sqrt A * (CFC.sqrt A * CFC.sqrt B) * CFC.sqrt B := by
        nth_rw 1 [← CFC.sqrt_mul_sqrt_self A hA.nonneg]
        nth_rw 1 [← CFC.sqrt_mul_sqrt_self B hB.nonneg]
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, mul_zero, zero_mul]
  · intro h
    simp [h]

end Matrix
