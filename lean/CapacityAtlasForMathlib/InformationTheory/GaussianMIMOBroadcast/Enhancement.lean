/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Gradient
import CapacityAtlasForMathlib.LinearAlgebra.NoiseEnhancement

open Matrix
open scoped BigOperators MatrixOrder

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {m tx : ℕ}

lemma cumulativeGradient_adjacent (A B : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (k : Fin m) :
    cumulativeGradient A B (Equiv.refl _) k.castSucc -
      cumulativeGradient A B (Equiv.refl _) k.succ = A k.castSucc - B k.succ := by
  have hf : Finset.univ.filter (fun j : Fin (m + 1) ↦ k.castSucc < j) =
      insert k.succ (Finset.univ.filter (fun j : Fin (m + 1) ↦ k.succ < j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hj : j = k.succ
      · exact Or.inl hj
      · have hjv : j.val ≠ k.val + 1 := fun he ↦ hj (Fin.ext he)
        exact Or.inr (by simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at h ⊢; omega)
    · rintro (rfl | h)
      · exact k.castSucc_lt_succ
      · exact lt_trans k.castSucc_lt_succ h
  have hn : k.succ ∉ Finset.univ.filter (fun j : Fin (m + 1) ↦ k.succ < j) := by simp
  simp only [cumulativeGradient, Equiv.refl_symm, Equiv.refl_apply, hf, Finset.sum_insert hn]
  abel

lemma cumulativeGradient_stationarity_adjacent
    (A B O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (L : Matrix (Fin tx) (Fin tx) ℝ)
    (hstat : ∀ k, cumulativeGradient A B (Equiv.refl _) k + O k = L) (k : Fin m) :
    A k.castSucc + O k.castSucc = B k.succ + O k.succ := by
  apply sub_eq_zero.mp
  calc
    _ = (cumulativeGradient A B (Equiv.refl _) k.castSucc + O k.castSucc) -
        (cumulativeGradient A B (Equiv.refl _) k.succ + O k.succ) := by
      simp only [add_sub_add_comm, cumulativeGradient_adjacent]
    _ = 0 := by rw [hstat, hstat, sub_self]

lemma receivedPrecision_one (N S : Matrix (Fin tx) (Fin tx) ℝ) :
    receivedPrecision 1 N S = (S + N)⁻¹ := by
  simp only [receivedPrecision, receivedCovariance, transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [add_comm]

lemma prefixCovariance_zero (Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin (m + 1))) : prefixCovariance Q π 0 = 0 := by
  simp [prefixCovariance]

lemma prefixCovariance_succ (Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin (m + 1))) (k : Fin m) :
    prefixCovariance Q π k.succ = prefixCovariance Q π k.castSucc + Q (π k.castSucc) := by
  have hf : Finset.univ.filter (fun j : Fin (m + 1) ↦ j < k.succ) =
      insert k.castSucc (Finset.univ.filter (fun j : Fin (m + 1) ↦ j < k.castSucc)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hj : j = k.castSucc
      · exact Or.inl hj
      · have hjv : j.val ≠ k.val := fun he ↦ hj (Fin.ext he)
        exact Or.inr (by simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at h ⊢; omega)
    · intro h
      rcases h with rfl | h
      · exact k.castSucc_lt_succ
      · exact lt_trans h k.castSucc_lt_succ
  have hn : k.castSucc ∉ Finset.univ.filter (fun j : Fin (m + 1) ↦ j < k.castSucc) := by simp
  simp only [prefixCovariance, hf, Finset.sum_insert hn, add_comm]

noncomputable def enhancedCovariance
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (k : Fin (m + 1)) : Matrix (Fin tx) (Fin tx) ℝ :=
  intermediateNoise (prefixCovariance Q (Equiv.refl _) k) (N k) ((γ k)⁻¹ • O k)

lemma prefix_add_enhancedCovariance
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (k : Fin (m + 1)) :
    prefixCovariance Q (Equiv.refl _) k + enhancedCovariance Q N O γ k =
      enhancedNoise (prefixCovariance Q (Equiv.refl _) k + N k) ((γ k)⁻¹ • O k) :=
  add_intermediateNoise _ _ _

theorem prefix_enhancedCovariance_precision
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (hQ : ∀ k, (Q k).PosSemidef) (hN : ∀ k, (N k).PosDef)
    (hO : ∀ k, (O k).PosSemidef) (hγ : ∀ k, 0 < γ k) (k : Fin (m + 1)) :
    γ k • (prefixCovariance Q (Equiv.refl _) k + enhancedCovariance Q N O γ k)⁻¹ =
      γ k • (prefixCovariance Q (Equiv.refl _) k + N k)⁻¹ + O k := by
  rw [enhancedCovariance, inv_add_intermediateNoise
    (prefixCovariance_posSemidef Q hQ (Equiv.refl _) k) (hN k)
    ((hO k).smul (inv_nonneg.mpr (hγ k).le))]
  simp only [smul_add, smul_smul, mul_inv_cancel₀ (hγ k).ne', one_smul]

lemma enhancedCovariance_initial
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (hN : ∀ k, (N k).PosDef) (hO : ∀ k, (O k).PosSemidef) (hγ : ∀ k, 0 < γ k) :
    (enhancedCovariance Q N O γ 0).PosDef ∧ enhancedCovariance Q N O γ 0 ≤ N 0 := by
  simp only [enhancedCovariance, intermediateNoise, prefixCovariance_zero, zero_add, sub_zero]
  exact ⟨enhancedNoise_posDef (hN 0) ((hO 0).smul (inv_nonneg.mpr (hγ 0).le)),
    enhancedNoise_le (hN 0) ((hO 0).smul (inv_nonneg.mpr (hγ 0).le))⟩

theorem enhancedCovariance_precision
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (hQ : ∀ k, (Q k).PosSemidef) (hN : ∀ k, (N k).PosDef)
    (hO : ∀ k, (O k).PosSemidef) (hγ : ∀ k, 0 < γ k)
    (hQO : ∀ k, Q k * O k = 0) (k : Fin (m + 1)) :
    γ k • (prefixCovariance Q (Equiv.refl _) k + Q k + enhancedCovariance Q N O γ k)⁻¹ =
      γ k • (prefixCovariance Q (Equiv.refl _) k + Q k + N k)⁻¹ + O k := by
  have hprefix := prefixCovariance_posSemidef Q hQ (Equiv.refl _) k
  have hn : (prefixCovariance Q (Equiv.refl _) k + N k).PosDef := by
    simpa only [add_comm] using (hN k).add_posSemidef hprefix
  have h := weighted_inv_add_enhancedNoise (hQ k) hn (hO k) (hQO k) (hγ k)
  rw [← prefix_add_enhancedCovariance Q N O γ k] at h
  convert h using 1 <;> congr 2 <;> abel

theorem enhancedCovariance_detRatio
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (hQ : ∀ k, (Q k).PosSemidef) (hN : ∀ k, (N k).PosDef)
    (hO : ∀ k, (O k).PosSemidef) (hγ : ∀ k, 0 < γ k)
    (hQO : ∀ k, Q k * O k = 0) (k : Fin (m + 1)) :
    (prefixCovariance Q (Equiv.refl _) k + Q k + enhancedCovariance Q N O γ k).det /
      (prefixCovariance Q (Equiv.refl _) k + enhancedCovariance Q N O γ k).det =
    (prefixCovariance Q (Equiv.refl _) k + Q k + N k).det /
      (prefixCovariance Q (Equiv.refl _) k + N k).det := by
  have h := detRatio_intermediateNoise
    (prefixCovariance_posSemidef Q hQ (Equiv.refl _) k) (hN k)
    ((hO k).smul (inv_nonneg.mpr (hγ k).le))
    (show Q k * ((γ k)⁻¹ • O k) = 0 by rw [Matrix.mul_smul, hQO, smul_zero])
  change _ = _ at h
  convert h using 1 <;> congr 2 <;> abel

theorem enhancedCovariance_step
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (hQ : ∀ k, (Q k).PosSemidef) (hN : ∀ k, (N k).PosDef)
    (hO : ∀ k, (O k).PosSemidef) (hγ : ∀ k, 0 < γ k)
    (hQO : ∀ k, Q k * O k = 0) (k : Fin m)
    (hmono : γ k.castSucc ≤ γ k.succ)
    (hprev : (enhancedCovariance Q N O γ k.castSucc).PosDef)
    (hadj : γ k.succ • (prefixCovariance Q (Equiv.refl _) k.succ + N k.succ)⁻¹ + O k.succ =
      γ k.castSucc • (prefixCovariance Q (Equiv.refl _) k.castSucc + Q k.castSucc + N k.castSucc)⁻¹ +
        O k.castSucc) :
    (enhancedCovariance Q N O γ k.succ).PosDef ∧
      enhancedCovariance Q N O γ k.castSucc ≤ enhancedCovariance Q N O γ k.succ ∧
      enhancedCovariance Q N O γ k.succ ≤ N k.succ := by
  rw [← enhancedCovariance_precision Q N O γ hQ hN hO hγ hQO k.castSucc] at hadj
  have hprop : (prefixCovariance Q (Equiv.refl _) k.succ + N k.succ)⁻¹ +
      (γ k.succ)⁻¹ • O k.succ = (γ k.castSucc / γ k.succ) •
        (prefixCovariance Q (Equiv.refl _) k.succ + enhancedCovariance Q N O γ k.castSucc)⁻¹ := by
    have h := congrArg (fun A ↦ (γ k.succ)⁻¹ • A) hadj
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ (hγ k.succ).ne', one_smul,
      div_eq_mul_inv, mul_comm, prefixCovariance_succ, Equiv.refl_apply] using h
  have hr : γ k.castSucc / γ k.succ ≤ 1 := (div_le_one (hγ k.succ)).mpr hmono
  have hp := prefixCovariance_posSemidef Q hQ (Equiv.refl _) k.succ
  have ho := (hO k.succ).smul (inv_nonneg.mpr (hγ k.succ).le)
  exact ⟨intermediateNoise_posDef hp hprev (hN k.succ) ho hr hprop,
    intermediateNoise_bounds hp hprev (hN k.succ) ho hr hprop⟩

/-- The explicit enhancement construction is positive definite, degraded, and below the noises. -/
theorem enhancedCovariance_chain
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (hQ : ∀ k, (Q k).PosSemidef) (hN : ∀ k, (N k).PosDef)
    (hO : ∀ k, (O k).PosSemidef) (hγ : ∀ k, 0 < γ k)
    (hQO : ∀ k, Q k * O k = 0) (hmono : Monotone γ)
    (hadj : ∀ k : Fin m,
      γ k.succ • (prefixCovariance Q (Equiv.refl _) k.succ + N k.succ)⁻¹ + O k.succ =
      γ k.castSucc • (prefixCovariance Q (Equiv.refl _) k.castSucc + Q k.castSucc + N k.castSucc)⁻¹ +
        O k.castSucc) :
    (∀ k, (enhancedCovariance Q N O γ k).PosDef) ∧
      (∀ k, enhancedCovariance Q N O γ k ≤ N k) ∧
      ∀ k : Fin m, enhancedCovariance Q N O γ k.castSucc ≤ enhancedCovariance Q N O γ k.succ := by
  have hgood (k : Fin (m + 1)) :
      (enhancedCovariance Q N O γ k).PosDef ∧ enhancedCovariance Q N O γ k ≤ N k := by
    induction k using Fin.induction with
    | zero => exact enhancedCovariance_initial Q N O γ hN hO hγ
    | succ k ih =>
      have h := enhancedCovariance_step Q N O γ hQ hN hO hγ hQO k
        (hmono k.castSucc_lt_succ.le) ih.1 (hadj k)
      exact ⟨h.1, h.2.2⟩
  exact ⟨fun k ↦ (hgood k).1, fun k ↦ (hgood k).2, fun k ↦
    (enhancedCovariance_step Q N O γ hQ hN hO hγ hQO k
      (hmono k.castSucc_lt_succ.le) (hgood k.castSucc).1 (hadj k)).2.1⟩

theorem enhancedCovariance_proportional
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (hQ : ∀ k, (Q k).PosSemidef) (hN : ∀ k, (N k).PosDef)
    (hO : ∀ k, (O k).PosSemidef) (hγ : ∀ k, 0 < γ k)
    (hQO : ∀ k, Q k * O k = 0) (k : Fin m)
    (hadj : γ k.succ • (prefixCovariance Q (Equiv.refl _) k.succ + N k.succ)⁻¹ + O k.succ =
      γ k.castSucc • (prefixCovariance Q (Equiv.refl _) k.castSucc + Q k.castSucc + N k.castSucc)⁻¹ +
        O k.castSucc) :
    γ k.succ • (prefixCovariance Q (Equiv.refl _) k.succ + enhancedCovariance Q N O γ k.succ)⁻¹ =
      γ k.castSucc • (prefixCovariance Q (Equiv.refl _) k.succ +
        enhancedCovariance Q N O γ k.castSucc)⁻¹ := by
  rw [prefix_enhancedCovariance_precision Q N O γ hQ hN hO hγ, hadj,
    ← enhancedCovariance_precision Q N O γ hQ hN hO hγ hQO, prefixCovariance_succ]
  rfl

theorem aligned_stationarity_adjacent
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (w : Fin (m + 1) → ℝ)
    (L : Matrix (Fin tx) (Fin tx) ℝ)
    (hstat : ∀ k, dpcGradient w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _) k + O k = L)
    (k : Fin m) :
    (w k.succ / (2 * Real.log 2)) •
      (prefixCovariance Q (Equiv.refl _) k.succ + N k.succ)⁻¹ + O k.succ =
    (w k.castSucc / (2 * Real.log 2)) •
      (prefixCovariance Q (Equiv.refl _) k.castSucc + Q k.castSucc + N k.castSucc)⁻¹ + O k.castSucc := by
  have h := cumulativeGradient_stationarity_adjacent
    (fun j ↦ (w j / (2 * Real.log 2)) •
      (prefixCovariance Q (Equiv.refl _) j + Q j + N j)⁻¹)
    (fun j ↦ (w j / (2 * Real.log 2)) • (prefixCovariance Q (Equiv.refl _) j + N j)⁻¹)
    O L (fun j ↦ by simpa only [dpcGradient, Equiv.refl_apply, receivedPrecision_one] using hstat j) k
  exact h.symm

theorem enhancedCovariance_dpcRate
    (Q N O : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (γ : Fin (m + 1) → ℝ)
    (hQ : ∀ k, (Q k).PosSemidef) (hN : ∀ k, (N k).PosDef)
    (hO : ∀ k, (O k).PosSemidef) (hγ : ∀ k, 0 < γ k)
    (hQO : ∀ k, Q k * O k = 0) (k : Fin (m + 1)) :
    dpcRate (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) (enhancedCovariance Q N O γ) Q (Equiv.refl _) k =
      dpcRate (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _) k := by
  have h := enhancedCovariance_detRatio Q N O γ hQ hN hO hγ hQO k
  simp only [dpcRate, receivedCovariance, Equiv.refl_apply, transpose_one,
    Matrix.one_mul, Matrix.mul_one]
  rw [add_comm (enhancedCovariance Q N O γ k), add_comm (enhancedCovariance Q N O γ k),
    add_comm (N k), add_comm (N k), h]

/-- An actual aligned DPC optimizer admits a degraded, rate-preserving enhanced channel. -/
theorem exists_aligned_max_enhancement
    (N : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (hN : ∀ k, (N k).PosDef)
    (w : Fin (m + 1) → ℝ) (hw : ∀ k, 0 < w k) (hmono : Monotone w)
    {P : ℝ} (hP : 0 < P) :
    ∃ Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ, AllocationAdmissible P Q ∧
      (∀ Q', AllocationAdmissible P Q' →
        weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q' (Equiv.refl _) ≤
          weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _)) ∧
      ∃ E : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ,
        (∀ k, (E k).PosDef) ∧ (∀ k, E k ≤ N k) ∧ Monotone E ∧
        ∀ k, dpcRate (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) E Q (Equiv.refl _) k =
          dpcRate (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _) k := by
  obtain ⟨Q, hQ, hmax, lam, hlam, O, hO, hstat, hOQ, _⟩ :=
    exists_weightedDpcRate_max_multipliers_for_order w
      (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N hN (Equiv.refl _) hP
  let γ := fun k ↦ w k / (2 * Real.log 2)
  have hc : 0 < 2 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hγ (k) : 0 < γ k := div_pos (hw k) hc
  have hm : Monotone γ := fun i j hij ↦ div_le_div_of_nonneg_right (hmono hij) hc.le
  have hQO (k) : Q k * O k = 0 := by
    have h := congrArg conjTranspose (hOQ k)
    simpa only [conjTranspose_mul, (hQ.1 k).isHermitian.eq, (hO k).isHermitian.eq,
      conjTranspose_zero] using h
  have hadj := aligned_stationarity_adjacent Q N O w (lam • 1) hstat
  obtain ⟨he, hle, hmon⟩ := enhancedCovariance_chain Q N O γ hQ.1 hN hO hγ hQO hm hadj
  exact ⟨Q, hQ, hmax, enhancedCovariance Q N O γ, he, hle,
    Fin.monotone_iff_le_succ.mpr hmon,
    enhancedCovariance_dpcRate Q N O γ hQ.1 hN hO hγ hQO⟩

end CapacityAtlas.Gaussian.MIMOBroadcast
