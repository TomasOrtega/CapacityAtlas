/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Enhancement
import CapacityAtlasForMathlib.LinearAlgebra.LogDetConcavity

open Matrix
open scoped BigOperators MatrixOrder

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {m tx : ℕ}

noncomputable def alignedLogObjective (γ : Fin (m + 1) → ℝ)
    (N Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) : ℝ :=
  ∑ k, γ k * (Real.log (prefixCovariance Q (Equiv.refl _) k + Q k + N k).det -
    Real.log (prefixCovariance Q (Equiv.refl _) k + N k).det)

lemma prefixCovariance_last_add (Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) :
    prefixCovariance Q (Equiv.refl _) (Fin.last m) + Q (Fin.last m) = ∑ k, Q k := by
  have hf : Finset.univ.filter (fun j : Fin (m + 1) ↦ j < Fin.last m) =
      Finset.univ.erase (Fin.last m) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ⟨fun h he ↦ by simp only [he, lt_self_iff_false] at h,
      fun h ↦ lt_of_le_of_ne (Fin.le_last j) h⟩
  simp only [prefixCovariance, hf, Equiv.refl_apply]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ _)

theorem alignedLogObjective_telescope (γ : Fin (m + 1) → ℝ)
    (N Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) :
    alignedLogObjective γ N Q =
      γ (Fin.last m) * Real.log ((∑ k, Q k) + N (Fin.last m)).det - γ 0 * Real.log (N 0).det +
      ∑ k : Fin m, (γ k.castSucc *
        Real.log (prefixCovariance Q (Equiv.refl _) k.succ + N k.castSucc).det -
        γ k.succ * Real.log (prefixCovariance Q (Equiv.refl _) k.succ + N k.succ).det) := by
  unfold alignedLogObjective
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun k ↦ γ k *
    Real.log (prefixCovariance Q (Equiv.refl _) k + Q k + N k).det)]
  rw [Fin.sum_univ_succ (fun k ↦ γ k * Real.log
    (prefixCovariance Q (Equiv.refl _) k + N k).det)]
  simp only [prefixCovariance_zero, zero_add, prefixCovariance_last_add,
    prefixCovariance_succ, Equiv.refl_apply]
  ring

lemma prefix_add_noise_posDef
    (Q N : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ k, (Q k).PosSemidef) (hN : ∀ k, (N k).PosDef) (k j : Fin (m + 1)) :
    (prefixCovariance Q (Equiv.refl _) k + N j).PosDef :=
  PosDef.posSemidef_add (prefixCovariance_posSemidef Q hQ (Equiv.refl _) k) (hN j)

theorem adjacent_logObjective_le
    (γ : Fin (m + 1) → ℝ) (E Q Y : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (hγ : ∀ k, 0 < γ k) (hm : Monotone γ) (hE : ∀ k, (E k).PosDef)
    (hQ : ∀ k, (Q k).PosSemidef) (hY : ∀ k, (Y k).PosSemidef) (k : Fin m)
    (hprop : γ k.succ • (prefixCovariance Q (Equiv.refl _) k.succ + E k.succ)⁻¹ =
      γ k.castSucc • (prefixCovariance Q (Equiv.refl _) k.succ + E k.castSucc)⁻¹) :
    γ k.castSucc * Real.log (prefixCovariance Y (Equiv.refl _) k.succ + E k.castSucc).det -
      γ k.succ * Real.log (prefixCovariance Y (Equiv.refl _) k.succ + E k.succ).det ≤
    γ k.castSucc * Real.log (prefixCovariance Q (Equiv.refl _) k.succ + E k.castSucc).det -
      γ k.succ * Real.log (prefixCovariance Q (Equiv.refl _) k.succ + E k.succ).det := by
  have ha := prefix_add_noise_posDef Q E hQ hE k.succ k.castSucc
  have hb := prefix_add_noise_posDef Q E hQ hE k.succ k.succ
  have hp : (prefixCovariance Q (Equiv.refl _) k.succ + E k.succ)⁻¹ =
      (γ k.castSucc / γ k.succ) •
        (prefixCovariance Q (Equiv.refl _) k.succ + E k.castSucc)⁻¹ := by
    have h := congrArg (fun Z ↦ (γ k.succ)⁻¹ • Z) hprop
    simpa only [smul_smul, inv_mul_cancel₀ (hγ k.succ).ne', one_smul,
      div_eq_mul_inv, mul_comm] using h
  have h := proportional_log_det_difference_le ha hb
    (prefix_add_noise_posDef Y E hY hE k.succ k.castSucc)
    (prefix_add_noise_posDef Y E hY hE k.succ k.succ)
    (div_pos (hγ k.castSucc) (hγ k.succ))
    ((div_le_one (hγ k.succ)).mpr (hm k.castSucc_lt_succ.le))
    (inv_proportional_smul ha hb hp) (by abel)
  have hh := mul_le_mul_of_nonneg_left h (hγ k.succ).le
  have he : γ k.succ * (γ k.castSucc / γ k.succ) = γ k.castSucc :=
    mul_div_cancel₀ _ (hγ k.succ).ne'
  simpa only [mul_sub, ← mul_assoc, he] using hh

theorem last_logObjective_le
    (γ : Fin (m + 1) → ℝ) (E Q Y : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (hγ : ∀ k, 0 < γ k) (hE : ∀ k, (E k).PosDef) {P lam : ℝ} (hlam : 0 ≤ lam)
    (hQ : AllocationAdmissible P Q) (hY : AllocationAdmissible P Y)
    (hstat : γ (Fin.last m) • ((∑ k, Q k) + E (Fin.last m))⁻¹ = lam • 1)
    (hcomp : lam * (P - ∑ k, trace (Q k)) = 0) :
    γ (Fin.last m) * Real.log ((∑ k, Y k) + E (Fin.last m)).det ≤
      γ (Fin.last m) * Real.log ((∑ k, Q k) + E (Fin.last m)).det := by
  have hq : ((∑ k, Q k) + E (Fin.last m)).PosDef :=
    PosDef.posSemidef_add (posSemidef_sum _ (fun k _ ↦ hQ.1 k)) (hE _)
  have hy : ((∑ k, Y k) + E (Fin.last m)).PosDef :=
    PosDef.posSemidef_add (posSemidef_sum _ (fun k _ ↦ hY.1 k)) (hE _)
  have h := mul_le_mul_of_nonneg_left (hy.log_det_le_tangent hq) (hγ (Fin.last m)).le
  rw [add_sub_add_right_eq_sub] at h
  have ht := congrArg (fun Z ↦ trace (Z * ((∑ k, Y k) - ∑ k, Q k))) hstat
  simp only [Matrix.smul_mul, trace_smul, smul_eq_mul, Matrix.one_mul, trace_sub, trace_sum] at ht
  have hb : lam * ((∑ k, trace (Y k)) - ∑ k, trace (Q k)) ≤ 0 := by
    have hp := mul_nonneg hlam (sub_nonneg.mpr hY.2)
    nlinarith
  nlinarith

/-- Proportional enhancement and the trace multiplier preserve the weighted support value. -/
theorem alignedLogObjective_le_of_proportional
    (γ : Fin (m + 1) → ℝ) (E Q Y : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (hγ : ∀ k, 0 < γ k) (hm : Monotone γ) (hE : ∀ k, (E k).PosDef)
    {P lam : ℝ} (hlam : 0 ≤ lam) (hQ : AllocationAdmissible P Q) (hY : AllocationAdmissible P Y)
    (hprop : ∀ k : Fin m,
      γ k.succ • (prefixCovariance Q (Equiv.refl _) k.succ + E k.succ)⁻¹ =
      γ k.castSucc • (prefixCovariance Q (Equiv.refl _) k.succ + E k.castSucc)⁻¹)
    (hstat : γ (Fin.last m) • ((∑ k, Q k) + E (Fin.last m))⁻¹ = lam • 1)
    (hcomp : lam * (P - ∑ k, trace (Q k)) = 0) :
    alignedLogObjective γ E Y ≤ alignedLogObjective γ E Q := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦
    adjacent_logObjective_le γ E Q Y hγ hm hE hQ.1 hY.1 k (hprop k))
  have hl := last_logObjective_le γ E Q Y hγ hE hlam hQ hY hstat hcomp
  rw [alignedLogObjective_telescope, alignedLogObjective_telescope]
  linarith

theorem weightedDpcRate_eq_alignedLogObjective
    (w : Fin (m + 1) → ℝ) (N Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (hN : ∀ k, (N k).PosDef) (hQ : ∀ k, (Q k).PosSemidef) :
    weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _) =
      alignedLogObjective (fun k ↦ w k / (2 * Real.log 2)) N Q := by
  unfold weightedDpcRate alignedLogObjective
  apply Finset.sum_congr rfl
  intro k _
  have hn := dpcRate_numerator_pos (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q hN hQ
    (Equiv.refl _) k
  have hd := dpcRate_denominator_pos (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q hN hQ
    (Equiv.refl _) k
  rw [dpcRate, Real.logb, Real.log_div hn.ne' hd.ne']
  simp only [Equiv.refl_apply, receivedCovariance, transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [add_comm (N k), add_comm (N k)]
  ring

lemma aligned_dpcGradient_last
    (w : Fin (m + 1) → ℝ) (N Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) :
    dpcGradient w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _) (Fin.last m) =
      (w (Fin.last m) / (2 * Real.log 2)) • ((∑ k, Q k) + N (Fin.last m))⁻¹ := by
  have hf : Finset.univ.filter (fun j : Fin (m + 1) ↦ Fin.last m < j) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact not_lt_of_ge (Fin.le_last j)
  simp only [dpcGradient, cumulativeGradient, Equiv.refl_apply, Equiv.refl_symm,
    hf, Finset.sum_empty, add_zero, receivedPrecision_one, prefixCovariance_last_add]

/-- The enhanced Gaussian channel has the same supporting weighted value as the original. -/
theorem exists_aligned_support_enhancement
    (N : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (hN : ∀ k, (N k).PosDef)
    (w : Fin (m + 1) → ℝ) (hw : ∀ k, 0 < w k) (hm : Monotone w) {P : ℝ} (hP : 0 < P) :
    ∃ Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ, AllocationAdmissible P Q ∧
      ∃ E : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ,
        (∀ k, (E k).PosDef) ∧ (∀ k, E k ≤ N k) ∧ Monotone E ∧
        (∀ k, dpcRate (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) E Q (Equiv.refl _) k =
          dpcRate (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _) k) ∧
        ∀ Y, AllocationAdmissible P Y →
          weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) E Y (Equiv.refl _) ≤
            weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _) := by
  obtain ⟨Q, hQ, _, lam, hlam, O, hO, hstat, hOQ, hcomp⟩ :=
    exists_weightedDpcRate_max_multipliers_for_order w
      (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N hN (Equiv.refl _) hP
  let γ := fun k ↦ w k / (2 * Real.log 2)
  have hc : 0 < 2 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hγ (k) : 0 < γ k := div_pos (hw k) hc
  have hmγ : Monotone γ := fun i j hij ↦ div_le_div_of_nonneg_right (hm hij) hc.le
  have hQO (k) : Q k * O k = 0 := by
    have h := congrArg conjTranspose (hOQ k)
    simpa only [conjTranspose_mul, (hQ.1 k).isHermitian.eq, (hO k).isHermitian.eq,
      conjTranspose_zero] using h
  have hadj := aligned_stationarity_adjacent Q N O w (lam • 1) hstat
  obtain ⟨he, hle, hmon⟩ := enhancedCovariance_chain Q N O γ hQ.1 hN hO hγ hQO hmγ hadj
  let E := enhancedCovariance Q N O γ
  have hrates := enhancedCovariance_dpcRate Q N O γ hQ.1 hN hO hγ hQO
  refine ⟨Q, hQ, E, he, hle, Fin.monotone_iff_le_succ.mpr hmon, hrates, ?_⟩
  intro Y hY
  have hlast : γ (Fin.last m) • ((∑ k, Q k) + E (Fin.last m))⁻¹ = lam • 1 := by
    have h := enhancedCovariance_precision Q N O γ hQ.1 hN hO hγ hQO (Fin.last m)
    rw [prefixCovariance_last_add] at h
    rw [h]
    simpa only [aligned_dpcGradient_last] using hstat (Fin.last m)
  have hbound := alignedLogObjective_le_of_proportional γ E Q Y hγ hmγ he hlam hQ hY
    (fun k ↦ enhancedCovariance_proportional Q N O γ hQ.1 hN hO hγ hQO k (hadj k)) hlast hcomp
  rw [← weightedDpcRate_eq_alignedLogObjective w E Y he hY.1,
    ← weightedDpcRate_eq_alignedLogObjective w E Q he hQ.1] at hbound
  convert hbound using 1
  unfold weightedDpcRate
  exact Finset.sum_congr rfl (fun k _ ↦ congrArg (w k * ·) (hrates k).symm)

end CapacityAtlas.Gaussian.MIMOBroadcast
