/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.EnhancedSupport

open Matrix
open scoped BigOperators MatrixOrder

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {m tx : ℕ}

/-- Enhancement exposes the precision and power identities used by the operational converse. -/
theorem exists_aligned_operational_enhancement
    (N : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) (hN : ∀ k, (N k).PosDef)
    (w : Fin (m + 1) → ℝ) (hw : ∀ k, 0 < w k) (hm : Monotone w) {P : ℝ} (hP : 0 < P) :
    ∃ Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ, AllocationAdmissible P Q ∧
      ∃ E : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ,
        (∀ k, (E k).PosDef) ∧ (∀ k, E k ≤ N k) ∧ Monotone E ∧
        (∀ k, dpcRate (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) E Q (Equiv.refl _) k =
          dpcRate (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _) k) ∧
        (∀ k : Fin m,
          w k.succ • (prefixCovariance Q (Equiv.refl _) k.succ + E k.succ)⁻¹ =
            w k.castSucc • (prefixCovariance Q (Equiv.refl _) k.succ + E k.castSucc)⁻¹) ∧
        ∃ lam : ℝ, 0 ≤ lam ∧
          w (Fin.last m) • ((∑ k, Q k) + E (Fin.last m))⁻¹ = lam • 1 ∧
          lam * (P - ∑ k, trace (Q k)) = 0 ∧
          ∀ Y, AllocationAdmissible P Y →
            weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) E Y (Equiv.refl _) ≤
              weightedDpcRate w (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N Q (Equiv.refl _) := by
  obtain ⟨Q, hQ, _, lam, hlam, O, hO, hstat, hOQ, hcomp⟩ :=
    exists_weightedDpcRate_max_multipliers_for_order w
      (fun _ ↦ (1 : Matrix (Fin tx) (Fin tx) ℝ)) N hN (Equiv.refl _) hP
  let c := 2 * Real.log 2
  let γ := fun k ↦ w k / c
  have hc : 0 < c := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hγ (k) : 0 < γ k := div_pos (hw k) hc
  have hmγ : Monotone γ := fun i j hij ↦ div_le_div_of_nonneg_right (hm hij) hc.le
  have hcγ (k) : c * γ k = w k := mul_div_cancel₀ _ hc.ne'
  have hQO (k) : Q k * O k = 0 := by
    have h := congrArg conjTranspose (hOQ k)
    simpa only [conjTranspose_mul, (hQ.1 k).isHermitian.eq, (hO k).isHermitian.eq,
      conjTranspose_zero] using h
  have hadj := aligned_stationarity_adjacent Q N O w (lam • 1) hstat
  obtain ⟨he, hle, hmon⟩ := enhancedCovariance_chain Q N O γ hQ.1 hN hO hγ hQO hmγ hadj
  let E := enhancedCovariance Q N O γ
  have hrates := enhancedCovariance_dpcRate Q N O γ hQ.1 hN hO hγ hQO
  have hprop (k : Fin m) :
      γ k.succ • (prefixCovariance Q (Equiv.refl _) k.succ + E k.succ)⁻¹ =
        γ k.castSucc • (prefixCovariance Q (Equiv.refl _) k.succ + E k.castSucc)⁻¹ :=
    enhancedCovariance_proportional Q N O γ hQ.1 hN hO hγ hQO k (hadj k)
  have hlast : γ (Fin.last m) • ((∑ k, Q k) + E (Fin.last m))⁻¹ = lam • 1 := by
    have h := enhancedCovariance_precision Q N O γ hQ.1 hN hO hγ hQO (Fin.last m)
    rw [prefixCovariance_last_add] at h
    rw [h]
    simpa only [aligned_dpcGradient_last] using hstat (Fin.last m)
  refine ⟨Q, hQ, E, he, hle, Fin.monotone_iff_le_succ.mpr hmon, hrates, ?_,
    c * lam, mul_nonneg hc.le hlam, ?_, ?_, ?_⟩
  · intro k
    simpa only [smul_smul, hcγ] using congrArg (fun Z ↦ c • Z) (hprop k)
  · simpa only [smul_smul, hcγ] using congrArg (fun Z ↦ c • Z) hlast
  · rw [mul_assoc, hcomp, mul_zero]
  · intro Y hY
    have hbound := alignedLogObjective_le_of_proportional γ E Q Y hγ hmγ he hlam hQ hY
      hprop hlast hcomp
    rw [← weightedDpcRate_eq_alignedLogObjective w E Y he hY.1,
      ← weightedDpcRate_eq_alignedLogObjective w E Q he hQ.1] at hbound
    convert hbound using 1
    unfold weightedDpcRate
    exact Finset.sum_congr rfl (fun k _ ↦ congrArg (w k * ·) (hrates k).symm)

end CapacityAtlas.Gaussian.MIMOBroadcast
