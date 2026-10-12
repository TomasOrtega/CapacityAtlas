/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.BlockEntropy
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.EnhancedSupport
import CapacityAtlasForMathlib.InformationTheory.GaussianProportionalMixtureEntropy

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n : ℕ} {rx : Fin K → ℕ}

theorem codePrefixEntropy_difference_le (c : Code K tx rx n) (htx : 0 < tx) (hn : 0 < n)
    (E F S : Matrix (Fin tx) (Fin tx) ℝ) (hE : E.PosDef) (hF : F.PosDef) (hS : S.PosSemidef)
    {f g : ℝ} (hf : 0 < f) (hg : 0 < g) (hfg : f ≤ g)
    (hprop : g • (S + F)⁻¹ = f • (S + E)⁻¹) (k : ℕ) :
    f * codePrefixEntropy c E k - g * codePrefixEntropy c F k ≤
      n * (f * MeasureInformation.entropyWith (multivariateGaussian 0 (S + E)) volume -
        g * MeasureInformation.entropyWith (multivariateGaussian 0 (S + F)) volume) := by
  letI : Nonempty (Fin tx) := ⟨⟨0, htx⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hSE := PosDef.posSemidef_add hS hE
  have hSF := PosDef.posSemidef_add hS hF
  have hp : g • (blockDiagonal (fun _ : Fin n ↦ S) + blockDiagonal (fun _ : Fin n ↦ F))⁻¹ =
      f • (blockDiagonal (fun _ : Fin n ↦ S) + blockDiagonal (fun _ : Fin n ↦ E))⁻¹ := by
    simp only [← blockDiagonal_add, Pi.add_def]
    rw [
      inv_blockDiagonal_posDef _ (fun _ ↦ hSF), inv_blockDiagonal_posDef _ (fun _ ↦ hSE)]
    rw [← blockDiagonal_smul, ← blockDiagonal_smul]
    apply congrArg blockDiagonal
    funext s
    exact hprop
  have hb (u : MessageTuple c) :=
    MeasureInformation.entropyWith_gaussianCodebook_weighted_difference_le_of_precision
      (messageLaw c) (fun x ↦ flattenGaussianBlock (c.encode (MeasureInformation.prefixMessage k u x)))
      (blockDiagonal (fun _ : Fin n ↦ E)) (blockDiagonal (fun _ : Fin n ↦ F))
      (blockDiagonal (fun _ : Fin n ↦ S))
      (posDef_blockDiagonal _ (fun _ ↦ hE)) (posDef_blockDiagonal _ (fun _ ↦ hF))
      (posSemidef_blockDiagonal _ (fun _ ↦ hS)) hf hg hfg hp
  have h := integral_mono (μ := messageLaw c) Integrable.of_finite (integrable_const _) hb
  simp only [integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
    integral_const, probReal_univ, one_smul, ← blockDiagonal_add, Pi.add_def,
    entropyWith_gaussianBlock _ hSE, entropyWith_gaussianBlock _ hSF] at h
  change f * codePrefixEntropy c E k - g * codePrefixEntropy c F k ≤ _ at h
  nlinarith

variable {m : ℕ} {rx : Fin (m + 1) → ℕ}

theorem codePrefixEntropy_telescope (c : Code (m + 1) tx rx n)
    (w : Fin (m + 1) → ℝ) (E : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) :
    (∑ k, w k * (codePrefixEntropy c (E k) (k.val + 1) - codePrefixEntropy c (E k) k.val)) =
      w (Fin.last m) * codePrefixEntropy c (E (Fin.last m)) (m + 1) -
        w 0 * codePrefixEntropy c (E 0) 0 +
      ∑ k : Fin m, (w k.castSucc * codePrefixEntropy c (E k.castSucc) (k.val + 1) -
        w k.succ * codePrefixEntropy c (E k.succ) (k.val + 1)) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun k ↦ w k * codePrefixEntropy c (E k) (k.val + 1)),
    Fin.sum_univ_succ (fun k ↦ w k * codePrefixEntropy c (E k) k.val)]
  simp only [Fin.val_last, Fin.val_zero, Fin.val_castSucc, Fin.val_succ]
  ring

theorem gaussianEntropyObjective_eq (w : Fin (m + 1) → ℝ)
    (E Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (hE : ∀ k, (E k).PosDef) (hQ : ∀ k, (Q k).PosSemidef) :
    (∑ k, w k * (MeasureInformation.entropyWith
      (multivariateGaussian 0 (prefixCovariance Q (Equiv.refl _) k + Q k + E k)) volume -
        MeasureInformation.entropyWith
      (multivariateGaussian 0 (prefixCovariance Q (Equiv.refl _) k + E k)) volume)) =
      alignedLogObjective w E Q / 2 := by
  unfold alignedLogObjective
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [MeasureInformation.entropyWith_multivariateGaussian _ _
    (PosDef.posSemidef_add ((prefixCovariance_posSemidef Q hQ (Equiv.refl _) k).add (hQ k)) (hE k)),
    MeasureInformation.entropyWith_multivariateGaussian _ _ (prefix_add_noise_posDef Q E hQ hE k k)]
  ring

theorem gaussianEntropyObjective_telescope (w : Fin (m + 1) → ℝ)
    (E Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ) :
    (∑ k, w k * (MeasureInformation.entropyWith
      (multivariateGaussian 0 (prefixCovariance Q (Equiv.refl _) k + Q k + E k)) volume -
        MeasureInformation.entropyWith
      (multivariateGaussian 0 (prefixCovariance Q (Equiv.refl _) k + E k)) volume)) =
      w (Fin.last m) * MeasureInformation.entropyWith
        (multivariateGaussian 0 ((∑ k, Q k) + E (Fin.last m))) volume -
      w 0 * MeasureInformation.entropyWith (multivariateGaussian 0 (E 0)) volume +
      ∑ k : Fin m, (w k.castSucc * MeasureInformation.entropyWith
        (multivariateGaussian 0 (prefixCovariance Q (Equiv.refl _) k.succ + E k.castSucc)) volume -
        w k.succ * MeasureInformation.entropyWith
        (multivariateGaussian 0 (prefixCovariance Q (Equiv.refl _) k.succ + E k.succ)) volume) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun k ↦ w k * MeasureInformation.entropyWith
    (multivariateGaussian 0 (prefixCovariance Q (Equiv.refl _) k + Q k + E k)) volume),
    Fin.sum_univ_succ (fun k ↦ w k * MeasureInformation.entropyWith
    (multivariateGaussian 0 (prefixCovariance Q (Equiv.refl _) k + E k)) volume)]
  simp only [prefixCovariance_zero, zero_add, prefixCovariance_last_add,
    prefixCovariance_succ, Equiv.refl_apply]
  ring

theorem weighted_codePrefixEntropy_le (c : Code (m + 1) tx rx n) (htx : 0 < tx) (hn : 0 < n)
    (w : Fin (m + 1) → ℝ) (E Q : Fin (m + 1) → Matrix (Fin tx) (Fin tx) ℝ)
    (hw : ∀ k, 0 < w k) (hm : Monotone w) (hE : ∀ k, (E k).PosDef)
    {P lam : ℝ} (hc : PowerAdmissible P c) (hlam : 0 ≤ lam) (hQ : AllocationAdmissible P Q)
    (hprop : ∀ k : Fin m,
      w k.succ • (prefixCovariance Q (Equiv.refl _) k.succ + E k.succ)⁻¹ =
        w k.castSucc • (prefixCovariance Q (Equiv.refl _) k.succ + E k.castSucc)⁻¹)
    (hstat : w (Fin.last m) • ((∑ k, Q k) + E (Fin.last m))⁻¹ = lam • 1)
    (hcomp : lam * (P - ∑ k, trace (Q k)) = 0) :
    (∑ k, w k * (codePrefixEntropy c (E k) (k.val + 1) - codePrefixEntropy c (E k) k.val)) ≤
      n * (alignedLogObjective w E Q / 2) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (k : Fin m) _ ↦
    codePrefixEntropy_difference_le c htx hn (E k.castSucc) (E k.succ)
      (prefixCovariance Q (Equiv.refl _) k.succ) (hE _) (hE _)
      (prefixCovariance_posSemidef Q hQ.1 (Equiv.refl _) k.succ)
      (hw _) (hw _) (hm k.castSucc_lt_succ.le) (hprop k) (k.val + 1))
  have ht := codePrefixEntropy_last_le c (E (Fin.last m)) (∑ k, Q k) (hE _)
    (posSemidef_sum _ (fun k _ ↦ hQ.1 k)) hc (hw _).le hlam hstat
    (by simpa only [trace_sum] using hcomp)
  rw [codePrefixEntropy_telescope, codePrefixEntropy_zero c (E 0) (hE 0),
    ← gaussianEntropyObjective_eq w E Q hE hQ.1, gaussianEntropyObjective_telescope]
  rw [← Finset.mul_sum] at hs
  nlinarith

end CapacityAtlas.Gaussian.MIMOBroadcast
