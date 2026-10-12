/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredBounds
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Asymptotic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

theorem exists_layered_thresholds
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (hN : ∀ i, (N i).PosDef) (π : Equiv.Perm (Fin K))
    (R : Fin K → ℝ)
    (hstrict : ∀ k, R (π k) = 0 ∨ R (π k) < dpcRate H N Q π k) :
    ∃ a b d : Fin K → ℝ,
      (∀ k, (∫ p, layerStateStatistic (H (π k)) (N (π k)) Q π k p
        ∂layerSourceLaw Q π (N (π k))) < a k) ∧
      (∀ k, a k < b k) ∧ (∀ k, 0 ≤ b k) ∧
      (∀ k, 0 < R (π k) → R (π k) * Real.log 2 + b k < d k ∧
        d k < ∫ p, layerObservationStatistic (H (π k)) (N (π k)) Q π k p
          ∂layerSourceLaw Q π (N (π k))) := by
  let s := fun k ↦ ∫ p, layerStateStatistic (H (π k)) (N (π k)) Q π k p
    ∂layerSourceLaw Q π (N (π k))
  let y := fun k ↦ ∫ p, layerObservationStatistic (H (π k)) (N (π k)) Q π k p
    ∂layerSourceLaw Q π (N (π k))
  have hs (k) : 0 ≤ s k := by
    dsimp only [s]
    rw [integral_layerStateStatistic _ _ Q (fun i ↦ (hQ i).posSemidef)
      (hN (π k)).posSemidef π k (hQ (π k))]
    exact ENNReal.toReal_nonneg
  have hex (k : Fin K) : ∃ a b d : ℝ, s k < a ∧ a < b ∧ 0 ≤ b ∧
      (0 < R (π k) → R (π k) * Real.log 2 + b < d ∧ d < y k) := by
    by_cases hz : R (π k) = 0
    · refine ⟨s k + 1, s k + 2, 0, by linarith, by linarith, by linarith [hs k], ?_⟩
      simp only [hz, lt_self_iff_false, false_implies]
    · have hlt : R (π k) < dpcRate H N Q π k := (hstrict k).resolve_left hz
      have hdiff : y k - s k = dpcRate H N Q π k * Real.log 2 :=
        layerInformationDifference_eq_dpcRate H N Q (fun i ↦ (hQ i).posSemidef) hN π k (hQ (π k))
      have hgap : 0 < y k - s k - R (π k) * Real.log 2 := by
        have hh := mul_lt_mul_of_pos_right hlt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
        linarith
      let gap := y k - s k - R (π k) * Real.log 2
      refine ⟨s k + gap / 4, s k + gap / 2, y k - gap / 4, ?_, ?_, ?_, ?_⟩
      · dsimp only [gap]; linarith
      · dsimp only [gap]; linarith
      · dsimp only [gap]; linarith [hs k]
      · intro _
        dsimp only [gap]
        constructor <;> linarith
  choose a b d h using hex
  exact ⟨a, b, d, fun k ↦ (h k).1, fun k ↦ (h k).2.1,
    fun k ↦ (h k).2.2.1, fun k ↦ (h k).2.2.2⟩

theorem messageCountAtRate_zero (n : ℕ) : FiniteChannel.messageCountAtRate 0 n = 1 := by
  simp [FiniteChannel.messageCountAtRate]

noncomputable def layeredActiveStages (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K)
    (R : Fin K → ℝ) : Finset (Fin K) :=
  Finset.univ.filter (fun i ↦ 0 < R (π (order i.val)))

@[simp] theorem mem_layeredActiveStages (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K)
    (R : Fin K → ℝ) (i : Fin K) :
    i ∈ layeredActiveStages π order R ↔ 0 < R (π (order i.val)) := by
  classical
  simp [layeredActiveStages]

theorem messageCountAtRate_inactive (π : Equiv.Perm (Fin K)) (order : ℕ → Fin K)
    (R : Fin K → ℝ) (hR : ∀ i, 0 ≤ R i) (n : ℕ) (i : Fin K)
    (hi : i ∉ layeredActiveStages π order R) :
    FiniteChannel.messageCountAtRate (R (π (order i.val))) n = 1 := by
  have hz : R (π (order i.val)) = 0 := le_antisymm (not_lt.mp (by simpa using hi)) (hR _)
  rw [hz, messageCountAtRate_zero]

end CapacityAtlas.Gaussian.MIMOBroadcast
