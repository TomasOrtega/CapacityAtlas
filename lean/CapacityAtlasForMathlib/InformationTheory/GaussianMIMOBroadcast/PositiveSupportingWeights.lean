/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.SupportingWeights

open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

lemma weightedDpcRate_add_const (w : Fin K → ℝ) (δ : ℝ)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) :
    weightedDpcRate (fun i ↦ w i + δ) H N Q π = weightedDpcRate w H N Q π +
      δ * weightedDpcRate (fun _ ↦ 1) H N Q π := by
  simp only [weightedDpcRate, add_mul, one_mul, Finset.sum_add_distrib, Finset.mul_sum]

lemma weightedDpcRate_nonneg (w : Fin K → ℝ) (hw : ∀ i, 0 ≤ w i)
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) :
    0 ≤ weightedDpcRate w H N Q π :=
  Finset.sum_nonneg fun k _ ↦ mul_nonneg (hw (π k)) (dpcRate_nonneg H N Q hN hQ π k)

/-- Bounds for strictly positive weights also control receivers with zero weight. -/
theorem exists_weightedDpcRate_bound_of_positive
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) {R : Fin K → ℝ}
    (hR : ∀ i, 0 ≤ R i)
    (hpositive : ∀ v : Fin K → ℝ, (∀ i, 0 < v i) →
      ∃ Q, AllocationAdmissible P Q ∧ ∃ π,
        (∑ i, v i * R i) ≤ weightedDpcRate v H N Q π)
    (w : Fin K → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ Q, AllocationAdmissible P Q ∧ ∃ π,
      (∑ i, w i * R i) ≤ weightedDpcRate w H N Q π := by
  obtain ⟨Q, hQ, π, hmax⟩ := exists_weightedDpcRate_max w H N hN hP
  obtain ⟨Q₁, hQ₁, π₁, hmax₁⟩ := exists_weightedDpcRate_max (fun _ ↦ 1) H N hN hP
  let B := weightedDpcRate (fun _ ↦ 1) H N Q₁ π₁
  have hB : 0 ≤ B := weightedDpcRate_nonneg (fun _ ↦ 1) (fun _ ↦ zero_le_one)
    H N hN Q₁ hQ₁.1 π₁
  refine ⟨Q, hQ, π, le_of_forall_pos_le_add fun ε hε ↦ ?_⟩
  let δ := ε / (B + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδB : δ * B ≤ ε := by
    have hδeq : δ * (B + 1) = ε := div_mul_cancel₀ ε (by linarith : B + 1 ≠ 0)
    nlinarith
  obtain ⟨Q', hQ', π', hbound⟩ := hpositive (fun i ↦ w i + δ)
    (fun i ↦ add_pos_of_nonneg_of_pos (hw i) hδ)
  calc
    (∑ i, w i * R i) ≤ ∑ i, (w i + δ) * R i :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hδ.le) (hR i)
    _ ≤ weightedDpcRate (fun i ↦ w i + δ) H N Q' π' := hbound
    _ = weightedDpcRate w H N Q' π' + δ * weightedDpcRate (fun _ ↦ 1) H N Q' π' :=
      weightedDpcRate_add_const w δ H N Q' π'
    _ ≤ weightedDpcRate w H N Q π + δ * B :=
      add_le_add (hmax Q' hQ' π') (mul_le_mul_of_nonneg_left (hmax₁ Q' hQ' π') hδ.le)
    _ ≤ weightedDpcRate w H N Q π + ε := add_le_add le_rfl hδB

theorem mem_region_iff_positive_weighted_bounds
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 ≤ P) {R : Fin K → ℝ} :
    R ∈ region H N P ↔ (∀ i, 0 ≤ R i) ∧ ∀ w : Fin K → ℝ, (∀ i, 0 < w i) →
      ∃ Q, AllocationAdmissible P Q ∧ ∃ π,
        (∑ i, w i * R i) ≤ weightedDpcRate w H N Q π := by
  rw [mem_region_iff_weighted_bounds H N hN hP]
  constructor
  · rintro ⟨hR, hbound⟩
    exact ⟨hR, fun w hw ↦ hbound w (fun i ↦ (hw i).le)⟩
  · rintro ⟨hR, hbound⟩
    exact ⟨hR, exists_weightedDpcRate_bound_of_positive H N hN hP hR hbound⟩

end CapacityAtlas.Gaussian.MIMOBroadcast
