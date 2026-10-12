/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Optimization
import Mathlib.Analysis.SpecificLimits.Basic

open Matrix Filter
open scoped BigOperators Topology

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

def InteriorAllocationAdmissible (P : ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) : Prop :=
  (∀ i, (Q i).PosDef) ∧ (∑ i, (Q i).trace) < P

theorem InteriorAllocationAdmissible.admissible {P : ℝ}
    {Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ} (hQ : InteriorAllocationAdmissible P Q) :
    AllocationAdmissible P Q := ⟨fun i ↦ (hQ.1 i).posSemidef, hQ.2.le⟩

noncomputable def regularizationScale (K tx : ℕ) (P : ℝ) : ℝ := P / (2 * ((K : ℝ) * tx + 1))

noncomputable def isotropicAllocation (K tx : ℕ) (P : ℝ) :
    Fin K → Matrix (Fin tx) (Fin tx) ℝ := fun _ ↦ regularizationScale K tx P • 1

theorem regularizationScale_pos {P : ℝ} (hP : 0 < P) : 0 < regularizationScale K tx P := by
  unfold regularizationScale
  positivity

theorem trace_isotropicAllocation (P : ℝ) :
    (∑ i, (isotropicAllocation K tx P i).trace) = regularizationScale K tx P * ((K : ℝ) * tx) := by
  simp only [isotropicAllocation, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem isotropicAllocation_interior {P : ℝ} (hP : 0 < P) :
    InteriorAllocationAdmissible P (isotropicAllocation K tx P) := by
  refine ⟨fun _ ↦ PosDef.one.smul (regularizationScale_pos hP), ?_⟩
  rw [trace_isotropicAllocation]
  unfold regularizationScale
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * ((K : ℝ) * tx + 1))]
  have hd : 0 ≤ (K : ℝ) * tx := by positivity
  nlinarith

noncomputable def allocationBlend
    (Q A : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (t : ℝ) :
    Fin K → Matrix (Fin tx) (Fin tx) ℝ := fun i ↦ (1 - t) • Q i + t • A i

theorem trace_allocationBlend (Q A : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (t : ℝ) :
    (∑ i, (allocationBlend Q A t i).trace) =
      (1 - t) * (∑ i, (Q i).trace) + t * (∑ i, (A i).trace) := by
  simp only [allocationBlend, trace_add, trace_smul, smul_eq_mul, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem allocationBlend_interior {P : ℝ}
    {Q A : Fin K → Matrix (Fin tx) (Fin tx) ℝ} (hQ : AllocationAdmissible P Q)
    (hA : InteriorAllocationAdmissible P A) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    InteriorAllocationAdmissible P (allocationBlend Q A t) := by
  refine ⟨fun i ↦ PosDef.posSemidef_add ((hQ.1 i).smul (sub_nonneg.mpr ht1))
    ((hA.1 i).smul ht0), ?_⟩
  rw [trace_allocationBlend]
  have hleft := mul_le_mul_of_nonneg_left hQ.2 (sub_nonneg.mpr ht1)
  have hright := mul_lt_mul_of_pos_left hA.2 ht0
  nlinarith

@[fun_prop]
theorem continuous_allocationBlend (Q A : Fin K → Matrix (Fin tx) (Fin tx) ℝ) :
    Continuous (allocationBlend Q A) := by unfold allocationBlend; fun_prop

@[simp]
theorem allocationBlend_zero (Q A : Fin K → Matrix (Fin tx) (Fin tx) ℝ) :
    allocationBlend Q A 0 = Q := by ext i j k; simp [allocationBlend]

noncomputable def approximationWeight (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) / 2

theorem approximationWeight_pos (n : ℕ) : 0 < approximationWeight n := by
  unfold approximationWeight
  positivity

theorem approximationWeight_lt_one (n : ℕ) : approximationWeight n < 1 := by
  unfold approximationWeight
  have h : 1 / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  linarith

theorem approximationWeight_tendsto_zero : Tendsto approximationWeight atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) / 2) atTop (𝓝 0)
  simpa only [zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2

theorem allocationBlend_tendsto (Q A : Fin K → Matrix (Fin tx) (Fin tx) ℝ) :
    Tendsto (fun n ↦ allocationBlend Q A (approximationWeight n)) atTop (𝓝 Q) := by
  simpa only [allocationBlend_zero, Function.comp_def] using
    (continuous_allocationBlend Q A).continuousAt.tendsto.comp approximationWeight_tendsto_zero

theorem dpcRate_allocationBlend_tendsto
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ}
    {Q A : Fin K → Matrix (Fin tx) (Fin tx) ℝ} (hQ : AllocationAdmissible P Q)
    (hA : InteriorAllocationAdmissible P A) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    Tendsto (fun n ↦ dpcRate H N (allocationBlend Q A (approximationWeight n)) π k)
      atTop (𝓝 (dpcRate H N Q π k)) := by
  apply ((continuousOn_dpcRate H N hN π k) Q hQ.1).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨allocationBlend_tendsto Q A, Eventually.of_forall
    (fun n ↦ (allocationBlend_interior hQ hA (approximationWeight_pos n)
      (approximationWeight_lt_one n).le).admissible.1)⟩

def interiorRawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) : Set (Fin K → ℝ) :=
  {R | (∀ i, 0 ≤ R i) ∧ ∃ Q, InteriorAllocationAdmissible P Q ∧
    ∃ π : Equiv.Perm (Fin K), ∀ k, R (π k) ≤ dpcRate H N Q π k}

theorem interiorRawRegion_subset_rawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    interiorRawRegion H N P ⊆ rawRegion H N P := by
  rintro R ⟨hR, Q, hQ, π, hπ⟩
  exact ⟨hR, Q, hQ.admissible, π, hπ⟩

theorem rawRegion_subset_closure_interiorRawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 < P) :
    rawRegion H N P ⊆ closure (interiorRawRegion H N P) := by
  rintro R ⟨hR, Q, hQ, π, hπ⟩
  let A := isotropicAllocation K tx P
  have hA : InteriorAllocationAdmissible P A := isotropicAllocation_interior hP
  let Qn := fun n ↦ allocationBlend Q A (approximationWeight n)
  let Rn := fun n i ↦ min (R i) (dpcRate H N (Qn n) π (π.symm i))
  have hQn (n : ℕ) : InteriorAllocationAdmissible P (Qn n) :=
    allocationBlend_interior hQ hA (approximationWeight_pos n) (approximationWeight_lt_one n).le
  have hlim : Tendsto Rn atTop (𝓝 R) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hRi : R i ≤ dpcRate H N Q π (π.symm i) := by simpa using hπ (π.symm i)
    simpa only [min_eq_left hRi] using
      (tendsto_const_nhds (x := R i) (f := atTop)).min
        (dpcRate_allocationBlend_tendsto H N hN hQ hA π (π.symm i))
  apply mem_closure_of_tendsto hlim (Eventually.of_forall ?_)
  intro n
  refine ⟨fun i ↦ le_min (hR i) (dpcRate_nonneg H N (Qn n) hN (hQn n).admissible.1 π
    (π.symm i)), Qn n, hQn n, π, fun k ↦ ?_⟩
  simpa only [Rn, Equiv.symm_apply_apply] using min_le_right (R (π k)) (dpcRate H N (Qn n) π k)

theorem region_subset_of_interiorRawRegion_subset
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 < P)
    {s : Set (Fin K → ℝ)} (hs : IsClosed s) (hconvex : Convex ℝ s)
    (hsub : interiorRawRegion H N P ⊆ s) : region H N P ⊆ s :=
  closure_minimal (convexHull_min
    ((rawRegion_subset_closure_interiorRawRegion H N hN hP).trans (closure_minimal hsub hs))
      hconvex) hs

theorem region_eq_closure_convexHull_interiorRawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 < P) :
    region H N P = closure (convexHull ℝ (interiorRawRegion H N P)) := by
  apply Set.Subset.antisymm
  · exact region_subset_of_interiorRawRegion_subset H N hN hP isClosed_closure
      (convex_convexHull ℝ _).closure (fun _ h ↦ subset_closure (subset_convexHull ℝ _ h))
  · exact closure_mono (convexHull_mono (interiorRawRegion_subset_rawRegion H N P))

def strictInteriorRawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) : Set (Fin K → ℝ) :=
  {R | (∀ i, 0 ≤ R i) ∧ ∃ Q, InteriorAllocationAdmissible P Q ∧
    ∃ π : Equiv.Perm (Fin K), ∀ k, R (π k) = 0 ∨ R (π k) < dpcRate H N Q π k}

theorem strictInteriorRawRegion_subset_interiorRawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) (P : ℝ) :
    strictInteriorRawRegion H N P ⊆ interiorRawRegion H N P := by
  rintro R ⟨hR, Q, hQ, π, hπ⟩
  refine ⟨hR, Q, hQ, π, fun k ↦ ?_⟩
  rcases hπ k with hzero | hlt
  · rw [hzero]
    exact dpcRate_nonneg H N Q hN hQ.admissible.1 π k
  · exact hlt.le

theorem interiorRawRegion_subset_closure_strictInteriorRawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    interiorRawRegion H N P ⊆ closure (strictInteriorRawRegion H N P) := by
  rintro R ⟨hR, Q, hQ, π, hπ⟩
  let Rn : ℕ → Fin K → ℝ := fun n i ↦ (1 - approximationWeight n) * R i
  have hlim : Tendsto Rn atTop (𝓝 R) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [sub_zero, one_mul] using
      ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
        approximationWeight_tendsto_zero).mul_const (R i)
  apply mem_closure_of_tendsto hlim (Eventually.of_forall ?_)
  intro n
  refine ⟨fun i ↦ mul_nonneg (sub_nonneg.mpr (approximationWeight_lt_one n).le) (hR i),
    Q, hQ, π, fun k ↦ ?_⟩
  by_cases hz : R (π k) = 0
  · exact Or.inl (by dsimp [Rn]; rw [hz, mul_zero])
  · right
    have hp : 0 < R (π k) := lt_of_le_of_ne (hR (π k)) (Ne.symm hz)
    have hweight := approximationWeight_pos n
    change (1 - approximationWeight n) * R (π k) < dpcRate H N Q π k
    nlinarith [hπ k, mul_pos hweight hp]

theorem region_subset_of_strictInteriorRawRegion_subset
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 < P)
    {s : Set (Fin K → ℝ)} (hs : IsClosed s) (hconvex : Convex ℝ s)
    (hsub : strictInteriorRawRegion H N P ⊆ s) : region H N P ⊆ s :=
  region_subset_of_interiorRawRegion_subset H N hN hP hs hconvex
    ((interiorRawRegion_subset_closure_strictInteriorRawRegion H N P).trans
      (closure_minimal hsub hs))

/-- Strict power, positive-definite covariances, and strict positive rates generate the full region. -/
theorem region_eq_closure_convexHull_strictInteriorRawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (hN : ∀ i, (N i).PosDef) {P : ℝ} (hP : 0 < P) :
    region H N P = closure (convexHull ℝ (strictInteriorRawRegion H N P)) := by
  apply Set.Subset.antisymm
  · exact region_subset_of_strictInteriorRawRegion_subset H N hN hP isClosed_closure
      (convex_convexHull ℝ _).closure (fun _ h ↦ subset_closure (subset_convexHull ℝ _ h))
  · exact closure_mono (convexHull_mono
      ((strictInteriorRawRegion_subset_interiorRawRegion H N hN P).trans
        (interiorRawRegion_subset_rawRegion H N P)))

end CapacityAtlas.Gaussian.MIMOBroadcast
