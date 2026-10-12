/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Basic
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.Optimization
import Mathlib.Data.Fin.Tuple.Sort

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx n : ℕ} {rx : Fin K → ℕ}

/-- Receiver permutation preserves the shared encoder and each receiver's own decoder. -/
def Code.relabel (c : Code K tx rx n) (σ : Equiv.Perm (Fin K)) :
    Code K tx (fun i ↦ rx (σ i)) n where
  messages i := c.messages (σ i)
  messages_pos i := c.messages_pos (σ i)
  encode m := c.encode (Equiv.piCongrLeft (fun i ↦ Fin (c.messages i)) σ m)
  decode i := c.decode (σ i)

@[simp] theorem rates_relabel (c : Code K tx rx n) (σ : Equiv.Perm (Fin K)) :
    rates (c.relabel σ) = fun i ↦ rates c (σ i) := rfl

theorem powerAdmissible_relabel_iff (c : Code K tx rx n) (σ : Equiv.Perm (Fin K)) (P : ℝ) :
    PowerAdmissible P (c.relabel σ) ↔ PowerAdmissible P c := by
  change (∏ i, (c.messages (σ i) : ℝ))⁻¹ *
    (∑ m : (i : Fin K) → Fin (c.messages (σ i)), ∑ s, ∑ a,
      (c.encode (Equiv.piCongrLeft (fun i ↦ Fin (c.messages i)) σ m) s a) ^ 2) ≤
        (n : ℝ) * P ↔
      (∏ i, (c.messages i : ℝ))⁻¹ * (∑ m, ∑ s, ∑ a, (c.encode m s a) ^ 2) ≤ (n : ℝ) * P
  rw [Equiv.prod_comp σ (fun i ↦ (c.messages i : ℝ))]
  rw [(Equiv.piCongrLeft (fun i ↦ Fin (c.messages i)) σ).sum_comp
    (fun m ↦ ∑ s, ∑ a, (c.encode m s a) ^ 2)]

theorem errorEvent_relabel
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (c : Code K tx rx n) (σ : Equiv.Perm (Fin K))
    (m : (i : Fin K) → Fin (c.messages (σ i))) :
    errorEvent (fun i ↦ H (σ i)) (c.relabel σ) m =
      (MeasurableEquiv.piCongrLeft (fun i ↦ Fin n → EuclideanSpace ℝ (Fin (rx i))) σ) ⁻¹'
        errorEvent H c (Equiv.piCongrLeft (fun i ↦ Fin (c.messages i)) σ m) := by
  ext z
  change (∃ i, (c.decode (σ i)).apply
    (fun s ↦ (H (σ i)).toEuclideanLin (c.encode
      (Equiv.piCongrLeft (fun j ↦ Fin (c.messages j)) σ m) s) + z i s) ≠ m i) ↔ _
  simp only [Set.mem_preimage, errorEvent, Set.mem_setOf_eq]
  have houtput (i : Fin K) : output H
      (c.encode (Equiv.piCongrLeft (fun j ↦ Fin (c.messages j)) σ m))
      ((MeasurableEquiv.piCongrLeft (fun j ↦ Fin n → EuclideanSpace ℝ (Fin (rx j))) σ) z)
      (σ i) = fun s ↦ (H (σ i)).toEuclideanLin
        (c.encode (Equiv.piCongrLeft (fun j ↦ Fin (c.messages j)) σ m) s) + z i s := by
    funext s
    change _ + ((MeasurableEquiv.piCongrLeft
      (fun j ↦ Fin n → EuclideanSpace ℝ (Fin (rx j))) σ) z) (σ i) s = _ + z i s
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨σ i, ?_⟩
    rwa [houtput, Equiv.piCongrLeft_apply_apply]
  · rintro ⟨j, hj⟩
    obtain ⟨i, rfl⟩ := σ.surjective j
    refine ⟨i, ?_⟩
    rwa [houtput, Equiv.piCongrLeft_apply_apply] at hj

theorem error_relabel
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (c : Code K tx rx n) (σ : Equiv.Perm (Fin K)) :
    error (fun i ↦ H (σ i)) (fun i ↦ N (σ i)) (c.relabel σ) = error H N c := by
  have hmp := measurePreserving_piCongrLeft
    (fun i ↦ Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 (N i))) σ
  have hrow (m : (i : Fin K) → Fin (c.messages (σ i))) :
      blockNoise (fun i ↦ N (σ i)) n (errorEvent (fun i ↦ H (σ i)) (c.relabel σ) m) =
        blockNoise N n (errorEvent H c (Equiv.piCongrLeft (fun i ↦ Fin (c.messages i)) σ m)) := by
    rw [errorEvent_relabel]
    exact hmp.measure_preimage (measurableSet_errorEvent H c _).nullMeasurableSet
  simp only [error, hrow]
  change (∏ i, (c.messages (σ i) : ℝ))⁻¹ * _ = _
  rw [Equiv.prod_comp σ (fun i ↦ (c.messages i : ℝ))]
  congr 1
  exact (Equiv.piCongrLeft (fun i ↦ Fin (c.messages i)) σ).sum_comp
    (fun m ↦ (blockNoise N n (errorEvent H c m)).toReal)

theorem mem_capacityRegion_relabel
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (σ : Equiv.Perm (Fin K)) {P : ℝ} {R : Fin K → ℝ}
    (hR : R ∈ capacityRegion H N P) :
    (fun i ↦ R (σ i)) ∈ capacityRegion (fun i ↦ H (σ i)) (fun i ↦ N (σ i)) P := by
  rw [capacityRegion_eq_achievableVectorRegion] at hR ⊢
  refine ⟨fun i ↦ hR.1 (σ i), fun ε hε ↦ ?_⟩
  obtain ⟨n₀, hn₀, hcodes⟩ := hR.2 ε hε
  refine ⟨n₀, hn₀, fun n hn ↦ ?_⟩
  obtain ⟨c, hc, he, hr⟩ := hcodes n hn
  refine ⟨c.relabel σ, (powerAdmissible_relabel_iff c σ P).mpr hc, ?_, ?_⟩
  · change error (fun i ↦ H (σ i)) (fun i ↦ N (σ i)) (c.relabel σ) ≤ ε
    rwa [error_relabel]
  · exact fun i ↦ hr (σ i)

theorem allocationAdmissible_relabel_iff
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (σ : Equiv.Perm (Fin K)) (P : ℝ) :
    AllocationAdmissible P (fun i ↦ Q (σ i)) ↔ AllocationAdmissible P Q := by
  simp only [AllocationAdmissible]
  rw [Equiv.sum_comp σ (fun i ↦ trace (Q i))]
  exact and_congr (σ.forall_congr (fun _ ↦ Iff.rfl)) Iff.rfl

@[simp] theorem prefixCovariance_relabel
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (σ π : Equiv.Perm (Fin K)) (k : Fin K) :
    prefixCovariance (fun i ↦ Q (σ i)) π k = prefixCovariance Q (π.trans σ) k := rfl

@[simp] theorem dpcRate_relabel
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (σ π : Equiv.Perm (Fin K)) (k : Fin K) :
    dpcRate (fun i ↦ H (σ i)) (fun i ↦ N (σ i)) (fun i ↦ Q (σ i)) π k =
      dpcRate H N Q (π.trans σ) k := rfl

theorem weightedDpcRate_relabel
    (w : Fin K → ℝ) (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (σ π : Equiv.Perm (Fin K)) :
    weightedDpcRate (fun i ↦ w (σ i)) (fun i ↦ H (σ i)) (fun i ↦ N (σ i))
      (fun i ↦ Q (σ i)) π = weightedDpcRate w H N Q (π.trans σ) := rfl

theorem exists_weightedDpcRate_bound_of_relabel
    (w : Fin K → ℝ) (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (σ : Equiv.Perm (Fin K)) {P : ℝ} {R : Fin K → ℝ}
    (hbound : ∃ Q, AllocationAdmissible P Q ∧
      (∑ i, w (σ i) * R (σ i)) ≤ weightedDpcRate (fun i ↦ w (σ i))
        (fun i ↦ H (σ i)) (fun i ↦ N (σ i)) Q (Equiv.refl _)) :
    ∃ Q, AllocationAdmissible P Q ∧
      (∑ i, w i * R i) ≤ weightedDpcRate w H N Q σ := by
  obtain ⟨Q, hQ, hb⟩ := hbound
  let Q' := fun i ↦ Q (σ.symm i)
  have hQ' : AllocationAdmissible P Q' := (allocationAdmissible_relabel_iff Q σ.symm P).mpr hQ
  have heq : (fun i ↦ Q' (σ i)) = Q := by ext i; simp only [Q', Equiv.symm_apply_apply]
  have hr := weightedDpcRate_relabel w H N Q' σ (Equiv.refl _)
  simp only [heq, Equiv.refl_trans] at hr
  refine ⟨Q', hQ', ?_⟩
  rw [← hr, ← Equiv.sum_comp σ (fun i ↦ w i * R i)]
  exact hb

/-- Bounds for monotone weights after relabeling give the bound for every receiver order. -/
theorem exists_weightedDpcRate_bound_of_sorted
    (w : Fin K → ℝ) (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} {R : Fin K → ℝ}
    (hbound : ∀ σ : Equiv.Perm (Fin K), Monotone (fun i ↦ w (σ i)) →
      ∃ Q, AllocationAdmissible P Q ∧
        (∑ i, w (σ i) * R (σ i)) ≤ weightedDpcRate (fun i ↦ w (σ i))
          (fun i ↦ H (σ i)) (fun i ↦ N (σ i)) Q (Equiv.refl _)) :
    ∃ Q, AllocationAdmissible P Q ∧ ∃ π,
      (∑ i, w i * R i) ≤ weightedDpcRate w H N Q π := by
  let σ := Tuple.sort w
  have hmono : Monotone (fun i ↦ w (σ i)) := Tuple.monotone_sort w
  obtain ⟨Q, hQ, hb⟩ := exists_weightedDpcRate_bound_of_relabel w H N σ (hbound σ hmono)
  exact ⟨Q, hQ, σ, hb⟩

end CapacityAtlas.Gaussian.MIMOBroadcast
