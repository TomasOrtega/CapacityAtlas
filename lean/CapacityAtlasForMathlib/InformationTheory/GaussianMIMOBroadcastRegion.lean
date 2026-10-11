/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped BigOperators

namespace CapacityAtlas.Gaussian.MIMOBroadcast

variable {K tx : ℕ} {rx : Fin K → ℕ}

/-- A shared trace budget across all receivers and transmit antennas. -/
def AllocationAdmissible (P : ℝ) (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) : Prop :=
  (∀ i, (Q i).PosSemidef) ∧ (∑ i, Matrix.trace (Q i)) ≤ P

/-- The layers that remain as interference at encoding position `k`. -/
def prefixCovariance (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (π : Equiv.Perm (Fin K)) (k : Fin K) : Matrix (Fin tx) (Fin tx) ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin K ↦ j < k), Q (π j)

def receivedCovariance {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (S : Matrix (Fin tx) (Fin tx) ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  N + H * S * H.transpose

theorem prefixCovariance_posSemidef (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hQ : ∀ i, (Q i).PosSemidef) (π : Equiv.Perm (Fin K)) (k : Fin K) :
    (prefixCovariance Q π k).PosSemidef :=
  Matrix.posSemidef_sum _ (fun j _ ↦ hQ (π j))

theorem receivedCovariance_posDef {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (S : Matrix (Fin tx) (Fin tx) ℝ)
    (hN : N.PosDef) (hS : S.PosSemidef) : (receivedCovariance H N S).PosDef := by
  apply hN.add_posSemidef
  simpa using hS.mul_mul_conjTranspose_same H

theorem receivedCovariance_det_pos {r : ℕ} (H : Matrix (Fin r) (Fin tx) ℝ)
    (N : Matrix (Fin r) (Fin r) ℝ) (S : Matrix (Fin tx) (Fin tx) ℝ)
    (hN : N.PosDef) (hS : S.PosSemidef) :
    0 < Matrix.det (receivedCovariance H N S) :=
  (receivedCovariance_posDef H N S hN hS).det_pos

/-- Real Gaussian rate in bits; the actual encoding order is the reverse of `π`. -/
noncomputable def dpcRate
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (π : Equiv.Perm (Fin K)) (k : Fin K) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2
    (Matrix.det (receivedCovariance (H (π k)) (N (π k))
      (prefixCovariance Q π k + Q (π k))) /
      Matrix.det (receivedCovariance (H (π k)) (N (π k)) (prefixCovariance Q π k)))

theorem dpcRate_denominator_pos
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hN : ∀ i, (N i).PosDef) (hQ : ∀ i, (Q i).PosSemidef)
    (π : Equiv.Perm (Fin K)) (k : Fin K) :
    0 < Matrix.det (receivedCovariance (H (π k)) (N (π k)) (prefixCovariance Q π k)) :=
  receivedCovariance_det_pos _ _ _ (hN (π k)) (prefixCovariance_posSemidef Q hQ π k)

theorem dpcRate_numerator_pos
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (hN : ∀ i, (N i).PosDef) (hQ : ∀ i, (Q i).PosSemidef)
    (π : Equiv.Perm (Fin K)) (k : Fin K) :
    0 < Matrix.det (receivedCovariance (H (π k)) (N (π k))
      (prefixCovariance Q π k + Q (π k))) :=
  receivedCovariance_det_pos _ _ _ (hN (π k))
    ((prefixCovariance_posSemidef Q hQ π k).add (hQ (π k)))

/-- All orders and covariance allocations, before convex closure. -/
def rawRegion
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    Set (Fin K → ℝ) :=
  {R | (∀ i, 0 ≤ R i) ∧ ∃ Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ,
    AllocationAdmissible P Q ∧ ∃ π : Equiv.Perm (Fin K),
      ∀ k, R (π k) ≤ dpcRate H N Q π k}

/-- Time sharing and boundary rates for Gaussian dirty-paper coding. -/
def region
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) (P : ℝ) :
    Set (Fin K → ℝ) :=
  closure (convexHull ℝ (rawRegion H N P))

end CapacityAtlas.Gaussian.MIMOBroadcast
