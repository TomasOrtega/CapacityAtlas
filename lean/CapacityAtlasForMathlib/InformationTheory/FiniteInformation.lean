/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution.Entropy
import CapacityAtlasForMathlib.InformationTheory.FiniteChannelCapacity
import CapacityAtlasForMathlib.InformationTheory.FiniteChannel.Encoded
import CapacityAtlasForMathlib.InformationTheory.FiniteDistribution.Joint

open scoped BigOperators

namespace CapacityAtlas.FiniteInformation

/-- The normalized joint law already justified by the finite-channel API. -/
def joint {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteDistribution A) (W : FiniteChannel A B) : FiniteDistribution (A × B) :=
  p.joint W.rowDistribution

/-- Entropy in bits of a finite observable. Reuses the atlas/PFR entropy bridge. -/
noncomputable def entropy {Ω A : Type*} [Fintype Ω] [Fintype A]
    (p : FiniteDistribution Ω) (f : Ω → A) : ℝ := by
  classical
  exact (p.map f).entropyBits

/-- Mutual information in bits, expressed through the existing finite entropy. -/
noncomputable def information {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]
    (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) : ℝ :=
  entropy p f + entropy p g - entropy p (fun ω ↦ (f ω, g ω))

/-- Conditional mutual information in bits. All variables live under one joint law. -/
noncomputable def conditional {Ω A B C : Type*}
    [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]
    (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) (h : Ω → C) : ℝ :=
  entropy p (fun ω ↦ (f ω, h ω)) + entropy p (fun ω ↦ (g ω, h ω)) -
    entropy p h - entropy p (fun ω ↦ (f ω, g ω, h ω))

/-- Conditional entropy, for example the entropy rate of a stationary Markov chain. -/
noncomputable def conditionalEntropy {Ω A B : Type*}
    [Fintype Ω] [Fintype A] [Fintype B]
    (p : FiniteDistribution Ω) (f : Ω → A) (g : Ω → B) : ℝ :=
  entropy p (fun ω ↦ (f ω, g ω)) - entropy p g

/-- Independently sampled finite variables. No new normalization lemma is assumed. -/
def independent {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteDistribution A) (q : FiniteDistribution B) : FiniteDistribution (A × B) :=
  joint p (FiniteChannel.ofRows fun _ ↦ q)

/-- Average error of a deterministic encoder/decoder through a fixed block law. -/
noncomputable def decodingError {A B : Type*} [Fintype A] [Fintype B]
    (W : FiniteChannel A B) (messages : ℕ) (encode : Fin messages → A)
    (decode : B → Fin messages) : ℝ := by
  classical
  exact (messages : ℝ)⁻¹ * ∑ m, ∑ y,
    if decode y = m then 0 else W.transition (encode m) y

end CapacityAtlas.FiniteInformation
