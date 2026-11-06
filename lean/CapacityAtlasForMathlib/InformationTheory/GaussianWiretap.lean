/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianOperational

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CapacityAtlas.Gaussian

/-- Independent uniform message and finite private seed. -/
structure WiretapCode (n : ℕ) where
  /-- Number of messages in the finite alphabet. -/
  messages : ℕ
  /-- The message alphabet contains at least one element. -/
  messages_pos : 0 < messages
  /-- Number of independent private randomization seeds. -/
  seeds : ℕ
  /-- The encoder seed alphabet is nonempty. -/
  seeds_pos : 0 < seeds
  /-- Real input block selected from a message and private seed. -/
  encode : Fin messages → Fin seeds → Fin n → ℝ
  /-- Measurable legitimate-receiver decoder without access to the private seed. -/
  decode : Decoder (Fin n → ℝ) messages

/-- Require every message/seed encoder block to have energy at most `n * P`. -/
def MessageSeedPowerAdmissible (P : ℝ) {n : ℕ} (c : WiretapCode n) : Prop :=
  ∀ m seed, (∑ t, (c.encode m seed t) ^ 2) ≤ (n : ℝ) * P

/-- Legitimate-receiver decoding error averaged uniformly over messages and encoder seeds. -/
noncomputable def wiretapError (N : ℝ) {n : ℕ} (c : WiretapCode n) : ℝ :=
  (c.messages * c.seeds : ℝ)⁻¹ * ∑ m, ∑ seed,
    ((noise N n) {z | c.decode.apply (fun t ↦ c.encode m seed t + z t) ≠ m}).toReal

/-- For `0 < N`, the eavesdropper output's Lebesgue density conditional on a fixed message,
averaged uniformly over encoder seeds. Values at `N ≤ 0` are only totalized formula values. -/
noncomputable def wiretapConditionalDensity (N : ℝ) {n : ℕ} (c : WiretapCode n)
    (m : Fin c.messages) (z : Fin n → ℝ) : ℝ :=
  (c.seeds : ℝ)⁻¹ * ∑ seed, ∏ t, gaussianPDFReal (c.encode m seed t) N.toNNReal (z t)

/-- For `0 < N`, the eavesdropper output's Lebesgue density averaged uniformly over messages
and encoder seeds. Values at `N ≤ 0` are only totalized formula values. -/
noncomputable def wiretapOutputDensity (N : ℝ) {n : ℕ} (c : WiretapCode n)
    (z : Fin n → ℝ) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m, wiretapConditionalDensity N c m z

/-- Density formula for unnormalized `I(M; Z^n)` in bits, valid for `0 < N`.
There is no division by blocklength. At `N ≤ 0` and positive blocklength, the densities
and this formula are zero; this value must not be used as noiseless mutual information. -/
noncomputable def wiretapLeakage (N : ℝ) {n : ℕ} (c : WiretapCode n) : ℝ :=
  ((c.messages : ℝ)⁻¹ * ∑ m,
    ∫ z : Fin n → ℝ, wiretapConditionalDensity N c m z *
      Real.log (wiretapConditionalDensity N c m z / wiretapOutputDensity N c z)) / Real.log 2

/-- Operational secrecy capacity for `0 < N₁` and `0 < N₂`, with vanishing decoding error
and unnormalized message leakage. At `N₂ ≤ 0`, the density-based leakage criterion is
outside its intended domain. -/
noncomputable def wiretapCapacity (P N₁ N₂ : ℝ) : ℝ :=
  Operational.capacity WiretapCode (fun _ c ↦ MessageSeedPowerAdmissible P c)
    (fun _ c ↦ max (wiretapError N₁ c) (wiretapLeakage N₂ c))
    (fun n c ↦ Operational.messageRate c.messages n)

end CapacityAtlas.Gaussian
