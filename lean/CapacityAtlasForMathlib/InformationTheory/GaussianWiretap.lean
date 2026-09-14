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
  messages : ℕ
  messages_pos : 0 < messages
  seeds : ℕ
  seeds_pos : 0 < seeds
  encode : Fin messages → Fin seeds → Fin n → ℝ
  decode : Decoder (Fin n → ℝ) messages

def MessageSeedPowerAdmissible (P : ℝ) {n : ℕ} (c : WiretapCode n) : Prop :=
  ∀ m seed, (∑ t, (c.encode m seed t) ^ 2) ≤ (n : ℝ) * P

noncomputable def wiretapError (N : ℝ) {n : ℕ} (c : WiretapCode n) : ℝ :=
  (c.messages * c.seeds : ℝ)⁻¹ * ∑ m, ∑ seed,
    ((noise N n) {z | c.decode.apply (fun t ↦ c.encode m seed t + z t) ≠ m}).toReal

noncomputable def wiretapConditionalDensity (N : ℝ) {n : ℕ} (c : WiretapCode n)
    (m : Fin c.messages) (z : Fin n → ℝ) : ℝ :=
  (c.seeds : ℝ)⁻¹ * ∑ seed, ∏ t, gaussianPDFReal (c.encode m seed t) N.toNNReal (z t)

noncomputable def wiretapOutputDensity (N : ℝ) {n : ℕ} (c : WiretapCode n)
    (z : Fin n → ℝ) : ℝ :=
  (c.messages : ℝ)⁻¹ * ∑ m, wiretapConditionalDensity N c m z

/-- Unnormalized I(M;Z^n) in bits. No division by blocklength. -/
noncomputable def wiretapLeakage (N : ℝ) {n : ℕ} (c : WiretapCode n) : ℝ :=
  ((c.messages : ℝ)⁻¹ * ∑ m,
    ∫ z : Fin n → ℝ, wiretapConditionalDensity N c m z *
      Real.log (wiretapConditionalDensity N c m z / wiretapOutputDensity N c z)) / Real.log 2

noncomputable def wiretapCapacity (P N₁ N₂ : ℝ) : ℝ :=
  Operational.capacity WiretapCode (fun _ c ↦ MessageSeedPowerAdmissible P c)
    (fun _ c ↦ max (wiretapError N₁ c) (wiretapLeakage N₂ c))
    (fun n c ↦ Operational.messageRate c.messages n)

end CapacityAtlas.Gaussian
