/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.OperationalRegion
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators

namespace CapacityAtlas.Deletion

/-- Only the retained subsequence is exposed to the decoder, not its positions. -/
def output {n : ℕ} (word keep : Fin n → Bool) : List Bool :=
  (List.finRange n).filterMap (fun t ↦ if keep t then some (word t) else none)

/-- Independent-deletion mask weight, with retention factor `1 - d` and deletion factor `d`. -/
noncomputable def maskProbability {n : ℕ} (d : ℝ) (keep : Fin n → Bool) : ℝ :=
  ∏ t, if keep t then 1 - d else d

/-- Deterministic binary block code whose decoder accepts a variable-length output list. -/
structure Code (n : ℕ) where
  /-- Number of distinct messages. -/
  messages : ℕ
  /-- The message set is nonempty. -/
  messages_pos : 0 < messages
  /-- Input word transmitted for each message. -/
  encode : Fin messages → Fin n → Bool
  /-- Message estimate from the retained bit sequence. -/
  decode : List Bool → Fin messages

/-- Average decoding error over uniform messages and independent deletion masks. -/
noncomputable def error (d : ℝ) {n : ℕ} (c : Code n) : ℝ := by
  classical
  exact (c.messages : ℝ)⁻¹ * ∑ m, ∑ keep : Fin n → Bool,
    if c.decode (output (c.encode m) keep) = m then 0 else maskProbability d keep

/-- Rate is per input bit, never per surviving output bit. -/
noncomputable def capacity (d : ℝ) : ℝ :=
  Operational.capacity Code (fun _ _ ↦ True) (fun _ c ↦ error d c)
    (fun n c ↦ Operational.messageRate c.messages n)

end CapacityAtlas.Deletion
