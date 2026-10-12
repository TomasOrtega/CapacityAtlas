/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Multisource.Approximation
import CapacityAtlasForMathlib.Network.Multisource.Repetition
import CapacityAtlasForMathlib.Network.Multisource.Routing
import CapacityAtlasForMathlib.Network.Multisource.LinearCode
import CapacityAtlasForMathlib.Network.Multisource.Converse

namespace CapacityAtlas.Multisource.Network

variable {vertices edges sources : ℕ} (G : Network vertices edges sources)

theorem exists_perfect_approximation (r : Fin sources → ℝ) (hr : r ∈ G.cutRegion)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : G.Code n,
      (∀ m, c.Successful m) ∧ ∀ i, r i - ε ≤ c.rate i := by
  classical
  obtain ⟨scale, hscale, demand, hrates, hcuts⟩ := G.exists_integer_approximation r hr ε hε
  obtain ⟨b, hb, coeff, output, hlocal, hdet⟩ :=
    G.exists_linear_of_integerCuts (G.packetBits scale) demand hcuts
  letI : Fintype (GaloisField 2 b) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 b) = 2 ^ b := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 b (Nat.ne_of_gt hb)
  have hbits : ∀ e, b * G.packetBits scale e ≤ G.packetBits (scale * b) e := by
    intro e
    exact packetBits_copies_le b (by simp [Nat.mul_comm]) e
  obtain ⟨code, hmessages, hdecode⟩ := G.exists_perfectCode_of_linear hcard
    (G.packetBits scale) demand hbits coeff output hlocal hdet
  refine ⟨scale * b, Nat.mul_pos hscale hb, code, fun m v hv ↦ hdecode v hv m, fun i ↦ ?_⟩
  have hrate : code.rate i = (demand i : ℝ) / scale := by
    unfold Code.rate Operational.messageRate
    rw [hmessages i]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Nat.cast_mul]
    rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
    have hs : (scale : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hscale)
    have hbn : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)
    field_simp [hs, hbn]
  rw [hrate]
  exact hrates i

theorem cutRegion_subset_capacityRegion : G.cutRegion ⊆ G.capacityRegion := by
  intro r hr
  exact mem_capacityRegion_of_perfect_approximation r hr.1
    (fun ε hε ↦ G.exists_perfect_approximation r hr ε hε)

theorem capacityRegion_eq_cutRegion : G.capacityRegion = G.cutRegion :=
  Set.Subset.antisymm G.capacityRegion_subset_cutRegion G.cutRegion_subset_capacityRegion

end CapacityAtlas.Multisource.Network
