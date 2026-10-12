/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.Network.Multisource.Basic
import CapacityAtlasForMathlib.Network.Multisource.Rounding

open scoped BigOperators

namespace CapacityAtlas.Multisource.Network

variable {vertices edges sources : ℕ} (G : Network vertices edges sources)

theorem rounded_cut_constraints (r : Fin sources → ℝ) (hr : r ∈ G.cutRegion)
    (scale : ℕ) (margin : ℝ) (hmargin : 0 ≤ margin)
    (hscale : (edges : ℝ) ≤ scale * margin)
    (v : Fin vertices) (hv : v ∈ G.sinks) (cut : Finset (Fin vertices)) (hcut : v ∉ cut) :
    (∑ i : Fin sources, if G.sourceNode i ∈ cut then roundedDemand scale margin (r i) else 0) ≤
      ∑ e : Fin edges, if G.source e ∈ cut ∧ G.target e ∉ cut then G.packetBits scale e else 0 := by
  classical
  let inside := Finset.univ.filter (fun i ↦ G.sourceNode i ∈ cut)
  let crossing := Finset.univ.filter (fun e ↦ G.source e ∈ cut ∧ G.target e ∉ cut)
  have hreal : ∑ i ∈ inside, r i ≤ ∑ e ∈ crossing, G.linkRate e := by
    simpa [inside, crossing, Finset.sum_filter, cutDemand, cutRate] using hr.2 v hv cut hcut
  have h := sum_roundedDemand_le_cut inside crossing r G.linkRate hr.1 hreal
    scale margin hmargin (by simpa using hscale)
  simpa [inside, crossing, Finset.sum_filter, packetBits] using h

theorem exists_integer_approximation (r : Fin sources → ℝ) (hr : r ∈ G.cutRegion)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ scale : ℕ, 0 < scale ∧ ∃ demand : Fin sources → ℕ,
      (∀ i, r i - ε ≤ (demand i : ℝ) / scale) ∧
      ∀ v ∈ G.sinks, ∀ cut : Finset (Fin vertices), v ∉ cut →
        (∑ i : Fin sources, if G.sourceNode i ∈ cut then demand i else 0) ≤
          ∑ e : Fin edges, if G.source e ∈ cut ∧ G.target e ∉ cut then
            G.packetBits scale e else 0 := by
  let margin := ε / 2
  have hmargin : 0 < margin := half_pos hε
  obtain ⟨scale, hscale⟩ := exists_nat_gt (max (((edges : ℝ) + 1) / margin) 0)
  have hpos : 0 < scale := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hscale)
  have hscaleReal : (0 : ℝ) < scale := by exact_mod_cast hpos
  have hbound : (edges : ℝ) + 1 < scale * margin :=
    (div_lt_iff₀ hmargin).mp (lt_of_le_of_lt (le_max_left _ _) hscale)
  have hlarge : (edges : ℝ) ≤ scale * margin := by linarith
  have hinv : (scale : ℝ)⁻¹ ≤ margin := by
    apply (inv_le_iff_one_le_mul₀ hscaleReal).mpr
    nlinarith [Nat.cast_nonneg edges (α := ℝ)]
  refine ⟨scale, hpos, fun i ↦ roundedDemand scale margin (r i), ?_, ?_⟩
  · intro i
    have hh := roundedDemand_rate_lower scale hpos margin (r i)
    dsimp [margin] at *
    linarith
  · exact G.rounded_cut_constraints r hr scale margin hmargin.le hlarge

end CapacityAtlas.Multisource.Network
