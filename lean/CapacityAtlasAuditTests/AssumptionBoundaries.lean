/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlas.Channels.QarySymmetric
import CapacityAtlas.Channels.MultipleAccess
import CapacityAtlas.Channels.InputCost
import CapacityAtlasForMathlib.InformationTheory.ConfidentialBroadcast.CoordinateLaw
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding.Asymptotic
import CapacityAtlasForMathlib.InformationTheory.Entropy.Kernel
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.Rejection
import CapacityAtlasForMathlib.LinearAlgebra.LogDetConcavity
import CapacityAtlasForMathlib.Network.LinearMulticast.Circuit
import CapacityAtlasForMathlib.Network.WirelessTransport.Grid

/-! These applications keep helper APIs usable without redundant assumptions. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CapacityAtlasAuditTests.AssumptionBoundaries

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hB : B.PosDef) {a : ℝ} (h : B⁻¹ = a • A⁻¹) :
    a • B = A :=
  Matrix.inv_proportional_smul hB h

example (q : ℕ) {p : ℝ} (hp : p ≤ ((q - 1 : ℕ) : ℝ) / q) : p ≤ 1 :=
  CapacityAtlas.Channel.qarySymmetric_p_le_one q hp

example {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]
    (channel : CapacityAtlas.FiniteChannel (X₁ × X₂) Y) :
    CapacityAtlas.MultipleAccess.operationalRegion channel =
      CapacityAtlas.MultipleAccess.informationRegion channel :=
  CapacityAtlas.Channel.multipleAccessCapacityStatement channel

example {X Y : Type*} [Fintype X] [Fintype Y]
    (channel : CapacityAtlas.FiniteChannel X Y) (cost : X → ℝ) (budget : ℝ)
    (hfeasible : ∃ symbol, cost symbol ≤ budget) :
    channel.constrainedOperationalCapacityBits cost budget =
      channel.constrainedInformationCapacityBits cost budget :=
  channel.finiteDMCInputCostCapacityStatement cost budget hfeasible

example {R : ℝ} {m : ℕ} (hR : 0 < R) (i : Fin m) :
    0 ≤ (i.val : ℝ) * CapacityAtlas.WirelessTransport.gridStep R m ∧
      (i.val : ℝ) * CapacityAtlas.WirelessTransport.gridStep R m +
        CapacityAtlas.WirelessTransport.gridStep R m ≤ R / 2 :=
  CapacityAtlas.WirelessTransport.grid_coord_bounds hR i

example {R Δ : ℝ} {m : ℕ} (hR : 0 < R)
    (i : CapacityAtlas.WirelessTransport.GridIndex m) :
    ‖CapacityAtlas.WirelessTransport.gridTx R Δ m i‖ ≤ R :=
  CapacityAtlas.WirelessTransport.gridTx_norm_le hR i

example (R a : ℝ) (n : ℕ) :
    (CapacityAtlas.FiniteChannel.messageCountAtRate R n - 1 : ℕ) *
        (ENNReal.ofReal (Real.exp ((n : ℝ) * a)))⁻¹ ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) * (a - R * Real.log 2)))) :=
  CapacityAtlas.MeasureChannel.roundedMessage_threshold_le R a n

example {X Y Z O : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype O] [DecidableEq O] {W : CapacityAtlas.FiniteBroadcastChannel X Y Z}
    {n : ℕ} (c : CapacityAtlas.ConfidentialBroadcast.Code W n)
    (V : CapacityAtlas.FiniteChannel X O) (observe : Y × Z → O)
    (hobserve : ∀ x, ((CapacityAtlas.ConfidentialBroadcast.receiverPair W).rowDistribution x).map
      observe = V.rowDistribution x) :
    c.fullJoint.map (fun z ↦ (z.1.1, fun j ↦ observe (z.2 j))) = c.joint V :=
  c.fullJoint_observe V observe hobserve

example {X Y M : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace M] [Fintype M] (κ : Kernel X Y) [IsMarkovKernel κ]
    (code : CapacityAtlas.MeasureChannel.OneShotCode X Y M) :
    CapacityAtlas.MeasureChannel.averageError κ code ≤ 1 :=
  CapacityAtlas.MeasureChannel.averageError_le_one κ code

example {S T T' : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace T']
    (κ : Kernel T S) (μ : Measure T) (f : T' ≃ᵐ T) :
    Kernel.entropy (Kernel.comap κ f f.measurable) (μ.comap f) = Kernel.entropy κ μ :=
  Kernel.entropy_comap_equiv κ f

example {U : Type*} [MeasurableSpace U] (μ : Measure U) {g : U → ℝ≥0∞}
    (hg : Measurable g) {B E : Set U} (hB : MeasurableSet B) (hE : MeasurableSet E)
    {T : ℝ} (hT : 0 < T) (hcut : ∀ u ∈ B, g u ≤ ENNReal.ofReal T) :
    (μ.prod CapacityAtlas.MeasureBinning.seedLaw)
        (CapacityAtlas.MeasureBinning.seededAcceptance g B T ∩ Prod.fst ⁻¹' E) =
      (μ.withDensity g) (B ∩ E) / ENNReal.ofReal T :=
  CapacityAtlas.MeasureBinning.measure_seededAcceptance_inter μ hg hB hE hT hcut

open scoped Classical in
example {I W T : Type} [Fintype W] [Fintype I]
    (G : CapacityAtlas.LinearMulticast.Circuit I W) (output : T → I → I ⊕ W)
    (route : ∀ t, ∃ c : G.Variable → ZMod 2, G.outputMatrix c (output t) = 1) :
    ∃ b : ℕ, 0 < b ∧ ∃ c : G.Variable → GaloisField 2 b,
      ∀ t, (G.outputMatrix c (output t)).det ≠ 0 :=
  G.simultaneous output route

end CapacityAtlasAuditTests.AssumptionBoundaries
