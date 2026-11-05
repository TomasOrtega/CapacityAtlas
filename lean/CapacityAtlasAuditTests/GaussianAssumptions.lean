/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlas.Claims.GaussianInterference
import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureScore
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.LayeredReadback
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.RegionProperties
import CapacityAtlasForMathlib.InformationTheory.GaussianProportionalEntropy
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.EnhancedEntropy
import CapacityAtlasForMathlib.InformationTheory.GaussianDeBruijn
import CapacityAtlasForMathlib.InformationTheory.GaussianFisherBasis
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.CodeConverse
import CapacityAtlasForMathlib.InformationTheory.GaussianInterference.Capacity
import CapacityAtlasForMathlib.Probability.GaussianDensity
import CapacityAtlasForMathlib.InformationTheory.GaussianMIMOBroadcast.AchievabilityClosure
import CapacityAtlasForMathlib.InformationTheory.GaussianMixtureEntropy

/-! Exact signature checks keep Gaussian APIs free of the removed assumptions. -/

open MeasureTheory ProbabilityTheory InformationTheory Real Matrix Filter
open CapacityAtlas.MeasureChannel CapacityAtlas.MeasureBinning
open scoped BigOperators ENNReal Topology Classical MatrixOrder

namespace CapacityAtlas.MeasureInformation

example : ∀ {α : Type*} [Fintype α]
    (a s : α → ℝ) (_ : ∀ k, 0 ≤ a k),
    |(∑ k, a k * s k) / ∑ k, a k| ≤ ∑ k, |s k| :=
  @abs_weighted_average_le_sum_abs

end CapacityAtlas.MeasureInformation

namespace CapacityAtlas.Gaussian.MIMOBroadcast

example : ∀ {K tx : ℕ} {rx : Fin K → ℕ} (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (perm : Equiv.Perm (Fin K)) (order : ℕ → Fin K)
    (_ : ∀ i j : Fin K, i < j → order j.val < order i.val)
    (n : ℕ) (L : ℕ → ℕ) (T : ℕ → ℝ) (hT : ∀ i, 0 < T i)
    (initial : LayerBlocks K tx n) (i : Fin K),
    let D := gaussianStages H N Q hQ perm order n L T hT
    ((sequenceReferenceLaw (fun j ↦ (D j).referenceKernel) initial i.val) ⊗ₘ (D i.val).target)
      (D i.val).goodᶜ = (blockLayerLaw Q perm n)
        {x | ENNReal.ofReal (T i.val) < blockLayerStateLikelihood
          (H (perm (order i.val))) (N (perm (order i.val))) Q perm (order i.val) n x} :=
  @gaussianStages_jointBad_eq_terminal

end CapacityAtlas.Gaussian.MIMOBroadcast

namespace CapacityAtlas.Gaussian.MIMOBroadcast

example : ∀ {K tx : ℕ} {rx : Fin K → ℕ} (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} (_ : 0 ≤ P),
    region (0 : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) N P = {0} :=
  @region_zero_channel

end CapacityAtlas.Gaussian.MIMOBroadcast

namespace CapacityAtlas.MeasureInformation

example : ∀ {P Q A B a : ℝ} (_ : 0 < P) (_ : 0 < A) (_ : 0 < B)
    (_ : a ≤ 1) (_ : A = a * B) (_ : P + (B - A) ≤ Q),
    a * log P - log Q ≤ a * log A - log B :=
  @proportional_log_sub_le

end CapacityAtlas.MeasureInformation

namespace CapacityAtlas.Gaussian.MIMOBroadcast

example : ∀ {K tx n : ℕ} {rx : Fin K → ℕ} (c : Code K tx rx n) (_ : 0 < tx) (_ : 0 < n)
    (E F S : Matrix (Fin tx) (Fin tx) ℝ) (_ : E.PosDef) (_ : F.PosDef) (_ : S.PosSemidef)
    {f g : ℝ} (_ : 0 < f) (_ : f ≤ g)
    (_ : g • (S + F)⁻¹ = f • (S + E)⁻¹) (k : ℕ),
    f * codePrefixEntropy c E k - g * codePrefixEntropy c F k ≤
      n * (f * MeasureInformation.entropyWith (multivariateGaussian 0 (S + E)) volume -
        g * MeasureInformation.entropyWith (multivariateGaussian 0 (S + F)) volume) :=
  @codePrefixEntropy_difference_le

end CapacityAtlas.Gaussian.MIMOBroadcast

namespace CapacityAtlas.MeasureInformation

example : ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (w : α → ℝ) (_ : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (_ : N.PosDef)
    (x v : EuclideanSpace ℝ ι),
    HasLineDerivAt ℝ (fun y ↦ 1 + log (gaussianMixturePDFReal w m N y))
      (lineDeriv ℝ (gaussianMixturePDFReal w m N) x v / gaussianMixturePDFReal w m N x) x v :=
  @hasLineDerivAt_one_add_log_gaussianMixturePDFReal

end CapacityAtlas.MeasureInformation

namespace CapacityAtlas.Gaussian.Interference

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (_ : 0 < L) (_ : 0 ≤ P)
    (_ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U)
    {K n : ℕ} (c : Code K n) (_ : PowerAdmissible μ P c)
    (i j : Fin K) (_ : i ≠ j),
    (1 - error μ c) * (Real.log (c.messages i) + Real.log (c.messages j)) ≤
      (n : ℝ) * Real.log (1 + U ^ 2 * P / converseNoise L U) + 2 * Real.log 2 :=
  @code_pair_converse

end CapacityAtlas.Gaussian.Interference

namespace ProbabilityTheory

example : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (EuclideanSpace ℝ ι)} [IsFiniteMeasure μ]
    (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (_ : Integrable (fun x : EuclideanSpace ℝ ι ↦ (x - m) ⬝ᵥ S⁻¹ *ᵥ (x - m)) μ),
    Integrable (fun x ↦ Real.log (multivariateGaussianPDFReal m S x)) μ :=
  @integrable_log_multivariateGaussianPDFReal

end ProbabilityTheory

namespace CapacityAtlas.Gaussian.MIMOBroadcast

example : ∀ {K : ℕ} {rx : Fin K → ℕ}
    (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin 0) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} (_ : 0 ≤ P), capacityRegion H N P = region H N P :=
  @capacityRegion_eq_region_no_transmit_antennas

end CapacityAtlas.Gaussian.MIMOBroadcast

namespace CapacityAtlas.MeasureInformation

example : ∀ {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α (EuclideanSpace ℝ ι))
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (_ : N.PosDef)
    (_ : ∀ x, κ x = multivariateGaussian (m x) N)
    (S : Matrix ι ι ℝ) (_ : S.PosDef)
    (_ : ∀ i j, covariance (fun y : EuclideanSpace ℝ ι ↦ y i)
      (fun y ↦ y j) (κ ∘ₘ μ) = S i j),
    mutualInfo (μ ⊗ₘ κ) ≤ ENNReal.ofReal ((log S.det - log N.det) / 2) :=
  @mutualInfo_gaussianMixture_le_of_covariance_ennreal

end CapacityAtlas.MeasureInformation

namespace CapacityAtlas.Gaussian.Interference

example : ∀ {K n : ℕ} (μ : Measure ℂ) (c : Code K n) (m : c.Message) (i : Fin K),
    (∫ H, receiverErrorAt c m H i ∂stateLaw μ K n) =
      ((stateLaw μ K n).prod (blockNoise K n)).real (receiverEvent c m i) :=
  @integral_receiverErrorAt

end CapacityAtlas.Gaussian.Interference

namespace CapacityAtlas.MeasureInformation

example : ∀ {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype α] [Fintype β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure α) (f : α → β) (m : β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ),
    gaussianCodebookKernel m N ∘ₘ μ.map f = gaussianCodebookKernel (m ∘ f) N ∘ₘ μ :=
  @gaussianCodebookKernel_comp_map

example : ∀ {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype α] [Fintype β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure α) (ν : Measure β) (m : α → β → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ),
    gaussianMarginalCodebookKernel ν m N ∘ₘ μ =
      gaussianCodebookKernel (fun p : α × β ↦ m p.1 p.2) N ∘ₘ μ.prod ν :=
  @gaussianMarginalCodebookKernel_comp

end CapacityAtlas.MeasureInformation

namespace CapacityAtlas.MeasureInformation

example : ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (w : α → ℝ) (_ : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (_ : N.PosDef)
    (v x : EuclideanSpace ℝ ι),
    |directionalScore (gaussianMixturePDFReal w m N) v x| ≤
      ∑ k, |v ⬝ᵥ N⁻¹ *ᵥ (x - m k)| :=
  @abs_directionalScore_gaussianMixturePDFReal_le

example : ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (w : α → ℝ) (_ : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (_ : N.PosDef)
    (v k : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (p : ℝ≥0∞) (_ : p ≠ ⊤),
    MemLp (directionalScore (gaussianMixturePDFReal w m N) v) p
      (multivariateGaussian k S) :=
  @memLp_directionalScore_gaussianMixturePDFReal

example : ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] (w : α → ℝ) (_ : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (_ : N.PosDef)
    (v k : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ),
    MemLp (fun x ↦ lineDeriv ℝ
      (fun y ↦ lineDeriv ℝ (gaussianMixturePDFReal w m N) y v) x v /
        gaussianMixturePDFReal w m N x) 2 (multivariateGaussian k S) :=
  @memLp_two_secondDeriv_div_gaussianMixturePDFReal

end CapacityAtlas.MeasureInformation

namespace CapacityAtlas.Gaussian.Interference

example : ∀ {K n : ℕ} (c : Code K n) (H : StateBlock K n) (i j : Fin K)
    (_ : i ≠ j) (m : c.Message) {U : ℝ}
    (_ : ∀ s, ‖H s i i‖ ≤ U) (_ : ∀ s, ‖H s i j‖ ≤ U),
    pairEnergy c H i j m ≤ 2 * U ^ 2 * energy c m H :=
  @pairEnergy_le_energy

example : ∀ {K n : ℕ} (μ : Measure ℂ) (c : Code K n) {P U : ℝ}
    (_ : PowerAdmissible μ P c) (i j : Fin K) (_ : i ≠ j)
    (_ : ∀ᵐ H ∂stateLaw μ K n, (∀ s, ‖H s i i‖ ≤ U) ∧ (∀ s, ‖H s i j‖ ≤ U))
    (m : c.Message), Integrable (fun H ↦ pairEnergy c H i j m) (stateLaw μ K n) :=
  @integrable_pairEnergy

example : ∀ {K n : ℕ} (μ : Measure ℂ) (c : Code K n) {P U : ℝ}
    (_ : PowerAdmissible μ P c) (i j : Fin K) (_ : i ≠ j)
    (_ : ∀ᵐ H ∂stateLaw μ K n, (∀ s, ‖H s i i‖ ≤ U) ∧ (∀ s, ‖H s i j‖ ≤ U)),
    (∫ H, ∫ m, pairEnergy c H i j m ∂messageLaw c ∂stateLaw μ K n) ≤
      2 * U ^ 2 * ((n : ℝ) * P) :=
  @integral_pairEnergy_le

end CapacityAtlas.Gaussian.Interference

namespace CapacityAtlas.Gaussian.MIMOBroadcast

example : ∀ {K tx : ℕ} {rx : Fin K → ℕ} (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    {P : ℝ} (_ : 0 ≤ P),
    capacityRegion (0 : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) N P =
      region (tx := tx) 0 N P :=
  @capacityRegion_eq_region_zero_channel

end CapacityAtlas.Gaussian.MIMOBroadcast

namespace CapacityAtlas.MeasureInformation

example : ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (w : α → ℝ) (_ : ∀ a, 0 ≤ w a)
    (m : α → EuclideanSpace ℝ ι) (N : Matrix ι ι ℝ) (_ : N.PosDef)
    (b b' : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)),
    (∑ i, directionalFisherWith volume (gaussianMixturePDFReal w m N) (b i)) =
      ∑ i, directionalFisherWith volume (gaussianMixturePDFReal w m N) (b' i) :=
  @sum_directionalFisherWith_gaussianMixturePDFReal_basis

end CapacityAtlas.MeasureInformation

namespace CapacityAtlas.Gaussian.MIMOBroadcast

example : ∀ {K tx : ℕ} {rx : Fin K → ℕ}
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ)
    (perm : Equiv.Perm (Fin K)) (k : Fin K), dpcRate 0 N Q perm k = 0 :=
  @dpcRate_zero_channel

example : ∀ {K tx : ℕ} {rx : Fin K → ℕ}
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ) {P : ℝ} (_ : 0 ≤ P),
    rawRegion (0 : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ) N P = {0} :=
  @rawRegion_zero_channel

example : ∀ {K tx : ℕ} {rx : Fin K → ℕ} (H : (i : Fin K) → Matrix (Fin (rx i)) (Fin tx) ℝ)
    (N : (i : Fin K) → Matrix (Fin (rx i)) (Fin (rx i)) ℝ)
    (Q : Fin K → Matrix (Fin tx) (Fin tx) ℝ) (hQ : ∀ i, (Q i).PosDef)
    (perm : Equiv.Perm (Fin K)) (order : ℕ → Fin K)
    (_ : ∀ i j : Fin K, i < j → order j.val < order i.val)
    (n : ℕ) (L : ℕ → ℕ) (T : ℕ → ℝ) (hT : ∀ i, 0 < T i)
    (initial : LayerBlocks K tx n),
    let D := gaussianStages H N Q hQ perm order n L T hT
    sequenceSampleLaw (fun j ↦ (D j).sampleLaw) K
      (sequenceSuccess initial (fun j ↦ (D j).next) (fun j ↦ (D j).success) K)ᶜ ≤
      ∑ i : Fin K, (2 : ℝ≥0∞) ^ i.val *
        (2 * (blockLayerLaw Q perm n)
          {x | ENNReal.ofReal (T i.val) < blockLayerStateLikelihood
            (H (perm (order i.val))) (N (perm (order i.val))) Q perm (order i.val) n x} +
          ENNReal.ofReal (Real.exp (-(L i.val : ℝ) * ((1 / 2 : ℝ) / T i.val)))) :=
  @gaussianStages_failure_le_terminal

end CapacityAtlas.Gaussian.MIMOBroadcast

namespace CapacityAtlas.Gaussian.Interference

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (_ : 0 < L) (_ : 0 ≤ P)
    (_ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U)
    {K n : ℕ} (_ : 0 < n) (c : Code K n) (_ : PowerAdmissible μ P c)
    (i j : Fin K) (_ : i ≠ j),
    (1 - error μ c) * (rates c i + rates c j) ≤
      Real.logb 2 (1 + U ^ 2 * P / converseNoise L U) + 2 / n :=
  @code_pair_rates_bound

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (_ : 0 < L) (_ : 0 ≤ P)
    (_ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U)
    {K : ℕ} {R : Fin K → ℝ} (_ : R ∈ capacityRegion μ K P)
    (i j : Fin K) (_ : i ≠ j),
    R i + R j ≤ Real.logb 2 (1 + U ^ 2 * P / converseNoise L U) :=
  @capacityRegion_pair_bound

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (_ : 0 < L) (_ : 0 ≤ P)
    (_ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U)
    {K : ℕ} (_ : 2 ≤ K) {R : Fin K → ℝ} (_ : R ∈ capacityRegion μ K P),
    (∑ i, R i) ≤ (K : ℝ) / 2 * Real.logb 2 (1 + U ^ 2 * P / converseNoise L U) :=
  @capacityRegion_sum_bound

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (_ : 0 < L) (_ : 0 ≤ P)
    (_ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) {K : ℕ} (_ : 2 ≤ K),
    sumCapacity μ K P ≤
      (K : ℝ) / 2 * Real.logb 2 (1 + U ^ 2 * P / converseNoise L U) :=
  @sumCapacity_converse

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U P : ℝ} (_ : 0 < L) (_ : 0 ≤ P)
    (_ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) {K : ℕ} (_ : 2 ≤ K),
    BddAbove {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i} :=
  @sumRates_bddAbove

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U : ℝ} (_ : 0 < L)
    (_ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) {K : ℕ} (_ : 2 ≤ K) (P : ℝ),
    BddAbove {s | ∃ R ∈ capacityRegion μ K P, s = ∑ i, R i} :=
  @sumRates_bddAbove_all

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ]
    {L U : ℝ} (_ : 0 < L)
    (_ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U) {K : ℕ} (_ : 2 ≤ K),
    Monotone (sumCapacity μ K) :=
  @sumCapacity_monotone

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {K : ℕ} (_ : 2 ≤ K) {L U : ℝ} (_ : 0 < L)
    (_ : ∀ᵐ z ∂μ, L ≤ ‖z‖ ∧ ‖z‖ ≤ U),
    Tendsto (fun P : ℝ ↦ sumCapacity μ K P / Real.logb 2 P)
      atTop (𝓝 ((K : ℝ) / 2)) :=
  @sum_degrees_of_freedom

end CapacityAtlas.Gaussian.Interference

namespace CapacityAtlas.Claims

example (μ : Measure ℂ) [IsProbabilityMeasure μ] {U : ℝ}
    (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ U) : 0 ≤ U := by
  obtain ⟨z, hz⟩ := hμ.exists
  exact (norm_nonneg z).trans hz

example : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {K : ℕ} (_ : 2 ≤ K) {hmin hmax : ℝ} (_ : 0 < hmin)
    (_ : ∀ᵐ h ∂μ, hmin ≤ ‖h‖ ∧ ‖h‖ ≤ hmax),
    Tendsto (fun P : ℝ ↦ Gaussian.Interference.sumCapacity μ K P / Real.logb 2 P)
      atTop (𝓝 ((K : ℝ) / 2)) :=
  @gaussianInterferenceDegreesOfFreedom

end CapacityAtlas.Claims
