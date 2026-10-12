/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.GaussianDirtyPaper.InformationDensity
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomCoding.Tensor
import CapacityAtlasForMathlib.InformationTheory.MeasureRandomBinning.IID

open MeasureTheory ProbabilityTheory Matrix Real Filter CapacityAtlas.MeasureChannel
  CapacityAtlas.MeasureInformation
open scoped BigOperators ENNReal Topology

namespace CapacityAtlas.Gaussian.DirtyPaper

variable {ι ο : Type*} [Fintype ι] [Fintype ο] [DecidableEq ι] [DecidableEq ο]

noncomputable def stateChannel (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) :
    Kernel (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (EuclideanSpace ℝ ο) :=
  (gaussianChannel H N).comap (fun p ↦ p.2 + p.1) (by fun_prop)

instance stateChannel_isMarkovKernel (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) :
    IsMarkovKernel (stateChannel H N) := by unfold stateChannel; infer_instance

theorem stateChannel_apply (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    stateChannel H N p = multivariateGaussian (H.toEuclideanLin (p.2 + p.1)) N := by
  rw [stateChannel, Kernel.comap_apply, gaussianChannel_apply]

@[fun_prop]
theorem measurable_encoderInput (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ) (N : Matrix ο ο ℝ) :
    Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      encoderInput H Q N p.1 p.2) := by unfold encoderInput; fun_prop

theorem stateChannel_comap_encoderInput (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) :
    (stateChannel H N).comap (fun p ↦ (p.1, encoderInput H Q N p.1 p.2))
      (measurable_fst.prodMk (measurable_encoderInput H Q N)) = physicalKernel H Q N := by
  ext p A
  rfl

noncomputable def blockStateLaw (S : Matrix ι ι ℝ) (n : ℕ) :
    Measure (Fin n → EuclideanSpace ℝ ι) :=
  Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 S)

instance blockStateLaw_isProbabilityMeasure (S : Matrix ι ι ℝ) (n : ℕ) :
    IsProbabilityMeasure (blockStateLaw S n) := by unfold blockStateLaw; infer_instance

noncomputable def blockAuxiliaryLaw (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) : Measure (Fin n → EuclideanSpace ℝ ι) :=
  Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 (auxiliaryCovariance H Q S N))

instance blockAuxiliaryLaw_isProbabilityMeasure (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) : IsProbabilityMeasure (blockAuxiliaryLaw H Q S N n) := by
  unfold blockAuxiliaryLaw
  infer_instance

noncomputable def blockStateKernel (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) := iidKernel (gaussianChannel (costaCoefficient H Q N * H) Q) n

instance blockStateKernel_isMarkovKernel (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) : IsMarkovKernel (blockStateKernel H Q N n) := by
  unfold blockStateKernel
  infer_instance

noncomputable def blockReverseKernel (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) :=
  iidKernel (gaussianChannel (costaCoefficient H Q N) (residualCovariance H Q N)) n

instance blockReverseKernel_isMarkovKernel (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) : IsMarkovKernel (blockReverseKernel H Q N n) := by
  unfold blockReverseKernel
  infer_instance

noncomputable def blockChannel (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (n : ℕ) :
    Kernel ((Fin n → EuclideanSpace ℝ ι) × (Fin n → EuclideanSpace ℝ ι))
      (Fin n → EuclideanSpace ℝ ο) :=
  (iidKernel (stateChannel H N) n).comap (pairBlock n) (measurable_pairBlock n)

instance blockChannel_isMarkovKernel (H : Matrix ο ι ℝ) (N : Matrix ο ο ℝ) (n : ℕ) :
    IsMarkovKernel (blockChannel H N n) := by unfold blockChannel; infer_instance

noncomputable def blockEncoderInput (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ)
    (p : (Fin n → EuclideanSpace ℝ ι) × (Fin n → EuclideanSpace ℝ ι)) :
    Fin n → EuclideanSpace ℝ ι := fun i ↦ encoderInput H Q N (p.1 i) (p.2 i)

@[fun_prop]
theorem measurable_blockEncoderInput (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) : Measurable (blockEncoderInput H Q N n) := by
  unfold blockEncoderInput encoderInput
  fun_prop

noncomputable def blockStateLikelihood (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) :=
  iidLikelihood (fun p ↦ stateInformationDensity H Q S N p.1 p.2) n

noncomputable def blockObservationLikelihood (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) :=
  iidLikelihood (fun p ↦ observationInformationDensity H Q S N p.2 p.1) n

@[fun_prop]
theorem measurable_blockStateLikelihood (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) : Measurable (blockStateLikelihood H Q S N n) :=
  measurable_iidLikelihood (measurable_stateInformationDensity H Q S N) n

@[fun_prop]
theorem measurable_blockObservationLikelihood (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) : Measurable (blockObservationLikelihood H Q S N n) :=
  measurable_iidLikelihood
    ((measurable_observationInformationDensity H Q S N).comp measurable_swap) n

theorem blockStateKernel_output (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosSemidef) (hS : S.PosSemidef) (n : ℕ) :
    blockStateKernel H Q N n ∘ₘ blockStateLaw S n = blockAuxiliaryLaw H Q S N n := by
  rw [blockStateKernel, blockStateLaw, iidKernel_output,
    state_channel_output_eq_auxiliary, sourceLaw_map_auxiliary H Q S N hQ hS]
  rfl

theorem blockStateKernel_withDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef)
    (n : ℕ) (s : Fin n → EuclideanSpace ℝ ι) :
    blockStateKernel H Q N n s = (blockAuxiliaryLaw H Q S N n).withDensity
      (fun u ↦ blockStateLikelihood H Q S N n (s, u)) := by
  have hrow (s : EuclideanSpace ℝ ι) :
      gaussianChannel (costaCoefficient H Q N * H) Q s =
        (gaussianChannel (costaCoefficient H Q N * H) Q ∘ₘ multivariateGaussian 0 S).withDensity
          (fun u ↦ ENNReal.ofReal (exp (stateInformationDensity H Q S N s u))) := by
    rw [state_channel_output_eq_auxiliary, sourceLaw_map_auxiliary H Q S N hQ.posSemidef hS]
    exact stateKernel_eq_withDensity H Q S N hQ hS s
  have h := iidKernel_likelihood _ (multivariateGaussian 0 S)
    (measurable_stateInformationDensity H Q S N) hrow n s
  change blockStateKernel H Q N n s =
    (blockStateKernel H Q N n ∘ₘ blockStateLaw S n).withDensity _ at h
  rw [blockStateKernel_output H Q S N hQ.posSemidef hS] at h
  exact h

theorem blockStateKernel_joint (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) :
    (blockStateLaw S n ⊗ₘ blockStateKernel H Q N n).map (pairBlock n) =
      Measure.pi (fun _ : Fin n ↦
        multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q) :=
  iidKernel_joint _ _ n

theorem blockReverseKernel_withDensity (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef)
    (n : ℕ) (y : Fin n → EuclideanSpace ℝ ο) :
    blockReverseKernel H Q N n y = (blockAuxiliaryLaw H Q S N n).withDensity
      (fun u ↦ blockObservationLikelihood H Q S N n (u, y)) := by
  have hrow (y : EuclideanSpace ℝ ο) :
      gaussianChannel (costaCoefficient H Q N) (residualCovariance H Q N) y =
        (gaussianChannel (costaCoefficient H Q N) (residualCovariance H Q N) ∘ₘ
          (sourceLaw Q S N).map (observation H)).withDensity
            (fun u ↦ ENNReal.ofReal (exp (observationInformationDensity H Q S N y u))) := by
    rw [regression_output_eq_auxiliary H Q S N hQ.posSemidef hN,
      sourceLaw_map_auxiliary H Q S N hQ.posSemidef hS]
    exact observationKernel_eq_withDensity H Q S N hQ hS hN y
  have h := iidKernel_likelihood _ ((sourceLaw Q S N).map (observation H))
    (measurable_observationInformationDensity H Q S N) hrow n y
  rw [iidKernel_output, regression_output_eq_auxiliary H Q S N hQ.posSemidef hN,
    sourceLaw_map_auxiliary H Q S N hQ.posSemidef hS] at h
  exact h

theorem blockChannel_comap_encoderInput (H : Matrix ο ι ℝ) (Q : Matrix ι ι ℝ)
    (N : Matrix ο ο ℝ) (n : ℕ) :
    (blockChannel H N n).comap (fun p ↦ (p.1, blockEncoderInput H Q N n p))
      (measurable_fst.prodMk (measurable_blockEncoderInput H Q N n)) =
        (iidKernel (physicalKernel H Q N) n).comap (pairBlock n) (measurable_pairBlock n) := by
  ext p A
  rfl

noncomputable def blockEnergy (n : ℕ) (x : Fin n → EuclideanSpace ℝ ι) : ℝ :=
  iidSum (fun v ↦ ‖v‖ ^ 2) n x

omit [DecidableEq ι] in
@[fun_prop]
theorem measurable_blockEnergy (n : ℕ) : Measurable (blockEnergy (ι := ι) n) := by
  unfold blockEnergy iidSum
  fun_prop

def blockAllowed (P : ℝ) (n : ℕ) :
    Set ((Fin n → EuclideanSpace ℝ ι) × (Fin n → EuclideanSpace ℝ ι)) :=
  {p | blockEnergy n p.2 ≤ (n : ℝ) * P}

omit [DecidableEq ι] in
theorem measurableSet_blockAllowed (P : ℝ) (n : ℕ) :
    MeasurableSet (blockAllowed (ι := ι) P n) :=
  measurableSet_le ((measurable_blockEnergy n).comp measurable_snd) measurable_const

omit [DecidableEq ι] in
theorem zero_mem_blockAllowed {P : ℝ} (hP : 0 ≤ P) (n : ℕ)
    (s : Fin n → EuclideanSpace ℝ ι) : (s, 0) ∈ blockAllowed P n := by
  simp only [blockAllowed, Set.mem_setOf_eq, blockEnergy, iidSum, Pi.zero_apply,
    norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
  positivity

theorem blockStateLikelihood_upperTail_tendsto_zero
    (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosDef) (hS : S.PosSemidef) {a : ℝ}
    (ha : (mutualInfoRV (auxiliary H Q N) Prod.snd (sourceLaw Q S N)).toReal < a) :
    Tendsto (fun n ↦ (blockStateLaw S n ⊗ₘ blockStateKernel H Q N n)
      {z | ENNReal.ofReal (exp ((n : ℝ) * a)) < blockStateLikelihood H Q S N n z})
      atTop (𝓝 0) := by
  let ν := multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q
  let info := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
    stateInformationDensity H Q S N p.1 p.2
  have hinfo := measurable_stateInformationDensity H Q S N
  have hmean : (∫ z, info z ∂ν) < a := by
    simpa only [info, ν, integral_stateInformationDensity_joint H Q S N hQ hS] using ha
  have heq (n : ℕ) : (blockStateLaw S n ⊗ₘ blockStateKernel H Q N n)
      {z | ENNReal.ofReal (exp ((n : ℝ) * a)) < blockStateLikelihood H Q S N n z} =
      (Measure.pi (fun _ : Fin n ↦ ν)) {z | (n : ℝ) * a < iidSum info n z} := by
    have hs : Measurable (iidSum info n) :=
      Finset.measurable_sum _ (fun i _ ↦ hinfo.comp (measurable_pi_apply i))
    rw [← blockStateKernel_joint H Q S N n, Measure.map_apply (measurable_pairBlock n)
      (measurableSet_lt measurable_const hs)]
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, blockStateLikelihood, iidLikelihood,
      ENNReal.ofReal_lt_ofReal_iff (exp_pos _), exp_lt_exp]
    rfl
  simp_rw [heq]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (iidSum_upperTail_tendsto_zero ν (memLp_two_stateInformationDensity_joint H Q S N hQ hS)
      hmean) (fun _ ↦ zero_le)
  intro n
  apply measure_mono
  intro z hz
  exact (show (n : ℝ) * a < iidSum info n z from hz).le

theorem blockCost_rejection_tendsto_zero
    (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosSemidef) {P : ℝ} (hP : Q.trace < P) :
    Tendsto (fun n ↦ (blockStateLaw S n ⊗ₘ blockStateKernel H Q N n)
      {z | (z.1, blockEncoderInput H Q N n z) ∉ blockAllowed P n}) atTop (𝓝 0) := by
  let ν := multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q
  let cost := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ inputCost H Q N p.1 p.2
  have hcost := measurable_inputCost H Q N
  have hmean : (∫ z, cost z ∂ν) < P := by
    simpa only [cost, ν, integral_inputCost_joint H Q S N hQ] using hP
  have heq (n : ℕ) : (blockStateLaw S n ⊗ₘ blockStateKernel H Q N n)
      {z | (z.1, blockEncoderInput H Q N n z) ∉ blockAllowed P n} =
      (Measure.pi (fun _ : Fin n ↦ ν)) {z | iidSum cost n z ≤ (n : ℝ) * P}ᶜ := by
    have hs : Measurable (iidSum cost n) :=
      Finset.measurable_sum _ (fun i _ ↦ hcost.comp (measurable_pi_apply i))
    rw [← blockStateKernel_joint H Q S N n, Measure.map_apply (measurable_pairBlock n)
      (measurableSet_le hs measurable_const).compl]
    rfl
  simp_rw [heq]
  exact iidCost_rejection_tendsto_zero ν (memLp_two_inputCost_joint H Q S N) hmean

theorem iidObservationLikelihood_lowerTail_tendsto_zero
    (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) {d : ℝ}
    (hd : d < (mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N)).toReal) :
    Tendsto (fun n ↦ (Measure.pi (fun _ : Fin n ↦
      (multivariateGaussian 0 S ⊗ₘ gaussianChannel (costaCoefficient H Q N * H) Q) ⊗ₘ
        physicalKernel H Q N))
      {z | ENNReal.ofReal (exp (iidSum
        (fun p ↦ observationInformationDensity H Q S N p.2 p.1.2) n z)) ≤
          ENNReal.ofReal (exp ((n : ℝ) * d))}) atTop (𝓝 0) := by
  apply iidLikelihood_lowerTail_tendsto_zero _
    (memLp_two_observationInformationDensity_physical H Q S N hQ hS hN)
  simpa only [integral_observationInformationDensity_physical H Q S N hQ hS hN] using hd

theorem blockConditionalMiss_tendsto_zero
    (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef) {d : ℝ}
    (hd : d < (mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N)).toReal) :
    Tendsto (fun n ↦ ∫⁻ z, MeasureBinning.conditionalMiss (blockChannel H N n)
      (blockEncoderInput H Q N n)
      {p | ENNReal.ofReal (exp ((n : ℝ) * d)) < blockObservationLikelihood H Q S N n p} z
      ∂(blockStateLaw S n ⊗ₘ blockStateKernel H Q N n)) atTop (𝓝 0) := by
  have hK : MeasureBinning.auxiliaryChannel (stateChannel H N)
      (fun p ↦ encoderInput H Q N p.1 p.2) (measurable_encoderInput H Q N) =
        physicalKernel H Q N := stateChannel_comap_encoderInput H Q N
  apply MeasureBinning.iid_conditionalMiss_tendsto_zero (stateChannel H N)
    (multivariateGaussian 0 S) (gaussianChannel (costaCoefficient H Q N * H) Q)
    (fun p ↦ encoderInput H Q N p.1 p.2) (measurable_encoderInput H Q N)
    ((measurable_observationInformationDensity H Q S N).comp measurable_swap)
  · rw [hK]
    exact memLp_two_observationInformationDensity_physical H Q S N hQ hS hN
  · rw [hK]
    simp only [Function.comp_def, Prod.swap_prod_mk]
    rw [integral_observationInformationDensity_physical H Q S N hQ hS hN]
    exact hd

/-- Deterministic Costa codes with a power bound for every message and state. -/
theorem exists_stateCodes
    (H : Matrix ο ι ℝ) (Q S : Matrix ι ι ℝ) (N : Matrix ο ο ℝ)
    (hQ : Q.PosDef) (hS : S.PosSemidef) (hN : N.PosDef)
    {P R : ℝ} (hP : Q.trace < P) (hR : 0 ≤ R)
    (hRate : R * log 2 < (log (outputCovariance H Q N).det - log N.det) / 2) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n, n₀ ≤ n →
      ∃ code : MeasureBinning.StateCode (Fin n → EuclideanSpace ℝ ι)
          (Fin n → EuclideanSpace ℝ ι) (Fin n → EuclideanSpace ℝ ο)
          (Fin (FiniteChannel.messageCountAtRate R n)),
        (∀ m s, blockEnergy n (code.encode m s) ≤ (n : ℝ) * P) ∧
          (MeasureBinning.stateAverageError (blockChannel H N n) (blockStateLaw S n) code).toReal ≤ ε ∧
          R ≤ logb 2 (FiniteChannel.messageCountAtRate R n : ℝ) / n := by
  let Is := (mutualInfoRV (auxiliary H Q N) Prod.snd (sourceLaw Q S N)).toReal
  let Iy := (mutualInfoRV (auxiliary H Q N) (observation H) (sourceLaw Q S N)).toReal
  have hgap : R * log 2 < Iy - Is := by
    simpa only [Iy, Is, costa_information_difference H Q S N hQ hS hN] using hRate
  let δ := (Iy - Is - R * log 2) / 4
  have hδ : 0 < δ := by unfold δ; linarith
  have hIs : 0 ≤ Is := ENNReal.toReal_nonneg
  have hP₀ : 0 ≤ P := hQ.posSemidef.trace_nonneg.trans hP.le
  exact MeasureBinning.exists_stateCodes_of_tails_tendsto_zero
    (blockChannel H N) (blockStateLaw S) (blockStateKernel H Q N) (blockAuxiliaryLaw H Q S N)
    (blockStateLikelihood H Q S N) (measurable_blockStateLikelihood H Q S N)
    (blockStateKernel_withDensity H Q S N hQ hS)
    (blockReverseKernel H Q N) (blockObservationLikelihood H Q S N)
    (measurable_blockObservationLikelihood H Q S N)
    (blockReverseKernel_withDensity H Q S N hQ hS hN)
    (blockEncoderInput H Q N) (measurable_blockEncoderInput H Q N)
    (fun _ _ ↦ 0) (fun _ ↦ measurable_const)
    (blockAllowed P) (measurableSet_blockAllowed P) (zero_mem_blockAllowed hP₀)
    (a := Is + δ) (b := Is + 2 * δ) (d := Iy - δ)
    hR (by positivity) (by linarith) (by dsimp [δ]; linarith)
    (blockStateLikelihood_upperTail_tendsto_zero H Q S N hQ hS (by change Is < Is + δ; linarith))
    (blockCost_rejection_tendsto_zero H Q S N hQ.posSemidef hP)
    (blockConditionalMiss_tendsto_zero H Q S N hQ hS hN (by change Iy - δ < Iy; linarith))

end CapacityAtlas.Gaussian.DirtyPaper
