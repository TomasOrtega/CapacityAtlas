/-
Adapted from the PFR project, licensed under Apache-2.0.
See LICENSES/PFR-Apache-2.0.txt.
Source: https://github.com/teorth/pfr/blob/85d5879ae144170098815201491639f6e7d3c352/PFR/ForMathlib/Entropy/Kernel/MutualInfo.lean
Adaptations: retained the declarations needed by finite entropy and changed local imports.
-/

import Mathlib.Probability.Kernel.Composition.Comp
import CapacityAtlasForMathlib.Probability.Kernel.Disintegration
import CapacityAtlasForMathlib.InformationTheory.Entropy.Kernel

open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {S T U : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

/-- Mutual information of a kernel into a product space with respect to a measure. -/
noncomputable
def mutualInfo (κ : Kernel T (S × U)) (μ : Measure T) : ℝ :=
  Hk[fst κ, μ] + Hk[snd κ, μ] - Hk[κ, μ]

notation3:100 "Ik[" κ " , " μ "]" => ProbabilityTheory.Kernel.mutualInfo κ μ

lemma mutualInfo_congr {κ η : Kernel T (S × U)} {μ : Measure T} (h : κ =ᵐ[μ] η) :
    Ik[κ, μ] = Ik[η, μ] := by
  rw [mutualInfo, mutualInfo]
  have h1 : fst κ =ᵐ[μ] fst η := by
    filter_upwards [h] with t ht
    rw [fst_apply, ht, fst_apply]
  have h2 : snd κ =ᵐ[μ] snd η := by
    filter_upwards [h] with t ht
    rw [snd_apply, ht, snd_apply]
  rw [entropy_congr h1, entropy_congr h2, entropy_congr h]

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass U]

variable [MeasurableSingletonClass T]

lemma mutualInfo_nonneg' {κ : Kernel T (S × U)} {μ : Measure T} [IsFiniteMeasure μ]
    [FiniteSupport μ] (hκ : FiniteKernelSupport κ) :
    0 ≤ Ik[κ, μ] := by
  simp_rw [mutualInfo, entropy, integral_eq_setIntegral (ae_mem_support μ),
    setIntegral_finset _ .finset, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  simp_rw [← mul_add, ← mul_sub, fst_apply, snd_apply]
  have (x : T) : FiniteSupport (κ x) := ⟨hκ x⟩
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg measureMutualInfo_nonneg

lemma mutualInfo_nonneg [Countable T] {κ : Kernel T (S × U)} {μ : Measure T} [IsFiniteMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    0 ≤ Ik[κ, μ] := by
  rw [mutualInfo_congr hκ.ae_eq_mk]
  exact mutualInfo_nonneg' hκ.finiteKernelSupport_mk

variable [Countable S] [Countable T]

variable [Countable U]

lemma mutualInfo_eq_snd_sub [Nonempty U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Ik[κ, μ] = Hk[snd κ, μ] - Hk[condKernel κ, μ ⊗ₘ (fst κ)] := by
  rw [mutualInfo, chain_rule hκ]
  ring

lemma entropy_condKernel_le_entropy_snd [Nonempty U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[condKernel κ, μ ⊗ₘ (fst κ)] ≤ Hk[snd κ, μ] := by
  rw [← sub_nonneg, ← mutualInfo_eq_snd_sub hκ]
  exact mutualInfo_nonneg hκ

end

end ProbabilityTheory.Kernel
