/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasForMathlib.InformationTheory.DifferentialEntropy
import CapacityAtlasForMathlib.InformationTheory.MeasureInformation
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal

namespace CapacityAtlas.MeasureInformation

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Only the support of the dominated measure must have positive density. -/
theorem absolutelyContinuous_withDensity_of_ae_ne_zero {μ ν : Measure α} {f : α → ℝ≥0∞}
    (hac : μ ≪ ν) (hf : Measurable f) (hpos : ∀ᵐ x ∂μ, f x ≠ 0) :
    μ ≪ ν.withDensity f := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero ↦ ?_
  rw [withDensity_apply _ hs, lintegral_eq_zero_iff hf, Filter.EventuallyEq,
    ae_restrict_iff' hs] at hzero
  have hnull : ∀ᵐ x ∂μ, x ∉ s := by
    filter_upwards [hac.ae_le hzero, hpos] with x hx hp
    exact fun hxs ↦ hp (hx hxs)
  simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hnull

theorem snd_absolutelyContinuous_of_joint (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (ν : Measure β) [SigmaFinite ν] (hac : ρ ≪ ρ.fst.prod ν) : ρ.snd ≪ ν := by
  simpa [Measure.snd] using hac.map measurable_snd

theorem prod_marginals_eq_withDensity (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (ν : Measure β) [SigmaFinite ν] (hac : ρ ≪ ρ.fst.prod ν) :
    ρ.fst.prod ρ.snd = (ρ.fst.prod ν).withDensity (fun p ↦ ρ.snd.rnDeriv ν p.2) := by
  have hq := snd_absolutelyContinuous_of_joint ρ ν hac
  nth_rw 1 [← Measure.withDensity_rnDeriv_eq ρ.snd ν hq]
  exact prod_withDensity_right (ρ.snd.measurable_rnDeriv ν)

theorem joint_absolutelyContinuous_prod_marginals
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (ν : Measure β) [SigmaFinite ν] (hac : ρ ≪ ρ.fst.prod ν) :
    ρ ≪ ρ.fst.prod ρ.snd := by
  rw [prod_marginals_eq_withDensity ρ ν hac]
  apply absolutelyContinuous_withDensity_of_ae_ne_zero hac (by fun_prop)
  exact (ae_of_ae_map measurable_snd.aemeasurable
    (Measure.rnDeriv_pos (snd_absolutelyContinuous_of_joint ρ ν hac))).mono
      (fun _ h ↦ h.ne')

/-- The product-reference density depends only on the output coordinate. -/
theorem llr_prod_marginals_reference (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (ν : Measure β) [SigmaFinite ν] (hac : ρ ≪ ρ.fst.prod ν) :
    llr (ρ.fst.prod ρ.snd) (ρ.fst.prod ν) =ᵐ[ρ]
      fun p ↦ llr ρ.snd ν p.2 := by
  have hrn := Measure.rnDeriv_withDensity (ρ.fst.prod ν)
    ((ρ.snd.measurable_rnDeriv ν).comp measurable_snd)
  dsimp only [Function.comp_def] at hrn
  rw [← prod_marginals_eq_withDensity ρ ν hac] at hrn
  filter_upwards [hac.ae_le hrn] with p hp
  simp only [llr, hp]

/-- Change the reference law inside the logarithm by the Radon–Nikodym chain rule. -/
theorem llr_sub_of_absolutelyContinuous {μ τ ν : Measure α}
    [SigmaFinite μ] [SigmaFinite τ] [SigmaFinite ν]
    (hμτ : μ ≪ τ) (hτν : τ ≪ ν) :
    llr μ τ =ᵐ[μ] fun x ↦ llr μ ν x - llr τ ν x := by
  have hμν := hμτ.trans hτν
  filter_upwards [hμν.ae_le (Measure.rnDeriv_mul_rnDeriv (κ := ν) hμτ),
    Measure.rnDeriv_pos hμτ, hμτ.ae_le (Measure.rnDeriv_pos hτν),
    hμτ.ae_le (Measure.rnDeriv_lt_top μ τ),
    hμν.ae_le (Measure.rnDeriv_lt_top τ ν)] with x heq hpos₁ hpos₂ hfin₁ hfin₂
  simp only [Pi.mul_apply] at heq
  simp only [llr, ← heq, ENNReal.toReal_mul,
    log_mul (ENNReal.toReal_pos hpos₁.ne' hfin₁.ne).ne'
      (ENNReal.toReal_pos hpos₂.ne' hfin₂.ne).ne']
  ring

theorem llr_mutualInfo_eq_sub (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (ν : Measure β) [SigmaFinite ν] (hac : ρ ≪ ρ.fst.prod ν) :
    llr ρ (ρ.fst.prod ρ.snd) =ᵐ[ρ]
      fun p ↦ llr ρ (ρ.fst.prod ν) p - llr ρ.snd ν p.2 := by
  have hτν : ρ.fst.prod ρ.snd ≪ ρ.fst.prod ν :=
    Measure.AbsolutelyContinuous.rfl.prod (snd_absolutelyContinuous_of_joint ρ ν hac)
  filter_upwards [llr_sub_of_absolutelyContinuous
    (joint_absolutelyContinuous_prod_marginals ρ ν hac) hτν,
    llr_prod_marginals_reference ρ ν hac] with p hp hq
  rw [hp, hq]

theorem mutualInfo_ne_top_of_integrable_log_density
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (ν : Measure β) [SigmaFinite ν] (hac : ρ ≪ ρ.fst.prod ν)
    (hjoint : Integrable (llr ρ (ρ.fst.prod ν)) ρ)
    (hout : Integrable (llr ρ.snd ν) ρ.snd) : mutualInfo ρ ≠ ⊤ := by
  have hpull : Integrable (fun p : α × β ↦ llr ρ.snd ν p.2) ρ :=
    (integrable_map_measure hout.aestronglyMeasurable measurable_snd.aemeasurable).mp hout
  apply klDiv_ne_top_iff.mpr
  exact ⟨joint_absolutelyContinuous_prod_marginals ρ ν hac,
    (hjoint.sub hpull).congr (llr_mutualInfo_eq_sub ρ ν hac).symm⟩

/-- Mutual information is the output entropy minus the joint conditional-reference entropy. -/
theorem mutualInfo_eq_entropy_sub_joint
    (ρ : Measure (α × β)) [IsProbabilityMeasure ρ]
    (ν : Measure β) [SigmaFinite ν] (hac : ρ ≪ ρ.fst.prod ν)
    (hjoint : Integrable (llr ρ (ρ.fst.prod ν)) ρ)
    (hout : Integrable (llr ρ.snd ν) ρ.snd) :
    (mutualInfo ρ).toReal = entropyWith ρ.snd ν - entropyWith ρ (ρ.fst.prod ν) := by
  have hpull : Integrable (fun p : α × β ↦ llr ρ.snd ν p.2) ρ :=
    (integrable_map_measure hout.aestronglyMeasurable measurable_snd.aemeasurable).mp hout
  have hfinite := mutualInfo_ne_top_of_integrable_log_density ρ ν hac hjoint hout
  have hspec := klDiv_ne_top_iff.mp hfinite
  rw [mutualInfo, toReal_klDiv hspec.1 hspec.2]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae (llr_mutualInfo_eq_sub ρ ν hac), integral_sub hjoint hpull]
  have hmap : (∫ p : α × β, llr ρ.snd ν p.2 ∂ρ) = ∫ y, llr ρ.snd ν y ∂ρ.snd :=
    (integral_map measurable_snd.aemeasurable hout.aestronglyMeasurable).symm
  rw [hmap]
  simp only [entropyWith]
  ring

section KernelDensity

variable (μ : Measure α) [IsProbabilityMeasure μ]
  (κ : Kernel α β) [IsMarkovKernel κ] (ν : Measure β) [SigmaFinite ν]
  {f : α × β → ℝ≥0∞}

/-- A measurable family of row densities is also the density of the joint law. -/
theorem compProd_eq_withDensity_of_rows (hf : Measurable f)
    (hrows : ∀ a, κ a = ν.withDensity (fun b ↦ f (a, b))) :
    μ ⊗ₘ κ = (μ.prod ν).withDensity f := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_prod _ (hf.indicator hs).aemeasurable]
  apply lintegral_congr
  intro a
  rw [hrows a, withDensity_apply _ (measurable_prodMk_left hs),
    ← lintegral_indicator (measurable_prodMk_left hs)]
  rfl

theorem llr_eq_log_density {δ : Type*} [MeasurableSpace δ]
    (law reference : Measure δ) [SigmaFinite reference] {density : δ → ℝ≥0∞}
    (hdensity : Measurable density) (hlaw : law = reference.withDensity density) :
    llr law reference =ᵐ[law] fun x ↦ log (density x).toReal := by
  have hac : law ≪ reference := by
    rw [hlaw]
    exact withDensity_absolutelyContinuous _ _
  have hrn : law.rnDeriv reference =ᵐ[reference] density := by
    rw [hlaw]
    exact Measure.rnDeriv_withDensity _ hdensity
  filter_upwards [hac.ae_le hrn] with x hx
  simp only [llr, hx]

theorem entropyWith_compProd_eq_integral (hf : Measurable f)
    (hrows : ∀ a, κ a = ν.withDensity (fun b ↦ f (a, b)))
    (hlog : Integrable (fun p ↦ log (f p).toReal) (μ ⊗ₘ κ)) :
    entropyWith (μ ⊗ₘ κ) (μ.prod ν) = ∫ a, entropyWith (κ a) ν ∂μ := by
  have hllr := llr_eq_log_density (μ ⊗ₘ κ) (μ.prod ν) hf
    (compProd_eq_withDensity_of_rows μ κ ν hf hrows)
  calc
    entropyWith (μ ⊗ₘ κ) (μ.prod ν) = -∫ p, log (f p).toReal ∂(μ ⊗ₘ κ) := by
      rw [entropyWith, integral_congr_ae hllr]
    _ = ∫ a, -(∫ b, log (f (a, b)).toReal ∂κ a) ∂μ := by
      rw [Measure.integral_compProd hlog, integral_neg]
    _ = ∫ a, entropyWith (κ a) ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with a
      rw [entropyWith, integral_congr_ae
        (llr_eq_log_density (κ a) ν (hf.comp measurable_prodMk_left) (hrows a))]
      rfl

theorem mutualInfo_compProd_ne_top (hf : Measurable f)
    (hrows : ∀ a, κ a = ν.withDensity (fun b ↦ f (a, b)))
    (hlog : Integrable (fun p ↦ log (f p).toReal) (μ ⊗ₘ κ))
    (hout : Integrable (llr (κ ∘ₘ μ) ν) (κ ∘ₘ μ)) : mutualInfo (μ ⊗ₘ κ) ≠ ⊤ := by
  have hac : μ ⊗ₘ κ ≪ μ.prod ν := by
    rw [compProd_eq_withDensity_of_rows μ κ ν hf hrows]
    exact withDensity_absolutelyContinuous _ _
  have hjoint : Integrable (llr (μ ⊗ₘ κ) (μ.prod ν)) (μ ⊗ₘ κ) :=
    hlog.congr (llr_eq_log_density (μ ⊗ₘ κ) (μ.prod ν) hf
      (compProd_eq_withDensity_of_rows μ κ ν hf hrows)).symm
  apply mutualInfo_ne_top_of_integrable_log_density (μ ⊗ₘ κ) ν
  · simpa only [Measure.fst_compProd] using hac
  · simpa only [Measure.fst_compProd] using hjoint
  · simpa only [Measure.snd_compProd] using hout

/-- The differential-entropy identity follows from densities and their integrability. -/
theorem mutualInfo_compProd_eq_entropy_sub_integral (hf : Measurable f)
    (hrows : ∀ a, κ a = ν.withDensity (fun b ↦ f (a, b)))
    (hlog : Integrable (fun p ↦ log (f p).toReal) (μ ⊗ₘ κ))
    (hout : Integrable (llr (κ ∘ₘ μ) ν) (κ ∘ₘ μ)) :
    (mutualInfo (μ ⊗ₘ κ)).toReal =
      entropyWith (κ ∘ₘ μ) ν - ∫ a, entropyWith (κ a) ν ∂μ := by
  have hac : μ ⊗ₘ κ ≪ μ.prod ν := by
    rw [compProd_eq_withDensity_of_rows μ κ ν hf hrows]
    exact withDensity_absolutelyContinuous _ _
  have hjoint : Integrable (llr (μ ⊗ₘ κ) (μ.prod ν)) (μ ⊗ₘ κ) :=
    hlog.congr (llr_eq_log_density (μ ⊗ₘ κ) (μ.prod ν) hf
      (compProd_eq_withDensity_of_rows μ κ ν hf hrows)).symm
  have h := mutualInfo_eq_entropy_sub_joint (μ ⊗ₘ κ) ν
    (by simpa only [Measure.fst_compProd] using hac)
    (by simpa only [Measure.fst_compProd] using hjoint)
    (by simpa only [Measure.snd_compProd] using hout)
  simpa only [Measure.fst_compProd, Measure.snd_compProd,
    entropyWith_compProd_eq_integral μ κ ν hf hrows hlog] using h

end KernelDensity

end CapacityAtlas.MeasureInformation
