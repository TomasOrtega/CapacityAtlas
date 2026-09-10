/-
Adapted from the PFR project, licensed under Apache-2.0.
See LICENSES/PFR-Apache-2.0.txt.
Source: https://github.com/teorth/pfr/blob/85d5879ae144170098815201491639f6e7d3c352/PFR/ForMathlib/Entropy/Kernel/Basic.lean
Adaptations: retained the declarations needed by finite entropy, changed local imports,
and reused mathlib integration and kernel composition lemmas.
-/

import Mathlib.MeasureTheory.Integral.Prod
import CapacityAtlasForMathlib.MeasureTheory.Integral.Discrete
import CapacityAtlasForMathlib.InformationTheory.Entropy.Measure
import CapacityAtlasForMathlib.Probability.Kernel.Disintegration

open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

/-- Entropy of a kernel with respect to a measure. -/
noncomputable
def entropy (κ : Kernel T S) (μ : Measure T) := μ[fun y ↦ Hm[κ y]]

notation3:100 "Hk[" κ " , " μ "]" => ProbabilityTheory.Kernel.entropy κ μ

@[simp]
lemma entropy_zero_measure (κ : Kernel T S) : Hk[κ, (0 : Measure T)] = 0 := by simp [entropy]

@[simp]
lemma entropy_zero_kernel (μ : Measure T) : Hk[(0 : Kernel T S), μ] = 0 := by simp [entropy]

lemma entropy_congr {μ} {κ η : Kernel T S} (h : κ =ᵐ[μ] η) : Hk[κ, μ] = Hk[η, μ] := by
  simp_rw [entropy]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

@[simp]
lemma entropy_const (ν : Measure S) (μ : Measure T) :
    Hk[Kernel.const T ν, μ] = (μ Set.univ).toReal * Hm[ν] := by
  simp [entropy, Measure.real]

/-- Constant kernels with finite support, have finite kernel support. -/
lemma finiteKernelSupport_of_const (ν : Measure S) [FiniteSupport ν] :
    FiniteKernelSupport (Kernel.const T ν) := by
  intro t
  use ν.support
  simp [measure_compl_support ν]

/-- Composing a finitely supported measure with a finitely supported kernel gives a finitely
supported kernel. -/
lemma finiteSupport_of_compProd' [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    {μ : Measure T} [IsFiniteMeasure μ] {κ : Kernel T S}
    [IsZeroOrMarkovKernel κ] [FiniteSupport μ] (hκ : FiniteKernelSupport κ) :
    FiniteSupport (μ ⊗ₘ κ) := by
  let A := μ.support
  have hA := measure_compl_support μ
  rcases (local_support_of_finiteKernelSupport hκ A) with ⟨B, hB⟩
  use A ×ˢ B
  rw [Measure.ae_compProd_iff (by exact (Finset.finite_toSet _).measurableSet)]
  filter_upwards [ae_mem_support μ] with t ht
  filter_upwards [hB t ht] with s hs
  exact Finset.mk_mem_product ht hs

lemma aefiniteKernelSupport_condDistrib
    [Nonempty S] [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] :
    AEFiniteKernelSupport (condDistrib X Y μ) (μ.map Y) := by
  filter_upwards [condDistrib_ae_eq hX hY μ] with a ha
  rw [ha]
  exact finiteSupport_of_finiteRange.finite

lemma entropy_comap_equiv [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : Kernel T S) {μ : Measure T} (f : T' ≃ᵐ T)
    [IsFiniteMeasure μ] [FiniteSupport μ] :
    Hk[comap κ f f.measurable, μ.comap f] = Hk[κ, μ] := by
  simp only [entropy, ← MeasurableEquiv.map_symm, integral_map_equiv,
    coe_comap, Function.comp_apply, MeasurableEquiv.apply_symm_apply]

lemma entropy_comap_swap [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [MeasurableSingletonClass T']
    (κ : Kernel (T' × T) S) {μ : Measure (T' × T)} [IsFiniteMeasure μ] [FiniteSupport μ] :
    Hk[comap κ Prod.swap measurable_swap, μ.comap Prod.swap] = Hk[κ, μ] :=
  entropy_comap_equiv κ MeasurableEquiv.prodComm

lemma entropy_prodMkLeft_unit [MeasurableSingletonClass T]
    (κ : Kernel T S) {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ] :
    Hk[prodMkLeft Unit κ, μ.map (Prod.mk ())] = Hk[κ, μ] := by
  convert entropy_comap_equiv κ (.punitProd) (μ := μ)
  · rfl
  rw [← MeasurableEquiv.map_symm]
  congr

lemma entropy_compProd_aux [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] {μ} [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ] (hκ : FiniteKernelSupport κ)
    (hη : FiniteKernelSupport η) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ]
      + μ[fun t ↦ Hk[comap η (Prod.mk t) measurable_prodMk_left, (κ t)]] := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  let A := μ.support
  have hsum (F : T → ℝ) : ∫ (t : T), F t ∂μ = ∑ t ∈ A, (μ.real {t}) * (F t) := by
    rw [integral_eq_setIntegral (ae_mem_support μ), setIntegral_finset _ .finset]
    congr with t ht
  simp_rw [entropy, hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← mul_add]
  congr
  obtain ⟨B, hB⟩ := local_support_of_finiteKernelSupport hκ A
  obtain ⟨C, hC⟩ := local_support_of_finiteKernelSupport hη (A ×ˢ B)
  rw [integral_eq_setIntegral (hB t ht)]
  have hκη : ((κ ⊗ₖ η) t) (B ×ˢ C : Finset (S × U))ᶜ = 0 := by
    rw [Kernel.compProd_apply (Finset.measurableSet _).compl,
      lintegral_eq_setLIntegral (ae_iff.1 <| hB t ht), setLIntegral_eq_sum]
    apply Finset.sum_eq_zero
    intro s hs
    simpa using .inr <| measure_mono_null (by simp [*]) (hC (t, s) <| by simp [ht, hs])
  rw [measureEntropy_eq_sum hκη, measureEntropy_eq_sum (hB t ht),
    setIntegral_finset _ .finset,
    ← Finset.sum_add_distrib, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [measure_univ, inv_one, one_smul, coe_comap, Function.comp_apply, smul_eq_mul]
  have hts : (t, s) ∈ A ×ˢ B := by simp [ht, hs]
  rw [measureEntropy_eq_sum (hC (t, s) hts)]
  simp only [measure_univ, inv_one, one_smul]
  have : negMulLog ((κ t).real {s}) = ∑ u ∈ C, negMulLog ((κ t).real {s}) *
      ((comap η (Prod.mk t) measurable_prodMk_left) s).real {u} := by
    rw [← Finset.mul_sum]
    simp only [coe_comap, Function.comp_apply, sum_measureReal_singleton]
    suffices (η (t, s)).real ↑C = (η (t, s)).real Set.univ by simp [this]
    have := hC (t, s) hts
    rw [ae_iff, ← measureReal_eq_zero_iff] at this
    change (η (t, s)).real Cᶜ = 0 at this
    rw [← measureReal_add_measureReal_compl (s := C) _, this, add_zero]
    exact Finset.measurableSet C
  rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr with u
  have : ((κ ⊗ₖ η) t).real {(s, u)} = (κ t).real {s} * (η (t, s)).real {u} := by
    rw [measureReal_def, ← Set.singleton_prod_singleton,
      compProd_apply_prod (.singleton _) (.singleton _)]
    simp [ENNReal.toReal_mul, measureReal_def]
  rw [this, Kernel.comap_apply, negMulLog_mul, negMulLog, negMulLog]
  ring

lemma entropy_compProd' [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass T]
    [Countable T] [MeasurableSingletonClass U] {μ}
    [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[η, μ ⊗ₘ κ] := by
  rw [entropy_compProd_aux hκ hη]
  congr
  rw [entropy, Measure.integral_compProd]
  · simp_rw [entropy]
    congr
  · have := finiteSupport_of_compProd' hκ (μ := μ)
    exact integrable_of_finiteSupport (μ ⊗ₘ κ)

lemma entropy_compProd [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U] {μ}
    [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    Hk[κ ⊗ₖ η, μ] = Hk[κ, μ] + Hk[η, μ ⊗ₘ κ] := by
  have h_meas_eq : μ ⊗ₘ hκ.mk = μ ⊗ₘ κ := Measure.compProd_congr hκ.ae_eq_mk.symm
  have h_ent1 : Hk[hκ.mk ⊗ₖ hη.mk, μ] = Hk[κ ⊗ₖ η, μ] := by
    refine entropy_congr <| compProd_congr_ae hκ.ae_eq_mk.symm ?_
    convert hη.ae_eq_mk.symm
  have h_ent2 : Hk[hκ.mk, μ] = Hk[κ, μ] := entropy_congr hκ.ae_eq_mk.symm
  have h_ent3 : Hk[hη.mk, μ ⊗ₘ hκ.mk] = Hk[η, μ ⊗ₘ κ] := by
    rw [h_meas_eq, entropy_congr hη.ae_eq_mk]
  rw [← h_ent1, ← h_ent2, ← h_ent3,
    entropy_compProd' hκ.finiteKernelSupport_mk hη.finiteKernelSupport_mk]

lemma chain_rule [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]
    {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ] [hU : Nonempty U]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[κ, μ] = Hk[fst κ, μ] + Hk[condKernel κ, μ ⊗ₘ (fst κ)] := by
  conv_lhs => rw [disintegration κ]
  rw [entropy_compProd hκ.fst (aefiniteKernelSupport_of_cond _ hκ)]

end ProbabilityTheory.Kernel
