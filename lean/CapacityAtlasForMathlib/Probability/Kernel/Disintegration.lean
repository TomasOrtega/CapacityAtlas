/-
Adapted from the PFR project, licensed under Apache-2.0.
See LICENSES/PFR-Apache-2.0.txt.
Source: https://github.com/teorth/pfr/blob/85d5879ae144170098815201491639f6e7d3c352/PFR/Mathlib/Probability/Kernel/Disintegration.lean
Adaptations: retained the declarations needed by finite entropy, changed local imports,
and reused mathlib disintegration and composition lemmas where available.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.CondDistrib

open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]

namespace Kernel

section condKernel

variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]

lemma condKernel_apply (κ : Kernel T (S × U)) [IsFiniteKernel κ] (x : T × S)
    (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) :
    condKernel κ x = (κ x.1).condKernel x.2 := by
  have h := condKernel_apply_eq_condKernel κ x.1
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h
  refine h x.2 ?_
  rwa [fst_apply' _ _ (.singleton _)]

lemma condKernel_apply' (κ : Kernel T (S × U)) [IsFiniteKernel κ]
    (x : T × S) (hx : κ x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0) (s : Set U) :
    condKernel κ x s
      = (κ x.1 (Prod.fst ⁻¹' {x.2}))⁻¹ * (κ x.1) ({x.2} ×ˢ s) := by
  rw [condKernel_apply _ _ hx, Measure.condKernel_apply_of_ne_zero,
    Measure.fst_apply (.singleton _)]
  rwa [Measure.fst_apply (.singleton _)]

lemma disintegration (κ : Kernel T (S × U)) [IsFiniteKernel κ] :
    κ = (Kernel.fst κ) ⊗ₖ (condKernel κ) :=
  (Kernel.disintegrate κ (condKernel κ)).symm

end condKernel

end Kernel

section condDistrib

variable [MeasurableSingletonClass T]
variable [Countable U] [DiscreteMeasurableSpace U]

variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U}

lemma condDistrib_apply' [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) {s : Set S} (hs : MeasurableSet s) :
    condDistrib X Y μ x s = (μ (Y ⁻¹' {x}))⁻¹ * μ (Y ⁻¹' {x} ∩ X ⁻¹' s) := by
  rw [condDistrib_apply_of_ne_zero hX]
  · rw [Measure.map_apply hY (.singleton _),
      Measure.map_apply (hY.prodMk hX) ((measurableSet_singleton _).prod hs)]
    congr
  · rwa [Measure.map_apply hY (.singleton _)]

lemma condDistrib_apply [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (x : T) (hYx : μ (Y ⁻¹' {x}) ≠ 0) :
    condDistrib X Y μ x = (μ[|Y ⁻¹' {x}]).map X := by
  ext s hs
  rw [condDistrib_apply' hX hY μ x hYx hs, Measure.map_apply hX hs,
    cond_apply (hY (.singleton _))]

variable [Countable T]

lemma condDistrib_ae_eq [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    condDistrib X Y μ =ᵐ[μ.map Y] fun x ↦ (μ[|Y ⁻¹' {x}]).map X := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply hY (.singleton _)] at hx
  exact condDistrib_apply hX hY μ x hx

variable [Nonempty T]

lemma condDistrib_fst_of_ne_zero [Nonempty S]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) [IsFiniteMeasure μ]
    (u : U) (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    Kernel.fst (condDistrib (fun a ↦ (X a, Y a)) Z μ) u
      = condDistrib X Z μ u := by
  ext A hA
  rw [Kernel.fst_apply' _ _ hA, condDistrib_apply' (hX.prodMk hY) hZ _ _ hu]
  swap; · exact measurable_fst hA
  rw [condDistrib_apply' hX hZ _ _ hu hA]
  rfl

lemma condDistrib_fst_ae_eq [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.fst (condDistrib (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condDistrib X Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condDistrib_fst_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (.singleton _)] at hx

lemma condDistrib_snd_of_ne_zero [Nonempty S]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] (u : U) (hu : μ (Z ⁻¹' {u}) ≠ 0) :
    Kernel.snd (condDistrib (fun a ↦ (X a, Y a)) Z μ) u
      = condDistrib Y Z μ u := by
  ext A hA
  rw [Kernel.snd_apply' _ _ hA, condDistrib_apply' (hX.prodMk hY) hZ _ _ hu]
  swap; · exact measurable_snd hA
  rw [condDistrib_apply' hY hZ _ _ hu hA]
  rfl

lemma condDistrib_snd_ae_eq [Nonempty S] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.snd (condDistrib (fun a ↦ (X a, Y a)) Z μ)
      =ᵐ[μ.map Z] condDistrib Y Z μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condDistrib_snd_of_ne_zero hX hY hZ]
  rwa [Measure.map_apply hZ (.singleton _)] at hx

lemma condKernel_condDistrib_ae_eq [Nonempty S]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
  Kernel.condKernel (condDistrib (fun a ↦ (X a, Y a)) Z μ) =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))]
    condDistrib Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [Measure.map_apply (hZ.prodMk hX) (.singleton _)] at hx
  ext A hA
  have hx1 : μ (Z ⁻¹' {x.1}) ≠ 0 := by
    refine fun h_null ↦ hx (measure_mono_null ?_ h_null)
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    rw [← Prod.eta x, Prod.mk_inj] at hω
    exact hω.1
  rw [Kernel.condKernel_apply']
  swap
  · rw [condDistrib_apply' (hX.prodMk hY) hZ _ _ hx1]
    swap
    · exact measurable_fst (.singleton _)
    simp only [ne_eq, mul_eq_zero, ENNReal.inv_eq_zero, measure_ne_top μ, false_or]
    convert hx
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    conv_rhs => rw [← Prod.eta x]
    exact Prod.mk_inj.symm
  rw [condDistrib_apply' (hX.prodMk hY) hZ _ _ hx1]
  swap
  · exact measurable_fst (.singleton _)
  rw [condDistrib_apply' (hX.prodMk hY) hZ _ _ hx1]
  swap
  · exact (measurable_fst (.singleton _)).inter (measurable_snd hA)
  rw [condDistrib_apply' hY (hZ.prodMk hX) _ _ hx hA]
  have : (fun a ↦ (X a, Y a)) ⁻¹' (Prod.fst ⁻¹' {x.2}) = X ⁻¹' {x.2} := by rfl
  simp_rw [this]
  have : (fun a ↦ (X a, Y a)) ⁻¹' ({x.2} ×ˢ A) = X ⁻¹' {x.2} ∩ Y ⁻¹' A := by
    ext y;
    simp only [Set.singleton_prod, Set.mem_preimage, Set.mem_image, Prod.mk.injEq,
      exists_eq_right_right, Set.mem_inter_iff, Set.mem_singleton_iff]
    tauto
  simp_rw [this]
  have : (fun a ↦ (Z a, X a)) ⁻¹' {x} = Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
    conv_lhs => rw [← Prod.eta x, Prod.mk_inj]
  rw [this, ENNReal.mul_inv (Or.inr (measure_ne_top _ _)), inv_inv]
  swap; · left; simp [hx1]
  calc (μ (Z ⁻¹' {x.1})) * (μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2}))⁻¹ *
      ((μ (Z ⁻¹' {x.1}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ (X ⁻¹' {x.2} ∩ Y ⁻¹' A)))
    = (μ (Z ⁻¹' {x.1})) * (μ (Z ⁻¹' {x.1}))⁻¹ * (μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2}))⁻¹ *
      μ (Z ⁻¹' {x.1} ∩ (X ⁻¹' {x.2} ∩ Y ⁻¹' A)) := by
        ring
  _ = (μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2}))⁻¹ * μ (Z ⁻¹' {x.1} ∩ X ⁻¹' {x.2} ∩ Y ⁻¹' A) := by
        rw [ENNReal.mul_inv_cancel hx1 (measure_ne_top _ _), one_mul, Set.inter_assoc]

lemma swap_condDistrib_ae_eq (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.comap (condDistrib Y (fun a ↦ (X a, Z a)) μ) Prod.swap measurable_swap
      =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))] condDistrib Y (fun ω ↦ (Z ω, X ω)) μ := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  ext A hA
  rw [Kernel.comap_apply']
  have h_swap : (fun a ↦ (X a, Z a)) ⁻¹' {Prod.swap x} = (fun a ↦ (Z a, X a)) ⁻¹' {x} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.swap_prod_mk, Prod.mk_inj, Prod.mk_inj, and_comm]
  rw [condDistrib_apply' hY (hX.prodMk hZ) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prodMk hX) (.singleton _), ← h_swap] at hx
  rw [condDistrib_apply' hY (hZ.prodMk hX) _ _ _ hA]
  swap; · rwa [Measure.map_apply (hZ.prodMk hX) (.singleton _)] at hx
  rw [h_swap]

lemma condDistrib_const_unit (hX : Measurable X) (hY : Measurable Y)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Kernel.condKernel (Kernel.const Unit (μ.map (fun ω ↦ (X ω, Y ω))))
      =ᵐ[μ.map (fun ω ↦ ((), X ω))] Kernel.prodMkLeft Unit (condDistrib Y X μ) := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  have : (fun a ↦ ((), X a)) ⁻¹' {x} = X ⁻¹' {x.2} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← Prod.eta x, Prod.mk_inj]
    simp
  rw [Measure.map_apply (measurable_const.prodMk hX) (.singleton _), this] at hx
  ext s hs
  rw [Kernel.condKernel_apply']
  swap
  · rw [Kernel.const_apply,
      Measure.map_apply (hX.prodMk hY) (measurable_fst (.singleton _))]
    exact hx
  simp_rw [Kernel.const_apply,
    Measure.map_apply (hX.prodMk hY) (measurable_fst (.singleton _)),
    Measure.map_apply (hX.prodMk hY) ((measurableSet_singleton _).prod hs)]
  rw [Kernel.prodMkLeft_apply', condDistrib_apply' hY hX _ _ hx hs]
  rfl

omit [Countable U] [DiscreteMeasurableSpace U] in
lemma map_compProd_condDistrib [Nonempty S] (hX : Measurable X) (_hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.map Z ⊗ₘ condDistrib X Z μ = μ.map (fun ω ↦ (Z ω, X ω)) :=
  compProd_map_condDistrib hX.aemeasurable

end condDistrib

end ProbabilityTheory

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]

lemma _root_.MeasureTheory.Measure.compProd_apply_singleton
    [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (μ : Measure T) [SFinite μ]
    (κ : Kernel T S) [IsSFiniteKernel κ] (t : T) (s : S) :
    (μ ⊗ₘ κ) {(t, s)} = κ t {s} * μ {t} := by
  rw [← Set.singleton_prod_singleton, Measure.compProd_apply_prod (.singleton _) (.singleton _)]
  simp [mul_comm]

lemma _root_.MeasureTheory.Measure.ae_of_ae_compProd {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {p : α × β → Prop} (hp : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b) :=
  Measure.ae_ae_of_ae_compProd hp

lemma compProd_congr_ae {μ} [SFinite μ] {κ κ' : Kernel T S} [IsSFiniteKernel κ] [IsSFiniteKernel κ']
    {η η' : Kernel (T × S) U} [IsSFiniteKernel η] [IsSFiniteKernel η']
    (hκ : κ =ᵐ[μ] κ') (hη : η =ᵐ[μ ⊗ₘ κ] η') :
    κ ⊗ₖ η =ᵐ[μ] κ' ⊗ₖ η' := by
  have hη' := Measure.ae_of_ae_compProd hη
  filter_upwards [hκ, hη'] with a haκ haη
  ext s hs
  rw [compProd_apply hs, compProd_apply hs, ← haκ]
  refine lintegral_congr_ae ?_
  filter_upwards [haη] with b hb
  rw [hb]

/-- The analogue of FiniteSupport for probability kernels. -/
noncomputable def FiniteKernelSupport (κ : Kernel T S) : Prop :=
  ∀ t, ∃ A : Finset S, κ t Aᶜ = 0

/-- A kernel `κ` has almost everywhere finite support wrt a measure `μ` if, for almost every
point `t`, then `κ t` has finite support. Note that we don't require any uniformity wrt `t`. -/
noncomputable def AEFiniteKernelSupport (κ : Kernel T S) (μ : Measure T) : Prop :=
  ∀ᵐ t ∂μ, ∃ A : Finset S, κ t Aᶜ = 0

lemma FiniteKernelSupport.aefiniteKernelSupport {κ : Kernel T S} (hκ : FiniteKernelSupport κ)
    (μ : Measure T) :
    AEFiniteKernelSupport κ μ :=
  ae_of_all μ hκ

@[simp] lemma finiteKernelSupport_zero : FiniteKernelSupport (0 : Kernel T S) :=
  fun t ↦ ⟨∅, by simp⟩

@[simp] lemma aefiniteKernelSupport_zero {μ} : AEFiniteKernelSupport (0 : Kernel T S) μ :=
  finiteKernelSupport_zero.aefiniteKernelSupport _

section

variable [Countable T] [MeasurableSingletonClass T] {μ : Measure T}

/-- The definition doesn't use `_hκ`, but we keep it here still as it doesn't give anything
interesting otherwise. -/
@[nolint unusedArguments]
noncomputable
def AEFiniteKernelSupport.mk {μ} {κ : Kernel T S} (_hκ : AEFiniteKernelSupport κ μ) :
    Kernel T S := by
  classical
  exact if hS : Nonempty S then
    κ.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0}) (by rw [Set.setOf_exists]; measurability)
       (.const _ <| .dirac hS.some)
  else 0

@[simp] lemma AEFiniteKernelSupport.mk_zero
    {h : AEFiniteKernelSupport (0 : Kernel T S) μ} : h.mk = 0 := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp [mk]
  ext x
  by_cases hx : x ∈ {t | ∃ A : Finset S, (0 : Kernel T S) t Aᶜ = 0} <;>
    simp [AEFiniteKernelSupport.mk, Kernel.piecewise, hS]

@[simp] lemma AEFiniteKernelSupport.mk_eq_zero_of_isEmpty
    [IsEmpty S] {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    hκ.mk = 0 := by
  simp [mk]

open Classical in
lemma AEFiniteKernelSupport.mk_eq
    [hS : Nonempty S] {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    hκ.mk = κ.piecewise (s := {t | ∃ A : Finset S, κ t Aᶜ = 0})
      (by rw [Set.setOf_exists]; measurability) (.const _ <| .dirac hS.some) := by
  simp [mk, hS]

lemma AEFiniteKernelSupport.finiteKernelSupport_mk [MeasurableSingletonClass S] {κ : Kernel T S}
    (hκ : AEFiniteKernelSupport κ μ) :
    FiniteKernelSupport hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp
  intro t
  classical
  rw [mk_eq, piecewise_apply]
  split_ifs with ht
  · exact ht
  · refine ⟨{hS.some}, ?_⟩
    simp

lemma AEFiniteKernelSupport.ae_eq_mk
    {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ) :
    κ =ᵐ[μ] hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · filter_upwards with x
    ext s
    simp [Set.eq_empty_of_isEmpty s]
  filter_upwards [hκ] with t ht
  classical
  rw [AEFiniteKernelSupport.mk_eq, Kernel.piecewise_apply, if_pos (by exact ht)]

instance AEFiniteKernelSupport.isMarkovKernel_mk
    {κ : Kernel T S} [IsMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsMarkovKernel hκ.mk := by
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨fun x ↦ (IsEmpty.false x).elim⟩
  inhabit T
  have : Nonempty S := (κ default).nonempty_of_neZero
  rw [AEFiniteKernelSupport.mk_eq]
  infer_instance

instance AEFiniteKernelSupport.isZeroOrMarkovKernel_mk
    {κ : Kernel T S} [IsZeroOrMarkovKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsZeroOrMarkovKernel hκ.mk := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp only [mk_zero]
    infer_instance
  · infer_instance

instance AEFiniteKernelSupport.isSFiniteKernel_mk
    {κ : Kernel T S} [IsSFiniteKernel κ] (hκ : AEFiniteKernelSupport κ μ) :
    IsSFiniteKernel hκ.mk := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp only [mk_eq_zero_of_isEmpty]; infer_instance
  rw [AEFiniteKernelSupport.mk_eq]
  infer_instance

end

/-- Finite kernel support locally implies uniform finite kernel support. -/
lemma local_support_of_finiteKernelSupport
    {κ : Kernel T S} (h : FiniteKernelSupport κ) (A : Finset T) :
    ∃ B : Finset S, ∀ t ∈ A, ∀ᵐ x ∂(κ t), x ∈ B := by
  classical
  use A.biUnion (fun t ↦ (h t).choose)
  intro t ht
  change κ t (A.biUnion fun t ↦ (h t).choose)ᶜ = 0
  set B := (h t).choose
  refine measure_mono_null ?_ (h t).choose_spec
  intro s
  simp only [Finset.coe_biUnion, SetLike.mem_coe, Set.compl_iUnion, Set.mem_iInter,
    Set.mem_compl_iff]
  contrapose!; intro h
  use t

lemma AEFiniteKernelSupport.map [MeasurableSingletonClass U] {κ : Kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) {f : S → U} :
    AEFiniteKernelSupport (Kernel.map κ f) μ := by
  by_cases hf : Measurable f
  · filter_upwards [hκ] with t ⟨A, hA⟩
    classical
    use Finset.image f A
    rw [Kernel.map_apply' _ hf]
    · refine measure_mono_null ?_ hA
      intro s
      simp only [Finset.coe_image, Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_image, SetLike.mem_coe, not_exists, not_and]
      contrapose!; intro hs; use s
    · apply MeasurableSet.compl
      apply Set.Finite.measurableSet
      exact Finset.finite_toSet (Finset.image f A)
  · simp [map_of_not_measurable _ hf]

lemma AEFiniteKernelSupport.fst [MeasurableSingletonClass S] {κ : Kernel T (S × U)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (fst κ) μ := by
  rw [fst_eq]
  apply hκ.map

/-- Conditioning a kernel preserves finite kernel support. -/
lemma aefiniteKernelSupport_of_cond {κ : Kernel T (S × U)} [hU : Nonempty U]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] [Countable U] [Countable S] [Countable T]
    (μ : Measure T) (hκ : AEFiniteKernelSupport κ μ) [IsFiniteKernel κ] :
    AEFiniteKernelSupport (condKernel κ) (μ ⊗ₘ (Kernel.fst κ)) := by
  rw [AEFiniteKernelSupport, ae_iff_of_countable] at hκ ⊢
  intro (t, s) hts
  simp only [compProd_apply_singleton, ne_eq, mul_eq_zero, not_or] at hts
  push Not at hts
  rcases hκ t hts.2 with ⟨A, hA⟩
  classical
  use Finset.image Prod.snd A
  rw [condKernel_apply']; swap
  · rw [Kernel.fst_apply' _ _ (.singleton _)] at hts
    exact hts.1
  simp only [Finset.coe_image, Set.singleton_prod, mul_eq_zero, ENNReal.inv_eq_zero]
  right
  refine measure_mono_null ?_ hA
  intro x
  simp only [Set.mem_image, Set.mem_compl_iff, Finset.mem_coe, Prod.exists, exists_eq_right,
    not_exists, forall_exists_index, and_imp]
  intro y h hsyx
  rw [← hsyx]
  exact h s

end ProbabilityTheory.Kernel
