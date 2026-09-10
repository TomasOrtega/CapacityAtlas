/-
Adapted from the PFR project, licensed under Apache-2.0.
See LICENSES/PFR-Apache-2.0.txt.
Source: https://github.com/teorth/pfr/blob/85d5879ae144170098815201491639f6e7d3c352/PFR/ForMathlib/Entropy/Measure.lean
Adaptations: retained needed declarations, changed local imports, and omitted the unused
equality case of measureMutualInfo_nonneg_aux.
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import CapacityAtlasForMathlib.Probability.FiniteRange
import Mathlib.MeasureTheory.Measure.Dirac
import CapacityAtlasForMathlib.MeasureTheory.Measure.Real

open MeasureTheory Real Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]

section measureEntropy
variable {μ : Measure S}

/-- Entropy of a measure, normalized by its total mass. -/
noncomputable
def measureEntropy (μ : Measure S := by volume_tac) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

@[inherit_doc measureEntropy] notation:100 "Hm[" μ "]" => measureEntropy μ

/-- A measure has finite support if there exists a finite set whose complement has zero measure. -/
class FiniteSupport (μ : Measure S := by volume_tac) : Prop where
  finite : ∃ A : Finset S, ∀ᵐ x ∂μ, x ∈ A

/-- A set on which a measure with finite support is supported. -/
noncomputable
def _root_.MeasureTheory.Measure.support (μ : Measure S) [hμ : FiniteSupport μ] : Finset S :=
  hμ.finite.choose.filter (μ {·} ≠ 0)

lemma measure_compl_support (μ : Measure S) [hμ : FiniteSupport μ] : μ μ.supportᶜ = 0 := by
  let A := hμ.finite.choose
  have : (μ.support : Set S)ᶜ ⊆ (A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0), {x} := by
    intro z hz
    simp only [Measure.support, ne_eq, Finset.coe_filter, mem_compl_iff, mem_setOf_eq, not_and,
      Decidable.not_not] at hz
    by_cases h'z : z ∈ A
    · simp [hz h'z, h'z]
    · simp [h'z]
  apply le_antisymm ?_ bot_le
  calc μ (μ.support : Set S)ᶜ ≤ μ ((A : Set S)ᶜ ∪ ⋃ x ∈ A.filter (μ {·} = 0), {x}) :=
    measure_mono this
  _ ≤ μ (Aᶜ) + ∑ x ∈ A.filter (μ {·} = 0), μ {x} := by
    apply (measure_union_le _ _).trans
    gcongr
    apply measure_biUnion_finset_le
  _ ≤ 0 + ∑ x ∈ A.filter (μ {·} = 0), 0 := by
    gcongr with x hx
    · exact hμ.finite.choose_spec.le
    · simp only [Finset.mem_filter] at hx
      exact hx.2.le
  _ = 0 := by simp

lemma ae_mem_support (μ : Measure S) [FiniteSupport μ] : ∀ᵐ x ∂μ, x ∈ μ.support :=
  measure_compl_support _

@[simp] lemma mem_support {μ : Measure S} [hμ : FiniteSupport μ] {x : S} :
    x ∈ μ.support ↔ μ {x} ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [Measure.support, ne_eq, Finset.mem_filter] at h
    exact h.2
  · contrapose! h
    exact measure_mono_null (by simpa using h) (measure_compl_support μ)

instance finiteSupport_of_mul {μ : Measure S} [FiniteSupport μ] (c : ℝ≥0∞) :
    FiniteSupport (c • μ) := ⟨μ.support, Measure.ae_smul_measure (ae_mem_support _) _⟩

section

variable [MeasurableSingletonClass S]

instance finiteSupport_of_dirac (x : S) : FiniteSupport (Measure.dirac x) := ⟨{x}, by simp⟩

instance finiteSupport_of_finiteRange {μ : Measure Ω} {X : Ω → S} [hX' : FiniteRange X] :
    FiniteSupport (μ.map X) := by
  use hX'.toFinset
  exact FiniteRange.null_of_compl μ X

/-- Functions are integrable under a finitely supported finite measure. -/
lemma integrable_of_finiteSupport (μ : Measure S) [FiniteSupport μ]
    {β : Type*} [NormedAddCommGroup β] [IsFiniteMeasure μ] [Countable S]
    {f : S → β} :
    Integrable f μ := by
  let A := μ.support
  have hA : μ Aᶜ = 0 := measure_compl_support μ
  by_cases hA' : A = ∅
  · simp only [hA', Finset.coe_empty, compl_empty, Measure.measure_univ_eq_zero] at hA
    rw [hA]
    exact integrable_zero_measure
  have : ∃ s₀, s₀ ∈ A := by
    contrapose! hA'
    ext s
    simpa using hA' s
  rcases this with ⟨s₀, hs₀⟩
  let f' : A → β := fun a ↦ f a
  classical
  let g : S → A := fun s ↦ if h : s ∈ A then ⟨s, h⟩ else ⟨s₀, hs₀⟩
  have : (f' ∘ g) =ᵐ[μ] f := by
    apply Filter.eventuallyEq_of_mem (s := A) hA
    intro a ha
    simp at ha
    simp [f', g, ha]
  apply Integrable.congr _ this
  apply Integrable.comp_measurable .of_finite
  fun_prop

lemma integral_congr_finiteSupport {μ : Measure Ω} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : Ω → G} [FiniteSupport μ]
    (hfg : ∀ x, μ {x} ≠ 0 → f x = g x) : ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  refine integral_congr_ae <| measure_mono_null ?_ <| measure_compl_support μ
  exact fun x hx hx' ↦ hx <| hfg _ <| mem_support.1 hx'

end

lemma measureEntropy_eq_sum {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0) :
   Hm[μ] = ∑ s ∈ A, negMulLog (((μ Set.univ)⁻¹ • μ).real {s}) := by
  unfold measureEntropy
  rw [tsum_eq_sum]
  intro s hs
  suffices μ.real {s} = 0 by simp [this]
  rw [Measure.real, measure_mono_null (by simpa) hA]
  simp

@[simp]
lemma measureEntropy_zero : Hm[(0 : Measure S)] = 0 := by simp [measureEntropy]

lemma measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) : Hm[μ] = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

lemma measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑' s, negMulLog (μ.real {s}) := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [measureEntropy]
  · simp [measureEntropy]

lemma measureEntropy_of_isProbabilityMeasure_finite {μ : Measure S} {A : Finset S} (hA : μ Aᶜ = 0)
    [IsZeroOrProbabilityMeasure μ] :
    Hm[μ] = ∑ s ∈ A, negMulLog (μ.real {s}) := by
  rw [measureEntropy_eq_sum hA]
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ <;> simp

lemma measureEntropy_univ_smul : Hm[(μ Set.univ)⁻¹ • μ] = Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => simp [measureEntropy]

lemma measureEntropy_nonneg (μ : Measure S) : 0 ≤ Hm[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap; · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
  apply tsum_nonneg
  intro s
  apply negMulLog_nonneg (by positivity)
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => exact prob_le_one

variable [MeasurableSingletonClass S]

set_option linter.flexible false in

lemma measureEntropy_map_of_injective
    (μ : Measure T) (f : T → S) (hf_m : Measurable f) (hf : Function.Injective f) :
    Hm[μ.map f] = Hm[μ] := by
  have : μ.map f Set.univ = μ Set.univ := by
      rw [Measure.map_apply hf_m MeasurableSet.univ]
      simp
  simp_rw [measureEntropy, Measure.ennreal_smul_real_apply,
    map_measureReal_apply hf_m (.singleton _)]
  rw [this]
  classical
  let F (x : S) : ℝ := negMulLog ((μ Set.univ)⁻¹.toReal • μ.real (f ⁻¹' {x}))
  have : ∑' x : S, F x
      = ∑' x : (f '' Set.univ), F x := by
    apply (tsum_subtype_eq_of_support_subset _).symm
    intro x hx
    contrapose hx
    suffices f ⁻¹' {x} = ∅ by simp [F, this]
    contrapose! hx
    rw [Set.image_univ]
    exact hx
  rw [this, tsum_image _ hf.injOn, tsum_univ fun x ↦ F (f x)]
  congr! with s
  ext s'
  simpa using hf.eq_iff

end measureEntropy

section measureMutualInfo

/-- The mutual information between the marginals of a measure on a product space. -/
noncomputable
def measureMutualInfo (μ : Measure (S × T) := by volume_tac) : ℝ :=
  Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ]

@[inherit_doc measureMutualInfo] notation:100 "Im[" μ "]" => measureMutualInfo μ

lemma measureMutualInfo_def (μ : Measure (S × T)) :
    Im[μ] = Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ] := rfl

@[simp]
lemma measureMutualInfo_zero_measure : Im[(0 : Measure (S × T))] = 0 := by
  simp [measureMutualInfo]

lemma measureMutualInfo_of_not_isFiniteMeasure {μ : Measure (S × U)} (h : ¬ IsFiniteMeasure μ) :
    Im[μ] = 0 := by
  rw [measureMutualInfo_def]
  have h1 : ¬ IsFiniteMeasure (μ.map Prod.fst) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    exact Measure.map_apply measurable_fst MeasurableSet.univ
  have h2 : ¬ IsFiniteMeasure (μ.map Prod.snd) := by
    rw [not_isFiniteMeasure_iff] at h ⊢
    rw [← h]
    exact Measure.map_apply measurable_snd MeasurableSet.univ
  rw [measureEntropy_of_not_isFiniteMeasure h, measureEntropy_of_not_isFiniteMeasure h1,
    measureEntropy_of_not_isFiniteMeasure h2]
  simp

lemma measureMutualInfo_univ_smul (μ : Measure (S × U)) : Im[(μ Set.univ)⁻¹ • μ] = Im[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  rcases eq_zero_or_neZero μ with hμ | _
  · simp [hμ]
  rw [measureMutualInfo_def, measureMutualInfo_def]
  congr 1
  · congr 1
    · convert measureEntropy_univ_smul
      simp [Measure.map_smul, Measure.map_apply measurable_fst]
    · convert measureEntropy_univ_smul
      simp [Measure.map_smul, Measure.map_apply measurable_snd]
  convert measureEntropy_univ_smul

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]

/-- Nonnegativity of mutual information for a finitely supported probability measure. -/
lemma measureMutualInfo_nonneg_aux {μ : Measure (S × U)} [FiniteSupport μ]
    [IsZeroOrProbabilityMeasure μ] :
    0 ≤ Im[μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have : IsProbabilityMeasure (μ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let E := μ.support
  have hE := measure_compl_support μ
  classical
  set E1 : Finset S := Finset.image Prod.fst E
  set E2 : Finset U := Finset.image Prod.snd E
  have hE' : μ (E1 ×ˢ E2 : Finset (S × U))ᶜ = 0 := by
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    contrapose!
    intro h
    simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
      Finset.coe_product, mem_prod, not_and, Classical.not_imp] at h ⊢
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E, E2,
      mem_support]
    constructor
    · use u
    · use s
  have hE1 : (μ.map Prod.fst) E1ᶜ = 0 := by
    rw [Measure.map_apply measurable_fst (MeasurableSet.compl (Finset.measurableSet E1))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp only [preimage_compl, mem_compl_iff, mem_preimage, SetLike.mem_coe, mem_support, ne_eq,
      Decidable.not_not]
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, E1, E,
      mem_support]
    intro h; use u
  have hE1' : (μ.map Prod.fst).real E1 = 1 := by
    rw [prob_compl_eq_zero_iff E1.measurableSet] at hE1
    unfold Measure.real
    rw [hE1]
    norm_num
  have hE2 : (μ.map Prod.snd) E2ᶜ = 0 := by
    rw [Measure.map_apply measurable_snd (MeasurableSet.compl (Finset.measurableSet E2))]
    refine measure_mono_null ?_ hE
    intro ⟨s, u⟩
    simp only [preimage_compl, mem_compl_iff, mem_preimage, SetLike.mem_coe, mem_support, ne_eq,
      Decidable.not_not]
    contrapose!
    simp only [Finset.mem_image, Prod.exists, exists_eq_right, E2, E, mem_support]
    intro h; use s
  have hE2' : (μ.map Prod.snd).real E2 = 1 := by
    rw [prob_compl_eq_zero_iff E2.measurableSet] at hE2
    unfold Measure.real
    rw [hE2]
    norm_num
  have h_fst_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.fst).real {p.1} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_fst (.singleton _)]
    refine fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero
  have h_snd_ne_zero : ∀ p, μ.real {p} ≠ 0 → (μ.map Prod.snd).real {p.2} ≠ 0 := by
    intro p hp
    rw [map_measureReal_apply measurable_snd (.singleton _)]
    exact fun h_eq_zero ↦ hp <| measureReal_mono_null (by simp) h_eq_zero
  have h1 y : (μ.map Prod.fst).real {y} = ∑ z ∈ E2, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_fst (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        rintro ⟨s, u⟩ ⟨rfl, h2⟩
        contrapose! h2
        simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
          Finset.mem_image, Prod.exists, exists_eq_right, iUnion_exists, mem_iUnion,
          mem_singleton_iff, Prod.mk.injEq, true_and, exists_prop, exists_and_right,
          exists_eq_right', E2, E] at h2 ⊢
        use s
      · convert measure_empty (μ := μ)
        simp [Set.sdiff_eq_empty]
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _
  have h2 z : (μ.map Prod.snd).real {z} = ∑ y ∈ E1, μ.real {(y, z)} := by
    rw [map_measureReal_apply measurable_snd (.singleton _), ← measureReal_biUnion_finset]
    · apply measureReal_congr
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ hE
        rintro ⟨s, u⟩ ⟨rfl, h2⟩
        contrapose! h2
        simp only [mem_compl_iff, SetLike.mem_coe, mem_support, ne_eq, Decidable.not_not,
          Finset.mem_image, Prod.exists, exists_and_right, exists_eq_right, iUnion_exists,
          mem_iUnion, mem_singleton_iff, Prod.mk.injEq, and_true, exists_prop, exists_eq_right', E1,
          E] at h2 ⊢
        use u
      · convert measure_empty (μ := μ)
        simp [Set.sdiff_eq_empty]
    · intro s1 _ s2 _ h; simp [h]
    intros; exact .singleton _
  let w (p : S × U) := (μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2}
  let f (p : S × U) := ((μ.map Prod.fst).real {p.1} * (μ.map Prod.snd).real {p.2})⁻¹ * μ.real {p}
  have hw1 : ∀ p ∈ (E1 ×ˢ E2), 0 ≤ w p := by intros; positivity
  have hw2 : ∑ p ∈ E1 ×ˢ E2, w p = 1 := by
    rw [Finset.sum_product]
    simp only [← Finset.mul_sum, sum_measureReal_singleton, w]
    rw [← Finset.sum_mul]
    rw [show (1 : ℝ) = 1 * 1 by norm_num]
    congr
    convert hE1'
    simp
  have hf : ∀ p ∈ E1 ×ˢ E2, 0 ≤ f p := by intros; positivity
  have H :=
  calc
    ∑ p ∈ E1 ×ˢ E2, w p * f p
        = ∑ p ∈ E1 ×ˢ E2, μ.real {p} := by
          congr with p
          by_cases hp : μ.real {p} = 0
          · simp [f, hp]
          · simp [w, f]
            field_simp [h_fst_ne_zero p hp, h_snd_ne_zero p hp]
      _ = 1 := by
        simp only [sum_measureReal_singleton, Finset.coe_product]
        rw [show 1 = μ.real Set.univ by simp]
        apply measureReal_congr
        simpa using hE'
  have H1 : -measureMutualInfo (μ := μ) = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := calc
    _ = ∑ p ∈ E1 ×ˢ E2,
          (-(μ.real {p} * log (μ.real {p}))
          + (μ.real {p} * log ((μ.map Prod.snd).real {p.2})
            + μ.real {p} * log ((μ.map Prod.fst).real {p.1}))) := by
        have H0 : Hm[μ] = -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log (μ.real {p}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE', negMulLog, neg_mul,
            Finset.sum_neg_distrib]
        have H1 : Hm[μ.map Prod.fst] = -∑ p ∈ E1 ×ˢ E2,
            μ.real {p} * log ((μ.map Prod.fst).real {p.1}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE1, negMulLog, neg_mul,
            Finset.sum_neg_distrib, Finset.sum_product, ← Finset.sum_mul]
          congr! with s _
          exact h1 s
        have H2 : Hm[μ.map Prod.snd] =
            -∑ p ∈ E1 ×ˢ E2, μ.real {p} * log ((μ.map Prod.snd).real {p.2}) := by
          simp_rw [measureEntropy_of_isProbabilityMeasure_finite hE2, negMulLog, neg_mul,
            Finset.sum_neg_distrib, Finset.sum_product_right, ← Finset.sum_mul]
          congr! with s _
          exact h2 s
        simp_rw [measureMutualInfo_def, H0, H1, H2]
        simp [Finset.sum_add_distrib]
    _ = ∑ p ∈ E1 ×ˢ E2, w p * negMulLog (f p) := by
        congr! 1 with p _
        by_cases hp : μ.real {p} = 0
        · simp [f, hp]
        have := h_fst_ne_zero p hp
        have := h_snd_ne_zero p hp
        simp [negMulLog, log_mul, log_inv, h_fst_ne_zero p hp, h_snd_ne_zero p hp, hp, w, f]
        field_simp
        ring
  have H2 : 0 = negMulLog (∑ s ∈ (E1 ×ˢ E2), w s * f s) := by
    rw [H, negMulLog_one]
  rw [← neg_nonpos, H1, H2]
  exact concaveOn_negMulLog.le_map_sum hw1 hw2 hf

lemma measureMutualInfo_nonneg {μ : Measure (S × U)} [FiniteSupport μ] :
    0 ≤ Im[μ] := by
  by_cases hμ_fin : IsFiniteMeasure μ
  · rw [← measureMutualInfo_univ_smul μ]
    apply measureMutualInfo_nonneg_aux
  rw [measureMutualInfo_of_not_isFiniteMeasure hμ_fin]

end measureMutualInfo

end ProbabilityTheory
