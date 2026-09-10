/-
Adapted from the PFR project, licensed under Apache-2.0.
See LICENSES/PFR-Apache-2.0.txt.
Source: https://github.com/teorth/pfr/blob/85d5879ae144170098815201491639f6e7d3c352/PFR/ForMathlib/Entropy/Basic.lean
Adaptations: retained the declarations needed by finite entropy and changed local imports.
-/

import Mathlib.Probability.ConditionalProbability
import CapacityAtlasForMathlib.Probability.FiniteRange
import CapacityAtlasForMathlib.Probability.FunctionProduct
import CapacityAtlasForMathlib.InformationTheory.Entropy.KernelMutualInformation

open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

section entropy

/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := Hm[μ.map X]

@[inherit_doc entropy] notation3:max "H[" X "; " μ "]" => entropy X μ
@[inherit_doc entropy] notation3:max "H[" X "]" => entropy X volume

@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "; " μ "]" => entropy X (μ[|Y ← y])
@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "]" => entropy X (ℙ[|Y ← y])

/-- Entropy of a random variable agrees with entropy of its distribution. -/
lemma entropy_def (X : Ω → S) (μ : Measure Ω) : entropy X μ = Hm[μ.map X] := rfl

/-- Entropy of a random variable is also the kernel entropy of the distribution over a Dirac mass.
-/
lemma entropy_eq_kernel_entropy (X : Ω → S) (μ : Measure Ω) :
    H[X ; μ] = Hk[Kernel.const Unit (μ.map X), Measure.dirac ()] := by simp [entropy]

/-- Any variable on a zero measure space has zero entropy. -/
@[simp]
lemma entropy_zero_measure (X : Ω → S) : H[X ; (0 : Measure Ω)] = 0 := by simp [entropy]

/-- `H[X] = ∑ₛ P[X=s] log 1 / P[X=s]`. -/
lemma entropy_eq_sum (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] :
    entropy X μ = ∑' x, negMulLog ((μ.map X).real {x}) := by
  rw [entropy_def, measureEntropy_of_isProbabilityMeasure]

/-- If `X`, `Y` are `S`-valued and `T`-valued random variables, and `Y = f(X)` for
some injection `f : S \to T`, then `H[Y] = H[X]`.
For the upper bound only, see `entropy_comp_le`. -/
lemma entropy_comp_of_injective [MeasurableSpace T] [Countable S] [MeasurableSingletonClass S]
    [MeasurableSingletonClass T]
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Function.Injective f) :
    H[f ∘ X ; μ] = H[X ; μ] := by
  have hf_m : Measurable f := .of_discrete
  rw [entropy_def, ← Measure.map_map hf_m hX, measureEntropy_map_of_injective _ _ hf_m hf,
    entropy_def]

open Set

open Function

variable [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]

variable [Countable T]

/-- `H[X, Y] = H[Y, X]`. -/
lemma entropy_comm (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, Y⟩; μ] = H[⟨Y, X⟩ ; μ] := by
  change H[Prod.swap ∘ ⟨Y, X⟩ ; μ] = H[⟨Y, X⟩ ; μ]
  exact entropy_comp_of_injective μ (hY.prodMk hX) Prod.swap Prod.swap_injective

end entropy

section condEntropy

variable [MeasurableSpace T]

variable {X : Ω → S} {Y : Ω → T}

/-- Conditional entropy of a random variable w.r.t. another.
This is the expectation under the law of `Y` of the entropy of the law of `X` conditioned on the
event `Y = y`. -/
noncomputable
def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Y)[fun y ↦ H[X | Y ← y ; μ]]

lemma condEntropy_def (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    condEntropy X Y μ = (μ.map Y)[fun y ↦ H[X | Y ← y ; μ]] := rfl

@[inherit_doc condEntropy] notation3:max "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ
@[inherit_doc condEntropy] notation3:max "H[" X " | " Y "]" => condEntropy X Y volume

section

variable [MeasurableSingletonClass T]

/-- Conditional entropy of a random variable is equal to the entropy of its conditional kernel. -/
lemma condEntropy_eq_kernel_entropy [Nonempty S] [Countable S] [MeasurableSingletonClass S]
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] [FiniteRange Y] :
    H[X | Y ; μ] = Hk[condDistrib X Y μ, μ.map Y] := by
  rw [condEntropy_def, Kernel.entropy]
  apply integral_congr_finiteSupport
  intro t ht
  rw [Measure.map_apply hY (.singleton _)] at ht
  simp only [entropy_def]
  congr
  ext s hs
  rw [condDistrib_apply' hX hY _ _ ht hs, Measure.map_apply hX hs,
      cond_apply (hY (.singleton _))]

variable [Countable T] [Nonempty T] [Nonempty S] [MeasurableSingletonClass S] [Countable S]
  [Countable U] [MeasurableSingletonClass U]

lemma condEntropy_two_eq_kernel_entropy (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [FiniteRange Y] [FiniteRange Z] :
    H[X | ⟨Y, Z⟩ ; μ] =
      Hk[Kernel.condKernel (condDistrib (fun a ↦ (Y a, X a)) Z μ),
        Measure.map Z μ ⊗ₘ Kernel.fst (condDistrib (fun a ↦ (Y a, X a)) Z μ)] := by
  rw [Measure.compProd_congr (condDistrib_fst_ae_eq hY hX hZ μ),
      map_compProd_condDistrib hY hZ,
      Kernel.entropy_congr (condKernel_condDistrib_ae_eq hY hX hZ μ),
      ← Kernel.entropy_congr (swap_condDistrib_ae_eq hY hX hZ μ)]
  have : μ.map (fun ω ↦ (Z ω, Y ω)) = (μ.map (fun ω ↦ (Y ω, Z ω))).comap Prod.swap := by
    rw [map_prod_comap_swap hY hZ]
  rw [this, condEntropy_eq_kernel_entropy hX (hY.prodMk hZ), Kernel.entropy_comap_swap]

end

/-- Any random variable on a zero measure space has zero conditional entropy. -/
@[simp]
lemma condEntropy_zero_measure (X : Ω → S) (Y : Ω → T) : H[X | Y ; (0 : Measure Ω)] = 0 :=
  by simp [condEntropy]

/-- Conditional entropy is non-negative. -/
lemma condEntropy_nonneg (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : 0 ≤ H[X | Y ; μ] :=
  integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

end condEntropy

section pair

variable [MeasurableSpace T]
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]

/-- One form of the chain rule : `H[X, Y] = H[X] + H[Y | X]`. -/
lemma chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[⟨X, Y⟩ ; μ] = H[X ; μ] + H[Y | X ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [entropy_eq_kernel_entropy, Kernel.chain_rule]
  · simp_rw [← Kernel.map_const _ (hX.prodMk hY), Kernel.fst_map_prod _ hY, Kernel.map_const _ hX,
      Kernel.map_const _ (hX.prodMk hY)]
    congr 1
    · rw [Kernel.entropy, integral_dirac]
      rfl
    · simp_rw [condEntropy_eq_kernel_entropy hY hX]
      have : Measure.dirac () ⊗ₘ Kernel.const Unit (μ.map X) = μ.map (fun ω ↦ ((), X ω)) := by
        ext s _
        rw [Measure.dirac_unit_compProd_const, Measure.map_map measurable_prodMk_left hX]
        congr
      rw [this, Kernel.entropy_congr (condDistrib_const_unit hX hY μ)]
      have : μ.map (fun ω ↦ ((), X ω)) = (μ.map X).map (Prod.mk ()) := by
        ext s _
        rw [Measure.map_map measurable_prodMk_left hX]
        rfl
      rw [this, Kernel.entropy_prodMkLeft_unit]
  · apply Kernel.FiniteKernelSupport.aefiniteKernelSupport
    exact Kernel.finiteKernelSupport_of_const _

/-- Another form of the chain rule : `H[X, Y] = H[Y] + H[X | Y]`. -/
lemma chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] [FiniteRange Y] :
    H[⟨X, Y⟩ ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  rw [entropy_comm hX hY, chain_rule' μ hY hX]

variable [Countable U] [MeasurableSingletonClass U]

/-- Data-processing inequality for the entropy: `H[f(X)] ≤ H[X]`.
For equality under an injective map, see `entropy_comp_of_injective`. -/
lemma entropy_comp_le (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (f : S → U) [FiniteRange X] :
    H[f ∘ X ; μ] ≤ H[X ; μ] := by
  have hfX : Measurable (f ∘ X) := by fun_prop
  have : H[X ; μ] = H[⟨X, f ∘ X⟩ ; μ] := by
    refine (entropy_comp_of_injective μ hX (fun x ↦ (x, f x)) ?_).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule _ hX hfX]
  simp only [le_add_iff_nonneg_right]
  exact condEntropy_nonneg X (f ∘ X) μ

end pair

section submodularity

variable [MeasurableSpace T]


variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

variable [Countable U] [MeasurableSingletonClass U]

variable (μ)
variable [Countable S] [Countable T]

variable [IsZeroOrProbabilityMeasure μ]

/-- `H[X | Y, Z] ≤ H[X | Z]`. -/
lemma entropy_submodular (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[X | ⟨Y, Z⟩ ; μ] ≤ H[X | Z ; μ] := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := Nonempty.map X (μ.nonempty_of_neZero)
  have : Nonempty T := Nonempty.map Y (μ.nonempty_of_neZero)
  rw [condEntropy_eq_kernel_entropy hX hZ, condEntropy_two_eq_kernel_entropy hX hY hZ]
  refine (Kernel.entropy_condKernel_le_entropy_snd ?_).trans_eq ?_
  · apply Kernel.aefiniteKernelSupport_condDistrib
    all_goals fun_prop
  exact Kernel.entropy_congr (condDistrib_snd_ae_eq hY hX hZ _)

/-- The submodularity inequality: `H[X, Y, Z] + H[Z] ≤ H[X, Z] + H[Y, Z]`. -/
lemma entropy_triple_add_entropy_le (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[⟨X, ⟨Y, Z⟩⟩ ; μ] + H[Z ; μ] ≤ H[⟨X, Z⟩ ; μ] + H[⟨Y, Z⟩ ; μ] := by
  rw [chain_rule _ hX (hY.prodMk hZ), chain_rule _ hX hZ, chain_rule _ hY hZ]
  ring_nf
  exact add_le_add le_rfl (entropy_submodular _ hX hY hZ)

end submodularity
end ProbabilityTheory
