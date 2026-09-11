/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
Source: https://github.com/TomasOrtega/CapacityAtlasCausalState/blob/0176a0e9fed6ec13fd2f566d9906c3ea8103d1cc/CapacityAtlasCausal/BlockLaw.lean
Adapted imports and reused shared product distributions.
-/

import CapacityAtlasForMathlib.InformationTheory.CausalState
import CapacityAtlasForMathlib.InformationTheory.FiniteProductDistribution

open scoped BigOperators
open CapacityAtlas

namespace CapacityAtlasCausal

attribute [local instance] Classical.propDecidable

variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

/-- The independent state history preceding the final use. -/
noncomputable def historyDistribution (state : FiniteDistribution S) (n : ℕ) :
    FiniteDistribution (Fin n → S) :=
  state.iid n

@[simp]
theorem historyDistribution_apply (state : FiniteDistribution S) (n : ℕ)
    (history : Fin n → S) : historyDistribution state n history = ∏ i, state (history i) := rfl

/-- Conditional on the full state word, the outputs are independent. -/
noncomputable def conditionalOutput (channels : S → FiniteChannel X Y) {n : ℕ}
    (policy : CausalState.Policy S X n) (states : Fin n → S) :
    FiniteDistribution (Fin n → Y) :=
  FiniteDistribution.productFamily fun i ↦
    (channels (states i)).rowDistribution (policy.input states i)

omit [Fintype S] in
@[simp]
theorem conditionalOutput_apply (channels : S → FiniteChannel X Y) {n : ℕ}
    (policy : CausalState.Policy S X n) (states : Fin n → S) (outputs : Fin n → Y) :
    conditionalOutput channels policy states outputs =
      ∏ i, (channels (states i)).transition (policy.input states i) (outputs i) := rfl

theorem block_rowDistribution_eq_mixture (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (n : ℕ) (policy : CausalState.Policy S X n) :
    ((CausalState.blockChannel state channels n).rowDistribution policy) =
      FiniteDistribution.mixture (historyDistribution state n) (conditionalOutput channels policy) := by
  ext outputs
  rfl

/-- Past states select a function of the fresh current state. -/
def lastStrategy {n : ℕ} (policy : CausalState.Policy S X (n + 1))
    (history : Fin n → S) (state : S) : X :=
  policy (Fin.last n) (Fin.snoc history state)

theorem blockChannel_transition_snoc (state : FiniteDistribution S)
    (channels : S → FiniteChannel X Y) (n : ℕ)
    (policy : CausalState.Policy S X (n + 1)) (outputs : Fin n → Y) (output : Y) :
    (CausalState.blockChannel state channels (n + 1)).transition policy
        (Fin.snoc outputs output) =
      ∑ history : Fin n → S, historyDistribution state n history *
        conditionalOutput channels policy.init history outputs *
          (CausalState.strategyChannel state channels).transition
            (lastStrategy policy history) output := by
  classical
  rw [CausalState.blockChannel_transition,
    ← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ S)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.snocEquiv, Equiv.coe_fn_mk, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, CausalState.Policy.input_snoc_castSucc,
    CausalState.Policy.input_last]
  rw [Finset.sum_comm]
  simp only [historyDistribution_apply, conditionalOutput_apply,
    CausalState.strategyChannel_transition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro history _
  apply Finset.sum_congr rfl
  intro current _
  dsimp [lastStrategy]
  ring

end CapacityAtlasCausal
