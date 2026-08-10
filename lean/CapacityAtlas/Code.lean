import CapacityAtlas.FiniteChannel

open scoped BigOperators

namespace CapacityAtlas

variable {X Y : Type*}
variable [Fintype X] [Fintype Y]

/-- A deterministic one-use code for a fixed finite channel. -/
structure OneShotCode (W : FiniteChannel X Y) (M : Type*) [Fintype M] where
  encode : M → X
  decode : Y → M

namespace OneShotCode

variable {M : Type*} [Fintype M] [DecidableEq M]
variable {W : FiniteChannel X Y}

/-- Probability of correct decoding conditioned on a particular message. -/
def successProbability (code : OneShotCode W M) (message : M) : ℝ :=
  ∑ output, if code.decode output = message then
    W.transition (code.encode message) output
  else
    0

/-- Probability of error conditioned on a particular message. -/
def errorProbability (code : OneShotCode W M) (message : M) : ℝ :=
  1 - code.successProbability message

/-- Average success probability under the uniform message distribution. -/
noncomputable def averageSuccessProbability [Nonempty M] (code : OneShotCode W M) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ message, code.successProbability message

/-- Average error probability under the uniform message distribution. -/
noncomputable def averageErrorProbability [Nonempty M] (code : OneShotCode W M) : ℝ :=
  1 - code.averageSuccessProbability

end OneShotCode

end CapacityAtlas
