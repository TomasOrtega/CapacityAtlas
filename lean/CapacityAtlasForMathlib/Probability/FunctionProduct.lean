/-
Adapted from selected declarations by the PFR contributors; imports and API subset changed.
Licensed under Apache-2.0; see LICENSES/PFR-Apache-2.0.txt.
Source: https://github.com/teorth/pfr/blob/85d5879ae144170098815201491639f6e7d3c352/PFR/ForMathlib/Pair.lean
-/

import Mathlib.Util.Notation3
import Mathlib.Tactic.Basic

/-- The pair of two random variables. -/
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)

@[inherit_doc prod] notation3:100 "⟨" X ", " Y "⟩" => prod X Y
