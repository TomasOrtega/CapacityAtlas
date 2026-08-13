/-
Copyright 2026 The Capacity Atlas Authors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Lean

/-!
# Capacity Atlas declaration metadata

These lightweight attributes connect Lean declarations to stable atlas problem
identifiers and record the declaration's role.  The design is inspired by the
metadata attributes in Google DeepMind's `formal-conjectures` repository, while
using information-theory-specific roles rather than AMS subject tags.
-/

open Lean

namespace Lean.Parser.Attr

syntax (name := capacityProblem) "capacity_problem" str : attr
syntax (name := capacityClaim) "capacity_claim" str num : attr

end Lean.Parser.Attr

namespace CapacityAtlas.Metadata

/-- Stable identity and proposition version for a registered claim. -/
structure Claim where
  id : String
  version : Nat
  deriving Inhabited

/-- The stable Capacity Atlas identifier attached to a declaration. -/
initialize capacityProblemAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `capacityProblem
    descr := "Stable Capacity Atlas problem identifier."
    getParam := fun _ stx =>
      match stx with
      | `(attr| capacity_problem $problemId:str) => pure problemId.getString
      | _ => throwError "invalid `capacity_problem` attribute syntax"
  }

/-- The stable claim identifier and proposition version attached to a theorem. -/
initialize capacityClaimAttr : ParametricAttribute Claim ←
  registerParametricAttribute {
    name := `capacityClaim
    descr := "Stable Capacity Atlas claim identifier and proposition version."
    getParam := fun _ stx =>
      match stx with
      | `(attr| capacity_claim $claimId:str $version:num) =>
          pure { id := claimId.getString, version := version.getNat }
      | _ => throwError "invalid `capacity_claim` attribute syntax"
  }

/-- Marks a channel- or problem-specific definition. -/
initialize capacityDefinitionAttr : TagAttribute ←
  registerTagAttribute `capacity_definition "Capacity Atlas problem definition."

/-- Marks the canonical proposition representing a capacity problem. -/
initialize capacityStatementAttr : TagAttribute ←
  registerTagAttribute `capacity_statement "Canonical Capacity Atlas problem statement."

/-- Marks reusable information-theory infrastructure intended for possible upstreaming. -/
initialize capacitySharedApiAttr : TagAttribute ←
  registerTagAttribute `capacity_shared_api "Reusable Capacity Atlas API declaration."

/-- Marks an open research claim. -/
initialize capacityOpenAttr : TagAttribute ←
  registerTagAttribute `capacity_open "Open Capacity Atlas research claim."

/-- Marks a mathematically solved research claim. -/
initialize capacitySolvedAttr : TagAttribute ←
  registerTagAttribute `capacity_solved "Solved Capacity Atlas research claim."

/-- Marks a statement that is part of the reusable API. -/
initialize capacityApiAttr : TagAttribute ←
  registerTagAttribute `capacity_api "Capacity Atlas API statement."

/-- Marks a statement used to test a definition or formal model. -/
initialize capacityTestAttr : TagAttribute ←
  registerTagAttribute `capacity_test "Capacity Atlas test statement."

/-- Records that the attached claim has a complete proof in this repository. -/
initialize capacityFormalProofAttr : TagAttribute ←
  registerTagAttribute `capacity_formal_proof "Locally proved Capacity Atlas claim."

end CapacityAtlas.Metadata
