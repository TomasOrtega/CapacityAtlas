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
syntax (name := capacityDefinition) "capacity_definition" : attr
syntax (name := capacityStatement) "capacity_statement" : attr
syntax (name := capacityShortProof) "capacity_short_proof" : attr
syntax (name := capacitySharedApi) "capacity_shared_api" : attr

end Lean.Parser.Attr

namespace CapacityAtlas.Metadata

/-- The stable Capacity Atlas identifier attached to a declaration. -/
initialize capacityProblemAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `capacityProblem
    descr := "Stable Capacity Atlas problem identifier."
    getParam := fun _ stx =>
      match stx with
      | `(attr| capacity_problem $problemId:str) => pure problemId.getString
      | _ => throwUnsupportedSyntax
  }

/-- Marks a channel- or problem-specific definition. -/
initialize capacityDefinitionAttr : TagAttribute ←
  registerTagAttribute `capacityDefinition "Capacity Atlas problem definition."

/-- Marks the canonical proposition representing a capacity problem. -/
initialize capacityStatementAttr : TagAttribute ←
  registerTagAttribute `capacityStatement "Canonical Capacity Atlas problem statement."

/-- Marks a short proof retained in the registry as a test or compact result. -/
initialize capacityShortProofAttr : TagAttribute ←
  registerTagAttribute `capacityShortProof "Short proof retained in Capacity Atlas."

/-- Marks reusable information-theory infrastructure intended for possible upstreaming. -/
initialize capacitySharedApiAttr : TagAttribute ←
  registerTagAttribute `capacitySharedApi "Reusable Capacity Atlas API declaration."

end CapacityAtlas.Metadata
