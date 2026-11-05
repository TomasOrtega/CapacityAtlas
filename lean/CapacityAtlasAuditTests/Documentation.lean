/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import Lean

/-! These checks use the package options so disabling documentation linting fails the suite. -/

namespace CapacityAtlasAuditTests.Documentation

/--
warning: missing doc string for public def undocumented

Note: This linter can be disabled with `set_option linter.missingDocs false`
-/
#guard_msgs in
def undocumented : Nat := 0

/--
warning: empty doc string for public def emptyDocumentation

Note: This linter can be disabled with `set_option linter.missingDocs false`
-/
#guard_msgs in
/-- -/
def emptyDocumentation : Nat := 0

/--
warning: missing doc string for public abbrev undocumentedAbbreviation

Note: This linter can be disabled with `set_option linter.missingDocs false`
-/
#guard_msgs in
abbrev undocumentedAbbreviation := Nat

/--
warning: missing doc string for public field DocumentedStructure.value

Note: This linter can be disabled with `set_option linter.missingDocs false`
-/
#guard_msgs in
/-- A fixture whose field deliberately lacks documentation. -/
structure DocumentedStructure where
  value : Nat

#guard_msgs in
private def privateHelper : Nat := 0

#guard_msgs in
/-- The zero value used by documentation fixtures. -/
def documented : Nat := 0

#guard_msgs in
@[inherit_doc documented]
def inherited : Nat := 0

end CapacityAtlasAuditTests.Documentation
