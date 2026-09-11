/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See https://www.apache.org/licenses/LICENSE-2.0
-/

import CapacityAtlasUtil.Metadata
import Lean.AutoDecl
import Lean.Util.CollectAxioms

open Lean

namespace CapacityAtlas.Audit

open CapacityAtlas.Metadata

structure DeclarationRecord where
  declaration : String
  module : String
  problemId : Option String
  claimId : Option String
  claimVersion : Option Nat
  category : Option String
  formalProof : Bool
  proposition : Bool
  test : Bool
  axioms : Array String
  deriving ToJson

structure Report where
  declarations : Array DeclarationRecord
  errors : Array String
  deriving ToJson

private def standardAxioms : Array Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

private def moduleNameFor? (env : Environment) (declaration : Name) : Option Name :=
  env.getModuleIdxFor? declaration |>.map fun index => env.header.moduleNames[index]!

private def moduleIn (moduleName root : Name) : Bool :=
  moduleName == root || root.isPrefixOf moduleName

private def isPublicTheorem (info : ConstantInfo) : Bool :=
  info matches .thmInfo _

private def isAxiom (info : ConstantInfo) : Bool :=
  info matches .axiomInfo _

private def isPropositionDefinition (info : ConstantInfo) : MetaM Bool := do
  let .defnInfo value := info | return false
  Meta.forallTelescopeReducing value.type fun _ resultType =>
    Meta.isDefEq resultType (mkSort .zero)

private def category? (env : Environment) (declaration : Name) : Option String :=
  let categories := #[
    (capacityOpenAttr.hasTag env declaration, "open"),
    (capacitySolvedAttr.hasTag env declaration, "solved"),
    (capacityApiAttr.hasTag env declaration, "API"),
    (capacityTestAttr.hasTag env declaration, "test")
  ].filter (fun entry => entry.1)
  if categories.size == 1 then some categories[0]!.2 else none

private def unexpectedAxioms (axioms : Array Name) (allowSorry : Bool) : Array Name :=
  axioms.filter fun axiomName =>
    !standardAxioms.contains axiomName && !(allowSorry && axiomName == ``sorryAx)

/-- Check compiled declarations, including the bodies of canonical proposition definitions. -/
def audit (env : Environment) : CoreM Report := do
  let mut records := #[]
  let mut errors := #[]
  let declarations := env.constants.toList.toArray.qsort fun left right => Name.quickLt left.1 right.1
  for (declaration, info) in declarations do
    let some moduleName := moduleNameFor? env declaration | continue
    let inForMathlib := moduleIn moduleName `CapacityAtlasForMathlib
    let inUtil := moduleIn moduleName `CapacityAtlasUtil
    let inProblemLayer := moduleIn moduleName `CapacityAtlas
    let isTest := capacityTestAttr.hasTag env declaration
    let isFormalProof := capacityFormalProofAttr.hasTag env declaration
    let isProposition := capacityPropositionAttr.hasTag env declaration
    let isApi := capacityApiAttr.hasTag env declaration
    let isSharedApi := capacitySharedApiAttr.hasTag env declaration
    let claim? := capacityClaimAttr.getParam? env declaration
    let claimId? := claim?.map Claim.id
    let claimVersion? := claim?.map Claim.version
    let problemId? := capacityProblemAttr.getParam? env declaration
    let category := category? env declaration
    let relevant := inForMathlib || inUtil || inProblemLayer || isTest || isFormalProof ||
      isProposition || claim?.isSome
    unless relevant do continue
    let axioms ← Lean.collectAxioms declaration
    let isAutoOrPrivate ← Lean.isAutoDeclOrPrivate_Internal declaration
    let isProblemTheorem := inProblemLayer && isPublicTheorem info && !isAutoOrPrivate &&
      !env.isProjectionFn declaration
    if inProblemLayer && isAxiom info && !isAutoOrPrivate then
      errors := errors.push s!"{declaration}: public problem-layer axioms are not permitted"
    if isProblemTheorem then
      let categoryCount := #[
        capacityOpenAttr.hasTag env declaration,
        capacitySolvedAttr.hasTag env declaration,
        capacityApiAttr.hasTag env declaration,
        capacityTestAttr.hasTag env declaration
      ].count true
      if categoryCount != 1 then
        errors := errors.push
          s!"{declaration}: public problem-layer theorem must have exactly one classification"
    if claim?.isSome then
      unless isPublicTheorem info || isProposition do
        errors := errors.push
          s!"{declaration}: [capacity_claim] requires a theorem or [capacity_proposition] definition"
      if problemId?.isNone then
        errors := errors.push s!"{declaration}: [capacity_claim] requires [capacity_problem]"
      unless capacityStatementAttr.hasTag env declaration do
        errors := errors.push s!"{declaration}: [capacity_claim] requires [capacity_statement]"
      if category.isNone then
        errors := errors.push s!"{declaration}: [capacity_claim] requires exactly one category"
    if isProposition then
      unless ← (isPropositionDefinition info).run' do
        errors := errors.push
          s!"{declaration}: [capacity_proposition] must be a definition returning Prop"
      if claim?.isNone then
        errors := errors.push s!"{declaration}: [capacity_proposition] requires [capacity_claim]"
      unless (category == some "open" || category == some "solved") && !isSharedApi do
        errors := errors.push
          s!"{declaration}: [capacity_proposition] requires an open or solved category without API tags"
      if isFormalProof then
        errors := errors.push
          s!"{declaration}: [capacity_proposition] cannot be marked [capacity_formal_proof]"
    if (capacityOpenAttr.hasTag env declaration || capacitySolvedAttr.hasTag env declaration) &&
        claim?.isNone then
      errors := errors.push
        s!"{declaration}: research claim is missing [capacity_claim] identity and version"
    let admittedResearchClaim := claim?.isSome && isPublicTheorem info && !isProposition &&
      (capacityOpenAttr.hasTag env declaration || capacitySolvedAttr.hasTag env declaration) &&
      !isFormalProof && !isTest
    let requiresCleanAxioms :=
      inForMathlib || inUtil || isTest || isFormalProof || isApi || isSharedApi || isProposition
    let checkedAxioms := if requiresCleanAxioms || isProblemTheorem then axioms else #[]
    let unexpected := unexpectedAxioms checkedAxioms admittedResearchClaim
    unless unexpected.isEmpty do
      errors := errors.push
        s!"{declaration}: undeclared trust dependencies: {unexpected.toList}"
    if isProblemTheorem && axioms.contains ``sorryAx && !admittedResearchClaim then
      errors := errors.push
        s!"{declaration}: sorryAx is permitted only in a registered research claim"
    if isTest || isFormalProof || isProposition || claim?.isSome then
      records := records.push {
        declaration := declaration.toString
        module := moduleName.toString
        problemId := problemId?
        claimId := claimId?
        claimVersion := claimVersion?
        category
        formalProof := isFormalProof
        proposition := isProposition
        test := isTest
        axioms := axioms.map (fun axiomName : Name => axiomName.toString)
      }
  return { declarations := records, errors }

end CapacityAtlas.Audit
