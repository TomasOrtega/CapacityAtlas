# Formal proof provenance

Develop proofs and their supporting infrastructure in this monorepo by default
so other proofs can reuse them. Local proofs build against the shared definitions
and are checked by the repository's transitive axiom audit. A complete local
claim theorem carries `capacity_formal_proof`; see [the Lean guide](lean.md).
When an external proof is brought into the monorepo, its immutable record may
remain as historical provenance alongside the locally proved claim.

Contributors may maintain proofs in external repositories when they prefer.
Capacity Atlas records those proofs as evidence for stable, versioned claims
using immutable links. This optional provenance mechanism is adapted from the
`formal_proof` mechanism of Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures).

## External repository contract

An external proof repository should contain a small manifest named
`capacity-atlas-proof.yaml`:

```yaml
problem: sun-jafar-11-message-index-coding
claim_id: nonlinear-converse

atlas:
  repository: TomasOrtega/CapacityAtlas
  commit: <40-character Capacity Atlas commit>
  claim_version: 1

lean:
  toolchain: v4.32.0
  file: SunJafar/Converse.lean
  declaration: SunJafar.nonlinearConverse
```

The proof repository should:

1. pin a Capacity Atlas commit or release
2. import the canonical claim declaration when one exists
3. build without `sorry`, `admit`, or unreviewed axioms
4. expose the named declaration from its root library
5. run its complete Lean build and transitive axiom checks in public CI
6. preserve the registered commit permanently

A canonical claim may be a `capacity_proposition` definition returning `Prop`.
This records the exact statement without admitting it as a theorem. For example,
an external theorem can have type `Canonical.claim parameters`. Its CI must
check that the exported theorem proves the canonical proposition at the pinned
Atlas commit, with the same parameters, and has only the permitted standard
axioms. The proposition definition itself never counts as a local proof;
`formal_status: proved` requires a complete linked proof record.

## Linked proof record

The corresponding problem YAML stores:

```yaml
formalization:
  status: stated
  claims:
    - id: nonlinear-converse
      kind: converse
      category: solved
      formal_status: proved
      version: 1
      description: Nonlinear zero-error symmetric-capacity upper bound.
  files:
    - path: lean/CapacityAtlas/Network/SunJafar11.lean
      declaration: CapacityAtlas.IndexCoding.sunJafar11_nonlinear_converse
      role: claim
      description: Canonical nonlinear converse claim.
      claim_id: nonlinear-converse
  proofs:
    - id: nonlinear-converse-proof-a
      claim_id: nonlinear-converse
      status: complete
      system: Lean
      repository: example/sun-jafar-lean
      commit: 0123456789abcdef0123456789abcdef01234567
      url: https://github.com/example/sun-jafar-lean/commit/0123456789abcdef0123456789abcdef01234567
      file: SunJafar/Converse.lean
      declaration: SunJafar.nonlinearConverse
      claim_version: 1
```

Capacity Atlas validates the immutable link and claim-version match. It does not
currently clone and rebuild every linked repository, which keeps central CI
bounded.

## Claim changes

When a canonical proposition changes materially, increment that claim's version.
Existing proof records then fail validation until they are rechecked or moved to
the new version. Unrelated claims retain their versions. This makes stale proof
evidence visible instead of silently applying it to a revised problem.

## Multiple proofs

Capacity Atlas permits several independent proofs of the same claim, developed
locally or in external repositories. Distinct proof strategies, human and AI
formalizations, and later Mathlib proofs may all coexist. No proof is privileged
merely by being first.
