# External Lean proof contract

Substantial proofs should live in dedicated repositories. Capacity Atlas records
them as evidence for a stable, versioned claim rather than vendoring their
source.

This design is adapted from the `formal_proof` mechanism and long-proof policy of
Google DeepMind's Formal Conjectures project.

## Required repository contract

An external repository should contain a small manifest named
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
5. run `lake build` in public CI
6. preserve the registered commit permanently

## Atlas record

The corresponding problem YAML stores:

```yaml
formalization:
  statement:
    status: statement
    language: Lean
    claims:
      - id: nonlinear-converse
        kind: converse
        status: proved
        version: 1
        description: Nonlinear zero-error symmetric-capacity upper bound.
    files:
      - path: lean/CapacityAtlas/Network/SunJafar11.lean
        declaration: CapacityAtlas.IndexCoding.sunJafar11_nonlinear_converse
        role: statement
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
currently clone and rebuild every external repository, which keeps central CI
bounded. A future verifier may consume the manifest and surface external CI
status.

## Claim changes

When a canonical proposition changes materially, increment that claim's version.
Existing proof records then fail validation until they are rechecked or
explicitly moved to the new version. Unrelated claims retain their versions.
This makes stale proofs visible rather than silently treating them as proofs of
a revised problem.

## Multiple proofs

Capacity Atlas permits several independent proofs of the same claim. Distinct
proof strategies, human and AI formalizations, and later Mathlib proofs may all
coexist. No external repository is privileged merely by being first.
