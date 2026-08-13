# Formal verification guide

Capacity Atlas uses Lean 4 to keep shared definitions, precise research claims,
and compact proofs in one project while allowing substantial proofs to develop
independently. The policy follows Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures): an
open claim is still valuable as a theorem declaration even when its body is
`by sorry`.

## Package layers

### `CapacityAtlasUtil`

This layer defines metadata attributes that connect declarations to registry
records:

```lean
@[capacity_problem "binary-symmetric-channel", capacity_definition]
def binarySymmetric ...
```

Declaration roles use `capacity_definition`, `capacity_statement`, and
`capacity_shared_api`. Claim categories use `capacity_open`,
`capacity_solved`, `capacity_api`, and `capacity_test`. A declaration with a
complete local proof also carries `capacity_formal_proof`.

### `CapacityAtlasForMathlib`

This is reusable information-theory infrastructure that may eventually be
proposed to Mathlib. It contains finite distributions and channels, code and
capacity definitions, network models, graph zero-error capacity, and finite
index coding. It is part of the trusted layer and may not contain `sorry` or
`admit`.

### `CapacityAtlas`

This layer contains concrete channel definitions, problem claims, and focused
tests. Every problem claim must fix the physical channel, code class,
operational criterion, rate normalization, and claimed capacity or bound.
Statements parameterized by an arbitrary operational theory, capacity function,
region, or bound do not qualify.

## Claim metadata

Each problem records one coverage status:

- `none`: no linked formal declaration
- `definitions`: concrete definitions or reusable API only
- `stated`: at least one research or structural claim is formally stated

Each claim has a stable `id`, mathematical `kind`, `category`, independent
`formal_status`, integer `version`, and description. Categories are:

- `open`: an open research claim
- `solved`: a mathematically solved research claim
- `API`: a reusable interface property
- `test`: a structural or computational check

The formal status is `stated` or `proved`. It records proof coverage, not the
mathematical status of the problem. In particular, a proved structural test does
not make a capacity claim formally proved.

Open claims are theorem declarations with `by sorry`. Solved claims without a
local proof may use the same form while their proof provenance is recorded
separately. A locally proved declaration carries `capacity_formal_proof` and may
not contain `sorry` or `admit`.

Increment a claim version only when its proposition changes materially.
Editorial changes and API refactors that preserve the proposition do not require
an increment.

## Formal proof provenance

Proof records are independent of both mathematical status and local statement
coverage. A linked proof is `partial` or `complete` and identifies an immutable
repository commit, file, declaration, claim identifier, and claim version. See
[formal-proofs.md](formal-proofs.md).

## What belongs here

Keep neutral shared definitions, concrete models, canonical claims, tests, and
short illuminating proofs in the central repository. A proof longer than about
25–50 lines, or one requiring substantial problem-specific infrastructure,
should normally live in a dedicated repository.

## Build and trust boundary

```bash
cd lean
lake exe cache get
lake --wfail build CapacityAtlasForMathlib CapacityAtlasUtil
lake build
```

The first build treats every warning as an error in reusable infrastructure and
metadata utilities. The complete build admits open and solved-but-unproved
problem claims. The validator separately rejects `sorry` and `admit` in locally
proved declarations, APIs, and tests. Compilation does not establish statement
faithfulness, so every claim change also needs mathematical review.
