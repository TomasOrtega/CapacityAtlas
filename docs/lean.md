# Formal verification guide

Capacity Atlas uses Lean 4 to keep shared definitions, precise research claims,
and compact proofs in one project while allowing substantial proofs to develop
independently. The policy follows Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures): an
open claim is still valuable as a precise theorem declaration even when its
central proof is intentionally admitted.

## Package layers

### `CapacityAtlasUtil`

This layer defines metadata attributes that connect declarations to registry
records:

```lean
@[capacity_problem "binary-symmetric-channel", capacity_definition]
def binarySymmetric ...

@[capacity_problem "binary-symmetric-channel",
  capacity_claim "operational-capacity" 2,
  capacity_statement, capacity_solved, capacity_formal_proof]
theorem binarySymmetric_operational_capacity ... := ...
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

Every claim theorem carries `@[capacity_claim "claim-id" version]`. Its problem
ID, claim ID, category, and version must agree with exactly one YAML record.
Every public theorem or lemma in the problem layer is classified as open
research, solved research, API, or test; a complete local research proof also
carries `capacity_formal_proof`.

Formal status follows compiled, transitive proof dependencies. A stated claim
may contain `sorry` directly or prove an implication from another admitted
research claim. Both forms depend transitively on `sorryAx`. A local proof, API,
or test must not depend on `sorryAx`, `Lean.trustCompiler`, `Lean.ofReduceBool`,
or an unreviewed axiom. Consequently, registered local results use
kernel-checked tools such as `decide`, `norm_num`, and `omega`, not
`native_decide`.

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
lake --wfail build CapacityAtlas
lake exe capacity_audit > /tmp/capacity-audit.json
cd ..
uv run --locked capacity-atlas validate --lean-report /tmp/capacity-audit.json
```

The first build treats every warning as an error in reusable infrastructure and
metadata utilities. Only the `CapacityAtlas` library disables the individual
`warn.sorry` diagnostic; `--wfail` remains enabled for every build. The audit
loads the compiled environment, computes each checked declaration's transitive
axioms as `#print axioms` does, and permits only `propext`, `Quot.sound`, and
`Classical.choice`, plus `sorryAx` for a registered admitted research claim.
It checks every declaration in the reusable libraries, all tagged tests and
local proofs, and every public problem-layer theorem or lemma.

Comparator is reserved for a future untrusted proof-submission or external-proof
ingestion service. The curated central repository uses the environment-level
axiom audit and does not run Comparator, `lean4export`, or Landrun in CI.

Compilation and the audit do not establish statement faithfulness, so every
claim change also needs mathematical review. A materially changed proposition
must increment its claim version; a proposition diff without the corresponding
metadata change is intentionally visible during review.
