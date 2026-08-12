# Lean formalization guide

Capacity Atlas is a formal specification registry. It keeps shared definitions,
canonical statements, and short proofs in one small Lean project while allowing
substantial proofs to develop independently.

## Package layers

### `CapacityAtlasUtil`

Metadata attributes and tooling used to connect Lean declarations to atlas
records:

```lean
@[capacity_problem "binary-symmetric-channel", capacity_definition]
def binarySymmetric ...
```

Available role attributes are:

- `capacity_definition`
- `capacity_statement`
- `capacity_short_proof`
- `capacity_shared_api`

The attribute system is inspired by the category and `formal_proof` metadata in
Google DeepMind's Formal Conjectures project. Capacity Atlas omits AMS tags and
uses its channel-specific YAML facets for subject classification.

### `CapacityAtlasForMathlib`

Reusable information-theory infrastructure that is useful across several
capacity problems and may eventually be proposed to Mathlib. Current modules
cover finite distributions, finite channels, one-shot and block codes,
information and operational capacity, broadcast, wiretap, interference, and
finite-state channel models, graph zero-error capacity, and general finite index
coding with separate message and receiver types, zero- and vanishing-error
criteria, and fixed-field linear-encoder capacity. The latter constrains the
encoder to be linear while allowing arbitrary zero-error decoders. It is not
called linear capacity unless equivalence with linear decoders is established.
The canonical declarations use `linearEncoderSymmetricCapacity*`. Deprecated
`linearSymmetricCapacity*` aliases remain for source compatibility and do not
assert decoder linearity.

### `CapacityAtlas`

Channel-specific definitions, canonical problem claims, tests, and compact
proofs. Compatibility imports preserve the original module paths while new code
should import the `CapacityAtlasForMathlib` modules directly.

## Formal coverage and claim status

Each problem records a local coverage status:

- `none`: no local Lean declaration exists
- `definitions`: the model or reusable API is formalized
- `statement`: one or more page claims have canonical declarations

Each formal claim then records:

- a stable `id`
- a `kind`: `definition`, `achievability`, `converse`, `exact-capacity`,
  `capacity-bounds`, or `structural`
- a `status`: `stated` for definitions, `open` for an unproved named `Prop`
  definition, or `proved` when complete proof evidence is linked
- its own integer `version`

Declaration entries identify their claim with `claim_id`. Increment only the
affected claim's version when its proposition changes in a way that can
invalidate a proof. Editorial changes and API refactors that preserve the
proposition do not require an increment. This separation prevents a proved
translation or graph lemma from being presented as a proved capacity claim.

## Proof status

Proof records are independent of local coverage status and live in problem YAML.
A registered proof is either `partial` or `complete`. It must point to an
immutable Lean repository commit and identify the declaration, claim identifier,
and claim version.

## What belongs here

Keep these in the central repository:

- neutral shared definitions
- canonical channel and code models
- the proposition that constitutes the capacity problem
- tests of definitions
- short, illuminating proofs

A proof longer than approximately 25–50 lines, or one requiring meaningful
problem-specific infrastructure, should normally live in a dedicated repository.
This threshold follows the successful contribution model used by Formal
Conjectures.

## Build and review

```bash
cd lean
lake exe cache get
lake build
```

CI rejects `sorry` and `admit` tokens in all three package layers and compiles the
library against the pinned Lean and Mathlib versions. Compilation does not by
itself establish that a statement faithfully represents the informal problem,
so every claim change also needs mathematical review.
