# Capacity Atlas data model

Each file in `data/problems/` represents one operational capacity question. The
file name and permanent `id` agree.

## Independent axes

`status` records mathematical status: `open`, `partially-solved`, or `solved`.

`tags` contains four controlled axes from `data/tags.yaml`:

- `model`: communication topology or channel family
- `features`: structural assumptions and phenomena
- `quantity`: the rate object to be determined
- `knowledge`: the form of the current answer

These axes are intentionally independent. A problem can be mathematically open
while having formally proved partial bounds.

`linear-encoder-only` is deliberately conservative: the encoder is linear over
a finite field while decoders may be arbitrary zero-error maps. It does not
assert that equivalent linear decoders have been constructed.

## Operational specification

The `model` and `quantity` blocks must make the problem reconstructible without
consulting the literature. State alphabets, transition law, memory, feedback,
state knowledge, constraints, code class, error criterion, and rate
normalization.

## Bounds

Every achievability, converse, exact result, or region bound is a separate
object. A bound records its direction, relation, method, year, assumptions, and
primary references. The headline `capacity` block summarizes the current
envelope but is not a substitute for provenance.

## Formalization

`formalization.status` is `none`, `definitions`, or `stated`. Definitions-only
records keep concrete models and shared infrastructure without presenting an
unfaithful problem claim.

Each item in `formalization.claims` has:

- a stable `id` and integer `version`
- a `kind`: `achievability`, `converse`, `exact-capacity`, `capacity-bounds`, or
  `structural`
- a `category`: `open`, `solved`, `API`, or `test`
- an independent `formal_status`: `stated` or `proved`
- a precise description

Files identify a declaration and its role: `definition`, `claim`, `test`, or
`API`. Claim declarations link through `claim_id`. Each claim theorem carries
the same identity and version in `@[capacity_claim "claim-id" version]` metadata.

`formalization.proofs` records formal proof provenance at immutable commits and
targets one exact claim identifier and version. A complete local proof or linked
proof is required before a claim may be marked `proved`. Mathematical status,
claim category, and formal-proof status are never inferred from one another.
A locally proved claim is marked `capacity_formal_proof` and has no transitive
`sorryAx` dependency. A locally stated claim may contain `sorry` directly or
derive from an admitted research premise; either way, its compiled declaration
transitively depends on `sorryAx` unless a complete linked proof supplies its
provenance.

The Browse page reflects this independence with separate **Status** and
**Formalization** controls. **Formally stated** means at least one
non-definition claim has a local declaration. **Formally proved** means an
achievability, converse, exact-capacity, or combined capacity-bound claim is
explicitly marked `proved`. A proved structural claim does not trigger that
filter.

## Discussion identity

The discussion key is derived from the permanent problem ID:

```text
capacityatlas:<problem-id>
```

Changing a page title or URL therefore does not detach its GitHub Discussion.

## Validation

The JSON Schema catches structural errors. The Python validator additionally
checks tag vocabulary, bibliography links, duplicate identifiers, local files
and declarations, category attributes, proof links, and the local-proof trust
boundary. With the compiled Lean report, it also enforces a one-to-one mapping
between YAML claims and tagged declarations and compares problem ID, claim ID,
category, and version. Duplicate and orphan claims fail validation.
