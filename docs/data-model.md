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

These axes are intentionally independent. For example, the Sun–Jafar instance is
mathematically open, has model `index-coding`, quantity `symmetric-capacity`, and
knowledge tags `bounds` and `linear-encoder-only`.

`linear-encoder-only` is deliberately conservative: it says the encoder is
linear over a finite field while decoders may be arbitrary zero-error maps. It
does not assert that equivalent linear decoders have been constructed.

## Operational specification

The `model` and `quantity` blocks must make the problem reconstructible without
consulting the literature. State alphabets, transition law, memory, feedback,
state knowledge, constraints, code class, error criterion, and rate
normalization.

## Bounds

Every achievability, converse, exact result, or region bound is a separate object.
A bound records its direction, relation, method, year, assumptions, and primary
references. The headline `capacity` block summarizes the current envelope but is
not a substitute for provenance.

## Formalization

`formalization.statement` records local Lean coverage. Its `claims` list gives
each proposition or definition a stable identifier, a kind, its own version, and
an explicit status. Claim kinds distinguish definitions, achievability,
converse, exact-capacity, combined capacity-bound, and structural results.
Definitions are `stated`; unproved named `Prop` definitions are `open`; and only
claims with complete local or registered external evidence are `proved`.

Declaration entries use `claim_id` when they state or prove a claim.
`formalization.proofs` records substantial external Lean proofs at immutable
commits and targets one exact claim identifier and version. Mathematical status
and formal proof status are never inferred from one another.

The Browse page reflects this independence with separate **Status** and
**Formalization** controls. `Formally stated` means at least one non-definition
claim has a local formal declaration. `Capacity claim formally proved` means an
achievability, converse, exact-capacity, or combined capacity-bound claim is
explicitly marked `proved`. A proved structural claim does not trigger that
capacity-proof filter. A formally proved bound may still belong to a
mathematically open problem.

## Discussion identity

The discussion key is derived from the permanent problem ID:

```text
capacityatlas:<problem-id>
```

Changing a page title or URL therefore does not detach its GitHub Discussion.

## Compatibility

The JSON Schema catches structural errors. The Python validator additionally
checks tag vocabulary, bibliography links, duplicate identifiers, local Lean
files and declarations, claim links and statuses, external proof commit links,
and claim-version matches.

The claim-level format replaces the former problem-wide `statement.version`.
External proof records now use `claim_id` and `claim_version` instead of `claim`
and `statement_version`; there is no implicit fallback because silently mapping
a proof to the wrong proposition would overstate formal coverage.
