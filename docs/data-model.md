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
knowledge tags `bounds` and `linear-only`.

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

`formalization.statement` records the local canonical Lean work and its version.
`formalization.proofs` records substantial external Lean proofs at immutable
commits. Mathematical status and formal proof status are never inferred from one
another.

The Browse page reflects this independence with separate **Status** and
**Formalization** controls. `Lean formalization available` means the local
statement status is not `none`. `Formally verified claim` means at least one
registered Lean proof has status `complete`. A formally verified claim may
establish a bound or another component of an open problem rather than solve the
entire capacity problem.

## Discussion identity

The discussion key is derived from the permanent problem ID:

```text
capacityatlas:<problem-id>
```

Changing a page title or URL therefore does not detach its GitHub Discussion.

## Compatibility

The JSON Schema catches structural errors. The Python validator additionally
checks tag vocabulary, bibliography links, duplicate identifiers, local Lean
files and declarations, external proof commit links, and statement-version
matches.
