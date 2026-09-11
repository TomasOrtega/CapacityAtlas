# Architecture

Capacity Atlas has one authoritative data layer and several generated views:

```text
problem YAML ─┬─ static website
              ├─ JSON API
              └─ faceted problem index

Lean source ──── shared definitions, canonical statements, and formal proofs

external repos ─ optional immutable proof records

GitHub Discussions ─ per-problem conversation
```

The site generator is intentionally small: Python, Jinja, plain CSS, and plain
JavaScript. There is no application server, database, or front-end framework.

## Proof development

The monorepo is the default home for Lean definitions, lemmas, proofs, and their
supporting infrastructure. Shared development makes results reusable across
problems and checks them against one pinned toolchain and Mathlib version.
Substantial proofs belong here too; their size does not require a separate
repository.

Reusable proof developments live in `CapacityAtlasForMathlib`, and registered
claim theorems in `CapacityAtlas` import them. The imported input-cost,
compound-channel, causal-state, feedback, and multiple-access proofs build and
run through the same axiom audit as the rest of the shared library. Original
immutable proof records remain available as historical provenance.

Contributors may use external repositories when they prefer independent
development, dependencies, or release schedules. An external repository proves
a pinned Capacity Atlas statement and supplies an immutable commit record.
Both local and external developments may provide independent proofs of the same
claim.

## Design provenance

The separation of registry metadata, statements, and proof status, the
`ForMathlib` layer, formal-proof links, and compact browse model are explicitly
inspired by Google DeepMind's Formal Conjectures. Capacity Atlas specializes
these patterns to channel-capacity problems and replaces broad mathematical
subject tags with information-theory facets.
