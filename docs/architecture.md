# Architecture

Capacity Atlas has one authoritative data layer and several generated views:

```text
problem YAML ─┬─ static website
              ├─ JSON API
              └─ faceted problem index

Lean source ──── canonical definitions and statements shown on problem pages

external repos ─ immutable proof records

GitHub Discussions ─ per-problem conversation
```

The site generator is intentionally small: Python, Jinja, plain CSS, and plain
JavaScript. There is no application server, database, or front-end framework.

## Why proofs are external

Coding theorems, converses, and computational certificates can grow into large
projects with their own dependencies and release schedules. Keeping them outside
the registry bounds CI cost, permits several independent proofs, and prevents one
problem from dominating the central repository. The external repository proves a
pinned Capacity Atlas statement and returns an immutable commit record.

## Design provenance

The registry/statement/proof split, `ForMathlib` layer, formal-proof links, and
compact browse model are explicitly inspired by Google DeepMind's Formal
Conjectures. Capacity Atlas specializes these patterns to channel-capacity
problems and replaces broad mathematical subject tags with information-theory
facets.
