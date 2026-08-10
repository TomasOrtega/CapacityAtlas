# Contributing to Capacity Atlas

Capacity Atlas treats a channel-capacity problem as a precise, versioned research
object. Contributions should improve reliability rather than merely increase the
number of entries.

The contribution model is inspired by Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures),
particularly its separation of statements from substantial external proofs and
its structured formal-proof metadata. See [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md).

## Ways to contribute

A focused pull request can:

- add a precisely specified capacity problem
- correct a channel model, normalization, bound, date, or citation
- add a newly published achievability or converse
- improve controlled tags or research-frontier exposition
- add a canonical Lean definition or statement
- register a substantial external Lean proof
- improve the generator, tests, accessibility, or documentation

Use Discussions for research conversation. Use Issues for actionable corrections,
missing entries, formalization work, or site bugs. Canonical changes arrive by
pull request.

## Mathematical evidence

Prefer primary sources. Every bound must identify:

- its exact relation and direction
- all assumptions and parameter ranges
- the code class and error criterion
- its proof method at a useful level of specificity
- a primary reference

Do not infer a best-known bound from an uncited plot, a secondary survey, or an
unverified AI output. If sources disagree, record the disagreement rather than
silently choosing one.

## Controlled tags

Every problem uses four independent axes from `data/tags.yaml`:

- `model`: communication topology or channel family
- `features`: structural assumptions and phenomena
- `quantity`: operational rate object
- `knowledge`: exact, characterized, regularized, bounds-only, or linear-only

Do not add free-form tags to a problem record. Propose a new controlled value only
when it will distinguish several entries and cannot be expressed by an existing
value. AMS classifications are intentionally not used.

## Lean policy

Capacity Atlas currently accepts only Lean 4.

- Reuse definitions in `CapacityAtlasForMathlib`.
- Put channel-specific definitions and statements in `CapacityAtlas`.
- Put metadata attributes and generator utilities in `CapacityAtlasUtil`.
- Attach `@[capacity_problem "problem-id"]` to problem-specific declarations.
- Mark roles with `@[capacity_definition]`, `@[capacity_statement]`,
  `@[capacity_short_proof]`, or `@[capacity_shared_api]`.
- Do not use `sorry`, `admit`, or unreviewed axioms.
- Increment the statement version whenever the proposition changes in a way that
  can invalidate an external proof.

The central repository should contain canonical statements, reusable API, tests,
and short illuminating proofs. As in Formal Conjectures' contribution policy, a
proof longer than roughly 25–50 lines should normally live elsewhere. The same
rule applies when a proof needs significant problem-specific infrastructure even
if its final theorem is short.

See [docs/lean.md](docs/lean.md) and
[docs/external-proofs.md](docs/external-proofs.md).

## External proofs

An external proof record must:

- use Lean 4
- identify the exact claim proved
- name a repository, file, and declaration
- pin a 40-character commit hash
- link to that immutable commit
- name the Capacity Atlas statement version it targets

The external repository should import a pinned Capacity Atlas commit or release
and prove the canonical proposition directly whenever possible.

## Problem files

Each problem lives at `data/problems/<id>.yaml`. The identifier is permanent,
lowercase, and hyphenated. Start from `docs/problem-template.yaml`.

Set up the locked development environment and Git hooks once:

```bash
make install
```

Run:

```bash
make lint
make validate
make test
make build
make lean
```

Generated `dist/` files are not committed.

## Licensing contributions

By submitting a contribution, you agree that:

- software and Lean contributions are provided under Apache-2.0
- atlas data and editorial prose are provided under CC-BY-4.0
- third-party material remains subject to its source license and must be clearly
  identified

Do not paste copyrighted paper text. State results in original prose and cite the
primary source.
