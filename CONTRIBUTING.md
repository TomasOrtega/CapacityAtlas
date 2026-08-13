# Contributing to Capacity Atlas

Capacity Atlas treats a channel-capacity problem as a precise, versioned research
object. Contributions should improve reliability rather than merely increase the
number of entries.

The contribution model is inspired by Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures),
particularly its statement-first convention and independent formal-proof
metadata. See [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md).

## Ways to contribute

A focused pull request can:

- add a precisely specified capacity problem
- correct a channel model, normalization, bound, date, or citation
- add a newly published achievability or converse
- improve controlled tags or research-frontier exposition
- add a canonical formal definition or claim
- register formal proof provenance
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
- `knowledge`: exact, characterized, regularized, bounds-only, or linear-encoder-only

Do not add free-form tags to a problem record. Propose a new controlled value only
when it will distinguish several entries and cannot be expressed by an existing
value. AMS classifications are intentionally not used.

## Formal verification policy

Capacity Atlas uses Lean 4 for formal verification.

- Reuse definitions in `CapacityAtlasForMathlib`.
- Put channel-specific definitions and statements in `CapacityAtlas`.
- Put metadata attributes and generator utilities in `CapacityAtlasUtil`.
- Attach `@[capacity_problem "problem-id"]` to problem-specific declarations.
- Mark declaration roles with `@[capacity_definition]`,
  `@[capacity_statement]`, or `@[capacity_shared_api]`.
- Attach `@[capacity_claim "claim-id" version]` to every registered claim
  theorem. The problem ID, claim ID, category, and version must match YAML.
- Classify formal claims independently as `open`, `solved`, `API`, or `test` and
  as formally `stated` or `proved`.
- Classify every public theorem or lemma in the problem layer as open research,
  solved research, API, test, or local formal proof. Research claims may be
  stated directly with `sorry` or proved from another admitted research claim.
- Mark a complete local proof with `@[capacity_formal_proof]` and use
  `@[capacity_test]` for tested structural claims.
- Do not introduce `sorryAx`, native-evaluation trust, or unreviewed axioms into
  `CapacityAtlasForMathlib`, `CapacityAtlasUtil`, reusable APIs, tests, or local
  formal proofs. The environment audit checks transitive dependencies, not just
  the theorem's source text.
- Increment that claim's version whenever its proposition changes in a way that
  can invalidate a formal proof.

The central repository should contain canonical claims, reusable API, tests,
and short illuminating proofs. As in Formal Conjectures' contribution policy, a
proof longer than roughly 25–50 lines should normally live elsewhere. The same
rule applies when a proof needs significant problem-specific infrastructure even
if its final theorem is short.

See [docs/lean.md](docs/lean.md) and
[docs/formal-proofs.md](docs/formal-proofs.md).

## Formal proof provenance

A linked proof record must:

- use Lean 4
- identify the exact claim proved
- name a repository, file, and declaration
- pin a 40-character commit hash
- link to that immutable commit
- name the Capacity Atlas claim identifier and version it targets

The proof repository should import a pinned Capacity Atlas commit or release
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

`make lean` builds the trusted libraries and problem library with warnings as
errors, then validates the compiled declaration registry and transitive axioms.

Generated `dist/` files are not committed.

## Licensing contributions

By submitting a contribution, you agree that:

- software and Lean contributions are provided under Apache-2.0
- atlas data and editorial prose are provided under CC-BY-4.0
- third-party material remains subject to its source license and must be clearly
  identified

Do not paste copyrighted paper text. State results in original prose and cite the
primary source.
