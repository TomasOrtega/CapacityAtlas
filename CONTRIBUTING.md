# Contributing to Capacity Atlas

Capacity Atlas treats a capacity problem as a precise research object. Contributions should make the atlas more reliable, not merely larger.

## Ways to contribute

A focused contribution can:

- add a well-specified channel-capacity problem
- correct a model, bound, date, or citation
- record a newly published bound
- improve the explanation of an open gap
- add or extend a Lean formalization
- improve the generator, tests, accessibility, or documentation

Use the GitHub issue forms for preliminary discussion. Small factual corrections may go directly to a pull request.

## Evidence standard

Prefer primary sources. Every mathematical bound must identify:

- its exact relation
- whether it is achievability, converse, exact, linear-only, or a region bound
- all assumptions under which it holds
- the method at a useful level of specificity
- a primary reference

Do not infer a currently best bound from an uncited plot, a secondary survey, or an unverified AI output. When sources disagree, describe the disagreement in the entry or issue rather than silently choosing one.

## Problem files

Each problem lives in `data/problems/<id>.yaml`. Start from `docs/problem-template.yaml`. The identifier is permanent, lowercase, and hyphenated. The filename must match it.

Run:

```bash
make validate
make test
make build
```

The JSON Schema catches structure errors. The Python validator additionally checks cross-references, duplicate bound identifiers, Lean paths, and named Lean declarations.

## Lean policy

Capacity Atlas currently accepts only Lean 4 formalizations.

- Reuse definitions under `lean/CapacityAtlas` instead of redeclaring channel models.
- Put generally useful objects in shared modules.
- Put problem-specific definitions in a channel or network module.
- Do not use `sorry`, `admit`, or unreviewed axioms.
- Do not mark a problem `complete` unless the operational theorem represented on the page is proved.
- A compiled transition kernel normally merits `definitions`, not `statement` or `complete`.
- Record every public declaration in the problem YAML.

See `docs/lean.md` for the module design and status criteria.

## Writing style

Write for an information-theory researcher who has not read the source paper recently. Define the channel before introducing notation. State assumptions explicitly. Explain the mechanism behind a bound, not only its theorem number. Keep the prose direct and avoid unnecessary notation.

## Pull requests

Keep pull requests narrow. The description should state:

- what changed
- which claims were checked
- which source supports each mathematical update
- what local checks passed
- whether the formalization status changed

A maintainer may ask for a smaller change, a primary citation, or a more exact model before merging.

## Generated files

Do not commit `dist/`. CI rebuilds it from the source data and templates.
