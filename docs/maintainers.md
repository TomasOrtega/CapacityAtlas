# Maintainer operations

## GitHub Pages

Select **Settings → Pages → Build and deployment → Source: GitHub Actions** and
set the custom domain to `capacityatlas.org`. The main workflow validates data,
runs tests and linting, compiles Lean, uploads `dist/`, and deploys only after the
site and Lean jobs succeed.

## Discussions

Follow `docs/discussions.md`. Keep the giscus repository and category IDs in
`data/site.yaml`. The category name and IDs are infrastructure configuration, not
problem data.

## Statement versions

Review every Lean statement change for semantic compatibility. Increment the
problem's statement version whenever an existing external proof might no longer
apply. Do not accept a proof record whose version differs from the statement.

## External proofs

Require immutable commit URLs and public CI. Do not merge a branch name such as
`main` as proof evidence. Large developments remain in their own repositories.

## Releases and benchmark snapshots

Software releases use semantic versions. Benchmark snapshots should use an
immutable tag such as:

```text
benchmark-v1-lean4.32.0
```

Increment the benchmark version when problems are added or removed, a statement
changes materially, or a misformalization is corrected. Do not rewrite existing
snapshot tags.

Before release:

1. run `make check`
2. run `make lean`
3. inspect the generated home, browse, open-problem, solved-problem, and Lean pages
4. verify giscus on one problem when enabled
5. update `pyproject.toml` and `CITATION.cff`
6. tag the exact deployed commit
