# Maintainer operations

## GitHub Pages

Select **Settings → Pages → Build and deployment → Source: GitHub Actions** and
set the custom domain to `capacityatlas.org`. The main workflow validates data,
runs tests and linting, compiles Lean, uploads `dist/`, and deploys only after the
site and Lean jobs succeed.

## Discussions

GitHub Discussions and the giscus embed are enabled. The repository and
`General` category IDs are stored in `data/site.yaml`. Keep those IDs synchronized
with the configured repository and category, and verify both the inline widget
and the direct GitHub links after any change. See `docs/discussions.md`.

## Claim versions

Review every Lean claim change for semantic compatibility. Increment the
affected claim's version whenever an existing external proof might no longer
apply. Do not accept a proof record whose version differs from its target claim.

## External proofs

Require immutable commit URLs and public CI. Do not merge a branch name such as
`main` as proof evidence. Large developments remain in their own repositories.

## Releases and benchmark snapshots

Software releases use semantic versions. Benchmark snapshots should use an
immutable tag such as:

```text
benchmark-v1-lean4.32.0
```

Increment the benchmark version when problems are added or removed, a claim
changes materially, or a misformalization is corrected. Do not rewrite existing
snapshot tags.

Before release:

1. run `make check`
2. run `make lean`
3. inspect the generated home page, filters, and representative problem pages
4. verify Discussion search and creation links
5. verify the inline giscus widget on an open and a solved problem
6. update `pyproject.toml` and `CITATION.cff`
7. tag the exact deployed commit
