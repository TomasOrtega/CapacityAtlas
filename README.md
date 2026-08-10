# Capacity Atlas

[![Site and data](https://github.com/TomasOrtega/CapacityAtlas/actions/workflows/ci.yml/badge.svg)](https://github.com/TomasOrtega/CapacityAtlas/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/formalization-Lean%204-blue)](lean/)
[![License: MIT](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE)

Capacity Atlas is a community-maintained atlas of channel capacities, open gaps, and Lean formalizations. Each entry fixes the complete channel model, names the operational quantity, records exact results or best known bounds, explains the remaining research frontier, and distinguishes definitions from proved theorems.

The repository is the source of truth. A small Python program validates the YAML data and builds a static website. GitHub Actions checks the data, tests the generator, compiles every Lean file, and deploys the generated pages.

## What is included

The initial release contains:

- 12 curated classical channel and network problems
- exact-capacity, capacity-region, and open-bound entries
- a searchable and filterable problem index
- detailed problem pages with assumptions, bound provenance, timelines, and concrete research targets
- static JSON endpoints for every problem
- a JSON Schema for reviewed data contributions
- a shared Lean library for finite channels, one-shot codes, binary channels, and multiple-unicast index coding
- GitHub issue forms and pull-request workflows for community contributions

Only Lean formalizations are accepted at present. A problem page uses a five-level status ladder: not started, definitions, statement, partial proof, and complete proof.

## Local development

Python 3.11 or newer is required.

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install -e '.[dev]'
make check
make serve
```

Then open `http://localhost:8000`. Both local development and the production custom domain use root-relative links.

To check the Lean library:

```bash
cd lean
lake update
lake build
```

The Lean toolchain and Mathlib release are pinned in `lean/lean-toolchain` and `lean/lakefile.toml`.

## Repository layout

```text
data/problems/       one YAML file per capacity problem
data/references.yaml shared bibliography records
schema/               machine-checkable data schema
site/templates/       Jinja templates
site/static/          plain CSS and JavaScript
src/capacity_atlas/   validator and static-site generator
lean/CapacityAtlas/   shared Lean definitions and formalizations
tests/                generator and data tests
docs/                 contributor and maintainer documentation
```

## Add or update a problem

1. Copy `docs/problem-template.yaml` into `data/problems/<problem-id>.yaml`.
2. State the model and operational criterion precisely.
3. Add every bound as a separate record with primary references.
4. Link only Lean files under `lean/`.
5. Run `make check` and `make lean`.
6. Open a focused pull request.

See [CONTRIBUTING.md](CONTRIBUTING.md) and [docs/data-model.md](docs/data-model.md) for the review standard.

## Deployment

The `ci.yml` workflow builds and deploys the static site from `main`. The repository uses GitHub Pages with **GitHub Actions** as its source and `capacityatlas.org` as its custom domain. The domain is stored in `data/site.yaml`; CI writes that value to `dist/CNAME` before uploading the Pages artifact. No database, server process, or deployment secret is required.

The public site is <https://capacityatlas.org/>.

## Scope

The first version favors a small, auditable classical-information-theory corpus. It does not yet attempt to cover every channel model, quantum channels, or every historical bound. The data model is broad enough to expand, but new entries should be curated rather than scraped.

## License and citation

Code, data, and Lean sources are available under the [MIT License](LICENSE). Citation metadata is in [CITATION.cff](CITATION.cff).
