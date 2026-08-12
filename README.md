# Capacity Atlas

[![Site, data, and Lean](https://github.com/TomasOrtega/CapacityAtlas/actions/workflows/ci.yml/badge.svg)](https://github.com/TomasOrtega/CapacityAtlas/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/formalization-Lean%204-blue)](lean/)
[![Software: Apache-2.0](https://img.shields.io/badge/software-Apache--2.0-blue)](LICENSE)
[![Content: CC-BY-4.0](https://img.shields.io/badge/content-CC--BY--4.0-lightgrey)](LICENSES/CC-BY-4.0.txt)

**Capacity Atlas** is a community-maintained registry of channel capacities,
known bounds, open gaps, canonical Lean claims, and external machine-checked
proofs. The public site is [capacityatlas.org](https://capacityatlas.org/).

The repository is deliberately a registry rather than a proof monorepo. It owns
stable problem identifiers, precise communication models, controlled
information-theory tags, primary references, and versioned formal claims.
Substantial formal proofs live in dedicated repositories and are linked by an
immutable commit.

## Design

The architecture takes explicit inspiration from Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
project. Capacity Atlas adapts its claim-level registry, structured
declaration metadata, external formal-proof links, separation of reusable
definitions from problem statements, benchmark-oriented versioning, and compact
browse interface. Capacity Atlas uses a channel-specific taxonomy and a stricter
no-placeholder policy in the central Lean tree.

See [ACKNOWLEDGEMENTS.md](ACKNOWLEDGEMENTS.md) for the exact attribution and
citation.

## Lean layout

```text
lean/
├── CapacityAtlas/              channel-specific definitions and statements
├── CapacityAtlasForMathlib/    reusable information-theory infrastructure
└── CapacityAtlasUtil/          registry metadata attributes and utilities
```

The central repository accepts only Lean 4 formalizations. It keeps shared API,
canonical statements, tests, and short illuminating proofs. A proof longer than
roughly 25–50 lines, or one needing significant problem-specific infrastructure,
should normally live in a separate repository. External proof repositories
should import a pinned Capacity Atlas release or commit and prove the registered
statement rather than restating it independently.

Lean status is shown on each problem page rather than in a separate site tab.
See [docs/lean.md](docs/lean.md) and
[docs/external-proofs.md](docs/external-proofs.md).

## Discussions

GitHub Discussions and giscus are enabled. Every problem page embeds the thread
identified by `capacityatlas:<problem-id>`, with strict matching so that titles
or routes can change without detaching the conversation. The page also retains
direct links to find or start the same Discussion on GitHub.

The repository and `General` category GraphQL IDs are pinned in
`data/site.yaml`. Discussion content, identities, reactions, edits, and
moderation remain entirely in GitHub; the static website has no comment database
or account system.

See [docs/discussions.md](docs/discussions.md).

## Local development

Python 3.11 or newer and
[uv](https://docs.astral.sh/uv/getting-started/installation/) are required.

```bash
uv sync --locked
uv run --locked prek install
make check
make serve
```

The installed prek hook applies Ruff fixes and formatting, checks repository
hygiene, and verifies that `uv.lock` stays synchronized before each commit.

Open `http://localhost:8000`.

Build the Lean library with:

```bash
cd lean
lake exe cache get
lake build
```

## Repository layout

```text
data/problems/       one YAML record per capacity problem
data/tags.yaml       controlled information-theory facets
data/references.yaml primary bibliography records
schema/               machine-checkable data schema
site/                 small static templates, CSS, and JavaScript
src/capacity_atlas/   loader, validator, and site generator
lean/                 shared definitions and canonical Lean records
docs/                 contribution and maintenance guides
```

## Contributing

Start from [docs/problem-template.yaml](docs/problem-template.yaml). Every
mathematical claim should cite a primary source and state its assumptions. Lean
contributions must reuse shared definitions, contain no `sorry` or `admit`, and
identify the stable problem ID. See [CONTRIBUTING.md](CONTRIBUTING.md).

## Licensing

- Software, Lean source, schemas, templates, stylesheets, scripts, and CI are
  licensed under **Apache-2.0**.
- Curated problem data, bibliographic metadata, and editorial documentation are
  licensed under **CC-BY-4.0**, unless otherwise noted.

The root `LICENSE` is Apache-2.0. License notices, legal-text links, and scope
details are in [LICENSES](LICENSES/) and [NOTICE](NOTICE).
