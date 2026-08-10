# Capacity Atlas

[![Site, data, and Lean](https://github.com/TomasOrtega/CapacityAtlas/actions/workflows/ci.yml/badge.svg)](https://github.com/TomasOrtega/CapacityAtlas/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/formalization-Lean%204-blue)](lean/)
[![Software: Apache-2.0](https://img.shields.io/badge/software-Apache--2.0-blue)](LICENSE)
[![Content: CC-BY-4.0](https://img.shields.io/badge/content-CC--BY--4.0-lightgrey)](LICENSES/CC-BY-4.0.txt)

**Capacity Atlas** is a community-maintained registry of channel capacities,
known bounds, open gaps, canonical Lean statements, and external machine-checked
proofs. The public site is [capacityatlas.org](https://capacityatlas.org/).

The repository is deliberately a registry rather than a proof monorepo. It owns
stable problem identifiers, precise communication models, controlled
information-theory tags, primary references, and versioned Lean statements.
Substantial formal proofs live in dedicated repositories and are linked by an
immutable commit.

## Current scope

The curated collection contains **32 classical and open capacity problems**,
including point-to-point channels, feedback, state information, multiple-access
and broadcast channels, relay and interference networks, wiretap channels,
zero-error information theory, arbitrarily varying channels, and index coding.

Each problem records:

- the exact model, assumptions, rate normalization, and error criterion
- the exact answer, characterization, or best known bounds
- independent controlled tags for model, features, quantity, and current knowledge
- a research-frontier explanation and concrete progress targets when open
- a versioned canonical Lean definition or statement when available
- zero or more external Lean proof records pinned to immutable commits
- a stable GitHub Discussion key of the form `capacityatlas:<problem-id>`

No AMS tags are used. The project is entirely within information theory, so its
facets describe communication models and operational quantities directly.

## Design

The architecture takes explicit inspiration from Google DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
project. Capacity Atlas adapts its statement-first registry, structured
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

GitHub Discussions is enabled. Each problem page links to a stable search and a
prefilled new thread using `capacityatlas:<problem-id>`. The repository and
`General` category GraphQL IDs are pinned in `data/site.yaml`.

The inline giscus embed is intentionally disabled because the giscus GitHub App
is not currently installed on the repository. After installation, set
`social.giscus.enabled` to `true`; no other identifiers need to be discovered.
Until then, all discussion links on the website work directly through GitHub.

See [docs/discussions.md](docs/discussions.md).

## Local development

Python 3.11 or newer is required.

```bash
python -m venv .venv
source .venv/bin/activate
python -m pip install -e '.[dev]'
make check
make serve
```

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
