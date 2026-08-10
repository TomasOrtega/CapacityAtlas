# Per-problem discussions

Capacity Atlas uses GitHub Discussions as the canonical store for research
conversation, identities, edits, reactions, and moderation. The static website
has no database or account system.

## Current configuration

Discussions and the giscus GitHub App are enabled for
`TomasOrtega/CapacityAtlas`. Each problem page:

- embeds the corresponding GitHub Discussion inline
- links to a search for the stable key `capacityatlas:<problem-id>`
- links to a prefilled new thread in the `General` category when none exists

The pinned identifiers live in `data/site.yaml`:

```yaml
giscus:
  enabled: true
  repo: TomasOrtega/CapacityAtlas
  repo_id: R_kgDOTzuIlQ
  category: General
  category_id: DIC_kwDOTzuIlc4DDFDj
```

## Mapping

Each page uses giscus's `specific` mapping with strict matching and the stable
term:

```text
capacityatlas:<problem-id>
```

This keeps the conversation attached if a problem title or website route
changes. When no matching thread exists, giscus creates it when a visitor first
comments or reacts.

## Maintenance

If the repository or Discussion category changes, update the name and GraphQL ID
together in `data/site.yaml`. After any configuration change, build the site and
check the rendered `data-repo`, `data-repo-id`, `data-category`,
`data-category-id`, `data-term`, and `data-strict` attributes on a representative
problem page.

Keep the direct GitHub links even while the embed is active. They provide a
usable fallback when scripts are blocked and let contributors participate without
using the embedded interface.

## Moderation

Use Discussions for proof ideas, attempted constructions, questions, literature
observations, and coordination. Use Issues for actionable changes to the atlas,
formalization, or website. Use pull requests for changes to canonical data or
code.
