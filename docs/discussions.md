# Per-problem discussions

Capacity Atlas uses GitHub Discussions as the canonical store for research
conversation, identities, edits, reactions, and moderation. The static website
has no database or account system.

## Current configuration

Discussions is enabled for `TomasOrtega/CapacityAtlas`. Problem pages provide two
working links:

- search for the thread with the stable key `capacityatlas:<problem-id>`
- start a prefilled thread in the `General` category when none exists

The GraphQL identifiers are recorded in `data/site.yaml`:

```yaml
repo_id: R_kgDOTzuIlQ
category: General
category_id: DIC_kwDOTzuIlc4DDFDj
```

## Inline comments

The giscus GitHub App is not installed on the repository, so the inline widget is
intentionally disabled rather than rendering a broken embed. To activate it:

1. Install the [giscus GitHub App](https://github.com/apps/giscus) for
   `TomasOrtega/CapacityAtlas`.
2. Set `social.giscus.enabled` to `true` in `data/site.yaml`.
3. Build the site and verify one open and one solved problem page.

No repository or category lookup is needed after installation because both IDs
are already pinned.

## Mapping

Each page uses giscus's `specific` mapping with strict matching and the stable
term:

```text
capacityatlas:<problem-id>
```

This keeps a thread attached if its problem title or website route changes.

## Moderation

Use Discussions for proof ideas, attempted constructions, questions, literature
observations, and coordination. Use Issues for actionable changes to the atlas,
formalization, or website. Use pull requests for changes to canonical data or
code.
