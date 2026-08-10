# Per-problem discussions

Capacity Atlas embeds GitHub Discussions through giscus. GitHub remains the
canonical store for comments, identities, edits, reactions, and moderation. The
static website has no database or account system.

## One-time repository setup

1. Open **Settings → General → Features** and enable **Discussions**.
2. Create an open-ended category named **Capacity Problems**.
3. Install the giscus GitHub App for `TomasOrtega/CapacityAtlas`.
4. Use the giscus configuration page to obtain the repository ID and category ID.
5. Edit `data/site.yaml`:

```yaml
social:
  discussions_enabled: true
  giscus:
    enabled: true
    repo: TomasOrtega/CapacityAtlas
    repo_id: R_...
    category: Capacity Problems
    category_id: DIC_...
```

## Mapping

Each page uses giscus's `specific` mapping with strict matching and the stable
term:

```text
capacityatlas:<problem-id>
```

This avoids collisions and keeps the thread attached if a title or route changes.
The page also links to a GitHub Discussions search for the same term.

## Moderation

Use Discussions for research ideas, attempted proofs, questions, literature
observations, and coordination. Use Issues for actionable changes to the atlas,
formalization, or website. Use pull requests for canonical data or code changes.
