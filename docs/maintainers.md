# Maintainer operations

## GitHub Pages

In repository settings, choose **Pages → Build and deployment → Source: GitHub Actions**. The `Site, Lean, and Pages` workflow validates and tests the site, builds Lean, uploads `dist/`, and deploys only after both jobs succeed on `main`.

The configured base path is `/CapacityAtlas`. A custom domain can later be introduced by changing `canonical_url` and `base_url` in `data/site.yaml` and adding a generated `CNAME` file.

## Social features

The initial site uses GitHub issues and pull requests as its social layer. Each problem page creates a prefilled discussion issue. This avoids a second account system and works before GitHub Discussions is enabled.

To add embedded comments later:

1. Enable GitHub Discussions.
2. Install and configure giscus for this public repository.
3. Add the repository and category IDs to `data/site.yaml`.
4. Render the giscus script only when the feature flag is enabled.

Keep issue-based discussion links as a no-JavaScript fallback.

## Releases

Before tagging a release:

1. run `make check`
2. run `make lean`
3. inspect the generated site at mobile and desktop widths
4. update the version in `pyproject.toml` and `CITATION.cff`
5. tag the exact commit deployed to Pages
