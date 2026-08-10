# Maintainer operations

## GitHub Pages

In repository settings, choose **Pages → Build and deployment → Source: GitHub Actions**. The `Site, Lean, and Pages` workflow validates and tests the site, builds Lean, uploads `dist/`, and deploys only after both jobs succeed on `main`.

The production site is rooted at `https://capacityatlas.org/`. `data/site.yaml` records both the canonical URL and the custom domain. The static-site generator writes `dist/CNAME` from that configuration, and the deployment workflow builds with no project subpath.

If the domain changes later, update `canonical_url` and `custom_domain` in `data/site.yaml`, update public metadata such as `CITATION.cff`, and change the custom domain in **Settings → Pages**.

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
