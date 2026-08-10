# Release checklist

Use this checklist before tagging a Capacity Atlas release.

- Validate every YAML entry and bibliography reference with `make validate`.
- Run the Python test suite and static-site build with `make check`.
- Compile the complete Lean library with `make lean`.
- Confirm that no formalization status exceeds what the linked declarations prove.
- Review newly changed mathematical claims against their primary sources.
- Inspect the generated home page, problem index, one solved entry, and one open entry.
- Confirm that the GitHub Pages deployment completed from the tagged commit.

The GitHub Actions workflow enforces the automated items. Mathematical faithfulness and conservative formalization labels remain review responsibilities.
