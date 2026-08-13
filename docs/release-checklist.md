# Release checklist

- Run `uv run --locked capacity-atlas validate`, the complete Python tests,
  `prek -a --quiet`, and the production site build.
- Run `lake --wfail build CapacityAtlasForMathlib CapacityAtlasUtil` and
  `lake --wfail build CapacityAtlas`.
- Run `lake exe capacity_audit`, then pass its JSON report to
  `capacity-atlas validate --lean-report`.
- Confirm each claim proposition, `capacity_claim` identity, YAML identity, and
  version agree; materially changed propositions must increment their version.
- Confirm CI actions use full commit SHAs, build jobs have read-only contents
  permission, deployment alone can write Pages and request an ID token, and all
  jobs have timeouts.
- Confirm the complete Apache-2.0 and CC-BY-4.0 legal texts remain present.
- Check every new mathematical claim against a primary source.
- Inspect the home page, combined filters, one solved entry, and one open entry.
- Verify custom-domain deployment and HTTPS.
- Verify Discussion search and creation links.
- Verify one embedded Discussion when giscus is enabled.
- Create an immutable benchmark tag when the problem set or formal claims changed.
