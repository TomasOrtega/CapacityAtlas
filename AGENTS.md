# Instructions for automated contributors

Capacity Atlas is a curated mathematical registry. Correctness and provenance
matter more than coverage.

1. Read `CONTRIBUTING.md`, `docs/data-model.md`, and `docs/lean.md` before editing.
2. Use primary sources for mathematical claims. Never invent a bound, date,
   theorem number, DOI, or attribution.
3. Preserve permanent problem IDs and discussion terms.
4. Use only values declared in `data/tags.yaml`. Do not add AMS tags.
5. Treat mathematical status, formal claim status, and formal-proof status as
   independent fields.
6. Increment a claim version only when its proposition changes materially.
7. Keep substantial Lean proofs in external repositories. Link immutable commits.
8. Do not introduce `sorry`, `admit`, unreviewed axioms, hidden network calls, or
   generated artifacts.
9. Keep the website static and dependency-light.
10. Run the complete validation, tests, lint, site build, and Lean build.

When AI assisted a change, disclose that assistance in the pull request. Human
review remains required for statement faithfulness and literature claims.
