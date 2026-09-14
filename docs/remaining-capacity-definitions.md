<!-- Copyright 2026 The Capacity Atlas Authors. SPDX-License-Identifier: CC-BY-4.0 -->

# Capacity definitions and proof-task contracts

This is a statement-first preparation of the ordered 50-problem campaign. The
first eight capacity proofs and the original Sun–Jafar statements are preserved.
All new research theorem bodies remain `by sorry`. The shared definition layer
has no admitted terms. Small structural regression tests are not capacity proofs.

## Start with the right claims

`capacity-backlog.json` separates `target_claims` from `context_claims`.
Completion requires every target to have a checked proof. Convenience aggregates,
unselected stronger bounds, and open conjectures are not prerequisites.
The `initial_state` fields are historical snapshots, not live completion status.
Use the canonical YAML and compiled audit for live proof status.

For Sun–Jafar, the four published linear/unrestricted bounds are the targets.
The open unrestricted exact-capacity conjecture is context only. `target_claims`
in `capacity_atlas.backlog` rejects an open conjecture selected as a literature task.

The no-feedback trapdoor task selects the analytic interval [1/2, log2(3/2)].
Its decimal bounds 0.572 and 0.5765 are explicitly deferred in the manifest.
The primitive-relay task selects CF and cut set, not the stronger TU converse.
The deletion upper bound retains its d >= 16/25 restriction. Numerical
certificates are still required by the eventual proofs.

## One proof target per bound

Inner/outer bounds and relay DF/CF/converse targets have independent identifiers,
versions, and proof statuses. The old conjunctions remain as context for compatibility.
Every new claim lists `bound_ids`, checked against actual literature-bound records.
The MIMO task now includes optimizer attainment and a water-filling witness,
not only equality with a covariance supremum. Zero-gain modes and zero channels
are explicitly handled in the water-level predicate.

## Gaussian constraints

`gaussian-power-conventions.json` records the exact predicate and averaging domain
for all ten Gaussian models, with matching sentences in each model record.

| Model | Constraint domain |
|---|---|
| AWGN, MIMO, fading | Block-average energy bounded for every message |
| MAC | A separate bound for every local message of each sender |
| Broadcast | A bound for every private-message pair |
| Wiretap | A bound for every message and private seed |
| Dirty paper | For every message, expected energy over the entire iid state word |
| Feedback AWGN | Expected energy over uniform message and induced Gaussian noise |
| Feedback MAC | Separate expected energies over independent messages and induced noise |
| Peak-amplitude Gaussian | Absolute amplitude bound for every message and coordinate |

Expected-energy predicates include integrability where needed. None of the
feedback constraints is silently made pathwise. Wiretap leakage is unnormalized.
An alternative message-averaged AWGN power model is named separately, with an
explicit unproved equivalence obligation. It does not redefine the registered model.

## Interfaces to establish before reusing proofs

`interface-obligations.json` names exact Lean propositions in
`CapacityAtlas.Obligations.Interfaces`. They are *definitions of propositions*,
not theorems, proof terms, or assumptions of any capacity claim. Their status is
`specified-unproved`. A model's `interface_obligations` are its required bridge tasks.

These include rate-closure and capacity bridges to the existing DMC definition,
channel/conditional-information bridges, finite-state path-sum and one-step
identities, feedback causality, relay/MAC/two-way likelihood normalization,
scalar/vector MIMO equivalence, and broadcast max-error versus joint-error bounds.
The alternate AWGN power-convention bridge is optional because the catalogue now
specifies the selected code class without claiming that equivalence.

The existing finite joint-law constructor now lives in
`FiniteDistribution/Joint.lean` with unchanged declaration names. Basic information
adapters no longer import coding/converse modules. Covariance uses Mathlib's
`Matrix.PosSemidef` and `Matrix.trace`.

Finite-state error is computed from a normalized chronological `historyLaw` and
its output marginal. The raw hidden-path sum remains available, but equality to
the normalized law is a named obligation. Other raw causal likelihoods have
explicit normalization obligations rather than an implied proof of normalization.

## Verification and limitations

`CapacityAtlas.Tests.ModelSanity` checks the real AWGN factor, distinct power
conventions, scalar MIMO output/power/objective reductions, water-filling examples,
finite-state normalization, a one-step path-sum reduction, a feedback future-noise
regression, and exact index-coding side-information sets. These are kernel-checked
structural tests with no admitted dependencies.

Python tests check the task contract, source links, versions, and imports. They do
not establish statement faithfulness. The former faithfulness-whitelist test is
now named as an inventory test. Literature and mathematical review remain required.

```bash
make check
make lean
```

No CI audit rule is weakened. A material proposition change requires a version
increment, including a change through a referenced operational definition.
