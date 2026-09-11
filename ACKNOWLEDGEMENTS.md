# Acknowledgements and design provenance

Capacity Atlas is an independent project. It is not affiliated with or endorsed
by Google DeepMind.

The repository and website take substantial design inspiration from:

> Moritz Firsching, Paul Lezeau, Salvatore Mercuri, Miklós Z. Horváth,
> Yaël Dillies, Calle Sönne, Eric Wieser, Fred Zhang, Thomas Hubert,
> Blaise Agüera y Arcas, and Pushmeet Kohli.
> **Formal Conjectures: An Open and Evolving Benchmark for Verified Discovery
> in Mathematics.** arXiv:2605.13171, 2026.

Project repository:
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)

Capacity Atlas adapts the following ideas from Formal Conjectures:

1. **Statement-first curation.** Open and solved-but-unproved claims are theorem
   declarations with `by sorry`, so precise statements remain useful before
   complete formal proofs exist.
2. **Independent mathematical and formal-proof status.** A problem may be
   mathematically solved without a formal proof, or have partial formal results
   without being mathematically closed.
3. **Linked proof provenance.** Proofs developed in external repositories can be
   linked through immutable commit URLs. Capacity Atlas defaults to local proof
   development for reuse; external repositories remain optional.
4. **Structured declaration metadata.** Lean attributes connect declarations to
   registry records and distinguish open, solved, API, test, and locally proved
   claims.
5. **A reusable pre-upstream layer.** `CapacityAtlasForMathlib` mirrors the role
   of `FormalConjecturesForMathlib`: definitions needed to state problems can
   mature locally before being proposed upstream.
6. **Simple generated browsing.** The public interface prioritizes counts,
   facets, compact result lists, and direct access to source records.
7. **Stable benchmark snapshots.** Claim versions and immutable releases
   make later AI evaluations reproducible.

Capacity Atlas does not copy Formal Conjectures' AMS taxonomy because all entries
belong to information theory. It instead uses controlled facets for channel
model, structural features, operational quantity, and current mathematical
knowledge.

Unless a file says otherwise, no source code from Formal Conjectures is included
in Capacity Atlas. The adopted elements above are architectural patterns and
contribution conventions. Formal Conjectures remains the authoritative source
for its own code, attributes, website, and policies.

## Copied Lean entropy code

The local entropy implementation includes code extracted and adapted from the
[PFR project](https://github.com/teorth/pfr/tree/85d5879ae144170098815201491639f6e7d3c352),
by the PFR contributors, at commit
`85d5879ae144170098815201491639f6e7d3c352`. Each copied file identifies its original
source and the local changes. PFR is not a package dependency; these copies are
maintained with Capacity Atlas's pinned mathlib version.

The copied code is distributed under PFR's Apache-2.0 license, reproduced in
[LICENSES/PFR-Apache-2.0.txt](LICENSES/PFR-Apache-2.0.txt).

## Imported Lean proof developments

The following proof developments were imported from the registered external
repositories at their immutable proof commits. Local paths below are relative to
`lean/CapacityAtlasForMathlib/InformationTheory/`; individual mathematical source
filenames and declaration namespaces are preserved.

- [TomasOrtega/CapacityAtlasInputCost](https://github.com/TomasOrtega/CapacityAtlasInputCost/tree/5e6a432bc276aa4e08b7f27658daf40e029cda48),
  commit `5e6a432bc276aa4e08b7f27658daf40e029cda48`:
  `CapacityAtlasCost/` maps to `InputCost/`.
- [TomasOrtega/CapacityAtlasCompound](https://github.com/TomasOrtega/CapacityAtlasCompound/tree/1d5cbdc0a8cfb5d034facdb8d1e2473bb3c40ebe),
  commit `1d5cbdc0a8cfb5d034facdb8d1e2473bb3c40ebe`:
  `CapacityAtlasCompound/` maps to `CompoundChannel/`.
- [TomasOrtega/CapacityAtlasCausalState](https://github.com/TomasOrtega/CapacityAtlasCausalState/tree/0176a0e9fed6ec13fd2f566d9906c3ea8103d1cc),
  commit `0176a0e9fed6ec13fd2f566d9906c3ea8103d1cc`:
  `CapacityAtlasCausal/` maps to `CausalState/`.
- [TomasOrtega/CapacityAtlasFeedback](https://github.com/TomasOrtega/CapacityAtlasFeedback/tree/b35299f221ad1c17ccbafb45082c22a5379a99e9),
  commit `b35299f221ad1c17ccbafb45082c22a5379a99e9`:
  `CapacityAtlasFeedback/` maps to `Feedback/`.
- [TomasOrtega/CapacityAtlasMAC](https://github.com/TomasOrtega/CapacityAtlasMAC/tree/ec5be554b9644df94dd58190963793f3f1d1da52),
  commit `ec5be554b9644df94dd58190963793f3f1d1da52`:
  `CapacityAtlasMAC/` maps to `MultipleAccess/`.

The compound, feedback, and multiple-access repositories' root
libraries map to `Capacity.lean` in their corresponding local directories.
`CapacityAtlasCost/Capacity.lean` maps to `InputCost/Capacity.lean`.
The input-cost root import umbrella and causal-state root certificate wrapper
are omitted. Canonical claims use the substantive capacity theorems directly.
Imports are adapted to the local shared modules,
and input-cost definitions move from the problem layer into
`InformationTheory/InputCost.lean`. The common axiom audit replaces standalone
`Audit.lean` and `AuditFixtures.lean` files. External-certificate comparison code
and redundant certificate aliases are unnecessary for directly proved local claims.
Package manifests and CI are provided by this monorepo. The original immutable
proof records remain in the registry for provenance.

Repeated Fano bounds, random-coding estimates, and output-relabeling arguments
are consolidated in shared modules. Multiple-access proofs reuse sender-swap
symmetry, and causal-state laws reuse the shared product-distribution API.
These refactors preserve the registered propositions and claim versions.

These sources are by the respective proof repository contributors and are
distributed under Apache-2.0, the same license reproduced in the root
[LICENSE](LICENSE). Mathlib remains a pinned dependency.
