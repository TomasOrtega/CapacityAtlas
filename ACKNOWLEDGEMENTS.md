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

1. **Statement-first curation.** A central repository can make precise formal
   statements useful even before complete proofs exist.
2. **Independent mathematical and formal-proof status.** A problem may be
   mathematically solved without a formal proof, or have partial formal results
   without being mathematically closed.
3. **External substantial proofs.** Longer proofs live in dedicated repositories
   and are linked through immutable commit URLs rather than copied into the
   central registry.
4. **Structured declaration metadata.** Lean attributes connect declarations to
   registry records and distinguish definitions, canonical statements, short
   proofs, and shared API.
5. **A reusable pre-upstream layer.** `CapacityAtlasForMathlib` mirrors the role
   of `FormalConjecturesForMathlib`: definitions needed to state problems can
   mature locally before being proposed upstream.
6. **Simple generated browsing.** The public interface prioritizes counts,
   facets, compact result lists, and direct access to source records.
7. **Stable benchmark snapshots.** Statement versions and immutable releases
   make later AI evaluations reproducible.

Capacity Atlas does not copy Formal Conjectures' AMS taxonomy because all entries
belong to information theory. It instead uses controlled facets for channel
model, structural features, operational quantity, and current mathematical
knowledge.

Unless a file says otherwise, no source code from Formal Conjectures is included
in Capacity Atlas. The adopted elements above are architectural patterns and
contribution conventions. Formal Conjectures remains the authoritative source
for its own code, attributes, website, and policies.
