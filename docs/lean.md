# Lean formalization guide

The Lean library is intentionally small. It establishes common objects once, then lets channel-specific files reuse them.

## Shared modules

- `CapacityAtlas.FiniteChannel` defines finite stochastic channels and serial composition.
- `CapacityAtlas.Code` defines deterministic one-shot codes and error probabilities.
- `CapacityAtlas.Channels.Binary` defines the BSC, BEC, and binary Z-channel.
- `CapacityAtlas.Network.IndexCoding` defines multiple-unicast instances and the Sun--Jafar 11-message instance.

New shared definitions should be mathematically neutral and useful to more than one page. Do not place a second finite-channel structure inside a problem file.

## Status ladder

### `none`

No linked Lean declaration exists.

### `definitions`

The model or reusable objects compile, but the operational statement has not been encoded.

### `statement`

The exact theorem represented on the page has a faithful Lean statement. Supporting lemmas may remain open only outside the merged branch. Merged code itself may not contain placeholders.

### `partial`

A strict part of the displayed result has been proved, such as achievability but not converse, or one bound in an open interval.

### `complete`

The displayed operational capacity or capacity region is proved under the page's assumptions. Definitions alone, a finite-blocklength special case, or an analytic identity without the coding theorem is not complete.

## Build and review

```bash
cd lean
lake update
lake build
```

CI rejects textual `sorry` and `admit` tokens in source modules and compiles the library against the pinned Mathlib version. Review should also check faithfulness: compilation does not establish that a theorem formalizes the intended communication problem.

## Next shared layer

The most useful next milestone is a finite probability and information layer that supports entropy, conditional entropy, mutual information, product channels, and block codes without duplicating Mathlib abstractions. That layer should precede formalizations of the finite-DMC coding theorem and elementary exact capacities.
