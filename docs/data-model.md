# Capacity problem data model

The canonical object in Capacity Atlas is a **capacity problem**, not merely a named channel. The same transition law can induce different problems under different feedback, state-information, cost, code-class, or error assumptions.

## Required sections

### Identity and status

`id`, `title`, `status`, `category`, `updated`, and `summary` provide stable discovery metadata. Use `solved` only when the displayed operational quantity is completely characterized under the listed assumptions.

### Model

`model` specifies the input alphabet, output alphabet, transition law, and assumptions. Assumptions should include memorylessness, information available to terminals, cost constraints, feedback, common randomness, and code restrictions when relevant.

### Quantity

`quantity` names the object being determined, its symbol, units, and operational criterion. Examples include Shannon capacity, zero-error capacity, symmetric capacity, secrecy capacity, and a capacity region.

### Capacity display

`capacity.kind` is one of:

- `exact`: a closed expression or exact number
- `characterization`: a complete optimization formula
- `bounds`: an unresolved lower/upper gap
- `region`: a complete capacity-region description

`capacity.display` is the concise expression shown on cards. Open numerical problems should also provide `lower` and `upper` so the page can render the gap.

### Bounds

Each bound is a separate, citable record. Its `direction` distinguishes achievability, converse, exactness, inner or outer regions, and linear-only exact results. Do not combine historically or mathematically distinct bounds into one row.

### Timeline and frontier

A timeline records substantive changes in knowledge, not every paper that mentioned the problem. An open entry should explain the central question, the actual bottleneck, and concrete results that would count as progress.

### Formalization

The formalization record links to Lean declarations and uses the status ladder described in `docs/lean.md`. Non-Lean links are rejected by the validator.

## References

Problem files refer to keys in `data/references.yaml`. Use a durable publisher, DOI, arXiv, or institutional URL. Add each source once and reuse it.

## Validation

Run `capacity-atlas validate`. In addition to JSON Schema validation, it checks:

- unique problem and bound identifiers
- category and bibliography references
- filename and identifier agreement
- Lean-only formalization language
- Lean paths constrained to `lean/`
- existence of each linked file
- existence of each named declaration in its linked file
