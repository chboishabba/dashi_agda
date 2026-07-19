# Wikidata ternary epistemic composition

This slice formalises the narrow claim needed for the Wikidata Ontology Working Group discussion: unresolved knowledge must remain representable during deterministic composition rather than being forced into a Boolean branch.

## What is proved

`DASHI.Ontology.EpistemicTrit` defines three scoped evidence states:

- `supported`
- `unresolved`
- `contradicted`

Its consensus operator is proved idempotent, commutative, and associative. Unresolved input is absorbing, and direct support/contradiction disagreement composes to `unresolved`. Two explicit Boolean forcing policies are also shown to lose information by collision: one identifies unresolved with supported; the other identifies unresolved with contradicted.

`DASHI.Ontology.ContextualClaimComposition` lifts this algebra pointwise over an arbitrary qualifier axis and accumulates source references. It proves the algebraic laws pointwise and provides an axis-extension operation. Existing coordinates are preserved definitionally, while newly introduced qualifier coordinates begin unresolved unless evidence is supplied.

`DASHI.Ontology.WikidataEpistemicBridge` provides a deliberately small adapter boundary for statement identity, qualifier-indexed state, source references, and rank metadata. Rank is explicitly not promoted to a truth value. Confidence is attached to the complete response assessment and is proved not to rewrite per-clause epistemic states.

## What is not claimed

This does not redefine Wikidata semantics, treat preferred/normal/deprecated rank as true/uncertain/false, infer evidence quality from references, or claim that confidence scores are calibrated probabilities. Those require separate data-model, provenance, calibration, and policy layers.

## DASHI / SensibLaw interpretation

The implemented theorem surface establishes the compositional kernel of the proposal:

1. retain a determinate positive or negative state only under agreement;
2. preserve absence, incompleteness, and conflict as an explicit unresolved state;
3. compose deterministically without temperature or sampling;
4. add a qualifier axis when the current ontology cannot express the relevant distinction;
5. retain provenance during composition.

This is the part that is now machine-checked. A production Wikidata or SensibLaw integration would next supply concrete qualifier carriers, reference-evidence adapters, calibration rules, and import/export conformance tests.
