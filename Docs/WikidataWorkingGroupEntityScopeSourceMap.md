# Wikidata entity-scope provenance map

This bounded map records which source layer supplies which part of the current BFO/entity/higher-order-class handoff. It is descriptive provenance, not a percentage-of-truth metric.

```mermaid
graph TD
  WDQ35120[Wikidata Q35120 entity] -->|target graph / broad root| Scope[DASHI entity-scope fibre]
  WDQ136[Wikidata Q136433660 BFO Entity] -->|target graph / BFO-local root| Scope
  P12602[P12602 BFO class ID] -->|identifier evidence| Mapping[DASHI query-indexed mapping licences]
  P2888[P2888 exact match] -->|semantic-interchange evidence| Mapping
  P1709[P1709 equivalent class] -->|class-equivalence evidence| Mapping
  P279[P279 subclass] -->|subclass evidence| Mapping
  BFOTalk[Talk:Q136433660 / BFO partition discussion] -->|scope calibration| Diagnostic[DASHI layered root diagnostic]
  ClassOrder[Wikidata class-order documentation] -->|order-of-predication calibration| Fiction[DASHI higher-order fiction/context fibre]
  FictionalProfession[Q17305127 fictional profession] -->|live modelling regression| Fiction
  PNF[DASHI PNF / argument-level transport] -->|retain referent + provenance across levels| Applicability[BFO applicability fibre]
  Scope --> Diagnostic
  Mapping --> Diagnostic
  Applicability --> WG[Working-group regression]
  Fiction --> WG
  Diagnostic --> WG
```

## Layer roles

- **Wikidata items/properties** supply current target-graph assertions and public modelling vocabulary.
- **BFO/Wikidata project discussion** supplies current scope/alignment calibration, not DASHI theorem proofs.
- **DASHI** supplies non-reconstruction, nonfactorability, query-indexed inference, provenance-preserving level transport, and ambiguity/non-promotion theorems.
- **JMD Lean** remains available through `LeanWikidataEverything` for independently checked Wikidata class-algebra, alignment, diagnostics, and RDF contracts.

## Critical non-collapse rules

- label equality is not ontology identity;
- identifier agreement is not semantic equivalence;
- exact match and equivalent class are not interchangeable property roles;
- ambiguous mapping is not source-ontology contradiction;
- class order is not fictional/narrative status;
- member classes classifying fictional individuals does not make the metaclass an in-world fictional entity;
- not established / outside scope / conflicting derivations are distinct evaluation states;
- changing ontology inspection level does not erase the referent or its provenance.
