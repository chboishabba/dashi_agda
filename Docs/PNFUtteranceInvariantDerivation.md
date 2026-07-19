# DASHI/PNF layered utterance meaning derivation

This package formalizes a strict seven-stage route:

```text
SourceSurface
  -> TextAtom / EnumerationAtom
  -> TypedReferent (Wikidata-indexed candidate)
  -> DerivedCandidate
  -> literal/symbolic AdmissibilityGate
  -> PredicatePNF
  -> InvariantExtraction
```

The construction order is load-bearing. Surface strings never become promoted world facts directly.

## Canonical modules

- `DASHI/Cognition/Utterance/LayeredMeaningCore.agda`
- `DASHI/Cognition/Utterance/AdmissibilityGate.agda`
- `DASHI/Cognition/Utterance/YeGrievanceInvariantExample.agda`
- `DASHI/Cognition/Utterance/All.agda`

## Independent literal-promotion blockers

`LiteralPromotionProof` requires all of:

1. an itemwise source assertion;
2. moral and present agency of the argument;
3. non-empty supporting evidence.

The module proves separately that promotion is impossible for:

- a frame label without itemwise assertion;
- a fictional character;
- a deceased historical person under a present-agency reading;
- an empty evidence chain.

Symbolic admission is a separate constructor and does not weaken literal promotion.

## Invariant extraction

The example does not encode `betrayed(x, Ye)` for every listed item. Instead it constructs typed `RuptureAnchor` values and records the candidate invariant:

```text
IntegratedSelfWorldRupture / loss_of_integrated_world
```

This is candidate-only and carries neither clinical authority nor runtime authority. The constructive direction is also bounded: recover the world-supporting relation represented by each anchor and compare historically evidenced rupture-to-form transformations.

## Wikidata boundary

Q identifiers are identifiers for typed referent candidates, not authority receipts. Their presence does not prove relations, motives, betrayal, diagnosis, or the invariant. External retrieval and evidence receipts remain outside this formal package.

## Status

This is a focused, additive cognition/PNF package. It does not alter existing PNF spectral ABI claims, theorem promotions, or authority boundaries.
