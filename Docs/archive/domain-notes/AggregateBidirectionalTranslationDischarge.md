# Aggregate Bidirectional Translation Discharge

## Scope

Agda module:

```text
DASHI.Interop.AggregateBidirectionalTranslationDischarge
```

This surface records the aggregate thread-tail rule:

```text
human ontology
  <-> dog ontology
  <-> octopus ontology
  <-> alien ontology
  <-> renderer ontology
  <-> machine ontology
```

DASHI permits bounded bidirectional transport between domains. The direction is
not special: animal-to-human explanation is only one instance of the more
general transport discipline.

## Formal Shape

`OntologyTransportSurface` owns the minimal bridge vocabulary:

- source and target ontology domains;
- source and target carriers;
- source and target observation quotients;
- forward and backward transport maps;
- forward and backward residual maps;
- projection-defect and epsilon surfaces;
- admissibility gates for each direction;
- an exact-isomorphism slot that is usable only with a zero-epsilon witness;
- a partial-translation slot for residual-bearing transport.

`AggregateBidirectionalTranslationDischarge` packages the canonical chain:

- human `<->` dog;
- dog `<->` octopus;
- octopus `<->` alien;
- alien `<->` renderer;
- renderer `<->` machine.

The canonical toy inhabitant marks every bridge as bounded and residual-bearing.
It does not assert zero defect.

The discharge also carries the two adjacent thread-tail certificates:

- `DASHI.Computation.PersistentTransportMotifs` for renderer/machine/program
  execution as persistent transport motifs;
- `DASHI.Ontology.WikidataAnimalSemanticJoinLayer` for public
  Wikidata/Wikipedia/WikiSpecies review joins over Animalexic candidates.

That makes the aggregate surface the linkage point rather than a free-floating
analogy: species-native meaning, public ontology review, renderer semantics,
and machine execution remain transport-compatible while keeping their
residuals typed separately.

## Residual Discipline

The intended reading is:

```text
epsilon = 0       -> exact isomorphism may be discharged by witness
epsilon nonzero   -> analogy or partial translation only
```

Projection defects remain part of the translated artifact. A bridge may be
useful while still losing distinctions, introducing context residuals, or
requiring side information.

## Non-Promotion Guards

The module explicitly blocks:

- universal translator claims;
- qualia identity claims;
- zero-defect claims without a witness;
- runtime optimizer claims.

It also records that residuals remain explicit.

## Validation Target

```text
agda -i . -l standard-library DASHI/Interop/AggregateBidirectionalTranslationDischarge.agda
```
