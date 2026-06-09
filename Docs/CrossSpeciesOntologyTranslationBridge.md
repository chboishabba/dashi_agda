# Cross-species ontology translation bridge

## Scope

This note records the bounded Animalexic/WikiSpecies translation lane:

```text
Animalexic observation
  -> social context
  -> ecological niche
  -> memory trace
  -> WikiSpecies-style taxon reference
  -> ontology alignment
  -> contextual translation candidate
```

Agda module:

```text
DASHI.Biology.CrossSpeciesOntologyTranslationBridge
```

The bridge is intentionally non-promoting. It does not claim cross-species
qualia identity, species isomorphism, anthropomorphic promotion, or
context-free translation.

## Relation To Animalexic

`AnimalexicAnimalUtteranceSurface` already blocks direct sound-to-word
semantics and direct qualia recovery. This module builds on that boundary by
treating a promoted Animalexic behavioural meaning as only one input to a
cross-species ontology candidate.

The safe path is:

```text
multimodal animal observation
  -> behavioural meaning candidate with receipts
  -> species/taxon/context carrier
  -> bounded ontology alignment
```

not:

```text
animal signal
  -> human word
  -> universal species dictionary
```

## WikiSpecies-Style Context Carrier

`WikiSpeciesContextCarrier` models taxonomy as a receipted context surface. It
contains:

- species carrier;
- taxon node;
- ecological context;
- social context;
- memory trace;
- ontology node;
- taxon and context receipts.

The module treats a WikiSpecies-style taxon reference as useful provenance for
species context. It does not allow taxonomy alone to determine behaviour,
meaning, subjective experience, or cross-species identity.

## Translation Surface

`CrossSpeciesOntologyTranslationSurface` aligns a source species and target
species through:

- source behavioural meaning;
- source and target taxa;
- source and target ecological contexts;
- source and target social contexts;
- source and target memory traces;
- source and target ontology nodes;
- translation residuals and an admissible translation receipt.

The resulting `ContextualMeaning` is a local candidate, not a promoted global
dictionary entry.

## Non-Promotion Guards

The four explicit guards are:

```text
NoQualiaIdentityClaim
NoSpeciesIsomorphismClaim
NoAnthropomorphicPromotionClaim
NoContextFreeTranslationClaim
```

The bridge also records boolean claim blockers:

```text
qualiaIdentityClaim = false
speciesIsomorphismClaim = false
anthropomorphicPromotionClaim = false
contextFreeTranslationClaim = false
```

Together these block the common category errors:

- treating similar observed behaviour as identical subjective experience;
- treating two species as structurally isomorphic;
- projecting human meanings into animal behaviour without receipts;
- translating outside ecological, social, and memory context.

## Residuals

The residual vocabulary tracks why a translation remains bounded:

```text
missing taxon receipt
missing ecological context
missing social context
missing memory trace
ambiguous behavioural class
target species projection risk
```

These residuals are diagnostic. They do not automatically promote or reject a
translation; they show where receipt pressure remains.

## Safe Reading

The admissible reading is:

```text
Animalexic/WikiSpecies translation narrows context-bound ontology classes
under taxon, ecology, social, memory, and receipt constraints.
```

The inadmissible reading is:

```text
DASHI recovers what another species means or feels in human terms.
```

## Integration Note

This file is imported by `DASHI.Biology.BioAnimalexicStackDischarge` and the
aggregate `DASHI.Everything` surface.

## Validation Target

Focused validation:

```text
agda -i . -l standard-library DASHI/Biology/CrossSpeciesOntologyTranslationBridge.agda
```
