# Wikidata animal semantic join layer

## Intention

`DASHI.Ontology.WikidataAnimalSemanticJoinLayer` records a bounded external
semantic join layer for Animalexic / WikiSpecies / WikiDog-style systems.

The purpose is not to let Animalexic invent a meaning space alone. A situated
animal observation and candidate latent behavioural predicate can be reviewed
against public species knowledge:

```text
Animalexic observation
  -> candidate latent behavioural predicate
  -> public ontology packet
  -> reviewed semantic join disposition
```

The public ontology packet may include:

- Wikidata ID;
- Wikipedia page / description;
- WikiSpecies taxon context;
- ethology notes;
- anatomy notes;
- sensory biology notes;
- habitat notes;
- vocalization notes;
- posture notes;
- social behaviour notes.

This is a review and promotion layer. It is not edit authority and not truth
authority.

## Relation To Existing Biology Bridge

The existing module
`DASHI.Biology.CrossSpeciesOntologyTranslationBridge` already represents the
Animalexic / WikiSpecies translation boundary:

```text
Animalexic behavioural meaning
  -> species/taxon/context carrier
  -> bounded ontology alignment
  -> contextual translation candidate
```

The new Wikidata/Wikipedia layer sits one step outward:

```text
cross-species contextual candidate
  -> public ontology packet
  -> review disposition
```

It does not replace the biology bridge. It supplies public ontology context for
reviewing candidate joins.

## Join Dispositions

The Agda surface names four candidate outcomes:

```text
joinPromoted
joinHeld
joinContradictory
joinUnsupported
```

These are review dispositions:

- `joinPromoted`: receipts and context are adequate for the local review
  purpose.
- `joinHeld`: the candidate is plausible but lacks enough receipts or context.
- `joinContradictory`: public ontology/species context conflicts with the
  candidate.
- `joinUnsupported`: the candidate has no adequate public ontology support.

None of these authorize a Wikidata edit. They only classify the local review
state.

## Public Ontology Packet

`PublicAnimalOntologyPacket` keeps public knowledge facets typed separately:

```text
WikidataID
WikipediaPage
SpeciesDescription
EthologyNote
AnatomyNote
SensoryBiologyNote
HabitatNote
VocalizationNote
PostureNote
SocialBehaviourNote
SourceReceipt
```

This separation matters because a candidate may be supported by one facet and
blocked by another. For example, a posture observation may be anatomically
plausible but ethologically unsupported in the current context.

## Residuals

The join layer records residual classes such as:

```text
missingWikidataID
missingWikipediaDescription
missingEthologyReceipt
missingAnatomyReceipt
missingSensoryBiologyReceipt
missingHabitatReceipt
missingVocalizationReceipt
missingPostureReceipt
missingSocialBehaviourReceipt
ontologyContradiction
observationOntologyMismatch
anthropomorphicProjectionRisk
```

These are review blockers or warnings, not proof that the animal's state is
known.

## Blocked Claims

The canonical boundary list blocks:

```text
reviewJoinLayerOnly
noEditAuthority
noTruthAuthority
noBlindEdit
noContextFreeTranslation
noQualiaIdentity
noAnthropomorphicPromotion
noPublicOntologyAsCompleteMeaningSpace
```

This keeps the layer from making the main category mistakes:

- public ontology context is not animal subjective experience;
- taxonomy is not behaviour by itself;
- an observation is not a context-free translation;
- a local review packet is not authority to edit Wikidata or Wikipedia;
- human-readable species text is not a complete animal meaning space.

## Toy Inhabitant

The module includes a toy dog-style inhabitant:

```text
toyDogObservation
toyDogLatentPlayBow
toyDogCandidateAffiliativePlay
toyDogQID
toyDogWikipediaPage
...
```

Its default disposition is `joinHeld`, with residuals:

```text
missingPostureReceipt
anthropomorphicProjectionRisk
```

That is intentional. A dog-like posture/vocalization/social candidate can be
reviewed against public species knowledge, but the toy fixture does not
pretend to recover canine qualia or authorize a blind edit.

## Safe Claim

Safe:

```text
Wikidata/Wikipedia species knowledge can act as a bounded public ontology
review layer for Animalexic candidate behavioural predicates.
```

## Integration

`DASHI.Interop.AggregateBidirectionalTranslationDischarge` imports the canonical
join layer and non-authority certificate.  This places the public ontology
review packet inside the same bidirectional transport chain as human, animal,
renderer, and machine ontologies while preserving the no-edit-authority and
no-truth-authority boundary.

Unsafe:

```text
Wikidata/Wikipedia proves the animal's meaning.
Animalexic may blindly edit public ontology.
Species descriptions recover qualia.
Cross-species observations translate context-free into human language.
Anthropomorphic readings are promoted without receipts.
```

## Validation

Targeted validation:

```text
agda -i . -l standard-library DASHI/Ontology/WikidataAnimalSemanticJoinLayer.agda
```
