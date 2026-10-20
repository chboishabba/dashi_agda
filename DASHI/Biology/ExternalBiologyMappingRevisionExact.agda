module DASHI.Biology.ExternalBiologyMappingRevisionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ExternalBiologyEvidenceCore as External
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- CROSS-DATABASE MAPPING + REVISION SEMANTICS
------------------------------------------------------------------------

data MappingRelation : Set where
  exactSequenceMapping : MappingRelation
  residueLevelMapping : MappingRelation
  encodedByMapping : MappingRelation
  annotationMapping : MappingRelation
  structurePredictionMapping : MappingRelation
  experimentalStructureMapping : MappingRelation
  reactionMapping : MappingRelation
  domainMapping : MappingRelation
  ontologyMapping : MappingRelation
  homologyMapping : MappingRelation
  relatedMapping : MappingRelation

record CrossDatabaseMapping : Set where
  constructor crossDatabaseMapping
  field
    mappingId : String
    sourceDatabase : External.BioSource
    sourceEntityReference : String
    targetDatabase : External.BioSource
    targetEntityReference : String
    relation : MappingRelation
    witnessReference : String
    exactIdentityWitnessed : Bool
    mappingAloneCreatesEntityIdentity : Bool
    mappingAloneCreatesEntityIdentityIsFalse :
      mappingAloneCreatesEntityIdentity ≡ false

open CrossDatabaseMapping public

mkMapping :
  String → External.BioSource → String → External.BioSource → String →
  MappingRelation → String → Bool → CrossDatabaseMapping
mkMapping mappingId sourceDatabase sourceEntity targetDatabase targetEntity relation witness exactIdentity =
  crossDatabaseMapping
    mappingId sourceDatabase sourceEntity targetDatabase targetEntity relation witness
    exactIdentity false refl

record MappingBoundary : Set where
  constructor mappingBoundary
  field
    crossReferenceAloneCreatesEntityIdentity : Bool
    crossReferenceAloneCreatesEntityIdentityIsFalse :
      crossReferenceAloneCreatesEntityIdentity ≡ false
    pdbChainAutomaticallyEqualsWholeCanonicalProtein : Bool
    pdbChainAutomaticallyEqualsWholeCanonicalProteinIsFalse :
      pdbChainAutomaticallyEqualsWholeCanonicalProtein ≡ false
    alphaFoldModelIsExperimentalStructure : Bool
    alphaFoldModelIsExperimentalStructureIsFalse :
      alphaFoldModelIsExperimentalStructure ≡ false
    geneTranscriptProteinAreDefinitionallyIdentical : Bool
    geneTranscriptProteinAreDefinitionallyIdenticalIsFalse :
      geneTranscriptProteinAreDefinitionallyIdentical ≡ false

canonicalMappingBoundary : MappingBoundary
canonicalMappingBoundary =
  mappingBoundary false refl false refl false refl false refl

data RevisionKind : Set where
  unchanged : RevisionKind
  added : RevisionKind
  removed : RevisionKind
  modified : RevisionKind

record RevisionReceipt : Set where
  constructor revisionReceipt
  field
    revisionId : String
    oldSnapshotReference : String
    newSnapshotReference : String
    entityReference : String
    kind : RevisionKind
    sequenceChanged : Bool
    annotationChanged : Bool
    identityChanged : Bool
    deltaReference : String
    oldStateRetainedForAudit : Bool
    absenceMeansBiologicalNonexistence : Bool
    absenceMeansBiologicalNonexistenceIsFalse :
      absenceMeansBiologicalNonexistence ≡ false

open RevisionReceipt public

mkRevisionReceipt :
  String → String → String → String → RevisionKind →
  Bool → Bool → Bool → String → RevisionReceipt
mkRevisionReceipt revisionId oldSnapshot newSnapshot entity kind sequenceChanged annotationChanged identityChanged delta =
  revisionReceipt
    revisionId oldSnapshot newSnapshot entity kind
    sequenceChanged annotationChanged identityChanged delta
    true false refl

record RevisionBoundary : Set where
  constructor revisionBoundary
  field
    absenceFromCurrentDatasetMeansBiologicalNonexistence : Bool
    absenceFromCurrentDatasetMeansBiologicalNonexistenceIsFalse :
      absenceFromCurrentDatasetMeansBiologicalNonexistence ≡ false
    entryRevisionImpliesSequenceRevision : Bool
    entryRevisionImpliesSequenceRevisionIsFalse :
      entryRevisionImpliesSequenceRevision ≡ false
    sequenceStableImpliesAllAnnotationsStable : Bool
    sequenceStableImpliesAllAnnotationsStableIsFalse :
      sequenceStableImpliesAllAnnotationsStable ≡ false
    newerReleaseAutomaticallyOverridesAllOlderEvidence : Bool
    newerReleaseAutomaticallyOverridesAllOlderEvidenceIsFalse :
      newerReleaseAutomaticallyOverridesAllOlderEvidence ≡ false

canonicalRevisionBoundary : RevisionBoundary
canonicalRevisionBoundary =
  revisionBoundary false refl false refl false refl false refl

canonicalExternalBiologyMappingRevisionReceipt : Receipt.GenericReceipt
canonicalExternalBiologyMappingRevisionReceipt =
  Receipt.mkNonPromotingReceipt
    "external biology mapping and revision semantics"
    "DASHI.Biology.ExternalBiologyMappingRevisionExact"
    "CrossDatabaseMapping / RevisionReceipt"
    "keeps mapping relation, witness and exact-identity status separate while preserving release-to-release deltas"
    "cross-references do not collapse entity identity; dataset disappearance is not biological nonexistence; annotation and sequence revisions remain distinct coordinates"
    "agda -i . DASHI/Biology/ExternalBiologyMappingRevisionExact.agda"
