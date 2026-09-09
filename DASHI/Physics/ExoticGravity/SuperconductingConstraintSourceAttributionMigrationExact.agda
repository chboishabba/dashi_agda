module DASHI.Physics.ExoticGravity.SuperconductingConstraintSourceAttributionMigrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentalConstraintRegistryExact as Registry
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- LEGACY EXPERIMENTAL-CONSTRAINT SOURCE ATTRIBUTION MIGRATION
--
-- The registry sourceReference strings are useful provenance but are not
-- silently promoted to complete attributed laboratory-result carriers.
------------------------------------------------------------------------

data MetadataStatus : Set where
  metadataKnown : String → MetadataStatus
  metadataUnresolved : MetadataStatus

data StableIdentifierStatus : Set where
  stableIdentifierKnown : String → StableIdentifierStatus
  stableIdentifierUnresolved : StableIdentifierStatus

data CarrierStatus : Set where
  carrierKnown : String → CarrierStatus
  carrierUnresolved : CarrierStatus

data InspectionStatus : Set where
  inspectedOn : String → InspectionStatus
  inspectionUnresolved : InspectionStatus

record ConstraintSourceCandidate : Set where
  constructor constraint-source-candidate
  field
    constraint : Registry.ExperimentalConstraint
    legacySourceReference : String
    sourceReferenceMatches :
      Registry.sourceReference constraint ≡ legacySourceReference
    authorOrResponsibleBody : MetadataStatus
    canonicalTitle : MetadataStatus
    stableIdentifier : StableIdentifierStatus
    carrierLocation : CarrierStatus
    inspectionStatus : InspectionStatus
    exactBoundedUse : String

open ConstraintSourceCandidate public

nasaStaticYBCOSourceCandidate : ConstraintSourceCandidate
nasaStaticYBCOSourceCandidate = constraint-source-candidate
  Registry.nasaStaticYBCO
  (Registry.sourceReference Registry.nasaStaticYBCO) refl
  metadataUnresolved
  metadataUnresolved
  stableIdentifierUnresolved
  carrierUnresolved
  inspectionUnresolved
  "source candidate for the registry's static/type-II YBCO null/artifact constraint only"

nasaRFArtifactSourceCandidate : ConstraintSourceCandidate
nasaRFArtifactSourceCandidate = constraint-source-candidate
  Registry.nasaRFArrtifact
  (Registry.sourceReference Registry.nasaRFArrtifact) refl
  metadataUnresolved
  metadataUnresolved
  (stableIdentifierKnown "AIAA-98-3139")
  carrierUnresolved
  inspectionUnresolved
  "source candidate for the registry's RF-associated instrumentation-artifact constraint only"

hathawaySourceCandidate : ConstraintSourceCandidate
hathawaySourceCandidate = constraint-source-candidate
  Registry.hathawayReplication
  (Registry.sourceReference Registry.hathawayReplication) refl
  metadataUnresolved
  metadataUnresolved
  stableIdentifierUnresolved
  carrierUnresolved
  inspectionUnresolved
  "source candidate for the registry's published rotating-disk null replication only"

tajmarTransitionSourceCandidate : ConstraintSourceCandidate
tajmarTransitionSourceCandidate = constraint-source-candidate
  Registry.tajmarTransitionMismatch
  (Registry.sourceReference Registry.tajmarTransitionMismatch) refl
  metadataUnresolved
  metadataUnresolved
  (stableIdentifierKnown "arXiv:0707.3806")
  carrierUnresolved
  inspectionUnresolved
  "source candidate for the registry's transition-mismatch/angular-response constraint only"

tajmarLargeTheoryBoundSourceCandidate : ConstraintSourceCandidate
tajmarLargeTheoryBoundSourceCandidate = constraint-source-candidate
  Registry.tajmarLargeTheoryBound
  (Registry.sourceReference Registry.tajmarLargeTheoryBound) refl
  metadataUnresolved
  metadataUnresolved
  (stableIdentifierKnown "arXiv:0707.3806")
  carrierUnresolved
  inspectionUnresolved
  "source candidate for the registry's large-effect-theory upper-bound constraint only"

------------------------------------------------------------------------
-- Migration residuals.  Known report/arXiv identifiers pay only identifier
-- identity; they do not synthesize authors, titles, carrier inspection, or scope.
------------------------------------------------------------------------

data ConstraintAttributionResidual : Set where
  missingAuthorOrResponsibleBody : ConstraintAttributionResidual
  missingCanonicalTitle : ConstraintAttributionResidual
  missingStableIdentifier : ConstraintAttributionResidual
  missingCarrierLocation : ConstraintAttributionResidual
  missingInspectionDate : ConstraintAttributionResidual
  missingExactResultLocator : ConstraintAttributionResidual

producerForConstraintAttributionResidual :
  ConstraintAttributionResidual → Search.ProducerClass
producerForConstraintAttributionResidual missingAuthorOrResponsibleBody =
  Search.attributionProducer
producerForConstraintAttributionResidual missingCanonicalTitle =
  Search.attributionProducer
producerForConstraintAttributionResidual missingStableIdentifier =
  Search.identityProducer
producerForConstraintAttributionResidual missingCarrierLocation =
  Search.propositionSourceProducer
producerForConstraintAttributionResidual missingInspectionDate =
  Search.temporalProducer
producerForConstraintAttributionResidual missingExactResultLocator =
  Search.discriminatorProducer

nasaStaticCurrentResiduals : List ConstraintAttributionResidual
nasaStaticCurrentResiduals =
  missingAuthorOrResponsibleBody ∷ missingCanonicalTitle ∷
  missingStableIdentifier ∷ missingCarrierLocation ∷
  missingInspectionDate ∷ missingExactResultLocator ∷ []

tajmarCurrentResiduals : List ConstraintAttributionResidual
tajmarCurrentResiduals =
  missingAuthorOrResponsibleBody ∷ missingCanonicalTitle ∷
  missingCarrierLocation ∷ missingInspectionDate ∷
  missingExactResultLocator ∷ []

record ConstraintSourceMigrationBoundary : Set where
  constructor constraint-source-migration-boundary
  field
    legacyReferenceStringIsCompleteAttributedSource : Bool
    knownArxivOrReportIdFillsMissingTitle : Bool
    knownIdentifierProvesCarrierWasInspected : Bool
    missingMetadataMayBeGuessed : Bool
    partialSourceCandidateStillUsefulForDiligence : Bool
    partialCandidateAutomaticallyCreatesObservationReceipt : Bool

canonicalConstraintSourceMigrationBoundary : ConstraintSourceMigrationBoundary
canonicalConstraintSourceMigrationBoundary =
  constraint-source-migration-boundary
    false false false false true false
