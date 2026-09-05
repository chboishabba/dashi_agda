module DASHI.Core.KnowledgeBoundaryKindBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.KnowledgeBoundaryTransitionBidiExact as T

------------------------------------------------------------------------
-- KNOWLEDGE-BOUNDARY KIND
--
-- A private->public transition is not semantically uniform. Routine patent
-- confidentiality, contractual proprietary periods, export-control release,
-- classification/declassification and discretionary disclosure are distinct
-- boundary mechanisms and must not be pooled without an explicit bridge.
------------------------------------------------------------------------

data BoundaryKind : Set where
  ordinaryPatentConfidentiality
  contractualProprietaryBoundary
  controlledGovernmentData
  exportControlledBoundary
  classifiedNationalSecurityBoundary
  internalInstitutionalBoundary
  discretionaryDisclosureBoundary
  unresolvedBoundaryKind
  : BoundaryKind

record TypedBoundaryTransition : Set where
  constructor typed-boundary-transition
  field
    personOrTeam : String
    knowledgeObject : String
    boundaryKind : BoundaryKind
    boundedReceipt : T.BoundaryStateReceipt
    publicReceipt : T.BoundaryStateReceipt
    sameObject : T.SameBoundaryObject boundedReceipt publicReceipt
    boundedState : T.state boundedReceipt ≡ T.boundedPrivate
    publicState : T.state publicReceipt ≡ T.releasedPublicly
    sourceReference : String
    boundedReading : String

open TypedBoundaryTransition public

record BoundaryKindBoundary : Set where
  constructor boundary-kind-boundary
  field
    patentPublicationEqualsDeclassification : Bool
    patentPublicationEqualsDeclassificationIsFalse :
      patentPublicationEqualsDeclassification ≡ false
    proprietaryPeriodEqualsClassification : Bool
    proprietaryPeriodEqualsClassificationIsFalse :
      proprietaryPeriodEqualsClassification ≡ false
    exportControlEqualsClassification : Bool
    exportControlEqualsClassificationIsFalse :
      exportControlEqualsClassification ≡ false
    routineLegalPublicationCountsAsSensitiveDisclosure : Bool
    routineLegalPublicationCountsAsSensitiveDisclosureIsFalse :
      routineLegalPublicationCountsAsSensitiveDisclosure ≡ false
    sameBoundaryKindRequiredForLikeForLikeEnrichment : Bool
    sameBoundaryKindRequiredForLikeForLikeEnrichmentIsTrue :
      sameBoundaryKindRequiredForLikeForLikeEnrichment ≡ true

canonicalBoundaryKindBoundary : BoundaryKindBoundary
canonicalBoundaryKindBoundary = boundary-kind-boundary
  false refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- Reverse acquisition: enrichment in a boundary-crossing hypothesis must be
-- stratified by boundary mechanism rather than pooling all transitions.
------------------------------------------------------------------------

data BoundaryKindAcquisitionTarget : Set where
  exactPriorPrivateState
  exactPublicReleaseState
  exactSameObjectWeld
  exactBoundaryKindReceipt
  matchedBoundaryKindControls
  : BoundaryKindAcquisitionTarget

record BoundaryKindReverseObligation : Set where
  constructor boundary-kind-reverse-obligation
  field
    subject : String
    target : BoundaryKindAcquisitionTarget
    requestedEvidence : String
    whatItCanPromote : String
    whatItCannotPromote : String

open BoundaryKindReverseObligation public
