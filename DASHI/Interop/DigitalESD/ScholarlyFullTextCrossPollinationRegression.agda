module DASHI.Interop.DigitalESD.ScholarlyFullTextCrossPollinationRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Interop.DigitalESD.ScholarlyFullTextCrossPollinationExact as X

metadataCannotBecomeParsedStudy :
  X.ERICMetadataCreatesParsedStudy → ⊥
metadataCannotBecomeParsedStudy =
  X.ericMetadataDoesNotCreateParsedStudy

artifactCannotBecomeObservation :
  X.FullTextArtifactCreatesSemanticObservation → ⊥
artifactCannotBecomeObservation =
  X.fullTextArtifactDoesNotCreateSemanticObservation

documentStructureCannotCreateClaimTruth :
  X.DocumentStructureCreatesClaimTruth → ⊥
documentStructureCannotCreateClaimTruth =
  X.documentStructureDoesNotCreateClaimTruth

studyFacetCandidateCannotCreateStudyTruth :
  X.StudyFacetCandidateCreatesStudyTruth → ⊥
studyFacetCandidateCannotCreateStudyTruth =
  X.studyFacetCandidateDoesNotCreateStudyTruth

reviewedObservationCannotCreateAuditAdmission :
  X.ReviewedStudyObservationCreatesSourceAuditAdmission → ⊥
reviewedObservationCannotCreateAuditAdmission =
  X.reviewedStudyObservationDoesNotCreateSourceAuditAdmission

digitalESDProjectionCannotReplaceCanonicalObservation :
  X.DigitalESDProjectionMayReplaceCanonicalObservation → ⊥
digitalESDProjectionCannotReplaceCanonicalObservation =
  X.digitalESDProjectionDoesNotReplaceCanonicalObservation

structuredNodeNeedNotBecomeText :
  X.StructuredDocumentNodeRequiresFakeTextRange → ⊥
structuredNodeNeedNotBecomeText =
  X.structuredDocumentNodeDoesNotRequireFakeTextRange
