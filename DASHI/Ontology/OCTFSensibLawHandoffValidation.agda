module DASHI.Ontology.OCTFSensibLawHandoffValidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Ontology.OCTFSensibLawHandoffExact

rosarioMeetingSignalStartsCandidateOnly :
  initialDisposition rosarioHotspotLane ≡ candidateOnly
rosarioMeetingSignalStartsCandidateOnly = refl

natLiveWriteRemainsHeld :
  currentNatLiveDisposition ≡ held
natLiveWriteRemainsHeld = refl

peterEgeDisjointnessStartsReviewFirst :
  initialDisposition peterEgeDisjointnessLane ≡ reviewable
peterEgeDisjointnessStartsReviewFirst = refl

meetingSignalCannotAssertOntologyTruth :
  MeetingSignalTruthPermission → ⊥
meetingSignalCannotAssertOntologyTruth = meetingSignalCannotPromoteTruth

handoffSignalCannotAuthorizeEdit :
  HandoffSignalEditPermission → ⊥
handoffSignalCannotAuthorizeEdit = handoffSignalCannotPromoteEditAuthority

canonicalStatusPinsAttributionSplit :
  sourceOwnersRemainDistinct canonicalOCTFHandoffStatus ≡ true
canonicalStatusPinsAttributionSplit =
  sourceOwnersRemainDistinctIsTrue canonicalOCTFHandoffStatus

canonicalStatusPinsReviewBoundary :
  reviewFirstBoundaryPreserved canonicalOCTFHandoffStatus ≡ true
canonicalStatusPinsReviewBoundary =
  reviewFirstBoundaryPreservedIsTrue canonicalOCTFHandoffStatus
