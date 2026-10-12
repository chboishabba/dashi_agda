{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974QualificationFeedbackWeldExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.ReliabilityAdaptiveQualificationFeedbackBidiExact as Feedback
import DASHI.Physics.Propulsion.Rocketdyne1974TwoMaterialDiscriminatorExact as Disc

------------------------------------------------------------------------
-- ROCKETDYNE QUALIFICATION-FEEDBACK WELD
--
-- The historical sequence has the shape
--   anomaly under an extreme Haynes-25 configuration
--       -> changed nozzle material/hardware
--       -> WC103 follow-up at a near-matched extreme condition.
--
-- That is exactly the engineering pattern consumed by the repository's
-- adaptive qualification-feedback lane.  The archive, however, does not by
-- itself prove that the change was a formally reviewed/approved qualification
-- revision in the generic Feedback sense.  We therefore expose a candidate
-- revision and subsequent observation while leaving review/approval false.
------------------------------------------------------------------------

record QualificationRevisionCandidate : Set where
  constructor qualification-revision-candidate
  field
    sourceObservation : Disc.HistoricalRun
    target : Feedback.RevisionTarget
    previousConfiguration : String
    candidateConfiguration : String
    observedChange : String
    followupSource : String
    archiveShowsChangedHardware : Bool
    formalReviewReceiptRecovered : Bool
    formalApprovalReceiptRecovered : Bool

haynesAnomalyToRevisionCandidate : QualificationRevisionCandidate
haynesAnomalyToRevisionCandidate =
  qualification-revision-candidate
    Disc.haynesDamageObserved
    Feedback.qualificationEnvelope
    "Haynes-25 nozzle-extension extreme-condition configuration"
    "WC103 columbium / silicide-coated follow-up configuration"
    "material/hardware revision after high-temperature nozzle damage"
    "NASA-CR-140308 R-9557 Test 870-2 / company-sponsored follow-up"
    true false false

wc103FollowupObservation : Disc.HistoricalRun
wc103FollowupObservation = Disc.wc103FollowupSurvived

formalApprovalStillUnpaid : Bool
formalApprovalStillUnpaid = false

record HistoricalFeedbackReceipt : Set where
  constructor historical-feedback-receipt
  field
    anomalyObserved : Bool
    changedConfigurationObserved : Bool
    subsequentExtremeRunObserved : Bool
    subsequentObservedOutcomeSurvived : Bool
    sequenceSupportsFeedbackHypothesis : Bool
    sequenceProvesFormalRevisionApproval : Bool
    sequenceProvesPopulationReliabilityImprovement : Bool
    sourceBoundary : String

rocketdyneHistoricalFeedbackReceipt : HistoricalFeedbackReceipt
rocketdyneHistoricalFeedbackReceipt =
  historical-feedback-receipt
    true true true true true false false
    "R-9557 establishes the anomaly/change/follow-up sequence; formal review governance and population-level post-revision reliability are separate acquisitions."

adaptiveQualificationBoundaryReceipt : Feedback.ReliabilityAdaptiveFeedbackBoundary
adaptiveQualificationBoundaryReceipt = Feedback.canonicalReliabilityAdaptiveFeedbackBoundary

record FeedbackAcquisitionFrontier : Set where
  constructor feedback-acquisition-frontier
  field
    rootCauseOrProcessAssociation : Bool
    revisionProposalDocument : Bool
    independentReviewReceipt : Bool
    approvedEffectiveRevision : Bool
    futureCapacityModel : Bool
    postRevisionPopulationComparison : Bool
    preferredNextSource : String

rocketdyneFeedbackFrontier : FeedbackAcquisitionFrontier
rocketdyneFeedbackFrontier =
  feedback-acquisition-frontier
    true false false false false false
    "Rocketdyne engineering change order, anomaly disposition, material-selection memorandum, qualification approval, or later fleet/lot reliability comparison."
