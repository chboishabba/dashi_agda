{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.Rocketdyne1974QualificationFeedbackWeldExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.ReliabilityAdaptiveQualificationFeedbackBidiExact as Feedback
import DASHI.Physics.Propulsion.Rocketdyne1974TwoMaterialDiscriminatorExact as Disc
import DASHI.Physics.Propulsion.Rocketdyne1974ProgrammeChallengesAndRelatedWorkExact as Challenges
import DASHI.Physics.Propulsion.Rocketdyne1974SiblingRCSComparisonExact as Sibling
import DASHI.Physics.Propulsion.Rocketdyne1974OperationalValveReliabilityLessonExact as OperationalValve

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
haynesAnomalyToRevisionCandidate = qualification-revision-candidate
  Disc.haynesDamageObserved Feedback.qualificationEnvelope
  "Haynes-25 nozzle-extension extreme-condition configuration"
  "WC103 columbium / silicide-coated follow-up configuration"
  "material/hardware revision after high-temperature nozzle damage"
  "NASA-CR-140308 R-9557 Test 870-2 / company-sponsored follow-up"
  true false false

wc103FollowupObservation : Disc.HistoricalRun
wc103FollowupObservation = Disc.wc103FollowupSurvived

formalApprovalStillUnpaid : Bool
formalApprovalStillUnpaid = true

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
rocketdyneHistoricalFeedbackReceipt = historical-feedback-receipt
  true true true true true false false
  "R-9557 establishes the anomaly/change/follow-up sequence; formal review governance and population-level post-revision reliability are separate acquisitions."

adaptiveQualificationBoundaryReceipt : Feedback.ReliabilityAdaptiveFeedbackBoundary
adaptiveQualificationBoundaryReceipt = Feedback.canonicalReliabilityAdaptiveFeedbackBoundary

record EnvironmentalProtectionFeedback : Set where
  constructor environmental-protection-feedback
  field
    sourceProblem : Challenges.ProgrammeChallenge
    target : Feedback.RevisionTarget
    directRecommendation : String
    recommendationRecovered : Bool
    formalApprovedProcedureRecovered : Bool
    boundary : String

environmentalProtectionRecommendation : EnvironmentalProtectionFeedback
environmentalProtectionRecommendation = environmental-protection-feedback
  Challenges.sandDustValveChallenge Feedback.serviceabilityRule
  "protect engine from sand and dust and/or purge before each mission unless a valve resistant to that environment is developed"
  true false
  "R-9557-1 pays the engineering recommendation, not a later approved operational procedure or fleet-wide reliability effect."

siblingComparisonBoundaryReceipt : Sibling.SiblingComparisonBoundary
siblingComparisonBoundaryReceipt = Sibling.siblingComparisonBoundary

siblingComparisonDoesNotProveReliability : Bool
siblingComparisonDoesNotProveReliability = true

operationalValveReliabilityBoundary : OperationalValve.OperationalValveReliabilityBoundary
operationalValveReliabilityBoundary = OperationalValve.operationalValveReliabilityBoundary

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
rocketdyneFeedbackFrontier = feedback-acquisition-frontier
  true false false false false false
  "Rocketdyne engineering change order, anomaly disposition, material-selection memorandum, Moog/NAS9-12996 valve failure analysis, qualification approval, purge/protection procedure, or later fleet/lot reliability comparison. Later metal-nitrate valve operations are methodological feedback only and cannot substitute for the 1974 population."
