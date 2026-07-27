module DASHI.Biology.OEFAIFeedbackFormalisationFull where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF
import DASHI.Biology.HumanCodingMachineCompilationBridge as Coding
import DASHI.Biology.OEFOverlapAnalytics as Overlap
import DASHI.Biology.FeedbackNonResponseGovernance as NonResponse
import DASHI.Biology.IntersectionalFeedbackPrivacyBoundary as Privacy
import DASHI.Biology.LongitudinalEngagementTrajectory as Longitudinal
import DASHI.Biology.PedagogicalJPlusOneRouting as Routing
import DASHI.Biology.StudentEngagementEvidenceBridge as ExistingEvidence
import DASHI.Biology.EducationBodyMemoryBridge as ExistingEducation

------------------------------------------------------------------------
-- Complete aggregate for the 2024 AJET OEF / AI feedback paper.

record OEFAIFeedbackFormalisationFull : Set where
  constructor mkOEFAIFeedbackFormalisationFull
  field
    sourceReference : OEF.PaperReference
    sourceReferenceIsCanonical : sourceReference ≡ OEF.canonicalPaperReference
    multiFibreHyperfabric : OEF.OEFMultiFibreFeedbackHyperfabric
    multiFibreHyperfabricIsCanonical :
      multiFibreHyperfabric ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric
    humanCodingCompilation : Coding.HumanCodingMachineCompilationBridge
    humanCodingCompilationIsCanonical :
      humanCodingCompilation ≡ Coding.canonicalHumanCodingMachineCompilationBridge
    overlapAnalytics : Overlap.OEFOverlapAnalytics
    overlapAnalyticsIsCanonical :
      overlapAnalytics ≡ Overlap.canonicalOEFOverlapAnalytics
    nonResponseGovernance : NonResponse.FeedbackNonResponseGovernance
    nonResponseGovernanceIsCanonical :
      nonResponseGovernance ≡ NonResponse.canonicalFeedbackNonResponseGovernance
    privacyBoundary : Privacy.IntersectionalFeedbackPrivacyBoundary
    privacyBoundaryIsCanonical :
      privacyBoundary ≡ Privacy.canonicalIntersectionalFeedbackPrivacyBoundary
    longitudinalTrajectory : Longitudinal.LongitudinalEngagementTrajectory
    longitudinalTrajectoryIsCanonical :
      longitudinalTrajectory ≡ Longitudinal.canonicalLongitudinalEngagementTrajectory
    pedagogicalRouting : Routing.PedagogicalJPlusOneRouting
    pedagogicalRoutingIsCanonical :
      pedagogicalRouting ≡ Routing.canonicalPedagogicalJPlusOneRouting
    existingStudentEngagementEvidence :
      ExistingEvidence.StudentEngagementEvidenceBridge
    existingStudentEngagementEvidenceIsCanonical :
      existingStudentEngagementEvidence ≡
      ExistingEvidence.canonicalStudentEngagementEvidenceBridge
    existingEducationBodyMemoryBridge :
      ExistingEducation.EducationBodyMemoryBridge
    existingEducationBodyMemoryBridgeIsCanonical :
      existingEducationBodyMemoryBridge ≡
      ExistingEducation.canonicalEducationBodyMemoryBridge
    sourceBound : Bool
    sourceBoundIsTrue : sourceBound ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    multiLabelPreserved : Bool
    multiLabelPreservedIsTrue : multiLabelPreserved ≡ true
    humanInterpretationPreserved : Bool
    humanInterpretationPreservedIsTrue : humanInterpretationPreserved ≡ true
    nonResponseUndetermined : Bool
    nonResponseUndeterminedIsTrue : nonResponseUndetermined ≡ true
    intersectionalAxesGoverned : Bool
    intersectionalAxesGovernedIsTrue : intersectionalAxesGoverned ≡ true
    longitudinalChangeNotCausalClosure : Bool
    longitudinalChangeNotCausalClosureIsTrue :
      longitudinalChangeNotCausalClosure ≡ true
    pedagogicalActionRequiresHumanReview : Bool
    pedagogicalActionRequiresHumanReviewIsTrue :
      pedagogicalActionRequiresHumanReview ≡ true
    noSemanticAuthority : Bool
    noSemanticAuthorityIsTrue : noSemanticAuthority ≡ true
    noPedagogicalAuthority : Bool
    noPedagogicalAuthorityIsTrue : noPedagogicalAuthority ≡ true
    reading : String

open OEFAIFeedbackFormalisationFull public

canonicalOEFAIFeedbackFormalisationFull : OEFAIFeedbackFormalisationFull
canonicalOEFAIFeedbackFormalisationFull =
  mkOEFAIFeedbackFormalisationFull
    OEF.canonicalPaperReference refl
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
    Coding.canonicalHumanCodingMachineCompilationBridge refl
    Overlap.canonicalOEFOverlapAnalytics refl
    NonResponse.canonicalFeedbackNonResponseGovernance refl
    Privacy.canonicalIntersectionalFeedbackPrivacyBoundary refl
    Longitudinal.canonicalLongitudinalEngagementTrajectory refl
    Routing.canonicalPedagogicalJPlusOneRouting refl
    ExistingEvidence.canonicalStudentEngagementEvidenceBridge refl
    ExistingEducation.canonicalEducationBodyMemoryBridge refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "The source paper is preserved as an MVP feasibility result. The complete DASHI extension adds overlapping OEF fibres, compiled-human-coding semantics, overlap analytics, non-response governance, intersectional privacy, longitudinal limits, and human-reviewed agency-safe pedagogical routing without promoting model output to student meaning or authority."

canonicalFullPaperTitle :
  OEF.paperTitle (sourceReference canonicalOEFAIFeedbackFormalisationFull) ≡
  "Making sense of student feedback and engagement using artificial intelligence"
canonicalFullPaperTitle = refl

canonicalFullPaperDOI :
  OEF.paperDOI (sourceReference canonicalOEFAIFeedbackFormalisationFull) ≡
  "10.14742/ajet.8903"
canonicalFullPaperDOI = refl
