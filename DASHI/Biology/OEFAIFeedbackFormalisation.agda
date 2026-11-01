module DASHI.Biology.OEFAIFeedbackFormalisation where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF
import DASHI.Biology.OEFOverlapAnalytics as Overlap
import DASHI.Biology.FeedbackNonResponseGovernance as NonResponse
import DASHI.Biology.IntersectionalFeedbackPrivacyBoundary as Privacy
import DASHI.Biology.LongitudinalEngagementTrajectory as Longitudinal
import DASHI.Biology.PedagogicalJPlusOneRouting as Routing
import DASHI.Biology.StudentEngagementEvidenceBridge as ExistingEvidence
import DASHI.Biology.EducationBodyMemoryBridge as ExistingEducation

------------------------------------------------------------------------
-- Aggregate bridge for the 2024 AJET OEF / AI feedback paper.
--
-- This module composes the source-bound paper formalisation with the
-- repository's existing student-engagement and education/body-memory lanes.
-- It preserves the MVP contribution while extending it through:
--   multi-fibre OEF bundles;
--   overlap analytics;
--   response/non-response governance;
--   intersectional privacy boundaries;
--   longitudinal trajectory limits; and
--   human-reviewed, agency-safe pedagogical +1 routing.

record OEFAIFeedbackFormalisation : Set where
  constructor mkOEFAIFeedbackFormalisation
  field
    sourceReference : OEF.PaperReference
    sourceReferenceIsCanonical : sourceReference ≡ OEF.canonicalPaperReference

    multiFibreHyperfabric : OEF.OEFMultiFibreFeedbackHyperfabric
    multiFibreHyperfabricIsCanonical :
      multiFibreHyperfabric ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric

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

open OEFAIFeedbackFormalisation public

canonicalOEFAIFeedbackFormalisation : OEFAIFeedbackFormalisation
canonicalOEFAIFeedbackFormalisation =
  mkOEFAIFeedbackFormalisation
    OEF.canonicalPaperReference refl
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
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
    "Dann et al. (2024), DOI 10.14742/ajet.8903, is retained as a successful MVP showing that manually OEF-labelled feedback can train a scalable classifier. DASHI extends the evidence surface without rewriting the source claim: OEF elements are overlapping fibres; feedback is a sparse voluntary projection; model outputs remain compiled human coding; aggregates do not equal individuals or equity; later-semester transfer does not establish causal redesign effects; and only contextual, privacy-governed, human-reviewed, agency-safe +1 candidates may enter pedagogical action."

canonicalFormalisationPaperTitle :
  OEF.paperTitle (sourceReference canonicalOEFAIFeedbackFormalisation) ≡
  "Making sense of student feedback and engagement using artificial intelligence"
canonicalFormalisationPaperTitle = refl

canonicalFormalisationPaperDOI :
  OEF.paperDOI (sourceReference canonicalOEFAIFeedbackFormalisation) ≡
  "10.14742/ajet.8903"
canonicalFormalisationPaperDOI = refl

canonicalFormalisationMultiLabelPreserved :
  multiLabelPreserved canonicalOEFAIFeedbackFormalisation ≡ true
canonicalFormalisationMultiLabelPreserved =
  multiLabelPreservedIsTrue canonicalOEFAIFeedbackFormalisation

canonicalFormalisationHumanReviewRequired :
  pedagogicalActionRequiresHumanReview canonicalOEFAIFeedbackFormalisation ≡ true
canonicalFormalisationHumanReviewRequired =
  pedagogicalActionRequiresHumanReviewIsTrue canonicalOEFAIFeedbackFormalisation
