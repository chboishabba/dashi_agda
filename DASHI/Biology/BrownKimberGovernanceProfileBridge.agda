module DASHI.Biology.BrownKimberGovernanceProfileBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Core.EpistemicInquiryGovernance as Governance

------------------------------------------------------------------------
-- REFINED BROWN/KIMBER -> CONSTITUTIVE GOVERNANCE BRIDGE
--
-- Source anchor:
--   Alice Brown and Megan Kimber (2026),
--   "Repositioning Student Voice and Agency: A Call for the Epistemic
--   Expansion of Scholarship of Teaching and Learning Inquiry",
--   Active Learning in Higher Education 27(2), 253-264.
--   DOI: 10.1177/14697874261426374.
--
-- Partnership context:
--   Alison Cook-Sather, Catherine Bovill, Peter Felten (2014),
--   "Engaging Students as Partners in Learning and Teaching: A Guide for
--   Faculty", Jossey-Bass.
--
-- This module refines the earlier bridge by keeping authorised consumer family
-- and inquiry-question family as separate coordinates and by assigning a
-- coordinate-wise authority profile rather than a scalar participation score.
------------------------------------------------------------------------

data RefinedStageAuthorises :
    Voice.EpistemicParticipationStage →
    Governance.InquiryCoordinate → Set where
  questionContributorShapesQuestion :
    RefinedStageAuthorises
      Voice.questionContributorStage
      Governance.questionCoordinate

  codingContributorShapesProjection :
    RefinedStageAuthorises
      Voice.codingFrameContributorStage
      Governance.projectionCoordinate

  coInterpreterShapesRelevance :
    RefinedStageAuthorises
      Voice.coInterpreterStage
      Governance.relevanceCoordinate

  coDesignerShapesCarrier :
    RefinedStageAuthorises
      Voice.coDesignerStage
      Governance.carrierCoordinate

  coDesignerShapesConsumerFamily :
    RefinedStageAuthorises
      Voice.coDesignerStage
      Governance.consumerCoordinate

  coDesignerShapesQuestion :
    RefinedStageAuthorises
      Voice.coDesignerStage
      Governance.questionCoordinate

  coDesignerShapesProjection :
    RefinedStageAuthorises
      Voice.coDesignerStage
      Governance.projectionCoordinate

  coDesignerShapesDynamics :
    RefinedStageAuthorises
      Voice.coDesignerStage
      Governance.dynamicsCoordinate

  evidenceReviewerShapesResidual :
    RefinedStageAuthorises
      Voice.evidenceReturnReviewerStage
      Governance.residualCoordinate

  evidenceReviewerShapesRevision :
    RefinedStageAuthorises
      Voice.evidenceReturnReviewerStage
      Governance.revisionCoordinate

refinedStageGovernance :
  Governance.EpistemicGovernance Voice.EpistemicParticipationStage
refinedStageGovernance =
  Governance.epistemicGovernance RefinedStageAuthorises

feedbackSourceStillHasNoConstitutiveAuthority :
  (coordinate : Governance.InquiryCoordinate) →
  RefinedStageAuthorises Voice.feedbackSourceStage coordinate → ⊥
feedbackSourceStillHasNoConstitutiveAuthority coordinate ()

questionContributionDoesNotAutomaticallyChooseConsumerFamily :
  RefinedStageAuthorises
    Voice.questionContributorStage Governance.consumerCoordinate → ⊥
questionContributionDoesNotAutomaticallyChooseConsumerFamily ()

------------------------------------------------------------------------
-- Coordinate-wise authority level.  Voice itself is represented elsewhere;
-- therefore feedbackSourceStage remains noAuthority on every constitutive
-- coordinate even though it can contribute information.
------------------------------------------------------------------------

stageAuthorityLevel :
  Voice.EpistemicParticipationStage →
  Governance.InquiryCoordinate →
  Governance.AuthorityLevel
stageAuthorityLevel Voice.questionContributorStage Governance.questionCoordinate =
  Governance.coDeciding
stageAuthorityLevel Voice.codingFrameContributorStage Governance.projectionCoordinate =
  Governance.contesting
stageAuthorityLevel Voice.coInterpreterStage Governance.relevanceCoordinate =
  Governance.coDeciding
stageAuthorityLevel Voice.coDesignerStage Governance.carrierCoordinate =
  Governance.coDeciding
stageAuthorityLevel Voice.coDesignerStage Governance.consumerCoordinate =
  Governance.coDeciding
stageAuthorityLevel Voice.coDesignerStage Governance.questionCoordinate =
  Governance.coDeciding
stageAuthorityLevel Voice.coDesignerStage Governance.projectionCoordinate =
  Governance.coDeciding
stageAuthorityLevel Voice.coDesignerStage Governance.dynamicsCoordinate =
  Governance.coDeciding
stageAuthorityLevel Voice.evidenceReturnReviewerStage Governance.residualCoordinate =
  Governance.contesting
stageAuthorityLevel Voice.evidenceReturnReviewerStage Governance.revisionCoordinate =
  Governance.coDeciding
stageAuthorityLevel stage coordinate = Governance.noAuthority

brownKimberAuthorityProfile :
  Governance.EpistemicAuthorityProfile Voice.EpistemicParticipationStage
brownKimberAuthorityProfile =
  Governance.epistemicAuthorityProfile stageAuthorityLevel

feedbackAuthorityLevelIsZero :
  (coordinate : Governance.InquiryCoordinate) →
  Governance.authorityLevel brownKimberAuthorityProfile
    Voice.feedbackSourceStage coordinate
  ≡ Governance.noAuthority
feedbackAuthorityLevelIsZero coordinate = refl
