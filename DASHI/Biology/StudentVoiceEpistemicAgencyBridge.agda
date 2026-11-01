module DASHI.Biology.StudentVoiceEpistemicAgencyBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.OEFAIFeedbackFormalisation as OEF

------------------------------------------------------------------------
-- Student voice and epistemic agency correction.
--
-- The 2026 Brown/Kimber paper is not collapsed into the 2024 AI-feedback
-- paper.  It supplies a later methodological correction: soliciting feedback
-- alone does not make students co-producers of knowledge.

data Never : Set where

data EpistemicParticipationStage : Set where
  feedbackSourceStage : EpistemicParticipationStage
  questionContributorStage : EpistemicParticipationStage
  codingFrameContributorStage : EpistemicParticipationStage
  coInterpreterStage : EpistemicParticipationStage
  coDesignerStage : EpistemicParticipationStage
  evidenceReturnReviewerStage : EpistemicParticipationStage

canonicalEpistemicParticipationStages : List EpistemicParticipationStage
canonicalEpistemicParticipationStages =
  feedbackSourceStage
  ∷ questionContributorStage
  ∷ codingFrameContributorStage
  ∷ coInterpreterStage
  ∷ coDesignerStage
  ∷ evidenceReturnReviewerStage
  ∷ []

stageName : EpistemicParticipationStage → String
stageName feedbackSourceStage = "feedback source"
stageName questionContributorStage = "research-question contributor"
stageName codingFrameContributorStage = "coding-frame contributor"
stageName coInterpreterStage = "co-interpreter"
stageName coDesignerStage = "co-designer"
stageName evidenceReturnReviewerStage = "evidence-return reviewer"

data VoicePromotionRoute : Set where
  candidateEpistemicParticipationRoute : VoicePromotionRoute
  surveyEqualsVoiceRoute : VoicePromotionRoute
  feedbackEqualsAgencyRoute : VoicePromotionRoute
  researcherInterpretationEqualsCoProductionRoute : VoicePromotionRoute
  invitationEqualsPartnershipRoute : VoicePromotionRoute
  coDesignEqualsAutomaticJusticeRoute : VoicePromotionRoute

AdmissibleVoicePromotionRoute : VoicePromotionRoute → Set
AdmissibleVoicePromotionRoute candidateEpistemicParticipationRoute = ⊤
AdmissibleVoicePromotionRoute surveyEqualsVoiceRoute = Never
AdmissibleVoicePromotionRoute feedbackEqualsAgencyRoute = Never
AdmissibleVoicePromotionRoute researcherInterpretationEqualsCoProductionRoute = Never
AdmissibleVoicePromotionRoute invitationEqualsPartnershipRoute = Never
AdmissibleVoicePromotionRoute coDesignEqualsAutomaticJusticeRoute = Never

surveyEqualsVoiceBlocked :
  AdmissibleVoicePromotionRoute surveyEqualsVoiceRoute → Never
surveyEqualsVoiceBlocked ()

feedbackEqualsAgencyBlocked :
  AdmissibleVoicePromotionRoute feedbackEqualsAgencyRoute → Never
feedbackEqualsAgencyBlocked ()

researcherInterpretationEqualsCoProductionBlocked :
  AdmissibleVoicePromotionRoute researcherInterpretationEqualsCoProductionRoute → Never
researcherInterpretationEqualsCoProductionBlocked ()

invitationEqualsPartnershipBlocked :
  AdmissibleVoicePromotionRoute invitationEqualsPartnershipRoute → Never
invitationEqualsPartnershipBlocked ()

record EpistemicAgencyGate : Set where
  constructor mkEpistemicAgencyGate
  field
    studentsMayShapeQuestions : Bool
    studentsMayShapeQuestionsIsTrue : studentsMayShapeQuestions ≡ true
    studentsMayContestCodingFrame : Bool
    studentsMayContestCodingFrameIsTrue : studentsMayContestCodingFrame ≡ true
    studentsMayCoInterpretOutputs : Bool
    studentsMayCoInterpretOutputsIsTrue : studentsMayCoInterpretOutputs ≡ true
    studentsMayChooseOrRejectHandle : Bool
    studentsMayChooseOrRejectHandleIsTrue : studentsMayChooseOrRejectHandle ≡ true
    evidenceReturnedForReview : Bool
    evidenceReturnedForReviewIsTrue : evidenceReturnedForReview ≡ true
    participationNotForced : Bool
    participationNotForcedIsTrue : participationNotForced ≡ true

open EpistemicAgencyGate public

canonicalEpistemicAgencyGate : EpistemicAgencyGate
canonicalEpistemicAgencyGate =
  mkEpistemicAgencyGate
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

record StudentVoiceEpistemicAgencyBridge : Set where
  constructor mkStudentVoiceEpistemicAgencyBridge
  field
    sourcePaper : Sources.PaperReference
    sourcePaperIsCanonical : sourcePaper ≡ Sources.voiceAgencyPaper
    priorAIFormalisation : OEF.OEFAIFeedbackFormalisation
    priorAIFormalisationIsCanonical :
      priorAIFormalisation ≡ OEF.canonicalOEFAIFeedbackFormalisation
    participationStages : List EpistemicParticipationStage
    participationStagesAreCanonical :
      participationStages ≡ canonicalEpistemicParticipationStages
    agencyGate : EpistemicAgencyGate
    agencyGateIsCanonical : agencyGate ≡ canonicalEpistemicAgencyGate
    route : VoicePromotionRoute
    routeIsCandidate : route ≡ candidateEpistemicParticipationRoute
    routeAdmissible : AdmissibleVoicePromotionRoute route
    laterPaperCorrectsExtractiveRisk : Bool
    laterPaperCorrectsExtractiveRiskIsTrue :
      laterPaperCorrectsExtractiveRisk ≡ true
    studentsRemainSituatedEpistemicAgents : Bool
    studentsRemainSituatedEpistemicAgentsIsTrue :
      studentsRemainSituatedEpistemicAgents ≡ true
    noAutomaticEpistemicAuthority : Bool
    noAutomaticEpistemicAuthorityIsTrue :
      noAutomaticEpistemicAuthority ≡ true
    reading : String

open StudentVoiceEpistemicAgencyBridge public

canonicalStudentVoiceEpistemicAgencyBridge :
  StudentVoiceEpistemicAgencyBridge
canonicalStudentVoiceEpistemicAgencyBridge =
  mkStudentVoiceEpistemicAgencyBridge
    Sources.voiceAgencyPaper refl
    OEF.canonicalOEFAIFeedbackFormalisation refl
    canonicalEpistemicParticipationStages refl
    canonicalEpistemicAgencyGate refl
    candidateEpistemicParticipationRoute refl tt
    true refl
    true refl
    true refl
    "Brown and Kimber's epistemic-expansion paper is retained as a methodological correction to feedback-only SoTL: students may participate in question formation, coding-frame contestation, interpretation, co-design and evidence return. Survey capture alone does not become voice or agency, and co-design does not automatically become just or representative."

SurveyNotVoice : Set
SurveyNotVoice =
  AdmissibleVoicePromotionRoute surveyEqualsVoiceRoute → Never

surveyNotVoiceProof : SurveyNotVoice
surveyNotVoiceProof = surveyEqualsVoiceBlocked
