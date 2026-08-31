module DASHI.Biology.AliceBrownEducationAuditAdmissibilityCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AliceBrownCorpusLoom as Loom
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Biology.StudentIdentifiedSupportStrategiesBridge as Strategies
import DASHI.Biology.ParentAllyshipMultiObserverBridge as Multi
import DASHI.Biology.HumourOnlineEngagementFramework as Humour
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design

------------------------------------------------------------------------
-- ALICE BROWN -> EDUCATION CLAIM-AUDIT CROSS-POLLINATION
--
-- Attribution rule:
--   * Brown et al. source surfaces remain source-bounded;
--   * the audit gates below are DASHI constructions using those source fibres
--     as regression/counterexample material;
--   * this module does not claim Alice Brown, Kimber, Getenet, Burke,
--     Fanshawe, Pryce, Pabel or the dyslexia papers proposed the ACPUE/AERO
--     audit architecture or evaluated AERO.
------------------------------------------------------------------------

canonicalLoom : Loom.AliceBrownCorpusLoom
canonicalLoom = Loom.canonicalAliceBrownCorpusLoom

------------------------------------------------------------------------
-- 1. PARTICIPATION / EPISTEMIC-ROLE GATE
--
-- Student feedback, survey response and researcher interpretation are not
-- definitionally student epistemic agency.  Therefore assertions about what
-- students experience, prefer, need or judge require an explicit observer/
-- participation receipt rather than inheriting the researcher's role.
------------------------------------------------------------------------

data ParticipationClaimRoute : Set where
  situatedParticipantEvidenceRoute
  surveyEqualsVoiceRoute
  feedbackEqualsAgencyRoute
  researcherInterpretationEqualsStudentJudgementRoute
  invitationEqualsPartnershipRoute : ParticipationClaimRoute

data AdmissibleParticipationClaimRoute : ParticipationClaimRoute → Set where
  situatedParticipantEvidenceAdmissible :
    AdmissibleParticipationClaimRoute situatedParticipantEvidenceRoute

surveyDoesNotBecomeVoice :
  ¬ AdmissibleParticipationClaimRoute surveyEqualsVoiceRoute
surveyDoesNotBecomeVoice ()

feedbackDoesNotBecomeAgency :
  ¬ AdmissibleParticipationClaimRoute feedbackEqualsAgencyRoute
feedbackDoesNotBecomeAgency ()

researcherInterpretationDoesNotBecomeStudentJudgement :
  ¬ AdmissibleParticipationClaimRoute
      researcherInterpretationEqualsStudentJudgementRoute
researcherInterpretationDoesNotBecomeStudentJudgement ()

invitationDoesNotBecomePartnership :
  ¬ AdmissibleParticipationClaimRoute invitationEqualsPartnershipRoute
invitationDoesNotBecomePartnership ()

voiceSourceBoundaryRetained : Bool
voiceSourceBoundaryRetained =
  Voice.noAutomaticEpistemicAuthority
    Voice.canonicalStudentVoiceEpistemicAgencyBridge

------------------------------------------------------------------------
-- 2. LOCAL-CHOICE / UNIVERSAL-PRESCRIPTION GATE
--
-- The student-identified support-strategy owner explicitly retains the five
-- support families as local, optional, many-to-many candidates.  A source-
-- bounded support theme is therefore not itself a universal causal or
-- prescriptive rule.
------------------------------------------------------------------------

data SupportPromotionRoute : Set where
  localCandidateRoute
  identifiedThemeEqualsUniversalInterventionRoute
  localPreferenceEqualsCausalEffectRoute
  oneContextEqualsAllLearnersRoute : SupportPromotionRoute

data AdmissibleSupportPromotionRoute : SupportPromotionRoute → Set where
  localCandidateAdmissible : AdmissibleSupportPromotionRoute localCandidateRoute

identifiedThemeDoesNotBecomeUniversalIntervention :
  ¬ AdmissibleSupportPromotionRoute
      identifiedThemeEqualsUniversalInterventionRoute
identifiedThemeDoesNotBecomeUniversalIntervention ()

localPreferenceDoesNotBecomeCausalEffect :
  ¬ AdmissibleSupportPromotionRoute localPreferenceEqualsCausalEffectRoute
localPreferenceDoesNotBecomeCausalEffect ()

oneContextDoesNotBecomeAllLearners :
  ¬ AdmissibleSupportPromotionRoute oneContextEqualsAllLearnersRoute
oneContextDoesNotBecomeAllLearners ()

strategiesRemainNonUniversal : Bool
strategiesRemainNonUniversal =
  Strategies.noUniversalPrescription
    Strategies.canonicalStudentIdentifiedSupportStrategiesBridge

------------------------------------------------------------------------
-- 3. MULTI-OBSERVER GATE
--
-- Student, parent, teacher, researcher, institution and model projections are
-- all situated fibres.  A national evidence synthesis can aggregate them, but
-- no single projection is licensed to erase the others or to stand for the
-- complete educational state.
------------------------------------------------------------------------

data ObserverPromotionRoute : Set where
  pluralObserverRoute
  researcherEqualsWholeSystemRoute
  institutionEqualsStudentExperienceRoute
  parentEqualsChildVoiceRoute
  modelEqualsSemanticExperienceRoute : ObserverPromotionRoute

data AdmissibleObserverPromotionRoute : ObserverPromotionRoute → Set where
  pluralObserverAdmissible : AdmissibleObserverPromotionRoute pluralObserverRoute

researcherProjectionDoesNotEqualWhole :
  ¬ AdmissibleObserverPromotionRoute researcherEqualsWholeSystemRoute
researcherProjectionDoesNotEqualWhole ()

institutionDoesNotEqualStudentExperience :
  ¬ AdmissibleObserverPromotionRoute institutionEqualsStudentExperienceRoute
institutionDoesNotEqualStudentExperience ()

parentDoesNotEqualChildVoice :
  ¬ AdmissibleObserverPromotionRoute parentEqualsChildVoiceRoute
parentDoesNotEqualChildVoice ()

modelDoesNotEqualSemanticExperience :
  ¬ AdmissibleObserverPromotionRoute modelEqualsSemanticExperienceRoute
modelDoesNotEqualSemanticExperience ()

multiObserverNonCollapseRetained : Bool
multiObserverNonCollapseRetained =
  Multi.noObserverProjectionEqualsWhole
    Multi.canonicalParentAllyshipMultiObserverBridge

------------------------------------------------------------------------
-- 4. CONDITIONAL-INTERVENTION GATE
--
-- Brown/Pryce/Pabel's humour source is a seven-consideration framework.  Its
-- source grammar gives a useful regression against collapsing a conditional,
-- context-sensitive practice into an atomic universal intervention slogan.
------------------------------------------------------------------------

record ConditionalPracticeShape : Set where
  constructor conditionalPracticeShape
  field
    rationaleRequired : Bool
    presenterCondition : Bool
    audienceContextCondition : Bool
    contentCondition : Bool
    deliveryCondition : Bool
    practiceTypeCondition : Bool
    feedbackCondition : Bool

canonicalHumourConditionalShape : ConditionalPracticeShape
canonicalHumourConditionalShape =
  conditionalPracticeShape true true true true true true true

data ConditionalPromotionRoute : Set where
  retainConditionsRoute
  dropAudienceContextRoute
  dropFeedbackRoute
  conditionalPracticeEqualsUniversalEffectRoute : ConditionalPromotionRoute

data AdmissibleConditionalPromotionRoute : ConditionalPromotionRoute → Set where
  retainConditionsAdmissible :
    AdmissibleConditionalPromotionRoute retainConditionsRoute

dropAudienceContextBlocked :
  ¬ AdmissibleConditionalPromotionRoute dropAudienceContextRoute
dropAudienceContextBlocked ()

dropFeedbackBlocked :
  ¬ AdmissibleConditionalPromotionRoute dropFeedbackRoute
dropFeedbackBlocked ()

conditionalPracticeDoesNotBecomeUniversalEffect :
  ¬ AdmissibleConditionalPromotionRoute
      conditionalPracticeEqualsUniversalEffectRoute
conditionalPracticeDoesNotBecomeUniversalEffect ()

humourFrameworkPreservesContext : Bool
humourFrameworkPreservesContext =
  Humour.futureWorkSeeksStudentPerspectives
    Humour.canonicalHumourFrameworkSourceSurface

------------------------------------------------------------------------
-- 5. AUDIT-SIDE OBLIGATION BUNDLE
--
-- These are not new empirical conclusions.  They are extra questions that a
-- high-consequence education assertion should expose when its content concerns
-- learner experience, universal applicability, intervention choice or
-- downstream institutional use.
------------------------------------------------------------------------

data BrownDerivedAuditObligationKind : Set where
  participantRoleObligation
  observerPluralityObligation
  localChoiceObligation
  conditionalContextObligation
  epistemicReturnObligation
  representationBoundaryObligation : BrownDerivedAuditObligationKind

record BrownDerivedAuditObligation : Set where
  constructor brownDerivedAuditObligation
  field
    kind : BrownDerivedAuditObligationKind
    question : String
    sourceRole : String
    dashiReading : String

open BrownDerivedAuditObligation public

canonicalBrownDerivedAuditObligations : List BrownDerivedAuditObligation
canonicalBrownDerivedAuditObligations =
  brownDerivedAuditObligation
    participantRoleObligation
    "Whose experience or judgement is asserted, and what epistemic role did those participants actually occupy?"
    "Brown/Kimber student voice and epistemic agency source fibre"
    "feedback/survey response is not silently promoted to co-production or governing authority"
  ∷ brownDerivedAuditObligation
    observerPluralityObligation
    "Which observer fibres are represented, and which relevant observers are absent or only indirectly represented?"
    "Brown/dyslexia parent-allyship multi-observer corpus"
    "one situated projection cannot stand for the complete educational state"
  ∷ brownDerivedAuditObligation
    localChoiceObligation
    "Is a locally identified support/preference being promoted into a universal intervention or prescription?"
    "Getenet/Burke/Fanshawe/Brown student-identified support strategies"
    "candidate local supports remain optional and many-to-many unless causal/transport receipts are added"
  ∷ brownDerivedAuditObligation
    conditionalContextObligation
    "Which contextual conditions are constitutive of the practice claim, and have any been dropped downstream?"
    "Brown/Pryce/Pabel humour framework"
    "rationale, presenter, audience/context, content, delivery, practice type and feedback remain distinct conditions"
  ∷ brownDerivedAuditObligation
    epistemicReturnObligation
    "Was evidence/interpretation returned to participants for contestation or review where the claim depends on their situated meaning?"
    "Brown/Kimber epistemic participation stages"
    "interpretive authority remains reviewable rather than acquired automatically by the researcher or model"
  ∷ brownDerivedAuditObligation
    representationBoundaryObligation
    "Does a model, institutional record, parent report or researcher coding stand in for a different observer's lived/semantic state?"
    "Alice Brown corpus loom / multi-observer and AI-feedback fibres"
    "representation is retained as a projection, not promoted into transparent access to the whole state"
  ∷ []

------------------------------------------------------------------------
-- 6. COMMISSION / AERO CONSEQUENCE
------------------------------------------------------------------------

record BrownCommissionAuditGate : Set where
  constructor brownCommissionAuditGate
  field
    preserveParticipantRole : Bool
    preserveObserverPlurality : Bool
    preserveLocalChoice : Bool
    preserveConditionalContext : Bool
    preserveContestability : Bool
    preserveRepresentationBoundary : Bool
    sourceClaimsRemainDistinctFromDASHIGates : Bool

canonicalBrownCommissionAuditGate : BrownCommissionAuditGate
canonicalBrownCommissionAuditGate =
  brownCommissionAuditGate true true true true true true true

record AliceBrownAuditCrossPollinationBoundary : Set where
  constructor aliceBrownAuditCrossPollinationBoundary
  field
    aliceBrownCorpusDisprovesAERO : Bool
    studentVoiceMeansStudentsGovernAllPolicy : Bool
    localStudentPreferenceIsUniversalCausalLaw : Bool
    parentObservationEqualsChildExperience : Bool
    researcherCodingEqualsParticipantMeaning : Bool
    conditionalFrameworkEqualsUniversalIntervention : Bool
    brownCorpusSuppliesAuditCounterexamplesAndScopeConstraints : Bool
    dashiAuditInferencesRemainDASHIInferences : Bool

canonicalAliceBrownAuditCrossPollinationBoundary :
  AliceBrownAuditCrossPollinationBoundary
canonicalAliceBrownAuditCrossPollinationBoundary =
  aliceBrownAuditCrossPollinationBoundary
    false false false false false false true true
