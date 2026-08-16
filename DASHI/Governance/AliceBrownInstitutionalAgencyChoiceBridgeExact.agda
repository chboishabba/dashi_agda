module DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact where

------------------------------------------------------------------------
-- ALICE BROWN CORPUS -> INSTITUTIONAL ACCESS / AGENCY
--
-- Source-bound education papers are retained as their own fibres.  This bridge
-- imports only methodological constraints useful to institutional choice:
--
-- Alice Brown; Megan Kimber,
-- "Repositioning Student Voice and Agency: A Call for the Epistemic Expansion
-- of Scholarship of Teaching and Learning Inquiry",
-- Active Learning in Higher Education 27(2):253--264 (2026),
-- DOI 10.1177/14697874261426374.
--
-- Rachel Leslie; Melissa Fanshawe; Ellen Larsen; Alice Brown,
-- "The Perceptions Parents of Dyslexic Children Have on Barriers to Meaningful
-- Parent-School Partnerships in Australia", Exceptionality 33(1):40--58
-- (2025), DOI 10.1080/09362835.2024.2389081.
--
-- Rachel Leslie; Alice Brown; Ellen Larsen,
-- "Parental Allyship for Children With Dyslexia: A Conceptual Lens on
-- Disability Experience", Learning Disability Quarterly 48(1):3--12 (2025),
-- DOI 10.1177/07319487241251730.
--
-- These sources do NOT establish religious-school coercion, healthcare access,
-- or any named institutional wrong.  They supply source-bound participation,
-- observer-plurality and barrier vocabulary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Biology.ParentAllyshipMultiObserverBridge as Observers
import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Governance.EffectiveInstitutionalChoiceExact as Choice

------------------------------------------------------------------------
-- Three independent surfaces: option availability, subject participation,
-- and observer evidence.  None substitutes for the others.
------------------------------------------------------------------------

record InstitutionalAgencySurface : Set where
  constructor institutionalAgencySurface
  field
    formalOptionPresented : Bool
    effectivelyAccessible : Bool
    subjectCanContest : Bool
    subjectCanRefuse : Bool
    evidenceReturnedForReview : Bool

open InstitutionalAgencySurface public

data FormalOptionPromotesAgency : Set where

data ParentReportPromotesChildVoiceIdentity : Set where

data InstitutionRecordPromotesWholeSystemView : Set where

formalOptionDoesNotPromoteAgency : FormalOptionPromotesAgency → ⊥
formalOptionDoesNotPromoteAgency ()

parentReportDoesNotPromoteChildVoiceIdentity :
  ParentReportPromotesChildVoiceIdentity → ⊥
parentReportDoesNotPromoteChildVoiceIdentity ()

institutionRecordDoesNotPromoteWholeSystemView :
  InstitutionRecordPromotesWholeSystemView → ⊥
institutionRecordDoesNotPromoteWholeSystemView ()

------------------------------------------------------------------------
-- Existing source-bound theorems reused directly.
------------------------------------------------------------------------

surveyStillDoesNotEqualVoice :
  Voice.AdmissibleVoicePromotionRoute Voice.surveyEqualsVoiceRoute →
  Voice.Never
surveyStillDoesNotEqualVoice = Voice.surveyEqualsVoiceBlocked

invitationStillDoesNotEqualPartnership :
  Voice.AdmissibleVoicePromotionRoute Voice.invitationEqualsPartnershipRoute →
  Voice.Never
invitationStillDoesNotEqualPartnership = Voice.invitationEqualsPartnershipBlocked

studentObserver : Observers.ObserverProjection
studentObserver = Observers.canonicalStudentProjection

parentObserver : Observers.ObserverProjection
parentObserver = Observers.canonicalParentProjection

institutionObserver : Observers.ObserverProjection
institutionObserver = Observers.canonicalInstitutionProjection

studentAndParentRemainDistinctFibres : Bool
studentAndParentRemainDistinctFibres =
  Alice.studentAndParentObserverFibresRemainDistinct
    Alice.canonicalAliceBrownCorpusLoom

voicePaper : Sources.PaperReference
voicePaper = Sources.voiceAgencyPaper

parentBarrierPaper : Sources.PaperReference
parentBarrierPaper = Sources.partnershipBarriersPaper

parentAllyshipPaper : Sources.PaperReference
parentAllyshipPaper = Sources.parentalAllyshipLensPaper

record AliceInstitutionalChoiceBoundary : Set where
  constructor aliceInstitutionalChoiceBoundary
  field
    formalAvailabilityEqualsAgency : Bool
    studentVoiceCanBeReplacedByParentVoice : Bool
    parentExpertiseMayBeSituatedEvidence : Bool
    institutionalRecordEqualsWholeSystem : Bool
    participationAndAccessibilityAreDistinct : Bool
    sourcePapersEstablishReligiousCoercion : Bool

canonicalAliceInstitutionalChoiceBoundary : AliceInstitutionalChoiceBoundary
canonicalAliceInstitutionalChoiceBoundary =
  aliceInstitutionalChoiceBoundary false false true false true false
