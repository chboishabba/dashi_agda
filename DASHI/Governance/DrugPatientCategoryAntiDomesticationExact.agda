module DASHI.Governance.DrugPatientCategoryAntiDomesticationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition
import DASHI.Governance.FeministDrugClassificationAuthorityExact as Feminist

------------------------------------------------------------------------
-- PATIENT / USER VOICE AND ANTI-DOMESTICATION
--
-- Being admitted as a recognised patient/user voice can be real participation
-- while still withholding authority over the rule that decides which voices and
-- categories are admissible.  The exterior must remain representable as
-- exterior rather than being silently converted into nonexistence.
------------------------------------------------------------------------

data VoiceState : Set where
  admittedPatientVoice
  exteriorDrugUserVoice
  : VoiceState

data LegibilitySurface : Set where
  samePsychoactiveConcernSurface : LegibilitySurface

data MetaRuleStanding : Set where
  admittedWithoutMetaRulePower
  exteriorContestOfAdmissionRule
  : MetaRuleStanding

voiceSurface : VoiceState → LegibilitySurface
voiceSurface _ = samePsychoactiveConcernSurface

metaRuleStanding : VoiceState → MetaRuleStanding
metaRuleStanding admittedPatientVoice = admittedWithoutMetaRulePower
metaRuleStanding exteriorDrugUserVoice = exteriorContestOfAdmissionRule

sameConcernDifferentMetaRuleStanding :
  voiceSurface admittedPatientVoice ≡ voiceSurface exteriorDrugUserVoice
sameConcernDifferentMetaRuleStanding = refl

metaRuleStandingDiffers :
  metaRuleStanding admittedPatientVoice ≡
  metaRuleStanding exteriorDrugUserVoice → ⊥
metaRuleStandingDiffers ()

concernSurfaceCannotRecoverMetaRuleStanding :
  INF.FactorsThrough voiceSurface metaRuleStanding → ⊥
concernSurfaceCannotRecoverMetaRuleStanding =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      admittedPatientVoice exteriorDrugUserVoice refl (λ ()))

------------------------------------------------------------------------
-- Admitted category voice != authority over the admission/category rule.
------------------------------------------------------------------------

data CanAlterDrugCategoryAdmissionRule : VoiceState → Set where

admittedPatientVoiceCannotSelfIssueMetaRulePower :
  CanAlterDrugCategoryAdmissionRule admittedPatientVoice → ⊥
admittedPatientVoiceCannotSelfIssueMetaRulePower ()

record AdmittedPatientVoice : Set where
  constructor admittedPatientVoiceReceipt
  field
    participationIsReal : ⊤
    category : Feminist.DrugCategory
    ruleChangeAuthoritySeparate :
      CanAlterDrugCategoryAdmissionRule admittedPatientVoice → ⊥

canonicalAdmittedPatientVoice : AdmittedPatientVoice
canonicalAdmittedPatientVoice =
  admittedPatientVoiceReceipt tt Feminist.patientCategory
    admittedPatientVoiceCannotSelfIssueMetaRulePower

------------------------------------------------------------------------
-- Existing anti-domestication theorem retained directly.
------------------------------------------------------------------------

canonicalAntiDomestication : Opposition.AntiDomesticationRequirement
canonicalAntiDomestication = Opposition.canonicalAntiDomesticationRequirement

admittedOppositionStillCannotAutomaticallyAlterRule :
  Opposition.CanAlterAdmissionRule Opposition.recognisedOpposition → ⊥
admittedOppositionStillCannotAutomaticallyAlterRule =
  Opposition.recognisedOppositionCannotAutomaticallyAlterRule

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data RecognitionPromotesCoSovereignty : Set where

data ConsultationPromotesMetaRulePower : Set where

data NonAdmissionPromotesNonexistence : Set where

data PatientLabelPromotesOriginatingSubjectAuthority : Set where

recognitionDoesNotPromoteCoSovereignty : RecognitionPromotesCoSovereignty → ⊥
recognitionDoesNotPromoteCoSovereignty ()

consultationDoesNotPromoteMetaRulePower : ConsultationPromotesMetaRulePower → ⊥
consultationDoesNotPromoteMetaRulePower ()

nonAdmissionDoesNotPromoteNonexistence : NonAdmissionPromotesNonexistence → ⊥
nonAdmissionDoesNotPromoteNonexistence ()

patientLabelDoesNotPromoteOriginatingAuthority :
  PatientLabelPromotesOriginatingSubjectAuthority → ⊥
patientLabelDoesNotPromoteOriginatingAuthority ()

record DrugPatientAntiDomesticationBoundary : Set where
  constructor drugPatientAntiDomesticationBoundary
  field
    admittedPatientVoiceMayBeReal : Bool
    admittedPatientVoiceMayBeRealIsTrue : admittedPatientVoiceMayBeReal ≡ true
    admittedVoiceOwnsCategoryAdmissionRule : Bool
    admittedVoiceOwnsCategoryAdmissionRuleIsFalse :
      admittedVoiceOwnsCategoryAdmissionRule ≡ false
    exteriorVoiceMustRemainRepresentable : Bool
    exteriorVoiceMustRemainRepresentableIsTrue :
      exteriorVoiceMustRemainRepresentable ≡ true
    patientRecognitionEqualsOriginatingAuthority : Bool
    patientRecognitionEqualsOriginatingAuthorityIsFalse :
      patientRecognitionEqualsOriginatingAuthority ≡ false

canonicalDrugPatientAntiDomesticationBoundary :
  DrugPatientAntiDomesticationBoundary
canonicalDrugPatientAntiDomesticationBoundary =
  drugPatientAntiDomesticationBoundary
    true refl false refl true refl false refl
