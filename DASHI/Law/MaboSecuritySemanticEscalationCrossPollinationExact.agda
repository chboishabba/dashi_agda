module DASHI.Law.MaboSecuritySemanticEscalationCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact as Mabo
import DASHI.Law.MaboCountrySecurityClassificationCrossPollinationExact as Country
import DASHI.Law.SecuritySemanticEscalationDistanceExact as Esc

------------------------------------------------------------------------
-- Dynamic x-pollination: recognition/classification can remain administratively
-- stable while underlying Country/authority meaning is progressively erased.
------------------------------------------------------------------------

data RecognitionEscalationState : Set where
  sameAdministrativeSurfaceAuthorityVisible : RecognitionEscalationState
  sameAdministrativeSurfaceAuthorityErased : RecognitionEscalationState


data AdministrativeSurface : Set where
  sameRecognisedSecuritySurface : AdministrativeSurface

data AuthorityMeaning : Set where
  antecedentAuthorityVisible : AuthorityMeaning
  antecedentAuthorityInvisible : AuthorityMeaning

observeAdministrative : RecognitionEscalationState → AdministrativeSurface
observeAdministrative sameAdministrativeSurfaceAuthorityVisible = sameRecognisedSecuritySurface
observeAdministrative sameAdministrativeSurfaceAuthorityErased = sameRecognisedSecuritySurface

authorityMeaning : RecognitionEscalationState → AuthorityMeaning
authorityMeaning sameAdministrativeSurfaceAuthorityVisible = antecedentAuthorityVisible
authorityMeaning sameAdministrativeSurfaceAuthorityErased = antecedentAuthorityInvisible

authorityMeaningDiffers :
  authorityMeaning sameAdministrativeSurfaceAuthorityVisible ≡
  authorityMeaning sameAdministrativeSurfaceAuthorityErased → ⊥
authorityMeaningDiffers ()

administrativeSurfaceCannotRecoverAuthority :
  INF.FactorsThrough observeAdministrative authorityMeaning → ⊥
administrativeSurfaceCannotRecoverAuthority =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameAdministrativeSurfaceAuthorityVisible
      sameAdministrativeSurfaceAuthorityErased
      refl
      authorityMeaningDiffers)

maboRecognitionNonfactorabilityRetained :
  INF.FactorsThrough Mabo.crownRecognitionObserver Mabo.indigenousAuthorityOutcome → ⊥
maboRecognitionNonfactorabilityRetained = Mabo.crownRecognitionDoesNotFactorIndigenousAuthority

securityCountryNonfactorabilityRetained :
  INF.FactorsThrough Country.securityObserver Country.politicalAuthorityOutcome → ⊥
securityCountryNonfactorabilityRetained = Country.securityClassificationCannotFactorAuthority

------------------------------------------------------------------------
-- BIDI producer routing.
------------------------------------------------------------------------

data DynamicCountryClaim : Set where
  semanticEscalationErasedCountryMeaning : DynamicCountryClaim
  recognitionSurfaceRemainedStableDuringErasure : DynamicCountryClaim
  escalationConvertedPoliticalMeaningIntoThreatMeaning : DynamicCountryClaim
  escalationReachedCollectiveEnemyStage : DynamicCountryClaim
  escalationReachedTerminalisingPractice : DynamicCountryClaim

data DynamicCountryProducer : Set where
  beforeAfterCountryMeaningProducer : DynamicCountryProducer
  stableAdministrativeSurfaceProducer : DynamicCountryProducer
  semanticTransformationAndCountryProducer : DynamicCountryProducer
  collectiveEnemyClassificationProducer : DynamicCountryProducer
  terminalisationCommandConductProducer : DynamicCountryProducer

reverseDynamicCountry : DynamicCountryClaim → DynamicCountryProducer
reverseDynamicCountry semanticEscalationErasedCountryMeaning = beforeAfterCountryMeaningProducer
reverseDynamicCountry recognitionSurfaceRemainedStableDuringErasure = stableAdministrativeSurfaceProducer
reverseDynamicCountry escalationConvertedPoliticalMeaningIntoThreatMeaning = semanticTransformationAndCountryProducer
reverseDynamicCountry escalationReachedCollectiveEnemyStage = collectiveEnemyClassificationProducer
reverseDynamicCountry escalationReachedTerminalisingPractice = terminalisationCommandConductProducer

record MaboEscalationBoundary : Set where
  constructor maboEscalationBoundary
  field
    sharedCompressionMeansSameColonialHistory : Bool
    sharedCompressionMeansSameColonialHistoryIsFalse : sharedCompressionMeansSameColonialHistory ≡ false
    semanticEscalationProvesColonialIntent : Bool
    semanticEscalationProvesColonialIntentIsFalse : semanticEscalationProvesColonialIntent ≡ false
    crownRecognitionCreatesCountryAuthority : Bool
    crownRecognitionCreatesCountryAuthorityIsFalse : crownRecognitionCreatesCountryAuthority ≡ false
    securityClassificationCreatesPoliticalMeaning : Bool
    securityClassificationCreatesPoliticalMeaningIsFalse : securityClassificationCreatesPoliticalMeaning ≡ false
    countryErasureCanBeInferredWithoutBeforeAfterReceipts : Bool
    countryErasureCanBeInferredWithoutBeforeAfterReceiptsIsFalse : countryErasureCanBeInferredWithoutBeforeAfterReceipts ≡ false

canonicalMaboEscalationBoundary : MaboEscalationBoundary
canonicalMaboEscalationBoundary =
  maboEscalationBoundary false refl false refl false refl false refl false refl

escalationProducer : Esc.EscalationProducer
escalationProducer = Esc.orderedSameObjectPathProducer
