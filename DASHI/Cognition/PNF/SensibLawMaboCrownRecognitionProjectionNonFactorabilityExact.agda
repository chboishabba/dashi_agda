module DASHI.Cognition.PNF.SensibLawMaboCrownRecognitionProjectionNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- Synthetic representation witness.
--
-- This does not assert facts about named Indigenous communities. It proves that
-- a Crown-recognition-only observer is structurally too coarse to determine the
-- independently modelled Indigenous Country/community-authority state.
------------------------------------------------------------------------

data SituatedCrossOrderState : Set where
  sameCrownRecognitionWeakCommunityAuthority : SituatedCrossOrderState
  sameCrownRecognitionStrongCommunityAuthority : SituatedCrossOrderState


data CrownRecognitionObservation : Set where
  sameCrownRecognitionStatus : CrownRecognitionObservation

data IndigenousAuthorityOutcome : Set where
  communityAuthorityConstrained : IndigenousAuthorityOutcome
  communityAuthorityEffective : IndigenousAuthorityOutcome


crownRecognitionObserver : SituatedCrossOrderState → CrownRecognitionObservation
crownRecognitionObserver sameCrownRecognitionWeakCommunityAuthority = sameCrownRecognitionStatus
crownRecognitionObserver sameCrownRecognitionStrongCommunityAuthority = sameCrownRecognitionStatus

indigenousAuthorityOutcome : SituatedCrossOrderState → IndigenousAuthorityOutcome
indigenousAuthorityOutcome sameCrownRecognitionWeakCommunityAuthority = communityAuthorityConstrained
indigenousAuthorityOutcome sameCrownRecognitionStrongCommunityAuthority = communityAuthorityEffective

authorityOutcomesDiffer :
  indigenousAuthorityOutcome sameCrownRecognitionWeakCommunityAuthority ≡
  indigenousAuthorityOutcome sameCrownRecognitionStrongCommunityAuthority → ⊥
authorityOutcomesDiffer ()

crownRecognitionCannotRecoverIndigenousAuthorityWitness :
  INF.NonFactorabilityWitness crownRecognitionObserver indigenousAuthorityOutcome
crownRecognitionCannotRecoverIndigenousAuthorityWitness =
  INF.nonFactorabilityWitness
    sameCrownRecognitionWeakCommunityAuthority
    sameCrownRecognitionStrongCommunityAuthority
    refl
    authorityOutcomesDiffer

crownRecognitionDoesNotFactorIndigenousAuthority :
  INF.FactorsThrough crownRecognitionObserver indigenousAuthorityOutcome → ⊥
crownRecognitionDoesNotFactorIndigenousAuthority =
  INF.witnessRulesOutEveryFlatFactorisation
    crownRecognitionCannotRecoverIndigenousAuthorityWitness

crownRecognitionRechartingStillCannotRecoverIndigenousAuthority :
  ∀ {Recharted : Set} →
  (rechart : CrownRecognitionObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (crownRecognitionObserver state))
    indigenousAuthorityOutcome →
  ⊥
crownRecognitionRechartingStillCannotRecoverIndigenousAuthority rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart
    crownRecognitionCannotRecoverIndigenousAuthorityWitness

------------------------------------------------------------------------
-- Interface boundary: recognition is relational, not ontological creation.
------------------------------------------------------------------------

record CrownRecognitionObserverBoundary : Set where
  constructor crownRecognitionObserverBoundary
  field
    interfaceReference : String
    crownRecognitionMayAffectMunicipalLegalStatus : Bool
    crownRecognitionMayAffectMunicipalLegalStatusIsTrue : crownRecognitionMayAffectMunicipalLegalStatus ≡ true
    crownRecognitionCreatesIndigenousOrder : Bool
    crownRecognitionCreatesIndigenousOrderIsFalse : crownRecognitionCreatesIndigenousOrder ≡ false
    crownRecognitionExhaustsCountryRelation : Bool
    crownRecognitionExhaustsCountryRelationIsFalse : crownRecognitionExhaustsCountryRelation ≡ false
    crownRecognitionExhaustsCommunityAuthority : Bool
    crownRecognitionExhaustsCommunityAuthorityIsFalse : crownRecognitionExhaustsCommunityAuthority ≡ false
open CrownRecognitionObserverBoundary public

canonicalCrownRecognitionObserverBoundary : CrownRecognitionObserverBoundary
canonicalCrownRecognitionObserverBoundary = crownRecognitionObserverBoundary
  (TwoOrder.interfaceReference TwoOrder.nativeTitleRecognitionInterface)
  true refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Cross-check existing two-order boundaries.
------------------------------------------------------------------------

indigenousOrderExistenceNotCourtDetermined :
  TwoOrder.courtDeterminesOrderExistence TwoOrder.indigenousOrderFibre ≡ false
indigenousOrderExistenceNotCourtDetermined = refl

indigenousOrderNotCreatedByExternalRecognition :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
indigenousOrderNotCreatedByExternalRecognition = refl

nativeTitleInterfaceNotGloballySupreme :
  TwoOrder.crownOrderGloballySupreme TwoOrder.nativeTitleRecognitionInterface ≡ false
nativeTitleInterfaceNotGloballySupreme = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data CrownRecognitionSufficientForCommunityAuthority : Set where
data CrownRecognitionSufficientForCountryRelation : Set where
data CrownRecognitionCreatesIndigenousNormativeOrder : Set where

aRecognitionNotSufficientForCommunityAuthority : CrownRecognitionSufficientForCommunityAuthority → ⊥
aRecognitionNotSufficientForCommunityAuthority ()

recognitionNotSufficientForCountryRelation : CrownRecognitionSufficientForCountryRelation → ⊥
recognitionNotSufficientForCountryRelation ()

recognitionDoesNotCreateIndigenousNormativeOrder : CrownRecognitionCreatesIndigenousNormativeOrder → ⊥
recognitionDoesNotCreateIndigenousNormativeOrder ()
