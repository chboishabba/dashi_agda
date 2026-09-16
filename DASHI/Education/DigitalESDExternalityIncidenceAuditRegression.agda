module DASHI.Education.DigitalESDExternalityIncidenceAuditRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDExternalityIncidenceAuditExact as Audit

questionCountRegression : Audit.externalityAuditQuestionCount ≡ 9
questionCountRegression = refl

aggregateDoesNotDetermineBurdenRegression :
  Audit.ExternalityIncidenceBoundary.aggregateOutcomeDeterminesBurden
    Audit.canonicalExternalityIncidenceBoundary
  ≡ false
aggregateDoesNotDetermineBurdenRegression = refl

contributionDoesNotEqualBurdenRegression :
  Audit.ExternalityIncidenceBoundary.contributionEqualsBurden
    Audit.canonicalExternalityIncidenceBoundary
  ≡ false
contributionDoesNotEqualBurdenRegression = refl

serviceDoesNotDeterminePowerRegression :
  Audit.ExternalityIncidenceBoundary.serviceSurfaceDeterminesPowerTopology
    Audit.canonicalExternalityIncidenceBoundary
  ≡ false
serviceDoesNotDeterminePowerRegression = refl

participationDoesNotDetermineMediationRegression :
  Audit.ExternalityIncidenceBoundary.participationDeterminesMediation
    Audit.canonicalExternalityIncidenceBoundary
  ≡ false
participationDoesNotDetermineMediationRegression = refl

presentBenefitDoesNotDetermineFutureBurdenRegression :
  Audit.ExternalityIncidenceBoundary.presentBenefitDeterminesLaterBurden
    Audit.canonicalExternalityIncidenceBoundary
  ≡ false
presentBenefitDoesNotDetermineFutureBurdenRegression = refl

petroleumLabelDoesNotDetermineStageRegression :
  Audit.ExternalityIncidenceBoundary.coarseMaterialLabelDeterminesLifecycleStage
    Audit.canonicalExternalityIncidenceBoundary
  ≡ false
petroleumLabelDoesNotDetermineStageRegression = refl

capacityPlanningDoesNotCreatePermanentChokepointRegression :
  Audit.ExternalityIncidenceBoundary.capacityPlanningDeterminesPermanentChokepoint
    Audit.canonicalExternalityIncidenceBoundary
  ≡ false
capacityPlanningDoesNotCreatePermanentChokepointRegression = refl

refiningMarginDoesNotDetermineConsumerBenefitRegression :
  Audit.ExternalityIncidenceBoundary.intermediateMarginDeterminesEndUserBenefit
    Audit.canonicalExternalityIncidenceBoundary
  ≡ false
refiningMarginDoesNotDetermineConsumerBenefitRegression = refl

politicalCalibrationDoesNotCreateDigitalESDConclusionRegression :
  Audit.CrossDomainCalibrationCreatesDigitalESDPoliticalConclusion → ⊥
politicalCalibrationDoesNotCreateDigitalESDConclusionRegression =
  Audit.crossDomainCalibrationDoesNotCreateDigitalESDPoliticalConclusion
