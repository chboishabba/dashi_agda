module DASHI.Cognition.PNF.SensibLawLandBackIncomeProjectionNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSocioeconomicModeratorHyperfabricExact as Moderator

------------------------------------------------------------------------
-- Synthetic mathematical witness: cash income is not a sufficient statistic
-- for the richer land/authority/relational state required by a LAND BACK
-- consumer.
--
-- This is a DASHI/SensibLaw representation theorem. It is NOT an empirical
-- assertion that any two named communities have identical income.
------------------------------------------------------------------------

data SituatedLandState : Set where
  sameCashIncomeDispossessed
  sameCashIncomeLandSecure
  : SituatedLandState

data CashIncomeObservation : Set where
  sameObservedCashIncome : CashIncomeObservation

data LandAuthorityOutcome : Set where
  landAuthorityAbsent
  landAuthorityPresent
  : LandAuthorityOutcome

cashIncomeObserver : SituatedLandState → CashIncomeObservation
cashIncomeObserver sameCashIncomeDispossessed = sameObservedCashIncome
cashIncomeObserver sameCashIncomeLandSecure = sameObservedCashIncome

landAuthorityOutcome : SituatedLandState → LandAuthorityOutcome
landAuthorityOutcome sameCashIncomeDispossessed = landAuthorityAbsent
landAuthorityOutcome sameCashIncomeLandSecure = landAuthorityPresent

landAuthorityOutcomesDiffer :
  landAuthorityOutcome sameCashIncomeDispossessed ≡
  landAuthorityOutcome sameCashIncomeLandSecure → ⊥
landAuthorityOutcomesDiffer ()

cashIncomeCannotRecoverLandAuthorityWitness :
  INF.NonFactorabilityWitness cashIncomeObserver landAuthorityOutcome
cashIncomeCannotRecoverLandAuthorityWitness =
  INF.nonFactorabilityWitness
    sameCashIncomeDispossessed
    sameCashIncomeLandSecure
    refl
    landAuthorityOutcomesDiffer

cashIncomeDoesNotFactorLandAuthority :
  INF.FactorsThrough cashIncomeObserver landAuthorityOutcome → ⊥
cashIncomeDoesNotFactorLandAuthority =
  INF.witnessRulesOutEveryFlatFactorisation
    cashIncomeCannotRecoverLandAuthorityWitness

cashIncomeReweightingStillCannotRecoverLandAuthority :
  ∀ {Recharted : Set} →
  (rechart : CashIncomeObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (cashIncomeObserver state))
    landAuthorityOutcome →
  ⊥
cashIncomeReweightingStillCannotRecoverLandAuthority rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart
    cashIncomeCannotRecoverLandAuthorityWitness

------------------------------------------------------------------------
-- Richer consumer coordinates that cash-income alone does not encode.
------------------------------------------------------------------------

data LandBackWellbeingCoordinate : Set where
  householdCashIncomeCoordinate
  incomeDistributionCoordinate
  collectiveLandSecurityCoordinate
  indigenousDecisionAuthorityCoordinate
  culturalContinuityCoordinate
  ecologicalIntegrityCoordinate
  externalityBurdenCoordinate
  serviceAccessCoordinate
  sovereigntyCapacityCoordinate
  : LandBackWellbeingCoordinate

record MetricAdequacyBoundary : Set where
  constructor metricAdequacyBoundary
  field
    metricReference : String
    targetReference : String
    cashIncomeIsUsefulIndicator : Bool
    cashIncomeIsUsefulIndicatorIsTrue : cashIncomeIsUsefulIndicator ≡ true
    cashIncomeIsSufficientStatisticForLandBackWellbeing : Bool
    cashIncomeIsSufficientStatisticForLandBackWellbeingIsFalse : cashIncomeIsSufficientStatisticForLandBackWellbeing ≡ false
    lowerCashIncomeProvesLowerRelationalWellbeing : Bool
    lowerCashIncomeProvesLowerRelationalWellbeingIsFalse : lowerCashIncomeProvesLowerRelationalWellbeing ≡ false
    cashIncomeMayStillBeLegallyPolicyRelevant : Bool
    cashIncomeMayStillBeLegallyPolicyRelevantIsTrue : cashIncomeMayStillBeLegallyPolicyRelevant ≡ true
    boundaryReference : String
open MetricAdequacyBoundary public

canonicalIncomeAdequacyBoundary : MetricAdequacyBoundary
canonicalIncomeAdequacyBoundary = metricAdequacyBoundary
  "mean monthly household cash income / fiscal-income observation"
  "multi-coordinate LAND BACK wellbeing, land authority and material-justice state"
  true refl
  false refl
  false refl
  true refl
  "income remains a valid selected socioeconomic indicator, but cannot by itself encode land security, authority, distribution, cultural continuity, ecology or externalized costs"

------------------------------------------------------------------------
-- Cross-pollination with the refined Amazon evidence decomposition.
------------------------------------------------------------------------

amazonIncomeStateRemainsComparatorSpecific :
  Moderator.incomeState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.incomePenaltyComparatorSpecific
amazonIncomeStateRemainsComparatorSpecific = refl

amazonInequalityStateRemainsSeparatelyPositiveOnSomeComparators :
  Moderator.inequalityState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.inequalityBenefitComparatorSpecific
amazonInequalityStateRemainsSeparatelyPositiveOnSomeComparators = refl

moderatorIdentificationRemainsOpen :
  Moderator.moderatorState Moderator.currentRefinedSocioeconomicAtlas
  ≡ Moderator.governanceModeratorIdentificationOpen
moderatorIdentificationRemainsOpen = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data CashIncomeSufficientForLandAuthority : Set where
data CashIncomeSufficientForEcologicalIntegrity : Set where
data CashIncomeSufficientForCulturalContinuity : Set where
data LowerIncomeMeansLowerTotalWellbeing : Set where

cashIncomeNotSufficientForLandAuthority : CashIncomeSufficientForLandAuthority → ⊥
cashIncomeNotSufficientForLandAuthority ()

cashIncomeNotSufficientForEcology : CashIncomeSufficientForEcologicalIntegrity → ⊥
cashIncomeNotSufficientForEcology ()

cashIncomeNotSufficientForCulture : CashIncomeSufficientForCulturalContinuity → ⊥
cashIncomeNotSufficientForCulture ()

lowerIncomeDoesNotFixTotalWellbeingOrdering : LowerIncomeMeansLowerTotalWellbeing → ⊥
lowerIncomeDoesNotFixTotalWellbeingOrdering ()
