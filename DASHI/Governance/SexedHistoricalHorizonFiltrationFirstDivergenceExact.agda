module DASHI.Governance.SexedHistoricalHorizonFiltrationFirstDivergenceExact where

------------------------------------------------------------------------
-- HORIZON FILTRATION / FIRST FORECAST DIVERGENCE
--
-- Two fine histories can agree on short- and medium-horizon continuation codes
-- while diverging only at a longer horizon.  The first horizon exposing a
-- divergence is an observation-depth fact, not a historical change point.
--
-- Structural cross-pollination:
--   * history-conditioned future-cone non-descent;
--   * prior prefix/first-divergence style DASHI reasoning;
--   * LES history-conditioned continuation cones.
--
-- No empirical forecast, p-adic valuation identity, or environmental effect
-- size is asserted here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Environment.LESResearchCrossPollinationRound7Exact as LES7
import DASHI.Governance.SexedHistoricalStratifiedFutureConeQuotientExact as Future

------------------------------------------------------------------------
-- 1. Forecast horizons and monotone depth order.
------------------------------------------------------------------------

data Horizon : Set where
  shortHorizon mediumHorizon longHorizon : Horizon

data HorizonLe : Horizon → Horizon → Set where
  shortRefl : HorizonLe shortHorizon shortHorizon
  shortToMedium : HorizonLe shortHorizon mediumHorizon
  shortToLong : HorizonLe shortHorizon longHorizon
  mediumRefl : HorizonLe mediumHorizon mediumHorizon
  mediumToLong : HorizonLe mediumHorizon longHorizon
  longRefl : HorizonLe longHorizon longHorizon

------------------------------------------------------------------------
-- 2. Same fine histories as the future-cone quotient, now observed by depth.
------------------------------------------------------------------------

data HorizonConeCode : Set where
  commonShortCone
  commonMediumCone
  pluralLongCone
  institutionalLongCone
  : HorizonConeCode

coneAt : Horizon → Future.FuturePathHistory → HorizonConeCode
coneAt shortHorizon _ = commonShortCone
coneAt mediumHorizon _ = commonMediumCone
coneAt longHorizon Future.repairedThenPluralised = pluralLongCone
coneAt longHorizon Future.repairedThenInstitutionalised = institutionalLongCone

shortHorizonAgreement :
  coneAt shortHorizon Future.repairedThenPluralised
  ≡ coneAt shortHorizon Future.repairedThenInstitutionalised
shortHorizonAgreement = refl

mediumHorizonAgreement :
  coneAt mediumHorizon Future.repairedThenPluralised
  ≡ coneAt mediumHorizon Future.repairedThenInstitutionalised
mediumHorizonAgreement = refl

longHorizonDivergence :
  coneAt longHorizon Future.repairedThenPluralised
  ≡ coneAt longHorizon Future.repairedThenInstitutionalised → ⊥
longHorizonDivergence ()

------------------------------------------------------------------------
-- 3. First divergence receipt.
------------------------------------------------------------------------

record FirstForecastDivergenceAt (horizon : Horizon) : Set where
  constructor first-forecast-divergence-at
  field
    divergesHere :
      coneAt horizon Future.repairedThenPluralised
      ≡ coneAt horizon Future.repairedThenInstitutionalised → ⊥
    shortAgreesBefore :
      horizon ≡ mediumHorizon →
      coneAt shortHorizon Future.repairedThenPluralised
      ≡ coneAt shortHorizon Future.repairedThenInstitutionalised
    shortAgreesBeforeLong :
      horizon ≡ longHorizon →
      coneAt shortHorizon Future.repairedThenPluralised
      ≡ coneAt shortHorizon Future.repairedThenInstitutionalised
    mediumAgreesBeforeLong :
      horizon ≡ longHorizon →
      coneAt mediumHorizon Future.repairedThenPluralised
      ≡ coneAt mediumHorizon Future.repairedThenInstitutionalised

canonicalFirstForecastDivergence : FirstForecastDivergenceAt longHorizon
canonicalFirstForecastDivergence =
  first-forecast-divergence-at
    longHorizonDivergence
    (λ ())
    (λ _ → refl)
    (λ _ → refl)

------------------------------------------------------------------------
-- 4. Horizon-specific observers form a refinement ladder, but certainty is not
-- declared monotone.  More horizon can expose new branch distinctions.
------------------------------------------------------------------------

data HorizonObservation : Set where
  shortObservation mediumObservation longObservation : HorizonObservation

observeAtHorizon : Horizon → Future.FuturePathHistory → HorizonObservation × HorizonConeCode
observeAtHorizon shortHorizon h = shortObservation , coneAt shortHorizon h
observeAtHorizon mediumHorizon h = mediumObservation , coneAt mediumHorizon h
observeAtHorizon longHorizon h = longObservation , coneAt longHorizon h

shortObserverCannotRecoverLongCone :
  INF.FactorsThrough
    (observeAtHorizon shortHorizon)
    (coneAt longHorizon) → ⊥
shortObserverCannotRecoverLongCone =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      Future.repairedThenPluralised
      Future.repairedThenInstitutionalised
      refl
      longHorizonDivergence)

mediumObserverCannotRecoverLongCone :
  INF.FactorsThrough
    (observeAtHorizon mediumHorizon)
    (coneAt longHorizon) → ⊥
mediumObserverCannotRecoverLongCone =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      Future.repairedThenPluralised
      Future.repairedThenInstitutionalised
      refl
      longHorizonDivergence)

------------------------------------------------------------------------
-- 5. Consumer-indexed stopping rule by horizon.
------------------------------------------------------------------------

data HorizonDisposition : Set where
  closeAtShort
  closeAtMedium
  reopenAtLongDivergence
  : HorizonDisposition

forecastDisposition : Horizon → HorizonDisposition
forecastDisposition shortHorizon = closeAtShort
forecastDisposition mediumHorizon = closeAtMedium
forecastDisposition longHorizon = reopenAtLongDivergence

shortForecastCloses : forecastDisposition shortHorizon ≡ closeAtShort
shortForecastCloses = refl

mediumForecastCloses : forecastDisposition mediumHorizon ≡ closeAtMedium
mediumForecastCloses = refl

longForecastReopens : forecastDisposition longHorizon ≡ reopenAtLongDivergence
longForecastReopens = refl

------------------------------------------------------------------------
-- 6. LES cross-pollination remains structural: same generic future-cone
-- obstruction, different application semantics.
------------------------------------------------------------------------

lesFutureConeNonDescentStillAvailable :
  INF.FactorsThrough
    LES7.observeManagementHistory LES7.futureConeForManagementHistory → ⊥
lesFutureConeNonDescentStillAvailable =
  LES7.lesFutureConeCannotDescendThroughCoarsePresentSummary

------------------------------------------------------------------------
-- 7. No-promotion boundaries.
------------------------------------------------------------------------

data FirstForecastDivergenceIsHistoricalChangePoint : Set where

data LongerHorizonMeansMoreCertain : Set where

data ShortAgreementGuaranteesLongAgreement : Set where

data HorizonDepthIsPadicValuation : Set where

data SocialHorizonFixtureValidatesLESQuantitatively : Set where

data LongConeCodeIsEmpiricalPrediction : Set where

data LongDivergenceRefutesShortAction : Set where

firstForecastDivergenceIsNotHistoricalChangePoint :
  FirstForecastDivergenceIsHistoricalChangePoint → ⊥
firstForecastDivergenceIsNotHistoricalChangePoint ()

longerHorizonDoesNotMeanMoreCertain : LongerHorizonMeansMoreCertain → ⊥
longerHorizonDoesNotMeanMoreCertain ()

shortAgreementDoesNotGuaranteeLongAgreement :
  ShortAgreementGuaranteesLongAgreement → ⊥
shortAgreementDoesNotGuaranteeLongAgreement ()

horizonDepthIsNotPadicValuation : HorizonDepthIsPadicValuation → ⊥
horizonDepthIsNotPadicValuation ()

socialFixtureDoesNotValidateLESQuantitatively :
  SocialHorizonFixtureValidatesLESQuantitatively → ⊥
socialFixtureDoesNotValidateLESQuantitatively ()

longConeCodeIsNotEmpiricalPrediction : LongConeCodeIsEmpiricalPrediction → ⊥
longConeCodeIsNotEmpiricalPrediction ()

longDivergenceDoesNotRefuteShortAction : LongDivergenceRefutesShortAction → ⊥
longDivergenceDoesNotRefuteShortAction ()

record HorizonFiltrationFirstDivergenceBoundary : Set where
  constructor horizon-filtration-first-divergence-boundary
  field
    shortAgreementExplicit : Bool
    mediumAgreementExplicit : Bool
    longDivergenceExplicit : Bool
    firstDivergenceAtLongExplicit : Bool
    shortAgreementGuaranteesLongAgreement : Bool
    longerHorizonMeansMoreCertain : Bool
    firstDivergenceIsHistoricalChangePoint : Bool
    horizonDepthEqualsPadicValuation : Bool
    socialFixtureQuantitativelyValidatesLES : Bool

canonicalHorizonFiltrationFirstDivergenceBoundary :
  HorizonFiltrationFirstDivergenceBoundary
canonicalHorizonFiltrationFirstDivergenceBoundary =
  horizon-filtration-first-divergence-boundary
    true true true true false false false false false
