module DASHI.Law.CoerciveEncounterPopulationAggregationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Law.CoerciveEncounterFixtureCompilerExact as Fixture
import DASHI.Law.CoerciveEncounterLawfulnessProductExact as Product

------------------------------------------------------------------------
-- Population aggregation is computed from encounter fixtures but does not
-- erase the distinction between an aggregate statistic and an individual
-- encounter proof.
------------------------------------------------------------------------

record EncounterPopulation : Set where
  constructor encounterPopulation
  field
    populationLabel : String
    fixtures : List Fixture.EncounterFixture
    samplingFrameReference : String
    comparableEncounterDefinitionReference : String
    populationReference : String

open EncounterPopulation public

countFixtures : List Fixture.EncounterFixture → ℕ
countFixtures [] = zero
countFixtures (_ ∷ xs) = suc (countFixtures xs)

countFieldTrue :
  (Fixture.EncounterFixture → Fixture.FieldState) →
  List Fixture.EncounterFixture → ℕ
countFieldTrue selector [] = zero
countFieldTrue selector (x ∷ xs) with selector x
... | Fixture.observedTrue = suc (countFieldTrue selector xs)
... | _ = countFieldTrue selector xs

countSearchAfterWand : List Fixture.EncounterFixture → ℕ
countSearchAfterWand [] = zero
countSearchAfterWand (x ∷ xs) with Fixture.wandOccurred x | Fixture.searchOccurred x
... | Fixture.observedTrue | Fixture.observedTrue = suc (countSearchAfterWand xs)
... | _ | _ = countSearchAfterWand xs

countSearchAfterNoAlarm : List Fixture.EncounterFixture → ℕ
countSearchAfterNoAlarm [] = zero
countSearchAfterNoAlarm (x ∷ xs) with Fixture.scannerAlarm x | Fixture.searchOccurred x
... | Fixture.observedFalse | Fixture.observedTrue = suc (countSearchAfterNoAlarm xs)
... | _ | _ = countSearchAfterNoAlarm xs

countWandWithNoAlarm : List Fixture.EncounterFixture → ℕ
countWandWithNoAlarm [] = zero
countWandWithNoAlarm (x ∷ xs) with Fixture.wandOccurred x | Fixture.scannerAlarm x
... | Fixture.observedTrue | Fixture.observedFalse = suc (countWandWithNoAlarm xs)
... | _ | _ = countWandWithNoAlarm xs

countNonWeaponChargeAfterWand : List Fixture.EncounterFixture → ℕ
countNonWeaponChargeAfterWand [] = zero
countNonWeaponChargeAfterWand (x ∷ xs) with Fixture.wandOccurred x | Fixture.weaponFound x | Fixture.chargeOccurred x
... | Fixture.observedTrue | Fixture.observedFalse | Fixture.observedTrue =
      suc (countNonWeaponChargeAfterWand xs)
... | _ | _ | _ = countNonWeaponChargeAfterWand xs

isLawfulnessClosed : Fixture.EncounterFixture → Fixture.FieldState
isLawfulnessClosed f with Fixture.firstLawfulnessResidual f
... | Product.allLawfulnessCoordinatesClosed = Fixture.observedTrue
... | Product.firstOpenLawfulnessCoordinate _ = Fixture.observedFalse

countLawfulnessClosedSearches : List Fixture.EncounterFixture → ℕ
countLawfulnessClosedSearches [] = zero
countLawfulnessClosedSearches (x ∷ xs) with Fixture.searchOccurred x | isLawfulnessClosed x
... | Fixture.observedTrue | Fixture.observedTrue = suc (countLawfulnessClosedSearches xs)
... | _ | _ = countLawfulnessClosedSearches xs

countSearches : List Fixture.EncounterFixture → ℕ
countSearches = countFieldTrue Fixture.searchOccurred

countWands : List Fixture.EncounterFixture → ℕ
countWands = countFieldTrue Fixture.wandOccurred

------------------------------------------------------------------------
-- Typed estimands retain numerator and denominator semantics.  No division is
-- performed here, so zero-denominator and missing-data policy remain explicit.
------------------------------------------------------------------------

data EstimandKind : Set where
  searchGivenWand searchGivenNoAlarm nonWeaponChargeGivenWand
  lawfulnessClosedGivenSearch : EstimandKind

record CountRatio : Set where
  constructor countRatio
  field
    estimand : EstimandKind
    numerator denominator : ℕ
    numeratorMeaning : String
    denominatorMeaning : String
    ratioReference : String

open CountRatio public

gatewayRateCounts : EncounterPopulation → CountRatio
gatewayRateCounts p = countRatio
  searchGivenWand
  (countSearchAfterWand (fixtures p))
  (countWands (fixtures p))
  "encounters with wand observed true and search observed true"
  "encounters with wand observed true"
  "P(Search | Wand) count pair; division/calibration intentionally downstream"

noAlarmSearchRateCounts : EncounterPopulation → CountRatio
noAlarmSearchRateCounts p = countRatio
  searchGivenNoAlarm
  (countSearchAfterNoAlarm (fixtures p))
  (countWandWithNoAlarm (fixtures p))
  "encounters with scanner alarm observed false and search observed true"
  "wanded encounters with scanner alarm observed false"
  "P(Search | Wand, Alarm=false) count pair"

nonWeaponChargeRateCounts : EncounterPopulation → CountRatio
nonWeaponChargeRateCounts p = countRatio
  nonWeaponChargeGivenWand
  (countNonWeaponChargeAfterWand (fixtures p))
  (countWands (fixtures p))
  "wanded encounters with weapon observed false and charge observed true"
  "encounters with wand observed true"
  "P(non-weapon charge | Wand) count pair"

lawfulnessClosureRateCounts : EncounterPopulation → CountRatio
lawfulnessClosureRateCounts p = countRatio
  lawfulnessClosedGivenSearch
  (countLawfulnessClosedSearches (fixtures p))
  (countSearches (fixtures p))
  "searched encounters whose entire lawfulness vector closes"
  "encounters with search observed true"
  "P(LawfulnessClosed | SearchOccurred) count pair"

------------------------------------------------------------------------
-- Missingness remains a first-class denominator problem.
------------------------------------------------------------------------

countFieldMissing :
  (Fixture.EncounterFixture → Fixture.FieldState) →
  List Fixture.EncounterFixture → ℕ
countFieldMissing selector [] = zero
countFieldMissing selector (x ∷ xs) with selector x
... | Fixture.fieldMissing = suc (countFieldMissing selector xs)
... | _ = countFieldMissing selector xs

record MissingnessAudit : Set where
  constructor missingnessAudit
  field
    alarmMissing searchPredicateMissing bodyCameraMissing independentProducerMissing : ℕ
    auditPopulationSize : ℕ
    missingnessReference : String

open MissingnessAudit public

compileMissingnessAudit : EncounterPopulation → MissingnessAudit
compileMissingnessAudit p = missingnessAudit
  (countFieldMissing Fixture.scannerAlarm (fixtures p))
  (countFieldMissing Fixture.searchPredicateReceipt (fixtures p))
  (countFieldMissing Fixture.bodyCameraActivated (fixtures p))
  (countFieldMissing Fixture.independentProducerPresent (fixtures p))
  (countFixtures (fixtures p))
  "missingness counts retained separately from observed-false counts"

------------------------------------------------------------------------
-- Canonical two-encounter regression.
------------------------------------------------------------------------

canonicalPopulation : EncounterPopulation
canonicalPopulation = encounterPopulation
  "canonical coercive encounter population"
  (Fixture.canonicalMissingSafeguardFixture ∷ Fixture.canonicalMissingSafeguardFixture ∷ [])
  "synthetic complete fixture list"
  "same fixture schema and encounter definition"
  "abstract regression only; no real-person data"

canonicalPopulationSize : countFixtures (fixtures canonicalPopulation) ≡ 2
canonicalPopulationSize = refl

canonicalGatewayNumerator : numerator (gatewayRateCounts canonicalPopulation) ≡ 2
canonicalGatewayNumerator = refl

canonicalGatewayDenominator : denominator (gatewayRateCounts canonicalPopulation) ≡ 2
canonicalGatewayDenominator = refl

canonicalLawfulnessClosedNumerator :
  numerator (lawfulnessClosureRateCounts canonicalPopulation) ≡ 0
canonicalLawfulnessClosedNumerator = refl

canonicalLawfulnessSearchDenominator :
  denominator (lawfulnessClosureRateCounts canonicalPopulation) ≡ 2
canonicalLawfulnessSearchDenominator = refl

------------------------------------------------------------------------
-- Aggregate-statistic firewall.
------------------------------------------------------------------------

record PopulationAggregationBoundary : Set where
  constructor populationAggregationBoundary
  field
    aggregateStatisticProvesIndividualEncounterLawful : Bool
    aggregateStatisticProvesIndividualEncounterLawfulIsFalse :
      aggregateStatisticProvesIndividualEncounterLawful ≡ false
    highGatewayRateProvesPretextualIntent : Bool
    highGatewayRateProvesPretextualIntentIsFalse :
      highGatewayRateProvesPretextualIntent ≡ false
    observedFalseEqualsMissing : Bool
    observedFalseEqualsMissingIsFalse : observedFalseEqualsMissing ≡ false
    rawCountRatioProvesCausalEffect : Bool
    rawCountRatioProvesCausalEffectIsFalse : rawCountRatioProvesCausalEffect ≡ false

canonicalPopulationAggregationBoundary : PopulationAggregationBoundary
canonicalPopulationAggregationBoundary =
  populationAggregationBoundary false refl false refl false refl false refl
