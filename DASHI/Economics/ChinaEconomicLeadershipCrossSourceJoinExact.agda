module DASHI.Economics.ChinaEconomicLeadershipCrossSourceJoinExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Economics.ChinaOfficialEconomicSelfPosition2026Exact as Official
import DASHI.Economics.AIChinaTSMCGeoEconomicCalibration2026Exact as Independent

------------------------------------------------------------------------
-- CHINA ECONOMIC-LEADERSHIP CROSS-SOURCE JOIN
--
-- Joins official PRC self-position to independent IMF-style coordinates
-- without scalarising the vector into a political/economic "winner".
------------------------------------------------------------------------

data CrossSourceAxis : Set where
  manufacturingAxis : CrossSourceAxis
  goodsTradeAxis : CrossSourceAxis
  domesticDemandAxis : CrossSourceAxis
  highTechUpgradeAxis : CrossSourceAxis
  financeCurrencyAxis : CrossSourceAxis

record CrossSourceAxisJoin : Set where
  constructor cross-source-axis-join
  field
    axis : CrossSourceAxis
    officialReading : String
    independentReading : String
    officialSourceRef : String
    independentSourceRef : String
    comparableCoordinate : Bool
    comparableCoordinateIsTrue :
      comparableCoordinate ≡ true
    agreementOnDimension : Bool
    disagreementOrResidual : String
    createsScalarLeadershipScore : Bool
    createsScalarLeadershipScoreIsFalse :
      createsScalarLeadershipScore ≡ false
    settlesOverallLeadership : Bool
    settlesOverallLeadershipIsFalse :
      settlesOverallLeadership ≡ false

open CrossSourceAxisJoin public

manufacturingJoin : CrossSourceAxisJoin
manufacturingJoin =
  cross-source-axis-join
    manufacturingAxis
    "PRC official materials describe China as the world's largest manufacturing power/country."
    "Independent IMF evidence describes China as the dominant global manufacturing hub by gross production/value-added scale."
    "ChinaOfficialEconomicSelfPosition2026Exact.manufacturingSelfPosition"
    "AIChinaTSMCGeoEconomicCalibration2026Exact.chinaManufacturingScale"
    true refl
    true
    "dimension-level convergence does not settle finance, currency, domestic demand or overall leadership"
    false refl
    false refl

goodsTradeJoin : CrossSourceAxisJoin
goodsTradeJoin =
  cross-source-axis-join
    goodsTradeAxis
    "PRC official materials describe China as the world's largest trader in goods."
    "Independent calibration records broad export-network centrality as a distinct geo-economic coordinate."
    "ChinaOfficialEconomicSelfPosition2026Exact.broadSelfPosition"
    "AIChinaTSMCGeoEconomicCalibration2026Exact.exportNetworkCentrality"
    true refl
    true
    "requires metric/date harmonisation before quantitative equality is asserted"
    false refl
    false refl

domesticDemandJoin : CrossSourceAxisJoin
domesticDemandJoin =
  cross-source-axis-join
    domesticDemandAxis
    "PRC self-position includes a very large consumer-market claim."
    "Independent IMF calibration retains weak private domestic demand as a countervailing structural residual."
    "ChinaOfficialEconomicSelfPosition2026Exact.broadSelfPosition"
    "AIChinaTSMCGeoEconomicCalibration2026Exact.chinaDomesticDemandResidual"
    true refl
    false
    "large market scale and strong private domestic demand are different propositions"
    false refl
    false refl

record ChinaEconomicLeadershipJoin : Set where
  constructor china-economic-leadership-join
  field
    axisJoins : List CrossSourceAxisJoin
    officialAndIndependentSourcesSeparated : Bool
    officialAndIndependentSourcesSeparatedIsTrue :
      officialAndIndependentSourcesSeparated ≡ true
    positiveAndCountervailingCoordinatesRetained : Bool
    positiveAndCountervailingCoordinatesRetainedIsTrue :
      positiveAndCountervailingCoordinatesRetained ≡ true
    scalarWinnerProduced : Bool
    scalarWinnerProducedIsFalse :
      scalarWinnerProduced ≡ false
    comprehensiveVictoryClaimClosed : Bool
    comprehensiveVictoryClaimClosedIsFalse :
      comprehensiveVictoryClaimClosed ≡ false

open ChinaEconomicLeadershipJoin public

canonicalChinaEconomicLeadershipJoin : ChinaEconomicLeadershipJoin
canonicalChinaEconomicLeadershipJoin =
  china-economic-leadership-join
    (manufacturingJoin ∷ goodsTradeJoin ∷ domesticDemandJoin ∷ [])
    true refl
    true refl
    false refl
    false refl

data ManufacturingLeadershipMeansOverallVictory : Set where
data OfficialClaimEqualsIndependentMeasurement : Set where
data LargeConsumerMarketMeansStrongPrivateDemand : Set where
data ParetoJoinCreatesWinner : Set where

manufacturingDoesNotCloseOverallVictory :
  ManufacturingLeadershipMeansOverallVictory → ⊥
manufacturingDoesNotCloseOverallVictory ()

officialClaimDoesNotEqualIndependentMeasurement :
  OfficialClaimEqualsIndependentMeasurement → ⊥
officialClaimDoesNotEqualIndependentMeasurement ()

largeMarketDoesNotMeanStrongPrivateDemand :
  LargeConsumerMarketMeansStrongPrivateDemand → ⊥
largeMarketDoesNotMeanStrongPrivateDemand ()

crossSourceJoinDoesNotCreateWinner :
  ParetoJoinCreatesWinner → ⊥
crossSourceJoinDoesNotCreateWinner ()
