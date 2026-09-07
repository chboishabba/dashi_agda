module DASHI.Economics.MarxCapitalAIInfrastructureCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.MarxLabourUnionSourceBoundaryExact as Marx
import DASHI.Culture.LopezRiosCriticalTheoryPsychologyCrossPollinationExact as Critical
import DASHI.Economics.ReflexiveFlowValidationExact as Econ
import DASHI.Economics.UnitEconomicsMarginExact as Unit

------------------------------------------------------------------------
-- MARX / CAPITAL x AI INFRASTRUCTURE ECONOMICS
--
-- Cross-pollination only.  Marx's bounded Capital Vol. I owner supplies source
-- context for the capital/labour relation, labour-power, working-day conflict
-- and cooperation.  DASHI's capital/revenue/valuation graphs are modern formal
-- constructions and are not attributed to Marx.
------------------------------------------------------------------------

data CapitalAnalysisCoordinate : Set where
  ownershipOfProductiveInfrastructure : CapitalAnalysisCoordinate
  labourPowerPurchase : CapitalAnalysisCoordinate
  labourTimeAndIntensity : CapitalAnalysisCoordinate
  cooperativeProduction : CapitalAnalysisCoordinate
  capitalProvision : CapitalAnalysisCoordinate
  realisedCustomerRevenue : CapitalAnalysisCoordinate
  markedValuationGain : CapitalAnalysisCoordinate
  debtAndFinancing : CapitalAnalysisCoordinate
  depreciationAndReplacement : CapitalAnalysisCoordinate
  terminalPayer : CapitalAnalysisCoordinate


record CapitalAnalysisCoordinateReceipt : Set where
  constructor capitalAnalysisCoordinateReceipt
  field
    coordinate : CapitalAnalysisCoordinate
    sourceOrFormalOwner : String
    SourceProposition : Set
    sourceProposition : SourceProposition

open CapitalAnalysisCoordinateReceipt public

record MarxAIEconomicReadingBoundary : Set where
  constructor marxAIEconomicReadingBoundary
  field
    marxBoundary : Marx.MarxLabourUnionSourceBoundary
    criticalTheoryBoundary : Critical.LopezRiosCriticalTheoryPsychologyBoundary
    marxSuppliesBoundedCapitalLabourContext : Bool
    dashiReflexiveFinanceGraphIsMarxTheorem : Bool
    dashiReflexiveFinanceGraphIsMarxTheoremIsFalse :
      dashiReflexiveFinanceGraphIsMarxTheorem ≡ false
    valuationGainEqualsRealisedSurplusOrExternalCash : Bool
    valuationGainEqualsRealisedSurplusOrExternalCashIsFalse :
      valuationGainEqualsRealisedSurplusOrExternalCash ≡ false
    AIUsageGrowthProvesCapitalistProfitability : Bool
    AIUsageGrowthProvesCapitalistProfitabilityIsFalse :
      AIUsageGrowthProvesCapitalistProfitability ≡ false
    capitalRelationAloneExhaustsCurrentAIRegime : Bool
    capitalRelationAloneExhaustsCurrentAIRegimeIsFalse :
      capitalRelationAloneExhaustsCurrentAIRegime ≡ false

canonicalMarxAIEconomicReadingBoundary : MarxAIEconomicReadingBoundary
canonicalMarxAIEconomicReadingBoundary =
  marxAIEconomicReadingBoundary
    Marx.canonicalMarxLabourUnionSourceBoundary
    Critical.canonicalLopezRiosCriticalTheoryPsychologyBoundary
    true false refl false refl false refl false refl

-- The useful formal bridge is a distinction, not an identification: capital
-- supplied, customer revenue and valuation exposure are separately typed.
data CapitalProvisionEqualsRealisedRevenuePermission : Set where

data ValuationExposureEqualsProductiveFlowPermission : Set where

data LabourSourceContextProvesFirmLevelProfitabilityPermission : Set where

capitalProvisionDoesNotEqualRealisedRevenue :
  CapitalProvisionEqualsRealisedRevenuePermission → ⊥
capitalProvisionDoesNotEqualRealisedRevenue ()

valuationExposureDoesNotEqualProductiveFlow :
  ValuationExposureEqualsProductiveFlowPermission → ⊥
valuationExposureDoesNotEqualProductiveFlow ()

labourSourceContextDoesNotProveFirmLevelProfitability :
  LabourSourceContextProvesFirmLevelProfitabilityPermission → ⊥
labourSourceContextDoesNotProveFirmLevelProfitability ()

markedGainDoesNotCloseExternalCash :
  Econ.MarkedGainImpliesExternalCashPermission → ⊥
markedGainDoesNotCloseExternalCash = Econ.markedGainDoesNotAutoPromoteToExternalCash

usageDoesNotCloseUnitEconomics :
  Unit.HighUsageImpliesPositiveUnitEconomicsPermission → ⊥
usageDoesNotCloseUnitEconomics =
  Unit.highUsageDoesNotAutoPromoteToPositiveUnitEconomics
