module DASHI.Economics.AIOpenClosedGrowthCapitalRecoveryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital
import DASHI.Economics.AIUbiquityRentInversionExact as Ubiquity

------------------------------------------------------------------------
-- GROWTH / MARGIN / SUBSTITUTION ACCOUNTING INTERFACE
--
-- Revenue growth alone does not close capital recovery.  The relevant state
-- also includes quality-adjusted price compression, throughput growth,
-- compute intensity, operating leverage and funding cost.
------------------------------------------------------------------------

record GrowthRequirement : Set₁ where
  field
    Revenue0 RevenueTarget Horizon RequiredCAGR : Set
    revenue0 : Revenue0
    revenueTarget : RevenueTarget
    horizon : Horizon
    requiredCAGR : RequiredCAGR

record OperatingLeverageState : Set₁ where
  field
    Revenue ComputeCost OtherOperatingCost EBITDA Depreciation FinancingCost : Set
    revenue : Revenue
    computeCost : ComputeCost
    otherOperatingCost : OtherOperatingCost
    ebitda : EBITDA
    depreciation : Depreciation
    financingCost : FinancingCost

record PriceVolumeSubstitutionState : Set₁ where
  field
    RevenueGrowthFactor PricePerQualityUnitFactor RequiredQualityVolumeFactor : Set
    revenueGrowthFactor : RevenueGrowthFactor
    pricePerQualityUnitFactor : PricePerQualityUnitFactor
    requiredQualityVolumeFactor : RequiredQualityVolumeFactor

record CapitalRecoveryRequirement : Set₁ where
  field
    OperatingMargin : Set
    ComputeIntensity : Set
    RealisedROIC : Set
    WeightedFundingCost : Set
    ReplacementCapexBurden : Set
    operatingMargin : OperatingMargin
    computeIntensity : ComputeIntensity
    realisedROIC : RealisedROIC
    weightedFundingCost : WeightedFundingCost
    replacementCapexBurden : ReplacementCapexBurden

------------------------------------------------------------------------
-- No scalar is hard-coded as a theorem here.  Numeric application modules can
-- instantiate the interfaces from audited filings / prospectuses and prove
-- the arithmetic separately.
------------------------------------------------------------------------

data RevenueGrowthImpliesPositiveEBITDAPermission : Set where
data FallingInferenceCostImpliesHigherRevenuePermission : Set where
data PositiveEBITDAImpliesCapitalRecoveryPermission : Set where
data ExtremeGrowthForecastImpliesAchievableGrowthPermission : Set where

revenueGrowthDoesNotAutoProvePositiveEBITDA :
  RevenueGrowthImpliesPositiveEBITDAPermission → ⊥
revenueGrowthDoesNotAutoProvePositiveEBITDA ()

fallingInferenceCostDoesNotAutoProveHigherRevenue :
  FallingInferenceCostImpliesHigherRevenuePermission → ⊥
fallingInferenceCostDoesNotAutoProveHigherRevenue ()

positiveEBITDADoesNotAutoProveCapitalRecovery :
  PositiveEBITDAImpliesCapitalRecoveryPermission → ⊥
positiveEBITDADoesNotAutoProveCapitalRecovery ()

extremeGrowthForecastDoesNotAutoProveAchievability :
  ExtremeGrowthForecastImpliesAchievableGrowthPermission → ⊥
extremeGrowthForecastDoesNotAutoProveAchievability ()

------------------------------------------------------------------------
-- Existing boundary: capability / adoption can improve while capital recovery
-- remains unclosed.
------------------------------------------------------------------------

technologySuccessCapitalLossBoundary : Ubiquity.TechnologySuccessCapitalLossBoundary
technologySuccessCapitalLossBoundary =
  Ubiquity.canonicalTechnologySuccessCapitalLossBoundary

capitalCrackSpreadInterface : Set₁
capitalCrackSpreadInterface = Capital.AICapitalCrackSpread
