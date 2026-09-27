module DASHI.Economics.JPYJGBTreasuryFundingTransmission2026Exact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Agda.Builtin.String using (String)

import DASHI.Economics.GlobalFundingLiquidityRealisationExact as Funding
import DASHI.Economics.SystemicCrisisCompressionBridge as Crisis

------------------------------------------------------------------------
-- JPY / JGB / US TREASURY FUNDING TRANSMISSION
--
-- The yen is modelled simultaneously as a domestic sovereign currency and a
-- global funding currency.  No deterministic claim is made that BOJ tightening
-- or yen appreciation must cause Treasury liquidation.
------------------------------------------------------------------------

record CurrentRegimeSource : Set where
  constructor currentRegimeSource
  field
    publisher : String
    date : String
    boundedProposition : String
    primaryOrOfficial : Bool

open CurrentRegimeSource public

imfJapan2026 : CurrentRegimeSource
imfJapan2026 =
  currentRegimeSource
    "International Monetary Fund"
    "2026"
    "Japan faces weak demand in super-long JGB sectors, changing BOJ balance-sheet conditions and material fiscal-risk sensitivity in long yields."
    true

usJapanFX2026 : CurrentRegimeSource
usJapanFX2026 =
  currentRegimeSource
    "US/Japan public reporting and official statements"
    "2026"
    "US authorities considered and later participated in yen-support operations; the bounded fact does not by itself establish a hidden master strategy."
    false

treasuryBuyback2026 : CurrentRegimeSource
treasuryBuyback2026 =
  currentRegimeSource
    "US Department of the Treasury"
    "2026-08-19"
    "Treasury increased long-end liquidity-support buyback capacity; this is a liquidity operation and is not definitionally yield-curve control."
    true

record YenFundingValve : Set where
  constructor yenFundingValve
  field
    bojNormalisation : Trit
    yenAppreciation : Trit
    carrySpreadCompression : Trit
    leveragedCarryUnwind : Trit
    globalMarginPressure : Trit
    treasuryLiquidationPressure : Trit
    usDurationLossPressure : Trit

open YenFundingValve public

data BOJTighteningImpliesTreasuryLiquidationPermission : Set where
data YenAppreciationImpliesGlobalCrisisPermission : Set where
data TreasuryBuybackImpliesYCCPermission : Set where
data FXSupportImpliesMasterPlanPermission : Set where

bojTighteningDoesNotAutoCauseTreasuryLiquidation :
  BOJTighteningImpliesTreasuryLiquidationPermission → ⊥
bojTighteningDoesNotAutoCauseTreasuryLiquidation ()

yenAppreciationDoesNotAutoCauseGlobalCrisis :
  YenAppreciationImpliesGlobalCrisisPermission → ⊥
yenAppreciationDoesNotAutoCauseGlobalCrisis ()

buybackDoesNotDefinitionallyCloseYCC :
  TreasuryBuybackImpliesYCCPermission → ⊥
buybackDoesNotDefinitionallyCloseYCC ()

fxSupportDoesNotAutoProveMasterPlan :
  FXSupportImpliesMasterPlanPermission → ⊥
fxSupportDoesNotAutoProveMasterPlan ()

record CrossMarketFundingBridge : Set where
  constructor crossMarketFundingBridge
  field
    yenFundingShock : Bool
    globalDeleveraging : Bool
    treasuryPressure : Bool
    bankDurationPressure : Bool
    aiRefinancingPressure : Bool
    allLinksEmpiricallyObserved : Bool

open CrossMarketFundingBridge public

candidateCrossMarketBridge : CrossMarketFundingBridge
candidateCrossMarketBridge =
  crossMarketFundingBridge true true true true true false

fundingStateFromYenValve : YenFundingValve → Funding.FundingState
fundingStateFromYenValve v =
  Funding.fundingState
    (usDurationLossPressure v)
    (globalMarginPressure v)
    (globalMarginPressure v)
    (leveragedCarryUnwind v)
    zer
    zer
    zer
    zer

record DesiredDirectionVelocityBoundary : Set where
  constructor desiredDirectionVelocityBoundary
  field
    strongerYenMayBeDesired : Bool
    disorderlyYenMoveMayBeUndesired : Bool
    directionEqualsVelocity : Bool
    directionEqualsVelocityIsFalse : directionEqualsVelocity ≡ false

canonicalDesiredDirectionVelocityBoundary : DesiredDirectionVelocityBoundary
canonicalDesiredDirectionVelocityBoundary =
  desiredDirectionVelocityBoundary true true false refl
