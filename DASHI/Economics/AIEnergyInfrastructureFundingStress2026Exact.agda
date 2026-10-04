module DASHI.Economics.AIEnergyInfrastructureFundingStress2026Exact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIFinancingReflexivityExact as Reflexive
import DASHI.Economics.AITerminalPayerEconomicValidationExact as Terminal
import DASHI.Economics.GlobalFundingLiquidityRealisationExact as Funding

------------------------------------------------------------------------
-- AI INFRASTRUCTURE FUNDING-STRESS / PHYSICAL-CAPITAL CANARY
------------------------------------------------------------------------

record SourceBoundedCanary : Set where
  constructor sourceBoundedCanary
  field
    subject : String
    date : String
    boundedProposition : String
    sourceClass : String
    establishesSystemicCrisis : Bool

open SourceBoundedCanary public

sbEnergyCanary2026 : SourceBoundedCanary
sbEnergyCanary2026 =
  sourceBoundedCanary
    "SoftBank-backed SB Energy"
    "2026-09"
    "Reported IPO slowing and approximately 10 percent demanded debt yields indicate materially harder external financing conditions for a large AI-infrastructure-linked developer."
    "financial press reporting"
    false

gasTurbineDemandCanary2026 : SourceBoundedCanary
gasTurbineDemandCanary2026 =
  sourceBoundedCanary
    "AI datacentre power buildout"
    "2026"
    "AI datacentre demand is materially contributing to new gas-turbine order books and therefore to physical generation-capacity investment, not merely consuming an unchanged electricity system."
    "company results and financial press reporting"
    false

record AIFundingStressCoordinates : Set where
  constructor aiFundingStressCoordinates
  field
    bondSpreadStress : Trit
    projectDebtYieldStress : Trit
    ipoDelayStress : Trit
    guaranteeIntensity : Trit
    offBalanceSheetExposure : Trit
    customerConcentration : Trit
    terminalPayerUncertainty : Trit
    obsolescencePressure : Trit

open AIFundingStressCoordinates public

record PhysicalCapitalStack : Set where
  constructor physicalCapitalStack
  field
    accelerators : Bool
    datacentreShell : Bool
    substations : Bool
    transmission : Bool
    gasTurbines : Bool
    pipelinesOrFuelLogistics : Bool
    coolingAndWater : Bool

open PhysicalCapitalStack public

canonicalBroadPhysicalStack : PhysicalCapitalStack
canonicalBroadPhysicalStack =
  physicalCapitalStack true true true true true true true

data HighBuildoutImpliesViabilityPermission : Set where
data HighDebtYieldImpliesBubbleBurstPermission : Set where
data FossilExposureImpliesNoRenewablesPermission : Set where

highBuildoutDoesNotAutoProveViability :
  HighBuildoutImpliesViabilityPermission → ⊥
highBuildoutDoesNotAutoProveViability ()

highDebtYieldDoesNotAutoProveBurst :
  HighDebtYieldImpliesBubbleBurstPermission → ⊥
highDebtYieldDoesNotAutoProveBurst ()

fossilExposureDoesNotAutoEraseRenewables :
  FossilExposureImpliesNoRenewablesPermission → ⊥
fossilExposureDoesNotAutoEraseRenewables ()

record FundingClock : Set where
  constructor fundingClock
  field
    externalCapitalStillRequired : Bool
    refinancingCostMaterial : Bool
    realisedIRRExceedsFundingCost : Bool
    terminalIndependentDemandEstablished : Bool
    rolloverDependenceMaterial : Bool

open FundingClock public

candidateBurryStyleFundingClock : FundingClock
candidateBurryStyleFundingClock =
  fundingClock true true false false true

record CapitalRecoveryRace : Set where
  constructor capitalRecoveryRace
  field
    inferenceUnitCostFalling : Bool
    usageVolumeGrowing : Bool
    proprietaryRevenuePerUnitFalling : Bool
    sunkInfrastructureRecoveryComplete : Bool
    technologyCanSucceedBeforeCapitalRecovers : Bool

canonicalCapitalRecoveryRace : CapitalRecoveryRace
canonicalCapitalRecoveryRace =
  capitalRecoveryRace true true true false true
