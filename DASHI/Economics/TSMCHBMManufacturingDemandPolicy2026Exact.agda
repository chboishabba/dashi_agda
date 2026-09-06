module DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIManufacturingChokepointTimescaleExact as Manufacturing
import DASHI.Economics.AICriticalInfrastructurePoliticsCrossPollinationExact as Politics

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    publisher : String
    date : String
    sourceLocation : String
    boundedProposition : String
    primarySource : Bool

open SourceReceipt public

tsmcCapacityPlanning : SourceReceipt
tsmcCapacityPlanning = sourceReceipt
  "TSMC"
  "2026 AGM materials"
  "2026 AGM Agenda"
  "TSMC states that it plans capacity with customers and customers' customers in response to a structural increase in long-term demand, invests in leading-edge and advanced packaging capacity, cites very strong multi-year AI-related demand, and says geographic expansion depends in part on necessary government support."
  true

skHynixHBMDemand : SourceReceipt
skHynixHBMDemand = sourceReceipt
  "SK hynix"
  "2026-07-29"
  "Q2 2026 business results"
  "SK hynix reports record performance driven by AI memory demand, additional supply requests, long-term agreements with around ten key customers, multi-year contract discussions, and HBM4 mass shipments."
  true

record ManufacturingDemandPolicyCalibration : Set where
  constructor manufacturingDemandPolicyCalibration
  field
    foundryPackagingReceipt : SourceReceipt
    hbmReceipt : SourceReceipt
    longHorizonCapacityPlanningObserved : Bool
    customerForwardCommitmentObserved : Bool
    governmentSupportCoordinateObserved : Bool
    advancedPackagingCoordinateObserved : Bool
    hbmDemandPressureObserved : Bool
    monopolyProven : Bool
    absoluteScarcityRentQuantified : Bool
    downstreamCommercialViabilityProven : Bool

canonicalManufacturingDemandPolicyCalibration :
  ManufacturingDemandPolicyCalibration
canonicalManufacturingDemandPolicyCalibration =
  manufacturingDemandPolicyCalibration
    tsmcCapacityPlanning skHynixHBMDemand
    true true true true true false false false

data CapacityPlanningProvesPermanentChokepointPermission : Set where

data GovernmentSupportProvesCommercialReturnPermission : Set where

capacityPlanningDoesNotAutoPromoteToPermanentChokepoint :
  CapacityPlanningProvesPermanentChokepointPermission → ⊥
capacityPlanningDoesNotAutoPromoteToPermanentChokepoint ()

governmentSupportDoesNotAutoPromoteToCommercialReturn :
  GovernmentSupportProvesCommercialReturnPermission → ⊥
governmentSupportDoesNotAutoPromoteToCommercialReturn ()

scarcityDoesNotCloseDownstreamViability :
  Manufacturing.Scarcity.ScarcityRentImpliesDownstreamViabilityPermission → ⊥
scarcityDoesNotCloseDownstreamViability =
  Manufacturing.scarcityRentDoesNotCloseDownstreamViability

criticalInfrastructurePatternDoesNotMergeHistoricalDomains :
  Politics.PoliticsCrossPollinationImpliesHistoricalIdentityPermission → ⊥
criticalInfrastructurePatternDoesNotMergeHistoricalDomains =
  Politics.politicsCrossPollinationDoesNotAutoPromoteToHistoricalIdentity
