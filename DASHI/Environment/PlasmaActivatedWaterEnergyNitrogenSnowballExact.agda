module DASHI.Environment.PlasmaActivatedWaterEnergyNitrogenSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.PlasmaActivatedWaterPrimaryProcessEnergySourceExact as Primary
import DASHI.Environment.PlasmaActivatedWaterAquaticNutrientBridgeExact as PAW
import DASHI.Environment.NitrogenPathwayEnergeticMaterialComparisonExact as Nitrogen
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- PAW PROCESS ENERGY -> FIXED-N -> COMMON N PACKET SNOWBALL
--
-- Primary process data may pay reactor electrical-energy/fixed-N coordinates.
-- DASHI owns conversion into the common N consumer packet. Agronomic response,
-- lifecycle carbon, cost, renewable matching and recommendation remain downstream.
------------------------------------------------------------------------

record PAWProcessEnergyAdmission
    {production : PAW.PlasmaWaterProductionIdentity}
    {composition : PAW.PlasmaActivatedWaterComposition production}
    (pawNitrogen : PAW.PlasmaNitrogenInputReceipt composition) : Set₁ where
  constructor paw-process-energy-admission
  field
    source : Primary.PAWProcessEnergyPrimarySource
    sourceIsCanonicalProcessStudy :
      source ≡ Primary.zhuangMicrobubbleNFertigation2025
    exactReactorConfigurationReference : String
    exactFeedGasReference : String
    exactWaterVolumeReference : String
    exactTreatmentTimeReference : String
    exactElectricalPowerReference : String
    exactCatalystConfigurationReference : String
    measuredNitrateReference : String
    measuredAmmoniumReference : String
    measuredTotalFixedNReference : String
    measuredEnergyEfficiencyReference : String
    gramsFixedNPerKWhReference : String
    pawNitrogenLedgerMatchesProcessReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner
    dashiWeldOwner : Attribution.ClaimOwner
    dashiOwnsWeld :
      dashiWeldOwner ≡ Attribution.dashiFormalisationOwner

open PAWProcessEnergyAdmission public

record PAWElectricalEnergyPacketAdmission
    {production : PAW.PlasmaWaterProductionIdentity}
    {composition : PAW.PlasmaActivatedWaterComposition production}
    (pawNitrogen : PAW.PlasmaNitrogenInputReceipt composition)
    (adapter : Nitrogen.PAWComparisonAdapter pawNitrogen)
    (process : PAWProcessEnergyAdmission pawNitrogen) : Set₁ where
  constructor paw-electrical-energy-packet-admission
  field
    measuredElectricalEnergy : SI.Quantity SI.Energy SI.unitScale
    processPowerTimeToEnergyReference : String
    measuredFixedNReference : String
    fixedNPerEnergyReference : String
    adapterEnergyMatchesMeasuredProcessEnergy :
      Nitrogen.PAWComparisonAdapter.externalEnergy adapter ≡ measuredElectricalEnergy
    sameReactorBoundaryReference : String
    sameProductionBatchReference : String
    sameNitrogenMassBoundaryReference : String
    conversionUncertaintyReference : String

open PAWElectricalEnergyPacketAdmission public

record PAWEnergyNitrogenAcquisitionState : Set where
  constructor paw-energy-nitrogen-acquisition-state
  field
    processSourceAcquired : Bool
    reactorIdentityAcquired : Bool
    powerAcquired : Bool
    treatmentTimeAcquired : Bool
    waterVolumeAcquired : Bool
    fixedNCompositionAcquired : Bool
    fixedNMassAcquired : Bool
    energyEfficiencyAcquired : Bool
    commonPacketAcquired : Bool
    gridOrRenewableOriginAcquired : Bool
    lifecycleEmissionAcquired : Bool
    costAcquired : Bool
    agronomicOutcomeAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open PAWEnergyNitrogenAcquisitionState public

record PAWEnergyNitrogenPaymentState : Set where
  constructor paw-energy-nitrogen-payment-state
  field
    sourceIdentityPaid : Bool
    reactorIdentityPaid : Bool
    sameBatchPaid : Bool
    electricalPowerPaid : Bool
    treatmentTimePaid : Bool
    fixedNMassPaid : Bool
    processEnergyPaid : Bool
    fixedNPerEnergyPaid : Bool
    packetEnergyBoundaryPaid : Bool
    renewableOriginPaid : Bool
    lifecycleEmissionsPaid : Bool
    costPaid : Bool
    agronomicNitrogenEfficiencyPaid : Bool
    matchedComparatorPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open PAWEnergyNitrogenPaymentState public

snowballAcquisitionDoesNotAdvancePAWEnergyPayment :
  PAWEnergyNitrogenAcquisitionState →
  PAWEnergyNitrogenPaymentState →
  PAWEnergyNitrogenPaymentState
snowballAcquisitionDoesNotAdvancePAWEnergyPayment _ payment = payment

------------------------------------------------------------------------
-- WrongType barriers.
------------------------------------------------------------------------

data FixedNPerEnergyMeansAgronomicEfficiencyPermission : Set where
data ReactorEfficiencyMeansLifecycleCarbonPermission : Set where
data RenewableCompatibleMeansRenewablePoweredPermission : Set where
data ProcessStudyMeansCommercialViabilityPermission : Set where
data PAWEnergyMeansBestNitrogenPathwayPermission : Set where
data ExternalProcessOwnsDashiPacketPermission : Set where

fixedNPerEnergyDoesNotEqualAgronomicEfficiency :
  FixedNPerEnergyMeansAgronomicEfficiencyPermission → ⊥
fixedNPerEnergyDoesNotEqualAgronomicEfficiency ()

reactorEfficiencyDoesNotPayLifecycleCarbon :
  ReactorEfficiencyMeansLifecycleCarbonPermission → ⊥
reactorEfficiencyDoesNotPayLifecycleCarbon ()

renewableCompatibleDoesNotMeanRenewablePowered :
  RenewableCompatibleMeansRenewablePoweredPermission → ⊥
renewableCompatibleDoesNotMeanRenewablePowered ()

processStudyDoesNotPayCommercialViability :
  ProcessStudyMeansCommercialViabilityPermission → ⊥
processStudyDoesNotPayCommercialViability ()

pawEnergyDoesNotSelectBestNitrogenPathway :
  PAWEnergyMeansBestNitrogenPathwayPermission → ⊥
pawEnergyDoesNotSelectBestNitrogenPathway ()

externalProcessDoesNotOwnDashiPacket :
  ExternalProcessOwnsDashiPacketPermission → ⊥
externalProcessDoesNotOwnDashiPacket ()

record PAWEnergyNitrogenBoundary : Set where
  constructor paw-energy-nitrogen-boundary
  field
    processYieldAgronomicEfficiencyAndOutcomeRemainDistinct : Bool
    electricalEnergyRenewableOriginAndLifecycleRemainDistinct : Bool
    sourceResultAndDashiPacketRemainDistinct : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    processEfficiencyAutomaticallyPaysRecommendation : Bool

canonicalPAWEnergyNitrogenBoundary : PAWEnergyNitrogenBoundary
canonicalPAWEnergyNitrogenBoundary =
  paw-energy-nitrogen-boundary true true true true false
