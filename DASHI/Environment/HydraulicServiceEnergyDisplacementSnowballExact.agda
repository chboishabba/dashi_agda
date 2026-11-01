module DASHI.Environment.HydraulicServiceEnergyDisplacementSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.AquaticLivingInfrastructureExact as Aquatic
import DASHI.Environment.WholeLandscapePrimaryDependencyReceiptsExact as Primary
import DASHI.Environment.WholeLandscapePrimaryHydraulicEnergySourceExact as EnergySource
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- HYDRAULIC SERVICE / ENERGY DISPLACEMENT SNOWBALL
--
-- Acquisition order != payment order.
--
-- The gravity-fed experiment may establish a bounded water-service receipt.
-- The low-pressure field experiment may establish a bounded hydraulic-energy
-- comparison.  Neither source alone proves electrical pump-energy displacement.
------------------------------------------------------------------------

record HydraulicServiceAcquisitionState : Set₁ where
  constructor hydraulic-service-acquisition-state
  field
    gravityServiceReceiptAcquired : Bool
    lowPressureEnergySourceAcquired : Bool
    poweredComparatorCircuitAcquired : Bool
    gravityCircuitAcquired : Bool
    deliveredFlowEvidenceAcquired : Bool
    pressureHeadEvidenceAcquired : Bool
    uniformityEvidenceAcquired : Bool
    hydraulicEnergyEvidenceAcquired : Bool
    electricalMeterEvidenceAcquired : Bool
    pumpMotorEfficiencyEvidenceAcquired : Bool
    lifecycleEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open HydraulicServiceAcquisitionState public

record HydraulicServicePaymentState : Set where
  constructor hydraulic-service-payment-state
  field
    gravityServicePaid : Bool
    poweredComparatorServicePaid : Bool
    sameDeliveredWaterServicePaid : Bool
    sameTemporalBoundaryPaid : Bool
    sameDistributionQualityPaid : Bool
    pressureHeadAccountingPaid : Bool
    hydraulicEnergyPerVolumePaid : Bool
    electricalInputEnergyPaid : Bool
    pumpMotorEfficiencyPaid : Bool
    electricalEnergyDisplacementPaid : Bool
    lifecycleEnergyPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open HydraulicServicePaymentState public

snowballAcquisitionDoesNotAdvanceHydraulicPayment :
  HydraulicServiceAcquisitionState →
  HydraulicServicePaymentState →
  HydraulicServicePaymentState
snowballAcquisitionDoesNotAdvanceHydraulicPayment _ payment = payment

------------------------------------------------------------------------
-- Matched water service.
------------------------------------------------------------------------

record MatchedHydraulicWaterService : Set where
  constructor matched-hydraulic-water-service
  field
    gravityPrimaryReceipt : Primary.HydraulicHeadWaterServicePrimaryReceipt
    gravityCircuit : Aquatic.HydraulicCircuit
    poweredCircuit : Aquatic.HydraulicCircuit
    sameDeliveredVolumeReference : String
    sameFlowDutyReference : String
    sameServiceDurationReference : String
    sameDistributionUniformityReference : String
    sameOutletOrConsumerBoundaryReference : String
    sameWaterQualityReference : String
    gravityHeadReference : String
    poweredPressureReference : String
    gravityLossReference : String
    poweredLossReference : String
    serviceMatchUncertaintyReference : String
    dashiFormalisationOwner : Attribution.ClaimOwner
    dashiOwnsServiceMatch :
      dashiFormalisationOwner ≡ Attribution.dashiFormalisationOwner

open MatchedHydraulicWaterService public

------------------------------------------------------------------------
-- Hydraulic energy can be paid before electrical energy.
------------------------------------------------------------------------

record HydraulicEnergyPerDeliveredVolumeReceipt
    (service : MatchedHydraulicWaterService) : Set where
  constructor hydraulic-energy-per-delivered-volume-receipt
  field
    primarySource :
      EnergySource.sokolLowPressureDrip2019 ≡
      EnergySource.sokolLowPressureDrip2019
    gravityHydraulicEnergyReference : String
    poweredHydraulicEnergyReference : String
    deliveredVolumeReference : String
    pressureFlowIntegrationReference : String
    commonEnergyBoundaryReference : String
    hydraulicEnergyDifferenceReference : String
    uncertaintyReference : String
    sourceClaimOwner : Attribution.ClaimOwner
    sourceRemainsExternal :
      sourceClaimOwner ≡ Attribution.externalSourceOwner
    dashiInferenceOwner : Attribution.ClaimOwner
    dashiOwnsMatchedComparison :
      dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open HydraulicEnergyPerDeliveredVolumeReceipt public

------------------------------------------------------------------------
-- Electrical energy displacement is a stronger, separate payment.
------------------------------------------------------------------------

record ElectricalPumpEnergyDisplacementReceipt
    {service : MatchedHydraulicWaterService}
    (hydraulicReceipt : HydraulicEnergyPerDeliveredVolumeReceipt service) : Set where
  constructor electrical-pump-energy-displacement-receipt
  field
    poweredElectricalEnergy : SI.Quantity SI.Energy SI.unitScale
    gravityElectricalEnergy : SI.Quantity SI.Energy SI.unitScale
    directMeterOrValidatedEfficiencyReference : String
    pumpEfficiencyReference : String
    motorDriveEfficiencyReference : String
    auxiliaryLoadsReference : String
    electricalBoundaryReference : String
    electricalEnergyDifferenceReference : String
    uncertaintyReference : String
    hydraulicEnergyAloneDidNotPayThisReceipt : Bool

open ElectricalPumpEnergyDisplacementReceipt public

record LifecycleWaterServiceEnergyReceipt
    {service : MatchedHydraulicWaterService}
    {hydraulicReceipt : HydraulicEnergyPerDeliveredVolumeReceipt service}
    (electricalReceipt : ElectricalPumpEnergyDisplacementReceipt hydraulicReceipt) : Set where
  constructor lifecycle-water-service-energy-receipt
  field
    embodiedInfrastructureReference : String
    maintenanceReference : String
    replacementReference : String
    serviceLifeReference : String
    waterLossReference : String
    reliabilityReference : String
    lifecycleBoundaryReference : String
    lifecycleEnergyDifferenceReference : String
    uncertaintyReference : String

open LifecycleWaterServiceEnergyReceipt public

------------------------------------------------------------------------
-- WrongType / snowball barriers.
------------------------------------------------------------------------

data HydraulicEnergyMeansElectricalDisplacementPermission : Set where
data GravityServiceMeansPumpAvoidedPermission : Set where
data SameFlowMeansSameWaterServicePermission : Set where
data LowerPressureMeansLowerLifecycleEnergyPermission : Set where
data SourceResultMeansDashiComparisonPermission : Set where
data AcquisitionMeansPaymentPermission : Set where

hydraulicEnergyDoesNotPayElectricalDisplacement :
  HydraulicEnergyMeansElectricalDisplacementPermission → ⊥
hydraulicEnergyDoesNotPayElectricalDisplacement ()

gravityServiceDoesNotByItselfProvePumpAvoided :
  GravityServiceMeansPumpAvoidedPermission → ⊥
gravityServiceDoesNotByItselfProvePumpAvoided ()

sameFlowDoesNotDefinitionallyMeanSameWaterService :
  SameFlowMeansSameWaterServicePermission → ⊥
sameFlowDoesNotDefinitionallyMeanSameWaterService ()

lowerPressureDoesNotDefinitionallyMeanLowerLifecycleEnergy :
  LowerPressureMeansLowerLifecycleEnergyPermission → ⊥
lowerPressureDoesNotDefinitionallyMeanLowerLifecycleEnergy ()

externalSourceDoesNotOwnDashiMatchedComparison :
  SourceResultMeansDashiComparisonPermission → ⊥
externalSourceDoesNotOwnDashiMatchedComparison ()

acquisitionDoesNotManufacturePayment :
  AcquisitionMeansPaymentPermission → ⊥
acquisitionDoesNotManufacturePayment ()

record HydraulicEnergySnowballBoundary : Set where
  constructor hydraulic-energy-snowball-boundary
  field
    acquisitionAndPaymentRemainDistinct : Bool
    matchedWaterServiceRequiredBeforeEnergyComparison : Bool
    hydraulicAndElectricalEnergyRemainDistinct : Bool
    electricalAndLifecycleEnergyRemainDistinct : Bool
    primarySourceAndDashiComparisonRemainDistinct : Bool
    lowerPressureAutomaticallyPaysElectricalEnergySaving : Bool

canonicalHydraulicEnergySnowballBoundary : HydraulicEnergySnowballBoundary
canonicalHydraulicEnergySnowballBoundary =
  hydraulic-energy-snowball-boundary true true true true true false
