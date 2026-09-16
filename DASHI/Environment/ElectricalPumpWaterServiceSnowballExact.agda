module DASHI.Environment.ElectricalPumpWaterServiceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.ElectricalPumpWaterServicePrimarySourceExact as Sources
import DASHI.Environment.HydraulicServiceEnergyDisplacementSnowballExact as Hydraulic
import DASHI.Environment.AquaticLivingInfrastructureExact as Aquatic
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- DIRECT ELECTRICAL-METER / WATER-SERVICE SNOWBALL
--
-- Primary institutional sources can license measurement protocol or bounded
-- operational observations. DASHI owns the same-service and unit-conversion
-- weld. A measured powered circuit still does not prove that a gravity system
-- can replace it at the same service boundary.
------------------------------------------------------------------------

record ElectricalMeterWaterServiceObservation : Set₁ where
  constructor electrical-meter-water-service-observation
  field
    source : Sources.ElectricalPumpPrimarySource
    poweredCircuit : Aquatic.HydraulicCircuit
    electricityMeterStartReference : String
    electricityMeterEndReference : String
    deliveredWaterStartReference : String
    deliveredWaterEndReference : String
    operatingHeadReference : String
    deliveredFlowReference : String
    serviceDurationReference : String
    distributionQualityReference : String
    auxiliaryLoadBoundaryReference : String
    measuredKWhReference : String
    measuredDeliveredVolumeReference : String
    electricalEnergyPerVolumeReference : String
    measurementUncertaintyReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner

open ElectricalMeterWaterServiceObservation public

------------------------------------------------------------------------
-- Explicit unit/quantity admission before the existing electrical receipt.
------------------------------------------------------------------------

record ElectricalMeterSIAdmission
    (observation : ElectricalMeterWaterServiceObservation) : Set₁ where
  constructor electrical-meter-si-admission
  field
    electricalEnergySI : SI.Quantity SI.Energy SI.unitScale
    deliveredVolumeConversionReference : String
    kWhToJouleConversionReference : String
    meterIntervalIdentityReference : String
    poweredCircuitIdentityReference : String
    auxiliaryBoundaryIdentityReference : String
    conversionUncertaintyReference : String
    dashiFormalisationOwner : Attribution.ClaimOwner
    dashiOwnsConversion :
      dashiFormalisationOwner ≡ Attribution.dashiFormalisationOwner

open ElectricalMeterSIAdmission public

------------------------------------------------------------------------
-- Same-service bridge into the existing hydraulic/electrical snowball.
------------------------------------------------------------------------

record PoweredElectricalServiceAdmission
    {service : Hydraulic.MatchedHydraulicWaterService}
    (observation : ElectricalMeterWaterServiceObservation)
    (si : ElectricalMeterSIAdmission observation) : Set₁ where
  constructor powered-electrical-service-admission
  field
    observedCircuitIsPoweredComparatorReference : String
    sameDeliveredVolumeReference : String
    sameFlowDutyReference : String
    sameServiceDurationReference : String
    sameDistributionQualityReference : String
    sameOutletConsumerBoundaryReference : String
    sameWaterQualityReference : String
    poweredPressureHeadReference : String
    poweredLossReference : String
    observationMatchesServiceReference : String
    directElectricalInputEnergyPaid : Bool
    gravityElectricalInputStillSeparate : Bool
    displacementStillRequiresGravityComparator : Bool

open PoweredElectricalServiceAdmission public

------------------------------------------------------------------------
-- Snowball state: meter evidence can arrive before gravity equivalence.
------------------------------------------------------------------------

record ElectricalServiceAcquisitionState : Set where
  constructor electrical-service-acquisition-state
  field
    measurementProtocolAcquired : Bool
    operationalCaseAcquired : Bool
    electricityMeterEvidenceAcquired : Bool
    deliveredVolumeEvidenceAcquired : Bool
    pressureHeadEvidenceAcquired : Bool
    poweredCircuitAcquired : Bool
    gravityCircuitAcquired : Bool
    matchedServiceAcquired : Bool
    siConversionAcquired : Bool
    lifecycleEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open ElectricalServiceAcquisitionState public

record ElectricalServicePaymentState : Set where
  constructor electrical-service-payment-state
  field
    sourceIdentityPaid : Bool
    exactMeterIntervalPaid : Bool
    exactWaterVolumePaid : Bool
    poweredCircuitIdentityPaid : Bool
    auxiliaryBoundaryPaid : Bool
    siConversionPaid : Bool
    poweredElectricalInputPaid : Bool
    sameWaterServicePaid : Bool
    gravityComparatorPaid : Bool
    gravityElectricalInputPaid : Bool
    electricalDisplacementPaid : Bool
    lifecycleEnergyPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open ElectricalServicePaymentState public

snowballAcquisitionDoesNotAdvanceElectricalServicePayment :
  ElectricalServiceAcquisitionState →
  ElectricalServicePaymentState →
  ElectricalServicePaymentState
snowballAcquisitionDoesNotAdvanceElectricalServicePayment _ payment = payment

------------------------------------------------------------------------
-- WrongType barriers.
------------------------------------------------------------------------

data MeterReadingMeansPumpOnlyEnergyPermission : Set where
data KWhMeansHydraulicEnergyPermission : Set where
data PoweredMeasurementMeansGravityDisplacementPermission : Set where
data InstitutionalCaseMeansUniversalSavingsPermission : Set where
data ElectricalSavingMeansLifecycleSavingPermission : Set where
data ExternalSourceOwnsDashiServiceWeldPermission : Set where

meterReadingDoesNotDefinitionallyMeanPumpOnlyEnergy :
  MeterReadingMeansPumpOnlyEnergyPermission → ⊥
meterReadingDoesNotDefinitionallyMeanPumpOnlyEnergy ()

kWhDoesNotEqualHydraulicEnergy :
  KWhMeansHydraulicEnergyPermission → ⊥
kWhDoesNotEqualHydraulicEnergy ()

poweredMeasurementDoesNotProveGravityDisplacement :
  PoweredMeasurementMeansGravityDisplacementPermission → ⊥
poweredMeasurementDoesNotProveGravityDisplacement ()

institutionalCaseDoesNotUniversaliseSavings :
  InstitutionalCaseMeansUniversalSavingsPermission → ⊥
institutionalCaseDoesNotUniversaliseSavings ()

electricalSavingDoesNotEqualLifecycleSaving :
  ElectricalSavingMeansLifecycleSavingPermission → ⊥
electricalSavingDoesNotEqualLifecycleSaving ()

externalSourceDoesNotOwnDashiServiceWeld :
  ExternalSourceOwnsDashiServiceWeldPermission → ⊥
externalSourceDoesNotOwnDashiServiceWeld ()

record ElectricalPumpWaterServiceBoundary : Set where
  constructor electrical-pump-water-service-boundary
  field
    protocolMeasurementAndDashiWeldRemainDistinct : Bool
    hydraulicAndElectricalEnergyRemainDistinct : Bool
    poweredMeasurementAndGravityDisplacementRemainDistinct : Bool
    electricalAndLifecycleEnergyRemainDistinct : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    sourceAutomaticallyPaysGravityReplacement : Bool

canonicalElectricalPumpWaterServiceBoundary : ElectricalPumpWaterServiceBoundary
canonicalElectricalPumpWaterServiceBoundary =
  electrical-pump-water-service-boundary true true true true true false
