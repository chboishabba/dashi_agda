module DASHI.Environment.Nitrogen15NTracerSPACPrimaryWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.WholeLandscapePrimaryDependencyReceiptsExact as Primary
import DASHI.Environment.WholeLandscapePrimaryDependencySourceRegistryExact as Sources
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Environment.NitrogenPathwayLESCausalTransitionBridgeExact as NitrogenLES

------------------------------------------------------------------------
-- PRIMARY 15N TRACER -> SPAC NUTRIENT-UPTAKE CONSUMER
--
-- External primary result:
--   fertilizer-derived crop N uptake / residual soil N / loss are separately
--   measured in the exact spring-wheat 15N field experiment.
--
-- DASHI reconstruction:
--   admission of that integrated uptake observation as a calibration/validation
--   carrier for the existing SPAC nutrient-uptake socket.
--
-- Integrated crop uptake != instantaneous root flux.  The source does not
-- directly instantiate an arbitrary SPAC model and does not transport to a
-- different N pathway, crop, soil, climate or horizon.
------------------------------------------------------------------------

record TracerSPACAdmission
    (receipt : Primary.NitrogenToCropSoilPrimaryReceipt)
    (spac : SPAC.SPACDomainRealization) : Set₁ where
  constructor tracer-spac-admission
  field
    sourceIsCanonical15NStudy :
      Primary.source receipt ≡ Sources.wheat15N2025
    exactCropMatchReference : String
    exactSiteSoilMatchReference : String
    exactFertiliserFormAndRateMatchReference : String
    exactHorizonMatchReference : String
    tracerPlantCompartmentMappingReference : String
    tracerIntegratedCropUptakeReference : String
    spacNutrientUptakeSocketReference : String
    tracerToSPACCalibrationReference : String
    sameSpatialBoundaryReference : String
    sameTemporalBoundaryReference : String
    conservationWeldReference : String
    validationReference : String
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource :
      externalClaimOwner ≡ Attribution.externalSourceOwner
    dashiWeldOwner : Attribution.ClaimOwner
    dashiOwnsFormalWeld :
      dashiWeldOwner ≡ Attribution.dashiFormalisationOwner

open TracerSPACAdmission public

-- Explicit reference to the canonical receiving socket already owned by SPAC.
spacRootUptakeMineralNSocket :
  (spac : SPAC.SPACDomainRealization) → String
spacRootUptakeMineralNSocket spac =
  SPAC.rootUptakeToMineralNReference (SPAC.biogeochemistryFeedback spac)

------------------------------------------------------------------------
-- Snowball acquisition/payment split.
------------------------------------------------------------------------

record TracerSPACAcquisitionState : Set₁ where
  constructor tracer-spac-acquisition-state
  field
    primaryTracerReceiptAcquired : Bool
    cropIdentityAcquired : Bool
    soilSiteIdentityAcquired : Bool
    fertiliserFormRateAcquired : Bool
    temporalBoundaryAcquired : Bool
    integratedCropUptakeAcquired : Bool
    spacRealisationAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open TracerSPACAcquisitionState public

record TracerSPACPaymentState : Set where
  constructor tracer-spac-payment-state
  field
    sameCropPaid : Bool
    sameSiteSoilPaid : Bool
    sameFertiliserFormRatePaid : Bool
    sameHorizonPaid : Bool
    plantCompartmentMappingPaid : Bool
    integratedUptakeConsumerPaid : Bool
    rootFluxEquivalencePaid : Bool
    conservationPaid : Bool
    validationPaid : Bool
    firstUnpaidGateReference : String

open TracerSPACPaymentState public

snowballAcquisitionDoesNotAdvanceTracerPayment :
  TracerSPACAcquisitionState →
  TracerSPACPaymentState →
  TracerSPACPaymentState
snowballAcquisitionDoesNotAdvanceTracerPayment _ payment = payment

------------------------------------------------------------------------
-- Admission into an existing nitrogen transition weld remains explicit.
------------------------------------------------------------------------

record PrimaryTracerNitrogenTransitionCalibration
    {receipt : Primary.NitrogenToCropSoilPrimaryReceipt}
    {spac : SPAC.SPACDomainRealization}
    (admission : TracerSPACAdmission receipt spac)
    (transitionWeld : NitrogenLES.NitrogenSPACTransitionWeld) : Set₁ where
  constructor primary-tracer-nitrogen-transition-calibration
  field
    sameSPACRealisationReference : String
    sameNitrogenInterventionReference : String
    sameCropAndCompartmentReference : String
    integratedUptakeMeasurementMatchesDeclaredConsumerReference : String
    transitionRootUptakeReference : String
    sourceCalibrationDoesNotReplaceTransitionModel : Bool
    sourceCalibrationDoesNotPayAllocationOrYield : Bool

open PrimaryTracerNitrogenTransitionCalibration public

------------------------------------------------------------------------
-- WrongType / attribution barriers.
------------------------------------------------------------------------

data IntegratedCropUptakeMeansInstantaneousRootFluxPermission : Set where
data WheatTracerMeansAllNitrogenPathwaysPermission : Set where
data SPACSocketMeansMeasuredUptakePermission : Set where
data SourceCalibrationMeansSPACValidationPermission : Set where
data UptakeCalibrationMeansAllocationPermission : Set where
data ExternalStudyOwnsDashiWeldPermission : Set where

integratedCropUptakeDoesNotEqualInstantaneousRootFlux :
  IntegratedCropUptakeMeansInstantaneousRootFluxPermission → ⊥
integratedCropUptakeDoesNotEqualInstantaneousRootFlux ()

wheatTracerDoesNotPayAllNitrogenPathways :
  WheatTracerMeansAllNitrogenPathwaysPermission → ⊥
wheatTracerDoesNotPayAllNitrogenPathways ()

spacSocketDoesNotManufactureMeasurement :
  SPACSocketMeansMeasuredUptakePermission → ⊥
spacSocketDoesNotManufactureMeasurement ()

sourceCalibrationDoesNotAutomaticallyValidateSPAC :
  SourceCalibrationMeansSPACValidationPermission → ⊥
sourceCalibrationDoesNotAutomaticallyValidateSPAC ()

uptakeCalibrationDoesNotPayAllocation :
  UptakeCalibrationMeansAllocationPermission → ⊥
uptakeCalibrationDoesNotPayAllocation ()

externalSourceDoesNotOwnDashiWeld :
  ExternalStudyOwnsDashiWeldPermission → ⊥
externalSourceDoesNotOwnDashiWeld ()

record Nitrogen15NTracerSPACBoundary : Set where
  constructor nitrogen15n-tracer-spac-boundary
  field
    integratedUptakeAndInstantaneousRootFluxRemainDistinct : Bool
    primarySourceAndDashiWeldRemainDistinct : Bool
    cropSiteFertiliserAndHorizonRemainFirstClass : Bool
    tracerCalibrationAndSPACValidationRemainDistinct : Bool
    uptakeAndAllocationRemainDistinct : Bool
    acquisitionAndPaymentRemainDistinct : Bool
    sourceAutomaticallyPaysAllNitrogenPathways : Bool

canonicalNitrogen15NTracerSPACBoundary : Nitrogen15NTracerSPACBoundary
canonicalNitrogen15NTracerSPACBoundary =
  nitrogen15n-tracer-spac-boundary true true true true true true false
