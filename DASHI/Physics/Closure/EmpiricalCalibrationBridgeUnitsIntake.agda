module DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnitsIntake where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnits as Units

------------------------------------------------------------------------
-- Option B unit-calibration intake.
--
-- This module is the concrete intake surface for the unit-preserving
-- empirical-calibration bridge.  It names the full external receipt required
-- by Option B, but does not construct units, dimensions, scale evidence,
-- numeric constants, authority, validation, or any W4/W5 promotion.

data ExternalUnitCalibrationValidationToken : Set where

record UnitCalibrationIntakeReceipt : Setω where
  field
    UnitCarrier : Set
    DimensionCarrier : Set

    dimensionOfUnit :
      UnitCarrier →
      DimensionCarrier

    internalEnergyCarrier : Set
    measuredQuantityCarrier : Set

    internalEnergyUnit :
      internalEnergyCarrier →
      UnitCarrier

    measuredQuantityUnit :
      measuredQuantityCarrier →
      UnitCarrier

    calibrationMap :
      internalEnergyCarrier →
      measuredQuantityCarrier

    dimensionPreservation :
      (e : internalEnergyCarrier) →
      dimensionOfUnit (measuredQuantityUnit (calibrationMap e))
      ≡
      dimensionOfUnit (internalEnergyUnit e)

    internalOrder :
      internalEnergyCarrier →
      internalEnergyCarrier →
      Set

    measuredOrder :
      measuredQuantityCarrier →
      measuredQuantityCarrier →
      Set

    monotonicity :
      (e₁ e₂ : internalEnergyCarrier) →
      internalOrder e₁ e₂ →
      measuredOrder (calibrationMap e₁) (calibrationMap e₂)

    scaleCarrier : Set
    calibrationTokenCarrier : Set

    scaleEvidence :
      Units.EmpiricalCalibrationScaleEvidence
        scaleCarrier
        calibrationTokenCarrier

    externalAuthority :
      Units.ExternalCalibrationAuthorityToken

    externalValidation :
      ExternalUnitCalibrationValidationToken

    unitCarrierLabel : String
    dimensionCarrierLabel : String
    internalEnergyUnitLabel : String
    measuredQuantityUnitLabel : String
    dimensionPreservationLabel : String
    scaleEvidenceLabel : String
    monotonicityLabel : String
    externalAuthorityLabel : String
    externalValidationLabel : String
    consumerWiringTargetLabel : String

intakeReceiptToUnitSurface :
  UnitCalibrationIntakeReceipt →
  Units.DimensionedUnitSurface
intakeReceiptToUnitSurface receipt =
  record
    { UnitCarrier =
        UnitCalibrationIntakeReceipt.UnitCarrier receipt
    ; DimensionCarrier =
        UnitCalibrationIntakeReceipt.DimensionCarrier receipt
    ; dimensionOfUnit =
        UnitCalibrationIntakeReceipt.dimensionOfUnit receipt
    ; unitCarrierLabel =
        UnitCalibrationIntakeReceipt.unitCarrierLabel receipt
    ; dimensionCarrierLabel =
        UnitCalibrationIntakeReceipt.dimensionCarrierLabel receipt
    }

intakeReceiptToBridge :
  UnitCalibrationIntakeReceipt →
  Units.UnitPreservingEmpiricalCalibrationBridge
intakeReceiptToBridge receipt =
  record
    { internalEnergyCarrier =
        UnitCalibrationIntakeReceipt.internalEnergyCarrier receipt
    ; measuredQuantityCarrier =
        UnitCalibrationIntakeReceipt.measuredQuantityCarrier receipt
    ; unitSurface =
        intakeReceiptToUnitSurface receipt
    ; internalEnergyUnit =
        UnitCalibrationIntakeReceipt.internalEnergyUnit receipt
    ; measuredQuantityUnit =
        UnitCalibrationIntakeReceipt.measuredQuantityUnit receipt
    ; calibrationMap =
        UnitCalibrationIntakeReceipt.calibrationMap receipt
    ; dimensionPreservation =
        UnitCalibrationIntakeReceipt.dimensionPreservation receipt
    ; internalOrder =
        UnitCalibrationIntakeReceipt.internalOrder receipt
    ; measuredOrder =
        UnitCalibrationIntakeReceipt.measuredOrder receipt
    ; monotonicity =
        UnitCalibrationIntakeReceipt.monotonicity receipt
    ; scaleCarrier =
        UnitCalibrationIntakeReceipt.scaleCarrier receipt
    ; calibrationTokenCarrier =
        UnitCalibrationIntakeReceipt.calibrationTokenCarrier receipt
    ; scaleOrCalibrationToken =
        UnitCalibrationIntakeReceipt.scaleEvidence receipt
    ; numericClaim =
        λ _ → ⊥
    ; bridgeLabel =
        UnitCalibrationIntakeReceipt.consumerWiringTargetLabel receipt
    ; unitPreservationLabel =
        UnitCalibrationIntakeReceipt.dimensionPreservationLabel receipt
    ; monotonicityLabel =
        UnitCalibrationIntakeReceipt.monotonicityLabel receipt
    ; authorityBoundaryLabel =
        UnitCalibrationIntakeReceipt.externalAuthorityLabel receipt
    }

externalUnitCalibrationValidationImpossibleHere :
  ExternalUnitCalibrationValidationToken →
  ⊥
externalUnitCalibrationValidationImpossibleHere ()

unitCalibrationIntakeReceiptImpossibleHere :
  UnitCalibrationIntakeReceipt →
  ⊥
unitCalibrationIntakeReceiptImpossibleHere receipt =
  Units.externalCalibrationAuthorityImpossibleHere
    (UnitCalibrationIntakeReceipt.externalAuthority receipt)

data UnitCalibrationIntakeMissingField : Set where
  missingUnitCarrier :
    UnitCalibrationIntakeMissingField
  missingDimensionCarrier :
    UnitCalibrationIntakeMissingField
  missingDimensionOfUnit :
    UnitCalibrationIntakeMissingField
  missingInternalEnergyUnitAssignment :
    UnitCalibrationIntakeMissingField
  missingMeasuredQuantityUnitAssignment :
    UnitCalibrationIntakeMissingField
  missingDimensionPreservation :
    UnitCalibrationIntakeMissingField
  missingScaleEvidence :
    UnitCalibrationIntakeMissingField
  missingMonotonicity :
    UnitCalibrationIntakeMissingField
  missingExternalAuthority :
    UnitCalibrationIntakeMissingField
  missingExternalValidation :
    UnitCalibrationIntakeMissingField

canonicalUnitCalibrationIntakeMissingFields :
  List UnitCalibrationIntakeMissingField
canonicalUnitCalibrationIntakeMissingFields =
  missingUnitCarrier
  ∷ missingDimensionCarrier
  ∷ missingDimensionOfUnit
  ∷ missingInternalEnergyUnitAssignment
  ∷ missingMeasuredQuantityUnitAssignment
  ∷ missingDimensionPreservation
  ∷ missingScaleEvidence
  ∷ missingMonotonicity
  ∷ missingExternalAuthority
  ∷ missingExternalValidation
  ∷ []

record UnitCalibrationIntakeCurrentStatus : Setω where
  field
    bridgeUnitsStatus :
      Units.EmpiricalCalibrationBridgeUnitsCurrentStatus

    currentStatus :
      Units.EmpiricalCalibrationBridgeUnitsStatus

    missingFields :
      List UnitCalibrationIntakeMissingField

    requiredReceipt : String
    unitCarrierRequirement : String
    dimensionCarrierRequirement : String
    unitAssignmentRequirement : String
    dimensionPreservationRequirement : String
    scaleEvidenceRequirement : String
    monotonicityRequirement : String
    externalAuthorityRequirement : String
    validationRequirement : String
    consumerWiringTarget : String
    blockerImpact : String

    noPromotionBoundary :
      List String

    impossibleAuthorityHere :
      Units.ExternalCalibrationAuthorityToken →
      ⊥

    impossibleValidationHere :
      ExternalUnitCalibrationValidationToken →
      ⊥

    impossibleReceiptHere :
      UnitCalibrationIntakeReceipt →
      ⊥

canonicalUnitCalibrationIntakeCurrentStatus :
  UnitCalibrationIntakeCurrentStatus
canonicalUnitCalibrationIntakeCurrentStatus =
  record
    { bridgeUnitsStatus =
        Units.canonicalEmpiricalCalibrationBridgeUnitsCurrentStatus
    ; currentStatus =
        Units.blockedAwaitingExternalUnitCalibration
    ; missingFields =
        canonicalUnitCalibrationIntakeMissingFields
    ; requiredReceipt =
        "provide UnitCalibrationIntakeReceipt carrying unit carrier, dimension carrier, unit assignments, dimension preservation, scale evidence, monotonicity, external authority, and validation"
    ; unitCarrierRequirement =
        "supply the physical UnitCarrier used by the measured calibration target"
    ; dimensionCarrierRequirement =
        "supply the DimensionCarrier and dimensionOfUnit map for the unit surface"
    ; unitAssignmentRequirement =
        "assign units to every internal energy input and every measured quantity output"
    ; dimensionPreservationRequirement =
        "prove measuredQuantityUnit (calibrationMap e) has the same dimension as internalEnergyUnit e for every input"
    ; scaleEvidenceRequirement =
        "supply EmpiricalCalibrationScaleEvidence as either scaleCarrier evidence or calibrationTokenCarrier evidence"
    ; monotonicityRequirement =
        "prove calibrationMap is monotone from the internal energy order to the measured quantity order"
    ; externalAuthorityRequirement =
        "supply ExternalCalibrationAuthorityToken outside this constructorless module before any numeric calibration authority is cited"
    ; validationRequirement =
        "supply ExternalUnitCalibrationValidationToken from the external validation lane before treating the receipt as empirically calibrated"
    ; consumerWiringTarget =
        "intakeReceiptToBridge is the consumer wiring target for Option B after an external UnitCalibrationIntakeReceipt exists"
    ; blockerImpact =
        "strict blocker unchanged: Option B, W4 chemistry, and W5 GR/QFT remain blocked awaiting external unit calibration, authority, and validation"
    ; noPromotionBoundary =
        "This module does not construct UnitCalibrationIntakeReceipt"
        ∷ "This module does not construct ExternalCalibrationAuthorityToken"
        ∷ "This module does not construct ExternalUnitCalibrationValidationToken"
        ∷ "This module does not choose SI units, dimensions, scale factors, datasets, or numeric constants"
        ∷ "This module does not promote W4 chemistry or W5 GR/QFT closure"
        ∷ []
    ; impossibleAuthorityHere =
        Units.externalCalibrationAuthorityImpossibleHere
    ; impossibleValidationHere =
        externalUnitCalibrationValidationImpossibleHere
    ; impossibleReceiptHere =
        unitCalibrationIntakeReceiptImpossibleHere
    }
