module DASHI.Physics.Closure.EmpiricalCompatibilityOptionBProviderAttempt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnits as Units
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnitsIntake as Intake
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnitsSourceDiagnostic as Source
import DASHI.Physics.Closure.EmpiricalCalibrationExternalReceiptRequestPack as Pack
import DASHI.Physics.Closure.P0ProviderReceiptRequestIndex as P0Provider
import DASHI.Physics.Closure.W4PhysicalCalibrationProviderAttempt as W4Attempt

------------------------------------------------------------------------
-- EMP-B / Option-B provider attempt.
--
-- This module attempts the unit-preserving empirical-compatibility route
-- against the current repo sources.  It is diagnostic-only: the current
-- source scan records the unit carrier, dimensional law, authority, and
-- validation inputs as missing, and the authority/validation tokens remain
-- constructorless here.

data OptionBProviderAttemptDecision : Set where
  noLocalUnitCalibrationIntakeReceipt :
    OptionBProviderAttemptDecision

data OptionBProviderSourcePresence : Set where
  sourceMissing :
    OptionBProviderSourcePresence

data OptionBProviderAttemptBlockedField : Set where
  absentPhysicalUnitCarrier :
    OptionBProviderAttemptBlockedField
  absentDimensionCarrier :
    OptionBProviderAttemptBlockedField
  absentDimensionOfUnit :
    OptionBProviderAttemptBlockedField
  absentUnitAssignments :
    OptionBProviderAttemptBlockedField
  absentDimensionPreservationLaw :
    OptionBProviderAttemptBlockedField
  absentScaleEvidence :
    OptionBProviderAttemptBlockedField
  absentMonotonicityLaw :
    OptionBProviderAttemptBlockedField
  absentExternalCalibrationAuthority :
    OptionBProviderAttemptBlockedField
  absentExternalValidation :
    OptionBProviderAttemptBlockedField

canonicalOptionBProviderAttemptBlockedFields :
  List OptionBProviderAttemptBlockedField
canonicalOptionBProviderAttemptBlockedFields =
  absentPhysicalUnitCarrier
  ∷ absentDimensionCarrier
  ∷ absentDimensionOfUnit
  ∷ absentUnitAssignments
  ∷ absentDimensionPreservationLaw
  ∷ absentScaleEvidence
  ∷ absentMonotonicityLaw
  ∷ absentExternalCalibrationAuthority
  ∷ absentExternalValidation
  ∷ []

record EmpiricalCompatibilityOptionBProviderAttempt : Setω where
  field
    providerRequestIndex :
      P0Provider.P0ProviderReceiptRequestIndex

    externalReceiptRequestPack :
      Pack.EmpiricalCalibrationExternalReceiptRequestPack

    optionBReceiptRequest :
      Pack.OptionBUnitCalibrationReceiptRequest

    sourceDiagnostic :
      Source.EmpiricalCalibrationBridgeUnitsSourceDiagnostic

    intakeStatus :
      Intake.UnitCalibrationIntakeCurrentStatus

    bridgeUnitsStatus :
      Units.EmpiricalCalibrationBridgeUnitsCurrentStatus

    w4ProviderAttempt :
      W4Attempt.W4PhysicalCalibrationProviderAttempt

    constructionDecision :
      OptionBProviderAttemptDecision

    unitCarrierSource :
      OptionBProviderSourcePresence

    calibrationAuthoritySource :
      OptionBProviderSourcePresence

    dimensionalLawSource :
      OptionBProviderSourcePresence

    validationSource :
      OptionBProviderSourcePresence

    sourceAvailability :
      Source.UnitCalibrationSourceAvailability

    unitCarrierAvailabilityIsMissing :
      Source.UnitCalibrationSourceAvailability.unitCarrier sourceAvailability
      ≡
      Source.missing

    dimensionCarrierAvailabilityIsMissing :
      Source.UnitCalibrationSourceAvailability.dimensionCarrier sourceAvailability
      ≡
      Source.missing

    dimensionPreservationAvailabilityIsMissing :
      Source.UnitCalibrationSourceAvailability.dimensionPreservation sourceAvailability
      ≡
      Source.missing

    calibrationAuthorityAvailabilityIsMissing :
      Source.UnitCalibrationSourceAvailability.externalCalibrationAuthority sourceAvailability
      ≡
      Source.missing

    validationAvailabilityIsMissing :
      Source.UnitCalibrationSourceAvailability.validationToken sourceAvailability
      ≡
      Source.missing

    intakeMissingFields :
      List Intake.UnitCalibrationIntakeMissingField

    intakeMissingFieldsAreCanonical :
      intakeMissingFields
      ≡
      Intake.canonicalUnitCalibrationIntakeMissingFields

    providerBlockedFields :
      List OptionBProviderAttemptBlockedField

    providerBlockedFieldsAreCanonical :
      providerBlockedFields
      ≡
      canonicalOptionBProviderAttemptBlockedFields

    exactMissingReceiptFields :
      List String

    exactMissingReceiptFieldsAreCurrent :
      exactMissingReceiptFields
      ≡
      Pack.OptionBUnitCalibrationReceiptRequest.exactMissingReceiptFields
        optionBReceiptRequest

    externalAuthorityImpossibleHere :
      Units.ExternalCalibrationAuthorityToken →
      ⊥

    externalValidationImpossibleHere :
      Intake.ExternalUnitCalibrationValidationToken →
      ⊥

    unitCalibrationReceiptImpossibleHere :
      Intake.UnitCalibrationIntakeReceipt →
      ⊥

    legitimatePositiveReceiptConstructionBlocked :
      Intake.UnitCalibrationIntakeReceipt →
      ⊥

    diagnosticBoundary :
      List String

    blockerImpact :
      List String

canonicalEmpiricalCompatibilityOptionBProviderAttempt :
  EmpiricalCompatibilityOptionBProviderAttempt
canonicalEmpiricalCompatibilityOptionBProviderAttempt =
  record
    { providerRequestIndex =
        P0Provider.canonicalP0ProviderReceiptRequestIndex
    ; externalReceiptRequestPack =
        Pack.canonicalEmpiricalCalibrationExternalReceiptRequestPack
    ; optionBReceiptRequest =
        Pack.canonicalOptionBUnitCalibrationReceiptRequest
    ; sourceDiagnostic =
        Source.canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic
    ; intakeStatus =
        Source.EmpiricalCalibrationBridgeUnitsSourceDiagnostic.intakeStatus
          Source.canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic
    ; bridgeUnitsStatus =
        Source.EmpiricalCalibrationBridgeUnitsSourceDiagnostic.bridgeUnitsStatus
          Source.canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic
    ; w4ProviderAttempt =
        W4Attempt.canonicalW4PhysicalCalibrationProviderAttempt
    ; constructionDecision =
        noLocalUnitCalibrationIntakeReceipt
    ; unitCarrierSource =
        sourceMissing
    ; calibrationAuthoritySource =
        sourceMissing
    ; dimensionalLawSource =
        sourceMissing
    ; validationSource =
        sourceMissing
    ; sourceAvailability =
        Source.canonicalUnitCalibrationSourceAvailability
    ; unitCarrierAvailabilityIsMissing =
        refl
    ; dimensionCarrierAvailabilityIsMissing =
        refl
    ; dimensionPreservationAvailabilityIsMissing =
        refl
    ; calibrationAuthorityAvailabilityIsMissing =
        refl
    ; validationAvailabilityIsMissing =
        refl
    ; intakeMissingFields =
        Source.EmpiricalCalibrationBridgeUnitsSourceDiagnostic.intakeMissingFields
          Source.canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic
    ; intakeMissingFieldsAreCanonical =
        refl
    ; providerBlockedFields =
        canonicalOptionBProviderAttemptBlockedFields
    ; providerBlockedFieldsAreCanonical =
        refl
    ; exactMissingReceiptFields =
        Pack.OptionBUnitCalibrationReceiptRequest.exactMissingReceiptFields
          Pack.canonicalOptionBUnitCalibrationReceiptRequest
    ; exactMissingReceiptFieldsAreCurrent =
        refl
    ; externalAuthorityImpossibleHere =
        Units.externalCalibrationAuthorityImpossibleHere
    ; externalValidationImpossibleHere =
        Intake.externalUnitCalibrationValidationImpossibleHere
    ; unitCalibrationReceiptImpossibleHere =
        Intake.unitCalibrationIntakeReceiptImpossibleHere
    ; legitimatePositiveReceiptConstructionBlocked =
        Intake.unitCalibrationIntakeReceiptImpossibleHere
    ; diagnosticBoundary =
        "Diagnostic only: no UnitCalibrationIntakeReceipt is constructed"
        ∷ "No Nat surrogate is promoted to a physical unit carrier"
        ∷ "Unit carrier, dimension carrier, dimensionOfUnit, unit assignments, dimensional preservation, scale evidence, monotonicity, authority, and validation remain external inputs"
        ∷ "ExternalCalibrationAuthorityToken and ExternalUnitCalibrationValidationToken are constructorless in the current Option B intake surface"
        ∷ []
    ; blockerImpact =
        "Option B remains blocked until a legitimate UnitCalibrationIntakeReceipt is externally supplied"
        ∷ "W4 physical calibration remains blocked on authority, physical unit carrier, calibrated maps, factorization, and dimensional preservation"
        ∷ "W5 cannot consume Option B as physical calibration without unit-preserving calibration authority and validation"
        ∷ []
    }

canonicalEmpiricalCompatibilityOptionBProviderAttemptIsDiagnostic :
  EmpiricalCompatibilityOptionBProviderAttempt.constructionDecision
    canonicalEmpiricalCompatibilityOptionBProviderAttempt
  ≡
  noLocalUnitCalibrationIntakeReceipt
canonicalEmpiricalCompatibilityOptionBProviderAttemptIsDiagnostic =
  refl

canonicalEmpiricalCompatibilityOptionBProviderAttemptBlocksReceipt :
  Intake.UnitCalibrationIntakeReceipt →
  ⊥
canonicalEmpiricalCompatibilityOptionBProviderAttemptBlocksReceipt =
  EmpiricalCompatibilityOptionBProviderAttempt.legitimatePositiveReceiptConstructionBlocked
    canonicalEmpiricalCompatibilityOptionBProviderAttempt
