module DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnitsSourceDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnits as Units
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnitsIntake as Intake

------------------------------------------------------------------------
-- Option B source diagnostic.
--
-- B2 names the full UnitCalibrationIntakeReceipt required by Option B.
-- This source scan records that the current repo does not supply the receipt
-- inputs.  It does not construct units, authority, validation, or a bridge.

data SourceInputAvailability : Set where
  present :
    SourceInputAvailability
  missing :
    SourceInputAvailability

record UnitCalibrationSourceAvailability : Set where
  field
    unitCarrier :
      SourceInputAvailability

    dimensionCarrier :
      SourceInputAvailability

    unitAssignments :
      SourceInputAvailability

    dimensionPreservation :
      SourceInputAvailability

    scaleEvidence :
      SourceInputAvailability

    monotonicity :
      SourceInputAvailability

    externalCalibrationAuthority :
      SourceInputAvailability

    validationToken :
      SourceInputAvailability

canonicalUnitCalibrationSourceAvailability :
  UnitCalibrationSourceAvailability
canonicalUnitCalibrationSourceAvailability =
  record
    { unitCarrier =
        missing
    ; dimensionCarrier =
        missing
    ; unitAssignments =
        missing
    ; dimensionPreservation =
        missing
    ; scaleEvidence =
        missing
    ; monotonicity =
        missing
    ; externalCalibrationAuthority =
        missing
    ; validationToken =
        missing
    }

record EmpiricalCalibrationBridgeUnitsSourceDiagnostic : Setω where
  field
    intakeStatus :
      Intake.UnitCalibrationIntakeCurrentStatus

    bridgeUnitsStatus :
      Units.EmpiricalCalibrationBridgeUnitsCurrentStatus

    sourceAvailability :
      UnitCalibrationSourceAvailability

    intakeMissingFields :
      List Intake.UnitCalibrationIntakeMissingField

    sourceScanMatchesB2MissingFields :
      intakeMissingFields
      ≡
      Intake.canonicalUnitCalibrationIntakeMissingFields

    requiredReceipt :
      String

    consumerWiringTarget :
      String

    blockerImpact :
      String

    noFabricationBoundary :
      List String

    impossibleAuthorityHere :
      Units.ExternalCalibrationAuthorityToken →
      ⊥

    impossibleValidationHere :
      Intake.ExternalUnitCalibrationValidationToken →
      ⊥

    impossibleReceiptHere :
      Intake.UnitCalibrationIntakeReceipt →
      ⊥

canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic :
  EmpiricalCalibrationBridgeUnitsSourceDiagnostic
canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic =
  record
    { intakeStatus =
        Intake.canonicalUnitCalibrationIntakeCurrentStatus
    ; bridgeUnitsStatus =
        Intake.UnitCalibrationIntakeCurrentStatus.bridgeUnitsStatus
          Intake.canonicalUnitCalibrationIntakeCurrentStatus
    ; sourceAvailability =
        canonicalUnitCalibrationSourceAvailability
    ; intakeMissingFields =
        Intake.UnitCalibrationIntakeCurrentStatus.missingFields
          Intake.canonicalUnitCalibrationIntakeCurrentStatus
    ; sourceScanMatchesB2MissingFields =
        refl
    ; requiredReceipt =
        Intake.UnitCalibrationIntakeCurrentStatus.requiredReceipt
          Intake.canonicalUnitCalibrationIntakeCurrentStatus
    ; consumerWiringTarget =
        Intake.UnitCalibrationIntakeCurrentStatus.consumerWiringTarget
          Intake.canonicalUnitCalibrationIntakeCurrentStatus
    ; blockerImpact =
        Intake.UnitCalibrationIntakeCurrentStatus.blockerImpact
          Intake.canonicalUnitCalibrationIntakeCurrentStatus
    ; noFabricationBoundary =
        "Current source scan found no UnitCalibrationIntakeReceipt"
        ∷ "Unit carrier and dimension carrier remain external source inputs"
        ∷ "Unit assignments, dimension preservation, scale evidence, and monotonicity remain external source inputs"
        ∷ "ExternalCalibrationAuthorityToken and ExternalUnitCalibrationValidationToken remain constructorless here"
        ∷ "No physical calibration is discharged by Nat surrogate or toy-fit data"
        ∷ []
    ; impossibleAuthorityHere =
        Units.externalCalibrationAuthorityImpossibleHere
    ; impossibleValidationHere =
        Intake.externalUnitCalibrationValidationImpossibleHere
    ; impossibleReceiptHere =
        Intake.unitCalibrationIntakeReceiptImpossibleHere
    }
