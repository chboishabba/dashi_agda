module DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservableSourceDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservable as Bridge
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservableIntake as Intake

------------------------------------------------------------------------
-- Option A current-source diagnostic.
--
-- The intake module names the external receipt shape.  This module only
-- records current source availability for that shape; it does not construct
-- a measured value, authority token, calibrated state, or adequacy receipt.

data EmpiricalCalibrationBridgeObservableSourcePresence : Set where
  sourcePresent :
    EmpiricalCalibrationBridgeObservableSourcePresence
  sourceMissing :
    EmpiricalCalibrationBridgeObservableSourcePresence

data EmpiricalCalibrationBridgeObservableSourceMissingField : Set where
  measuredValueMissing :
    EmpiricalCalibrationBridgeObservableSourceMissingField
  measurementWitnessMissing :
    EmpiricalCalibrationBridgeObservableSourceMissingField
  externalAuthorityWitnessMissing :
    EmpiricalCalibrationBridgeObservableSourceMissingField
  authorityTokenMissing :
    EmpiricalCalibrationBridgeObservableSourceMissingField
  calibratedStateMissing :
    EmpiricalCalibrationBridgeObservableSourceMissingField
  observableMatchesMeasuredValueMissing :
    EmpiricalCalibrationBridgeObservableSourceMissingField

data EmpiricalCalibrationBridgeObservableSourceClosureToken : Set where

currentMissingSourceFields :
  List EmpiricalCalibrationBridgeObservableSourceMissingField
currentMissingSourceFields =
  measuredValueMissing
  ∷ measurementWitnessMissing
  ∷ externalAuthorityWitnessMissing
  ∷ authorityTokenMissing
  ∷ calibratedStateMissing
  ∷ observableMatchesMeasuredValueMissing
  ∷ []

record EmpiricalCalibrationBridgeObservableSourceDiagnostic : Setω where
  field
    intakeStatus :
      Intake.EmpiricalCalibrationBridgeObservableIntakeCurrentStatus

    surface :
      Bridge.EmpiricalCalibrationBridgeObservableSurface

    measuredValueSource :
      EmpiricalCalibrationBridgeObservableSourcePresence

    measurementWitnessSource :
      EmpiricalCalibrationBridgeObservableSourcePresence

    externalAuthorityWitnessSource :
      EmpiricalCalibrationBridgeObservableSourcePresence

    authorityTokenSource :
      EmpiricalCalibrationBridgeObservableSourcePresence

    calibratedStateSource :
      EmpiricalCalibrationBridgeObservableSourcePresence

    observableMatchesMeasuredValueSource :
      EmpiricalCalibrationBridgeObservableSourcePresence

    missingSourceFields :
      List EmpiricalCalibrationBridgeObservableSourceMissingField

    intakeBlockedFields :
      List Intake.EmpiricalCalibrationBridgeObservableIntakeBlockedField

    intakeBlockedFieldsStillCanonical :
      intakeBlockedFields
      ≡
      Intake.canonicalEmpiricalCalibrationBridgeObservableIntakeBlockedFields

    bridgeMeasurementAvailability :
      Bridge.MeasurementAvailability

    bridgeMeasurementStillMissing :
      bridgeMeasurementAvailability
      ≡
      Bridge.noInRepoMeasuredValue

    authorityTokenImpossibleHere :
      Bridge.EmpiricalCalibrationAuthorityToken →
      Bridge.EmpiricalCalibrationAuthorityImpossibleHere

    receiptImpossibleHere :
      Intake.CurrentOptionAExternalReceipt →
      Bridge.EmpiricalCalibrationAuthorityImpossibleHere

    closureWouldNeed :
      EmpiricalCalibrationBridgeObservableSourceClosureToken →
      Set

    diagnosticBoundary :
      List String

    blockerImpact :
      List String

currentEmpiricalCalibrationBridgeObservableSourceDiagnostic :
  EmpiricalCalibrationBridgeObservableSourceDiagnostic
currentEmpiricalCalibrationBridgeObservableSourceDiagnostic =
  record
    { intakeStatus =
        Intake.canonicalEmpiricalCalibrationBridgeObservableIntakeCurrentStatus
    ; surface =
        Intake.EmpiricalCalibrationBridgeObservableIntakeCurrentStatus.surface
          Intake.canonicalEmpiricalCalibrationBridgeObservableIntakeCurrentStatus
    ; measuredValueSource =
        sourceMissing
    ; measurementWitnessSource =
        sourceMissing
    ; externalAuthorityWitnessSource =
        sourceMissing
    ; authorityTokenSource =
        sourceMissing
    ; calibratedStateSource =
        sourceMissing
    ; observableMatchesMeasuredValueSource =
        sourceMissing
    ; missingSourceFields =
        currentMissingSourceFields
    ; intakeBlockedFields =
        Intake.EmpiricalCalibrationBridgeObservableIntakeCurrentStatus.blockedFields
          Intake.canonicalEmpiricalCalibrationBridgeObservableIntakeCurrentStatus
    ; intakeBlockedFieldsStillCanonical =
        refl
    ; bridgeMeasurementAvailability =
        Intake.EmpiricalCalibrationBridgeObservableIntakeCurrentStatus.measurementAvailability
          Intake.canonicalEmpiricalCalibrationBridgeObservableIntakeCurrentStatus
    ; bridgeMeasurementStillMissing =
        refl
    ; authorityTokenImpossibleHere =
        Intake.EmpiricalCalibrationBridgeObservableIntakeCurrentStatus.authorityTokenImpossibleHere
          Intake.canonicalEmpiricalCalibrationBridgeObservableIntakeCurrentStatus
    ; receiptImpossibleHere =
        Intake.EmpiricalCalibrationBridgeObservableIntakeCurrentStatus.receiptImpossibleHere
          Intake.canonicalEmpiricalCalibrationBridgeObservableIntakeCurrentStatus
    ; closureWouldNeed =
        λ token → EmpiricalCalibrationBridgeObservableSourceClosureToken
    ; diagnosticBoundary =
        "Option A intake names the external receipt shape but no current source inhabits it"
        ∷ "No measuredValue source is present for the current simple-observable carrier"
        ∷ "No measurementWitness or externalAuthorityWitness source is present"
        ∷ "No EmpiricalCalibrationAuthorityToken source is present or constructed"
        ∷ "No calibratedState plus observableMatchesMeasuredValue source pair is present"
        ∷ []
    ; blockerImpact =
        "Strict blocker remains: Option A cannot promote empirical adequacy from the local Nat observable"
        ∷ "The next admissible move is still an external receipt supplying all missing source fields"
        ∷ "This diagnostic preserves A2's constructorless authority boundary and fabricates no receipt"
        ∷ []
    }
