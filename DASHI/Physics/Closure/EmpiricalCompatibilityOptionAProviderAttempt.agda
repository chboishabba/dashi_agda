module DASHI.Physics.Closure.EmpiricalCompatibilityOptionAProviderAttempt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservable as Bridge
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservableIntake as Intake
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservableSourceDiagnostic as Source
import DASHI.Physics.Closure.EmpiricalCalibrationExternalReceiptRequestPack as Pack
import DASHI.Physics.Closure.P0ProviderReceiptRequestIndex as Provider

------------------------------------------------------------------------
-- Option A measured-observable provider attempt.
--
-- The current repo has a Nat-valued bridge surface, an external intake shape,
-- and a request pack.  It does not have the measured observable payload or
-- authority needed to turn that surface into empirical compatibility.

data OptionAProviderAttemptDecision : Set where
  diagnosticOnlyNoLocalMeasuredObservableReceipt :
    OptionAProviderAttemptDecision

data OptionAProviderAttemptAbsentField : Set where
  measuredValueAbsent :
    OptionAProviderAttemptAbsentField
  measurementWitnessAbsent :
    OptionAProviderAttemptAbsentField
  externalAuthorityWitnessAbsent :
    OptionAProviderAttemptAbsentField
  authorityTokenAbsent :
    OptionAProviderAttemptAbsentField
  calibratedStateAbsent :
    OptionAProviderAttemptAbsentField
  observableMatchesMeasuredValueProofAbsent :
    OptionAProviderAttemptAbsentField

data OptionAProviderAttemptClosureToken : Set where

canonicalOptionAProviderAttemptAbsentFields :
  List OptionAProviderAttemptAbsentField
canonicalOptionAProviderAttemptAbsentFields =
  measuredValueAbsent
  ∷ measurementWitnessAbsent
  ∷ externalAuthorityWitnessAbsent
  ∷ authorityTokenAbsent
  ∷ calibratedStateAbsent
  ∷ observableMatchesMeasuredValueProofAbsent
  ∷ []

record EmpiricalCompatibilityOptionAProviderAttempt : Setω where
  field
    decision :
      OptionAProviderAttemptDecision

    providerIndex :
      Provider.P0ProviderReceiptRequestIndex

    externalReceiptRequestPack :
      Pack.EmpiricalCalibrationExternalReceiptRequestPack

    optionAMeasuredObservableRequest :
      Pack.OptionAMeasuredObservableReceiptRequest

    sourceDiagnostic :
      Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic

    intakeStatus :
      Intake.EmpiricalCalibrationBridgeObservableIntakeCurrentStatus

    surface :
      Bridge.EmpiricalCalibrationBridgeObservableSurface

    exactReceiptName :
      String

    exactMissingReceiptFields :
      List String

    absentReceiptFields :
      List OptionAProviderAttemptAbsentField

    absentReceiptFieldsAreCanonical :
      absentReceiptFields
      ≡
      canonicalOptionAProviderAttemptAbsentFields

    missingSourceFields :
      List Source.EmpiricalCalibrationBridgeObservableSourceMissingField

    missingSourceFieldsAreCanonical :
      missingSourceFields
      ≡
      Source.currentMissingSourceFields

    intakeBlockedFields :
      List Intake.EmpiricalCalibrationBridgeObservableIntakeBlockedField

    intakeBlockedFieldsAreCanonical :
      intakeBlockedFields
      ≡
      Intake.canonicalEmpiricalCalibrationBridgeObservableIntakeBlockedFields

    bridgeMeasurementAvailability :
      Bridge.MeasurementAvailability

    bridgeMeasurementStillMissing :
      bridgeMeasurementAvailability
      ≡
      Bridge.noInRepoMeasuredValue

    measuredValueSource :
      Source.EmpiricalCalibrationBridgeObservableSourcePresence

    measurementWitnessSource :
      Source.EmpiricalCalibrationBridgeObservableSourcePresence

    externalAuthorityWitnessSource :
      Source.EmpiricalCalibrationBridgeObservableSourcePresence

    authorityTokenSource :
      Source.EmpiricalCalibrationBridgeObservableSourcePresence

    observableMatchesMeasuredValueSource :
      Source.EmpiricalCalibrationBridgeObservableSourcePresence

    authorityTokenImpossibleHere :
      Bridge.EmpiricalCalibrationAuthorityToken →
      Bridge.EmpiricalCalibrationAuthorityImpossibleHere

    receiptImpossibleHere :
      Intake.CurrentOptionAExternalReceipt →
      Bridge.EmpiricalCalibrationAuthorityImpossibleHere

    positiveReceiptWouldNeedClosureToken :
      OptionAProviderAttemptClosureToken →
      Intake.CurrentOptionAExternalReceipt

    nonPromotionBoundary :
      List String

    providerDiagnostic :
      List String

canonicalEmpiricalCompatibilityOptionAProviderAttempt :
  EmpiricalCompatibilityOptionAProviderAttempt
canonicalEmpiricalCompatibilityOptionAProviderAttempt =
  record
    { decision =
        diagnosticOnlyNoLocalMeasuredObservableReceipt
    ; providerIndex =
        Provider.canonicalP0ProviderReceiptRequestIndex
    ; externalReceiptRequestPack =
        Provider.P0ProviderReceiptRequestIndex.optionABCExternalCalibrationRequestPack
          Provider.canonicalP0ProviderReceiptRequestIndex
    ; optionAMeasuredObservableRequest =
        Pack.EmpiricalCalibrationExternalReceiptRequestPack.optionAMeasuredObservableRequest
          Pack.canonicalEmpiricalCalibrationExternalReceiptRequestPack
    ; sourceDiagnostic =
        Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; intakeStatus =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.intakeStatus
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; surface =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.surface
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; exactReceiptName =
        Pack.OptionAMeasuredObservableReceiptRequest.exactReceiptName
          Pack.canonicalOptionAMeasuredObservableReceiptRequest
    ; exactMissingReceiptFields =
        Pack.OptionAMeasuredObservableReceiptRequest.exactMissingReceiptFields
          Pack.canonicalOptionAMeasuredObservableReceiptRequest
    ; absentReceiptFields =
        canonicalOptionAProviderAttemptAbsentFields
    ; absentReceiptFieldsAreCanonical =
        refl
    ; missingSourceFields =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.missingSourceFields
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; missingSourceFieldsAreCanonical =
        refl
    ; intakeBlockedFields =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.intakeBlockedFields
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; intakeBlockedFieldsAreCanonical =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.intakeBlockedFieldsStillCanonical
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; bridgeMeasurementAvailability =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.bridgeMeasurementAvailability
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; bridgeMeasurementStillMissing =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.bridgeMeasurementStillMissing
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; measuredValueSource =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.measuredValueSource
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; measurementWitnessSource =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.measurementWitnessSource
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; externalAuthorityWitnessSource =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.externalAuthorityWitnessSource
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; authorityTokenSource =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.authorityTokenSource
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; observableMatchesMeasuredValueSource =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.observableMatchesMeasuredValueSource
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; authorityTokenImpossibleHere =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.authorityTokenImpossibleHere
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; receiptImpossibleHere =
        Source.EmpiricalCalibrationBridgeObservableSourceDiagnostic.receiptImpossibleHere
          Source.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; positiveReceiptWouldNeedClosureToken =
        λ ()
    ; nonPromotionBoundary =
        "This provider attempt does not construct CurrentOptionAExternalReceipt"
        ∷ "It does not turn the local Nat energy observable into empirical compatibility"
        ∷ "It does not construct EmpiricalCalibrationAuthorityToken"
        ∷ "It preserves the A3 source diagnostic that all Option A receipt inputs are missing"
        ∷ []
    ; providerDiagnostic =
        "Diagnostic only: no positive measured-observable empirical bridge receipt is locally constructible"
        ∷ "The current bridge surface is a Nat-valued S/Nat-to-observable shape, not a measured external observable"
        ∷ "Absent measured-value fields: measuredValue and measurementWitness"
        ∷ "Absent authority fields: externalAuthorityWitness and EmpiricalCalibrationAuthorityToken"
        ∷ "Absent match fields: calibratedState and observableMatchesMeasuredValue proof"
        ∷ []
    }

optionAProviderAttemptDecisionIsDiagnostic :
  EmpiricalCompatibilityOptionAProviderAttempt.decision
    canonicalEmpiricalCompatibilityOptionAProviderAttempt
  ≡
  diagnosticOnlyNoLocalMeasuredObservableReceipt
optionAProviderAttemptDecisionIsDiagnostic =
  refl

optionAProviderAttemptMissingSourcesAreA3Canonical :
  EmpiricalCompatibilityOptionAProviderAttempt.missingSourceFields
    canonicalEmpiricalCompatibilityOptionAProviderAttempt
  ≡
  Source.currentMissingSourceFields
optionAProviderAttemptMissingSourcesAreA3Canonical =
  refl
