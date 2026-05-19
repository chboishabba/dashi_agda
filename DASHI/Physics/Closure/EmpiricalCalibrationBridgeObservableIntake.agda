module DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservableIntake where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservable as Bridge

------------------------------------------------------------------------
-- Option A intake request.
--
-- The bridge module supplies only a simple-observable surface and records
-- that the current repo has no measured value.  This module names the next
-- admissible external receipt shape.  It does not construct the authority
-- token, does not inhabit the receipt, and does not promote W3/W5 empirical
-- adequacy from the local Nat observable.

record EmpiricalCalibrationBridgeObservableExternalReceipt
  (surface : Bridge.EmpiricalCalibrationBridgeObservableSurface) : Setω where
  field
    measuredValue :
      Bridge.SimpleObservableCarrier.Carrier
        (Bridge.EmpiricalCalibrationBridgeObservableSurface.simpleObservable
          surface)

    measurementWitness :
      Bridge.EmpiricalCalibrationBridgeObservableSurface.measurementWitnessRequirement
        surface

    externalAuthorityWitness :
      Bridge.EmpiricalCalibrationBridgeObservableSurface.externalAuthorityRequirement
        surface

    authorityToken :
      Bridge.EmpiricalCalibrationAuthorityToken

    calibratedState :
      Bridge.EmpiricalCalibrationBridgeObservableSurface.State surface

    observableMatchesMeasuredValue :
      Bridge.EmpiricalCalibrationBridgeObservableSurface.observable surface
        calibratedState
      ≡
      measuredValue

externalReceiptToBridgeAdequacy :
  {surface : Bridge.EmpiricalCalibrationBridgeObservableSurface} →
  EmpiricalCalibrationBridgeObservableExternalReceipt surface →
  Bridge.EmpiricalCalibrationBridgeObservableAdequacy surface
externalReceiptToBridgeAdequacy receipt =
  record
    { authorityToken =
        EmpiricalCalibrationBridgeObservableExternalReceipt.authorityToken
          receipt
    ; measuredValue =
        EmpiricalCalibrationBridgeObservableExternalReceipt.measuredValue
          receipt
    ; measurementWitness =
        EmpiricalCalibrationBridgeObservableExternalReceipt.measurementWitness
          receipt
    ; externalAuthorityWitness =
        EmpiricalCalibrationBridgeObservableExternalReceipt.externalAuthorityWitness
          receipt
    ; calibratedState =
        EmpiricalCalibrationBridgeObservableExternalReceipt.calibratedState
          receipt
    ; observableMatchesMeasuredValue =
        EmpiricalCalibrationBridgeObservableExternalReceipt.observableMatchesMeasuredValue
          receipt
    }

externalReceiptImpossibleHere :
  {surface : Bridge.EmpiricalCalibrationBridgeObservableSurface} →
  EmpiricalCalibrationBridgeObservableExternalReceipt surface →
  Bridge.EmpiricalCalibrationAuthorityImpossibleHere
externalReceiptImpossibleHere receipt =
  Bridge.empiricalCalibrationAuthorityImpossibleHere
    (EmpiricalCalibrationBridgeObservableExternalReceipt.authorityToken receipt)

------------------------------------------------------------------------
-- Current intake status.

data EmpiricalCalibrationBridgeObservableIntakeBlockedField : Set where
  missingExternalMeasuredValue :
    EmpiricalCalibrationBridgeObservableIntakeBlockedField
  missingExternalMeasurementWitness :
    EmpiricalCalibrationBridgeObservableIntakeBlockedField
  missingExternalAuthorityReceipt :
    EmpiricalCalibrationBridgeObservableIntakeBlockedField
  missingExternalAuthorityToken :
    EmpiricalCalibrationBridgeObservableIntakeBlockedField
  missingObservableMatchesMeasuredValueProof :
    EmpiricalCalibrationBridgeObservableIntakeBlockedField

currentOptionASurface :
  Bridge.EmpiricalCalibrationBridgeObservableSurface
currentOptionASurface =
  Bridge.EmpiricalCalibrationBridgeObservableCurrentDiagnostic.surface
    Bridge.currentEmpiricalCalibrationBridgeObservableDiagnostic

CurrentOptionAExternalReceipt : Setω
CurrentOptionAExternalReceipt =
  EmpiricalCalibrationBridgeObservableExternalReceipt currentOptionASurface

canonicalEmpiricalCalibrationBridgeObservableIntakeBlockedFields :
  List EmpiricalCalibrationBridgeObservableIntakeBlockedField
canonicalEmpiricalCalibrationBridgeObservableIntakeBlockedFields =
  missingExternalMeasuredValue
  ∷ missingExternalMeasurementWitness
  ∷ missingExternalAuthorityReceipt
  ∷ missingExternalAuthorityToken
  ∷ missingObservableMatchesMeasuredValueProof
  ∷ []

record EmpiricalCalibrationBridgeObservableIntakeCurrentStatus : Setω where
  field
    bridgeDiagnostic :
      Bridge.EmpiricalCalibrationBridgeObservableCurrentDiagnostic

    surface :
      Bridge.EmpiricalCalibrationBridgeObservableSurface

    measurementAvailability :
      Bridge.MeasurementAvailability

    currentDiagnosticStillNoInRepoMeasuredValue :
      measurementAvailability
      ≡
      Bridge.noInRepoMeasuredValue

    blockedFields :
      List EmpiricalCalibrationBridgeObservableIntakeBlockedField

    bridgeBlockedReasons :
      List Bridge.EmpiricalCalibrationBlockedReason

    requiredReceiptShape :
      List String

    authorityBoundary :
      String

    nonPromotionBoundary :
      List String

    authorityTokenImpossibleHere :
      Bridge.EmpiricalCalibrationAuthorityToken →
      Bridge.EmpiricalCalibrationAuthorityImpossibleHere

    receiptImpossibleHere :
      CurrentOptionAExternalReceipt →
      Bridge.EmpiricalCalibrationAuthorityImpossibleHere

canonicalEmpiricalCalibrationBridgeObservableIntakeCurrentStatus :
  EmpiricalCalibrationBridgeObservableIntakeCurrentStatus
canonicalEmpiricalCalibrationBridgeObservableIntakeCurrentStatus =
  record
    { bridgeDiagnostic =
        Bridge.currentEmpiricalCalibrationBridgeObservableDiagnostic
    ; surface =
        currentOptionASurface
    ; measurementAvailability =
        Bridge.EmpiricalCalibrationBridgeObservableCurrentDiagnostic.measurementAvailability
          Bridge.currentEmpiricalCalibrationBridgeObservableDiagnostic
    ; currentDiagnosticStillNoInRepoMeasuredValue =
        refl
    ; blockedFields =
        canonicalEmpiricalCalibrationBridgeObservableIntakeBlockedFields
    ; bridgeBlockedReasons =
        Bridge.EmpiricalCalibrationBridgeObservableCurrentDiagnostic.blockedReasons
          Bridge.currentEmpiricalCalibrationBridgeObservableDiagnostic
    ; requiredReceiptShape =
        "external measuredValue in the surface simple-observable carrier"
        ∷ "external measurementWitness inhabiting surface.measurementWitnessRequirement"
        ∷ "externalAuthorityWitness inhabiting surface.externalAuthorityRequirement"
        ∷ "constructorless EmpiricalCalibrationAuthorityToken supplied externally"
        ∷ "calibratedState plus observableMatchesMeasuredValue proof"
        ∷ []
    ; authorityBoundary =
        "EmpiricalCalibrationAuthorityToken has no constructor in Option A or this intake module"
    ; nonPromotionBoundary =
        "This module only names the next admissible external intake receipt"
        ∷ "It does not provide the measured value missing from the current diagnostic"
        ∷ "It does not construct EmpiricalCalibrationAuthorityToken"
        ∷ "It does not claim W3 or W5 empirical adequacy from the local Nat observable"
        ∷ []
    ; authorityTokenImpossibleHere =
        Bridge.empiricalCalibrationAuthorityImpossibleHere
    ; receiptImpossibleHere =
        externalReceiptImpossibleHere
    }
