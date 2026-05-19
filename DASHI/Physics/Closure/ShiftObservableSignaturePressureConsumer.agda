module DASHI.Physics.Closure.ShiftObservableSignaturePressureConsumer where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.AlternativeCarrierSignatureStress as ACSS
open import DASHI.Physics.Closure.ObservableSignaturePressureTest as OSPT
open import DASHI.Physics.Closure.ObservableTransportGaugeEntry as OTGE
open import DASHI.Physics.Closure.ReceiptFromObservableSignature as RFOS
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.Closure.ShiftObservableSignatureReceiptInstance as SRI

------------------------------------------------------------------------
-- Repo-facing consumer for the held/control observable-signature pressure
-- report.
--
-- This is intentionally a packaging surface only. It consumes the existing
-- report produced by the live shift receipt lane and re-exposes the statuses
-- that downstream surfaces may cite without reopening the local receipt
-- instance directly.

record ShiftObservableSignaturePressureConsumer : Setω where
  field
    heldPressureReport :
      RFOS.ObservableSignaturePressureReport
        SRI.shiftExecutionContract
        SPTI.shiftObservableSignaturePressureTest
        SPTI.shiftHeldExitPoint

    heldObservableStatus :
      OTGE.GaugeEntryStatus

    heldSignatureStatus :
      ACSS.SignatureStressStatus

    heldPressureStatus :
      OSPT.PhysicsPressureStatus

shiftObservableSignaturePressureConsumer :
  ShiftObservableSignaturePressureConsumer
shiftObservableSignaturePressureConsumer =
  record
    { heldPressureReport = SRI.shiftHeldPressureReport
    ; heldObservableStatus =
        RFOS.ObservableSignaturePressureReport.observableStatus
          SRI.shiftHeldPressureReport
    ; heldSignatureStatus =
        RFOS.ObservableSignaturePressureReport.signatureStatus
          SRI.shiftHeldPressureReport
    ; heldPressureStatus =
        RFOS.ObservableSignaturePressureReport.pressureStatus
          SRI.shiftHeldPressureReport
    }
