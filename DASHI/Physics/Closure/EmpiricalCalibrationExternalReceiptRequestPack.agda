module DASHI.Physics.Closure.EmpiricalCalibrationExternalReceiptRequestPack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservableSourceDiagnostic as A3
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnitsSourceDiagnostic as B3
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnitsIntake as BIntake
import DASHI.Physics.Closure.EmpiricalCalibrationBridgeToyFitRealDatasetRouteDiagnostic as C3

------------------------------------------------------------------------
-- Consolidated external receipt request pack.
--
-- This module packages the current A3/B3/C3 diagnostics into one request
-- surface for an external provider or next worker.  It names the missing
-- receipt fields and route receipts only; it constructs no empirical
-- authority token, no unit-calibration receipt, no real-dataset authority
-- receipt, and performs no origin or calibration promotion.

data ExternalReceiptRequestPackCurrentStatus : Set where
  blockedAwaitingA3B3C3ExternalReceipts :
    ExternalReceiptRequestPackCurrentStatus

record OptionAMeasuredObservableReceiptRequest : Setω where
  field
    sourceDiagnostic :
      A3.EmpiricalCalibrationBridgeObservableSourceDiagnostic

    exactReceiptName :
      String

    exactMissingReceiptFields :
      List String

    missingSourceFields :
      List A3.EmpiricalCalibrationBridgeObservableSourceMissingField

    missingSourceFieldsStillA3Canonical :
      missingSourceFields
      ≡
      A3.currentMissingSourceFields

    providerInstruction :
      List String

    nonPromotionBoundary :
      List String

    strictBlockerImpact :
      List String

canonicalOptionAMeasuredObservableReceiptRequest :
  OptionAMeasuredObservableReceiptRequest
canonicalOptionAMeasuredObservableReceiptRequest =
  record
    { sourceDiagnostic =
        A3.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; exactReceiptName =
        "DASHI.Physics.Closure.EmpiricalCalibrationBridgeObservableIntake.CurrentOptionAExternalReceipt"
    ; exactMissingReceiptFields =
        "measuredValue : surface simple-observable carrier"
        ∷ "measurementWitness : surface.measurementWitnessRequirement"
        ∷ "externalAuthorityWitness : surface.externalAuthorityRequirement"
        ∷ "authorityToken : EmpiricalCalibrationAuthorityToken"
        ∷ "calibratedState : surface.State"
        ∷ "observableMatchesMeasuredValue : observable calibratedState == measuredValue"
        ∷ []
    ; missingSourceFields =
        A3.EmpiricalCalibrationBridgeObservableSourceDiagnostic.missingSourceFields
          A3.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    ; missingSourceFieldsStillA3Canonical =
        refl
    ; providerInstruction =
        "External provider must supply the measured observable receipt, including measured value, witnesses, authority token, calibrated state, and equality proof"
        ∷ "The local pack only reports that the A3 source scan found all Option A receipt inputs missing"
        ∷ []
    ; nonPromotionBoundary =
        "This pack does not construct CurrentOptionAExternalReceipt"
        ∷ "This pack does not construct EmpiricalCalibrationAuthorityToken"
        ∷ "This pack does not promote W3 or W5 empirical adequacy from the local Nat observable"
        ∷ []
    ; strictBlockerImpact =
        A3.EmpiricalCalibrationBridgeObservableSourceDiagnostic.blockerImpact
          A3.currentEmpiricalCalibrationBridgeObservableSourceDiagnostic
    }

record OptionBUnitCalibrationReceiptRequest : Setω where
  field
    sourceDiagnostic :
      B3.EmpiricalCalibrationBridgeUnitsSourceDiagnostic

    exactReceiptName :
      String

    exactMissingReceiptFields :
      List String

    missingIntakeFields :
      List BIntake.UnitCalibrationIntakeMissingField

    missingIntakeFieldsStillB3Canonical :
      missingIntakeFields
      ≡
      BIntake.canonicalUnitCalibrationIntakeMissingFields

    providerInstruction :
      List String

    nonPromotionBoundary :
      List String

    strictBlockerImpact :
      String

canonicalOptionBUnitCalibrationReceiptRequest :
  OptionBUnitCalibrationReceiptRequest
canonicalOptionBUnitCalibrationReceiptRequest =
  record
    { sourceDiagnostic =
        B3.canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic
    ; exactReceiptName =
        "DASHI.Physics.Closure.EmpiricalCalibrationBridgeUnitsIntake.UnitCalibrationIntakeReceipt"
    ; exactMissingReceiptFields =
        "UnitCarrier"
        ∷ "DimensionCarrier"
        ∷ "dimensionOfUnit"
        ∷ "internalEnergyCarrier"
        ∷ "measuredQuantityCarrier"
        ∷ "internalEnergyUnit"
        ∷ "measuredQuantityUnit"
        ∷ "calibrationMap"
        ∷ "dimensionPreservation"
        ∷ "internalOrder"
        ∷ "measuredOrder"
        ∷ "monotonicity"
        ∷ "scaleCarrier"
        ∷ "calibrationTokenCarrier"
        ∷ "scaleEvidence"
        ∷ "externalAuthority"
        ∷ "externalValidation"
        ∷ "unit and dimension labels"
        ∷ "consumerWiringTargetLabel"
        ∷ []
    ; missingIntakeFields =
        B3.EmpiricalCalibrationBridgeUnitsSourceDiagnostic.intakeMissingFields
          B3.canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic
    ; missingIntakeFieldsStillB3Canonical =
        refl
    ; providerInstruction =
        "External provider must supply UnitCalibrationIntakeReceipt with the unit surface, unit assignments, calibration map, preservation proof, monotonicity proof, scale evidence, authority, and validation"
        ∷ "The local pack only reports that the B3 source scan found the Option B receipt inputs missing"
        ∷ []
    ; nonPromotionBoundary =
        B3.EmpiricalCalibrationBridgeUnitsSourceDiagnostic.noFabricationBoundary
          B3.canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic
    ; strictBlockerImpact =
        B3.EmpiricalCalibrationBridgeUnitsSourceDiagnostic.blockerImpact
          B3.canonicalEmpiricalCalibrationBridgeUnitsSourceDiagnostic
    }

record OptionCRealDatasetAuthorityReceiptRequest : Setω where
  field
    routeDiagnostic :
      C3.RealDatasetAuthorityCurrentRouteDiagnostic

    exactRouteReceiptNames :
      List String

    missingRouteReceipts :
      List C3.RealDatasetAuthorityRouteMissing

    missingRouteReceiptsStillC3Canonical :
      missingRouteReceipts
      ≡
      C3.canonicalRealDatasetAuthorityMissingRouteReceipts

    providerInstruction :
      List String

    nonPromotionBoundary :
      List String

    strictBlockerImpact :
      List String

canonicalOptionCRealDatasetAuthorityReceiptRequest :
  OptionCRealDatasetAuthorityReceiptRequest
canonicalOptionCRealDatasetAuthorityReceiptRequest =
  record
    { routeDiagnostic =
        C3.canonicalRealDatasetAuthorityCurrentRouteDiagnostic
    ; exactRouteReceiptNames =
        C3.RealDatasetAuthorityCurrentRouteDiagnostic.exactMissingW3ExternalReceiptName
          C3.canonicalRealDatasetAuthorityCurrentRouteDiagnostic
        ∷ C3.RealDatasetAuthorityCurrentRouteDiagnostic.exactMissingW3PositiveRouteName
          C3.canonicalRealDatasetAuthorityCurrentRouteDiagnostic
        ∷ C3.RealDatasetAuthorityCurrentRouteDiagnostic.exactMissingW8ExternalReceiptName
          C3.canonicalRealDatasetAuthorityCurrentRouteDiagnostic
        ∷ C3.RealDatasetAuthorityCurrentRouteDiagnostic.c2RequiredRouteName
          C3.canonicalRealDatasetAuthorityCurrentRouteDiagnostic
        ∷ []
    ; missingRouteReceipts =
        C3.RealDatasetAuthorityCurrentRouteDiagnostic.missingRouteReceipts
          C3.canonicalRealDatasetAuthorityCurrentRouteDiagnostic
    ; missingRouteReceiptsStillC3Canonical =
        refl
    ; providerInstruction =
        "External provider must supply the real-dataset authority route: W3 accepted-authority external receipt, W3 positive route, and W8 origin-promotion external receipt"
        ∷ "The local pack only reports that C3 still blocks real-dataset authority promotion"
        ∷ []
    ; nonPromotionBoundary =
        C3.RealDatasetAuthorityCurrentRouteDiagnostic.noPromotionBoundary
          C3.canonicalRealDatasetAuthorityCurrentRouteDiagnostic
    ; strictBlockerImpact =
        "Strict blocker remains: Option C toy-fit adequacy is finite-dataset only"
        ∷ "No W3 accepted-authority promotion or W8 origin-promotion receipt is available from the toy fit"
        ∷ "The next admissible move is an external real-dataset authority receipt route"
        ∷ []
    }

record EmpiricalCalibrationExternalReceiptRequestPack : Setω where
  field
    currentStatus :
      ExternalReceiptRequestPackCurrentStatus

    optionAMeasuredObservableRequest :
      OptionAMeasuredObservableReceiptRequest

    optionBUnitCalibrationRequest :
      OptionBUnitCalibrationReceiptRequest

    optionCRealDatasetAuthorityRequest :
      OptionCRealDatasetAuthorityReceiptRequest

    consolidatedRequestBoundary :
      List String

    consolidatedStrictBlockerImpact :
      List String

canonicalEmpiricalCalibrationExternalReceiptRequestPack :
  EmpiricalCalibrationExternalReceiptRequestPack
canonicalEmpiricalCalibrationExternalReceiptRequestPack =
  record
    { currentStatus =
        blockedAwaitingA3B3C3ExternalReceipts
    ; optionAMeasuredObservableRequest =
        canonicalOptionAMeasuredObservableReceiptRequest
    ; optionBUnitCalibrationRequest =
        canonicalOptionBUnitCalibrationReceiptRequest
    ; optionCRealDatasetAuthorityRequest =
        canonicalOptionCRealDatasetAuthorityReceiptRequest
    ; consolidatedRequestBoundary =
        "Request pack only aggregates A3/B3/C3 diagnostics and exact external receipt requirements"
        ∷ "It does not supply measured observables, unit calibration, validation, real dataset authority, origin receipts, or authority tokens"
        ∷ "It does not discharge Option A, Option B, Option C, W3, W4, W5, or W8 blockers"
        ∷ []
    ; consolidatedStrictBlockerImpact =
        "Option A remains blocked until CurrentOptionAExternalReceipt is externally supplied"
        ∷ "Option B remains blocked until UnitCalibrationIntakeReceipt is externally supplied"
        ∷ "Option C remains blocked until the W3/W8 real-dataset authority route receipts are externally supplied"
        ∷ []
    }
