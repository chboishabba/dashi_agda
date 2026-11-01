module DASHI.Physics.Closure.HEPDataResidualObservableClassRequest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection as Projection
import DASHI.Physics.Closure.HEPDataObservableSchema as Schema
import DASHI.Physics.Closure.HEPDataObservableSelectionDiagnostic as Selection
import DASHI.Physics.Closure.HEPDataProviderReceiptRequestPack as Provider
import DASHI.Physics.Closure.HEPDataUnitCalibrationRequirementDiagnostic as Calibration

------------------------------------------------------------------------
-- HEPData residual/deviation observable class request.
--
-- Saturated internal observables can collapse to constants, so a provider
-- request must target non-collapsing residual/deviation/defect profiles rather
-- than naive raw values.  This module is only a typed request and diagnostic
-- surface: it constructs no HEPDataObservable, no provider receipt, no
-- calibration, no comparison law, and no authority or promotion token.

data HEPDataResidualObservableKind : Set where
  residualAfterFit :
    HEPDataResidualObservableKind
  symmetryBreakingDeviation :
    HEPDataResidualObservableKind
  fluctuationProfile :
    HEPDataResidualObservableKind
  anomalyScore :
    HEPDataResidualObservableKind
  defectProfile :
    HEPDataResidualObservableKind

canonicalHEPDataResidualObservableKinds :
  List HEPDataResidualObservableKind
canonicalHEPDataResidualObservableKinds =
  residualAfterFit
  ∷ symmetryBreakingDeviation
  ∷ fluctuationProfile
  ∷ anomalyScore
  ∷ defectProfile
  ∷ []

data HEPDataResidualClassRequiredField : Set where
  requiredResidualKind :
    HEPDataResidualClassRequiredField
  requiredBaselineOrInvarianceModel :
    HEPDataResidualClassRequiredField
  requiredResidualDefinition :
    HEPDataResidualClassRequiredField
  requiredUncertaintyOrCovarianceHandling :
    HEPDataResidualClassRequiredField
  requiredSelectionReceiptDependency :
    HEPDataResidualClassRequiredField
  requiredCalibrationDependency :
    HEPDataResidualClassRequiredField
  requiredProjectionTarget :
    HEPDataResidualClassRequiredField
  requiredComparisonLawTarget :
    HEPDataResidualClassRequiredField
  requiredNonCollapseJustification :
    HEPDataResidualClassRequiredField

canonicalHEPDataResidualClassRequiredFields :
  List HEPDataResidualClassRequiredField
canonicalHEPDataResidualClassRequiredFields =
  requiredResidualKind
  ∷ requiredBaselineOrInvarianceModel
  ∷ requiredResidualDefinition
  ∷ requiredUncertaintyOrCovarianceHandling
  ∷ requiredSelectionReceiptDependency
  ∷ requiredCalibrationDependency
  ∷ requiredProjectionTarget
  ∷ requiredComparisonLawTarget
  ∷ requiredNonCollapseJustification
  ∷ []

data HEPDataResidualClassRequestStatus : Set where
  blockedAwaitingResidualDeviationClassProviderReceipts :
    HEPDataResidualClassRequestStatus

data HEPDataResidualClassPromotionBoundary : Set where
  noRawValuePromotion :
    HEPDataResidualClassPromotionBoundary
  noProviderReceiptConstructed :
    HEPDataResidualClassPromotionBoundary
  noAuthorityTokenConstructed :
    HEPDataResidualClassPromotionBoundary
  noCalibrationConstructed :
    HEPDataResidualClassPromotionBoundary
  noComparisonLawConstructed :
    HEPDataResidualClassPromotionBoundary
  noW3W4W5W8ClosureClaim :
    HEPDataResidualClassPromotionBoundary

canonicalHEPDataResidualClassPromotionBoundary :
  List HEPDataResidualClassPromotionBoundary
canonicalHEPDataResidualClassPromotionBoundary =
  noRawValuePromotion
  ∷ noProviderReceiptConstructed
  ∷ noAuthorityTokenConstructed
  ∷ noCalibrationConstructed
  ∷ noComparisonLawConstructed
  ∷ noW3W4W5W8ClosureClaim
  ∷ []

record HEPDataResidualObservableClassRequestSurface : Set where
  field
    residualObservableKind :
      HEPDataResidualObservableKind

    baselineOrInvarianceModel :
      String

    residualDefinition :
      String

    uncertaintyOrCovarianceHandling :
      String

    selectionReceiptDependency :
      String

    calibrationDependency :
      String

    projectionTarget :
      String

    comparisonLawTarget :
      String

    nonCollapseJustification :
      String

record HEPDataResidualObservableClassRequestDiagnostic : Setω where
  field
    schemaRequestDiagnostic :
      Schema.HEPDataObservableSchemaRequestDiagnostic

    observableSelectionDiagnostic :
      Selection.HEPDataObservableSelectionDiagnostic

    unitCalibrationDiagnostic :
      Calibration.HEPDataUnitCalibrationRequirementDiagnostic

    projectionRejection :
      Projection.HEPDataMeasurementSurfaceProjectionRejection

    providerReceiptRequestPack :
      Provider.HEPDataProviderReceiptRequestPack

    currentStatus :
      HEPDataResidualClassRequestStatus

    allowedResidualKinds :
      List HEPDataResidualObservableKind

    allowedResidualKindsAreCanonical :
      allowedResidualKinds ≡ canonicalHEPDataResidualObservableKinds

    requiredFields :
      List HEPDataResidualClassRequiredField

    requiredFieldsAreCanonical :
      requiredFields ≡ canonicalHEPDataResidualClassRequiredFields

    rawConstantProjectionsInsufficient :
      Bool

    residualDeviationClassRequired :
      Bool

    requiredProviderPayloadFields :
      List String

    canonicalDiagnostic :
      String

    providerInstructions :
      List String

    nonPromotionBoundary :
      List HEPDataResidualClassPromotionBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ canonicalHEPDataResidualClassPromotionBoundary

    exactMissingExternalSurfaces :
      List String

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

canonicalHEPDataResidualObservableClassRequestDiagnostic :
  HEPDataResidualObservableClassRequestDiagnostic
canonicalHEPDataResidualObservableClassRequestDiagnostic =
  record
    { schemaRequestDiagnostic =
        Schema.canonicalHEPDataObservableSchemaRequestDiagnostic
    ; observableSelectionDiagnostic =
        Selection.canonicalHEPDataObservableSelectionDiagnostic
    ; unitCalibrationDiagnostic =
        Calibration.canonicalHEPDataUnitCalibrationRequirementDiagnostic
    ; projectionRejection =
        Projection.canonicalHEPDataMeasurementSurfaceProjectionRejection
    ; providerReceiptRequestPack =
        Provider.canonicalHEPDataProviderReceiptRequestPack
    ; currentStatus =
        blockedAwaitingResidualDeviationClassProviderReceipts
    ; allowedResidualKinds =
        canonicalHEPDataResidualObservableKinds
    ; allowedResidualKindsAreCanonical =
        refl
    ; requiredFields =
        canonicalHEPDataResidualClassRequiredFields
    ; requiredFieldsAreCanonical =
        refl
    ; rawConstantProjectionsInsufficient =
        true
    ; residualDeviationClassRequired =
        true
    ; requiredProviderPayloadFields =
        "residualObservableKind : residualAfterFit | symmetryBreakingDeviation | fluctuationProfile | anomalyScore | defectProfile"
        ∷ "baselineOrInvarianceModel : named fit, null model, symmetry, invariance, or defect-free reference"
        ∷ "residualDefinition : observed-minus-baseline, normalized pull, covariance-whitened residual, anomaly score, or declared defect profile law"
        ∷ "uncertaintyOrCovarianceHandling : covariance source, rank/conditioning behavior, whitening/regularization, and dropped-uncertainty prohibition"
        ∷ "selectionReceiptDependency : concrete HEPDataObservableSelectionReceipt for record/table/column/row/checksum binding"
        ∷ "calibrationDependency : HEPDataUnitCalibrationRequirementReceipt or typed first-missing calibration diagnostic"
        ∷ "projectionTarget : theorem-side MeasurementSurface/DashiState/delta target with projection contract name"
        ∷ "comparisonLawTarget : comparison law target for residual/deviation profile, not raw value equality"
        ∷ "nonCollapseJustification : explanation why this profile cannot collapse to the saturated internal constant projection"
        ∷ []
    ; canonicalDiagnostic =
        "raw constant projections are insufficient; HEPData provider receipts must target a residual/deviation/anomaly/symmetry-breaking/defect observable class before any receipt can promote"
    ; providerInstructions =
        "Do not answer this request with only a raw observed value column"
        ∷ "Supply the baseline or invariance model used to compute the residual/deviation profile"
        ∷ "Supply the residual definition and uncertainty/covariance propagation behavior"
        ∷ "Bind the class request to HEP-B selection, HEP-C calibration, HEP-D projection target, and a residual-aware comparison law"
        ∷ "If any dependency is missing, return the first missing typed receipt or diagnostic instead of a fabricated observable"
        ∷ []
    ; nonPromotionBoundary =
        canonicalHEPDataResidualClassPromotionBoundary
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; exactMissingExternalSurfaces =
        "selected HEPData table/column/row and checksum-bound selection receipt"
        ∷ "external data payload and accepted HEPData provider receipt chain"
        ∷ "baseline/invariance model receipt"
        ∷ "unit calibration and covariance/uncertainty handling receipt"
        ∷ "MeasurementSurface projection target receipt"
        ∷ "residual/deviation comparison law receipt"
        ∷ "accepted authority token and route"
        ∷ []
    ; coordinationMapNodeText =
        "rectangle \"HEP-R1\\nresidual/deviation observable class\\nrequest surface\\nraw constants insufficient\\nnon-promoting\" as HEPDATA_HEPR1 #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_PROVIDER --> HEPDATA_HEPR1 : retarget provider request from raw values to residual/deviation class\nHEPDATA_HEPB --> HEPDATA_HEPR1 : selection receipt dependency\nHEPDATA_HEPC --> HEPDATA_HEPR1 : calibration/covariance dependency\nHEPDATA_HEPD --> HEPDATA_HEPR1 : projection target dependency\nHEPDATA_HEPR1 --> Plateau : provider receipts cannot promote until residual/deviation class receipts close\nHEPDATA_HEPR1 --> W3 : no accepted-authority promotion\nHEPDATA_HEPR1 --> W4 : no calibration promotion\nHEPDATA_HEPR1 --> W5 : no physical closure promotion\nHEPDATA_HEPR1 --> W8 : no origin receipt promotion"
    }

canonicalHEPDataResidualObservableClassRequestStatus :
  HEPDataResidualClassRequestStatus
canonicalHEPDataResidualObservableClassRequestStatus =
  blockedAwaitingResidualDeviationClassProviderReceipts
