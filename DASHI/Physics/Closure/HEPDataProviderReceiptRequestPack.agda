module DASHI.Physics.Closure.HEPDataProviderReceiptRequestPack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataBridgeWorkerQueue as Queue
import DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic as HEPE
import DASHI.Physics.Closure.HEPDataITIRAuthorityAdapterDiagnostic as HEPF
import DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection as HEPD
import DASHI.Physics.Closure.HEPDataObservableSchema as HEPA
import DASHI.Physics.Closure.HEPDataObservableSelectionDiagnostic as HEPB
import DASHI.Physics.Closure.HEPDataUnitCalibrationRequirementDiagnostic as HEPC

------------------------------------------------------------------------
-- HEPData provider receipt request pack.
--
-- This is the consolidated provider-facing handoff for the HEP-A..F bridge
-- diagnostics.  It names the exact receipt chain required to turn local
-- HEPData source candidates into an accepted empirical bridge.  It constructs
-- no HEPDataObservable, no projection, no comparison law, no authority token,
-- and no W3/W8 promotion.

data HEPDataProviderReceiptRequestPackStatus : Set where
  blockedAwaitingHEPDataProviderReceiptChain :
    HEPDataProviderReceiptRequestPackStatus

data HEPDataProviderRequiredReceipt : Set where
  hepDataObservableSchemaPayload :
    HEPDataProviderRequiredReceipt
  hepDataResidualObservableClassReceipt :
    HEPDataProviderRequiredReceipt
  hepDataObservableSelectionReceipt :
    HEPDataProviderRequiredReceipt
  hepDataUnitCalibrationRequirementReceipt :
    HEPDataProviderRequiredReceipt
  theoremSideMeasurementSurfaceProjectionReceipt :
    HEPDataProviderRequiredReceipt
  hepDataDefectProjectionReceipt :
    HEPDataProviderRequiredReceipt
  hepDataITIRAcceptedAuthorityAdapterReceipt :
    HEPDataProviderRequiredReceipt
  hepDataComparisonLawReceipt :
    HEPDataProviderRequiredReceipt
  hepDataAcceptedDatasetAuthorityToken :
    HEPDataProviderRequiredReceipt
  hepDataAcceptedDatasetAuthorityRoute :
    HEPDataProviderRequiredReceipt

canonicalHEPDataProviderRequiredReceipts :
  List HEPDataProviderRequiredReceipt
canonicalHEPDataProviderRequiredReceipts =
  hepDataObservableSchemaPayload
  ∷ hepDataResidualObservableClassReceipt
  ∷ hepDataObservableSelectionReceipt
  ∷ hepDataUnitCalibrationRequirementReceipt
  ∷ theoremSideMeasurementSurfaceProjectionReceipt
  ∷ hepDataDefectProjectionReceipt
  ∷ hepDataITIRAcceptedAuthorityAdapterReceipt
  ∷ hepDataComparisonLawReceipt
  ∷ hepDataAcceptedDatasetAuthorityToken
  ∷ hepDataAcceptedDatasetAuthorityRoute
  ∷ []

record HEPDataProviderReceiptRequestPack : Setω where
  field
    bridgeWorkerQueue :
      Queue.HEPDataBridgeWorkerQueue

    observableSchemaRequest :
      HEPA.HEPDataObservableSchemaRequestDiagnostic

    observableSelectionDiagnostic :
      HEPB.HEPDataObservableSelectionDiagnostic

    unitCalibrationDiagnostic :
      HEPC.HEPDataUnitCalibrationRequirementDiagnostic

    projectionRejection :
      HEPD.HEPDataMeasurementSurfaceProjectionRejection

    comparisonAuthorityRouteDiagnostic :
      HEPE.HEPDataComparisonAuthorityRouteDiagnostic

    itirAuthorityAdapterDiagnostic :
      HEPF.HEPDataITIRAuthorityAdapterDiagnostic

    currentStatus :
      HEPDataProviderReceiptRequestPackStatus

    requiredReceipts :
      List HEPDataProviderRequiredReceipt

    requiredReceiptsAreCanonical :
      requiredReceipts ≡ canonicalHEPDataProviderRequiredReceipts

    exactReceiptNames :
      List String

    exactProviderPayloadFields :
      List String

    providerInstructions :
      List String

    nonPromotionBoundary :
      List String

    strictBlockerImpact :
      List String

canonicalHEPDataProviderReceiptRequestPack :
  HEPDataProviderReceiptRequestPack
canonicalHEPDataProviderReceiptRequestPack =
  record
    { bridgeWorkerQueue =
        Queue.canonicalHEPDataBridgeWorkerQueue
    ; observableSchemaRequest =
        HEPA.canonicalHEPDataObservableSchemaRequestDiagnostic
    ; observableSelectionDiagnostic =
        HEPB.canonicalHEPDataObservableSelectionDiagnostic
    ; unitCalibrationDiagnostic =
        HEPC.canonicalHEPDataUnitCalibrationRequirementDiagnostic
    ; projectionRejection =
        HEPD.canonicalHEPDataMeasurementSurfaceProjectionRejection
    ; comparisonAuthorityRouteDiagnostic =
        HEPE.canonicalHEPDataComparisonAuthorityRouteDiagnostic
    ; itirAuthorityAdapterDiagnostic =
        HEPF.canonicalHEPDataITIRAuthorityAdapterDiagnostic
    ; currentStatus =
        blockedAwaitingHEPDataProviderReceiptChain
    ; requiredReceipts =
        canonicalHEPDataProviderRequiredReceipts
    ; requiredReceiptsAreCanonical =
        refl
    ; exactReceiptNames =
        "DASHI.Physics.Closure.HEPDataObservableSchema.HEPDataObservable"
        ∷ "DASHI.Physics.Closure.HEPDataResidualObservableClassRequest.HEPDataResidualObservableClassRequestSurface"
        ∷ "DASHI.Physics.Closure.HEPDataObservableSelectionDiagnostic.HEPDataObservableSelectionReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataUnitCalibrationRequirementDiagnostic.HEPDataUnitCalibrationRequirementReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection.TheoremSideMeasurementSurfaceProjectionReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataDefectProjectionDiagnostic.HEPDataResidualProfileProjectionContract"
        ∷ "DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic.HEPDataITIRAcceptedAuthorityAdapterReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic.HEPDataComparisonLawReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic.HEPDataAcceptedDatasetAuthorityToken"
        ∷ "DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic.HEPDataAcceptedDatasetAuthorityRoute"
        ∷ []
    ; exactProviderPayloadFields =
        "record/table/citation/unit/binning/covariance/provenance/checksum HEPDataObservable payload"
        ∷ "residual/deviation/anomaly/symmetry-breaking/defect observable class with baseline, residual definition, covariance handling, and non-collapse justification"
        ∷ "checksum-bound named observable plus record/table/column/row selection receipt"
        ∷ "physical unit carrier, dimension carrier, calibration map, scale evidence, preservation or monotonicity law, validation authority"
        ∷ "theorem-side MeasurementSurface projection receipt satisfying delta/coarse_head and metric propagation requirements"
        ∷ "DASHI defect/residual projection receipt preserving nonconstant discriminator, severity/residual mapping, covariance propagation, and comparison-law target"
        ∷ "ITIR accepted-authority adapter receipt binding raw HEPData identity, cached checksum, local NPZ hash, source identity, projection boundary, and authority handoff"
        ∷ "comparison law receipt matching the schema comparisonLawTarget"
        ∷ "accepted dataset authority token and route tying all receipts together"
        ∷ []
    ; providerInstructions =
        "Supply the full HEPData receipt chain; do not treat source presence as authority"
        ∷ "Target residual/deviation/defect profiles rather than raw saturated values, unless a typed non-collapse proof is supplied"
        ∷ "If any receipt is unavailable, return a typed diagnostic identifying the first missing receipt in this chain"
        ∷ "Projection must satisfy the MeasurementSurface projection contract; rejected/degraded outcomes remain non-promoting"
        ∷ "Authority must pass through the HEPData-to-ITIR adapter route and then the accepted dataset authority route"
        ∷ []
    ; nonPromotionBoundary =
        "This request pack is a handoff surface only"
        ∷ "It constructs no HEPDataObservable, selection receipt, unit-calibration receipt, projection receipt, comparison law, authority adapter, authority token, or accepted route"
        ∷ "It does not promote W3 accepted empirical authority, W4 calibration, W5 physical closure, or W8 origin receipt"
        ∷ []
    ; strictBlockerImpact =
        "HEPData empirical compatibility remains blocked until the provider receipt chain is supplied"
        ∷ "Raw-value HEPData projection is no longer the intended default bridge; residual/deviation class receipts and defect projection receipts are now first-class requirements"
        ∷ "The local repo now has exact request surfaces rather than an unspecified empirical-source gap"
        ∷ "The next admissible move is a real provider receipt or a typed impossible-first-missing-receipt diagnostic"
        ∷ []
    }
