module DASHI.Physics.Closure.HEPDataResidualProviderReceiptRequestPack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataDefectProjectionDiagnostic as Defect
import DASHI.Physics.Closure.HEPDataProviderReceiptRequestPack as Provider
import DASHI.Physics.Closure.HEPDataResidualBridgeWorkerQueue as Queue
import DASHI.Physics.Closure.HEPDataResidualObservableClassRequest as Class
import DASHI.Physics.Closure.HEPDataResidualSourceCandidateDiagnostic as Source

------------------------------------------------------------------------
-- HEPData residual provider receipt request pack.
--
-- This module consolidates the HEP-R residual retargeting artifacts into a
-- provider-facing request surface.  It names the exact missing payload fields
-- and first-missing receipt policy only.  It constructs no selected HEPData
-- observable, baseline model, checksum-bound selection receipt, calibration
-- receipt, defect projection receipt, comparison law, accepted authority
-- route, or W3/W4/W5/W8 promotion.

data HEPDataResidualProviderReceiptRequestPackStatus : Set where
  blockedAwaitingResidualProviderReceiptChain :
    HEPDataResidualProviderReceiptRequestPackStatus

data HEPDataResidualProviderRequiredReceipt : Set where
  residualObservableClassReceipt :
    HEPDataResidualProviderRequiredReceipt
  exactSelectedResidualObservableReceipt :
    HEPDataResidualProviderRequiredReceipt
  checksumBoundSelectionReceipt :
    HEPDataResidualProviderRequiredReceipt
  baselineOrInvarianceModelReceipt :
    HEPDataResidualProviderRequiredReceipt
  residualDefinitionReceipt :
    HEPDataResidualProviderRequiredReceipt
  nonCollapseWitnessReceipt :
    HEPDataResidualProviderRequiredReceipt
  calibrationCovarianceReceipt :
    HEPDataResidualProviderRequiredReceipt
  theoremSideProjectionReceipt :
    HEPDataResidualProviderRequiredReceipt
  defectProjectionReceipt :
    HEPDataResidualProviderRequiredReceipt
  residualComparisonLawReceipt :
    HEPDataResidualProviderRequiredReceipt
  acceptedAuthorityRouteReceipt :
    HEPDataResidualProviderRequiredReceipt

canonicalHEPDataResidualProviderRequiredReceipts :
  List HEPDataResidualProviderRequiredReceipt
canonicalHEPDataResidualProviderRequiredReceipts =
  residualObservableClassReceipt
  ∷ exactSelectedResidualObservableReceipt
  ∷ checksumBoundSelectionReceipt
  ∷ baselineOrInvarianceModelReceipt
  ∷ residualDefinitionReceipt
  ∷ nonCollapseWitnessReceipt
  ∷ calibrationCovarianceReceipt
  ∷ theoremSideProjectionReceipt
  ∷ defectProjectionReceipt
  ∷ residualComparisonLawReceipt
  ∷ acceptedAuthorityRouteReceipt
  ∷ []

data HEPDataResidualProviderFirstMissingReceipt : Set where
  firstMissingResidualObservableClass :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingExactSelectedResidualObservable :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingChecksumBoundSelection :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingBaselineOrInvarianceModel :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingResidualDefinition :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingNonCollapseWitness :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingCalibrationCovariance :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingTheoremSideProjection :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingDefectProjection :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingResidualComparisonLaw :
    HEPDataResidualProviderFirstMissingReceipt
  firstMissingAcceptedAuthorityRoute :
    HEPDataResidualProviderFirstMissingReceipt

canonicalHEPDataResidualProviderFirstMissingPolicy :
  List HEPDataResidualProviderFirstMissingReceipt
canonicalHEPDataResidualProviderFirstMissingPolicy =
  firstMissingResidualObservableClass
  ∷ firstMissingExactSelectedResidualObservable
  ∷ firstMissingChecksumBoundSelection
  ∷ firstMissingBaselineOrInvarianceModel
  ∷ firstMissingResidualDefinition
  ∷ firstMissingNonCollapseWitness
  ∷ firstMissingCalibrationCovariance
  ∷ firstMissingTheoremSideProjection
  ∷ firstMissingDefectProjection
  ∷ firstMissingResidualComparisonLaw
  ∷ firstMissingAcceptedAuthorityRoute
  ∷ []

record HEPDataResidualProviderReceiptPolicy : Set where
  field
    firstMissingPolicy :
      List HEPDataResidualProviderFirstMissingReceipt

    firstMissingPolicyIsCanonical :
      firstMissingPolicy
      ≡
      canonicalHEPDataResidualProviderFirstMissingPolicy

    providerMustReturnFirstMissingOnly :
      String

    impossibleLocalPromotionBoundary :
      List String

canonicalHEPDataResidualProviderReceiptPolicy :
  HEPDataResidualProviderReceiptPolicy
canonicalHEPDataResidualProviderReceiptPolicy =
  record
    { firstMissingPolicy =
        canonicalHEPDataResidualProviderFirstMissingPolicy
    ; firstMissingPolicyIsCanonical =
        refl
    ; providerMustReturnFirstMissingOnly =
        "If the full residual provider chain is unavailable, return the earliest missing typed receipt in the canonical residual policy order"
    ; impossibleLocalPromotionBoundary =
        "Local residual source candidates do not satisfy any provider receipt"
        ∷ "A residual observable class request is not a selected observable receipt"
        ∷ "A defect projection diagnostic is not a defect projection receipt"
        ∷ "The broad HEPData provider pack remains blocked until all residual-specific receipts and authority route receipts are supplied"
        ∷ []
    }

record HEPDataResidualProviderPayloadRequest : Setω where
  field
    residualObservableClassDiagnostic :
      Class.HEPDataResidualObservableClassRequestDiagnostic

    defectProjectionDiagnostic :
      Defect.HEPDataDefectProjectionDiagnostic

    residualSourceCandidateDiagnostic :
      Source.HEPDataResidualSourceCandidateDiagnostic

    exactReceiptNames :
      List String

    exactRequiredPayloadFields :
      List String

    firstMissingReceiptPolicy :
      HEPDataResidualProviderReceiptPolicy

    residualSourceMissingFields :
      List Source.MissingResidualReceiptField

    residualSourceMissingFieldsAreCanonical :
      residualSourceMissingFields
      ≡
      Source.canonicalMissingResidualReceiptFields

    providerInstructions :
      List String

    nonPromotionBoundary :
      List String

    strictBlockerImpact :
      List String

canonicalHEPDataResidualProviderPayloadRequest :
  HEPDataResidualProviderPayloadRequest
canonicalHEPDataResidualProviderPayloadRequest =
  record
    { residualObservableClassDiagnostic =
        Class.canonicalHEPDataResidualObservableClassRequestDiagnostic
    ; defectProjectionDiagnostic =
        Defect.canonicalHEPDataDefectProjectionDiagnostic
    ; residualSourceCandidateDiagnostic =
        Source.canonicalHEPDataResidualSourceCandidateDiagnostic
    ; exactReceiptNames =
        "DASHI.Physics.Closure.HEPDataResidualObservableClassRequest.HEPDataResidualObservableClassRequestSurface"
        ∷ "DASHI.Physics.Closure.HEPDataObservableSchema.HEPDataObservable"
        ∷ "DASHI.Physics.Closure.HEPDataObservableSelectionDiagnostic.HEPDataObservableSelectionReceipt"
        ∷ "external residual baseline or invariance model receipt"
        ∷ "external residual definition receipt"
        ∷ "DASHI.Physics.Closure.HEPDataNonCollapseObservableObligation.HEPDataExternalNonCollapseWitnessReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataExternalResidualWitnessPayload.HEPDataExternalResidualWitnessPayload"
        ∷ "DASHI.Physics.Closure.HEPDataUnitCalibrationRequirementDiagnostic.HEPDataUnitCalibrationRequirementReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection.TheoremSideMeasurementSurfaceProjectionReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataDefectProjectionDiagnostic.HEPDataResidualProfileProjectionContract"
        ∷ "DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic.HEPDataComparisonLawReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic.HEPDataAcceptedDatasetAuthorityRoute"
        ∷ []
    ; exactRequiredPayloadFields =
        "residualObservableKind : residualAfterFit | symmetryBreakingDeviation | fluctuationProfile | anomalyScore | defectProfile"
        ∷ "exactSelectedResidualObservable : record/table/column/row/bin selection for the residual/deviation profile"
        ∷ "checksumBoundSelection : HEPData record identity, table identity, column identity, row/bin identity, source checksum, and cached artifact checksum"
        ∷ "baselineOrInvarianceModel : named fit, null model, symmetry, invariance, or defect-free reference used before residualization"
        ∷ "residualDefinition : observed-minus-baseline, normalized pull, covariance-whitened residual, anomaly score, or declared defect-profile law"
        ∷ "nonCollapseWitnessReceipt : two selected observations or bins with distinct residual profiles and preserved defect discriminator"
        ∷ "calibrationCovarianceReceipt : unit calibration, covariance source, rank/conditioning behavior, whitening/regularization, and dropped-uncertainty prohibition"
        ∷ "theoremSideProjectionReceipt : MeasurementSurface projection receipt satisfying the theorem-side delta/coarse_head and metric propagation requirements"
        ∷ "defectProjectionReceipt : residual-to-DASHI defect profile contract preserving nonconstant discriminator, severity mapping, covariance propagation, and comparison target"
        ∷ "residualComparisonLawReceipt : comparison law over residual/deviation profiles matching the schema comparisonLawTarget"
        ∷ "acceptedAuthorityRouteReceipt : HEPData-to-ITIR adapter receipt plus accepted dataset authority token and route"
        ∷ []
    ; firstMissingReceiptPolicy =
        canonicalHEPDataResidualProviderReceiptPolicy
    ; residualSourceMissingFields =
        Source.canonicalMissingResidualReceiptFields
    ; residualSourceMissingFieldsAreCanonical =
        refl
    ; providerInstructions =
        "Supply the full residual-specific provider receipt chain; do not answer with raw saturated values or local artifact paths"
        ∷ "Return the first missing typed receipt according to canonicalHEPDataResidualProviderFirstMissingPolicy when the full chain cannot be supplied"
        ∷ "Residual class, selected observable, checksum-bound selection, baseline, residual definition, non-collapse witness, calibration/covariance, projection, defect projection, comparison, and authority route must be mutually bound"
        ∷ "No provider response may promote W3/W4/W5/W8 unless later external promotion receipts are independently supplied"
        ∷ []
    ; nonPromotionBoundary =
        "This residual provider request pack is constructorless with respect to provider receipts"
        ∷ "It constructs no selected HEPData observable, no baseline model, no checksum-bound selection, no non-collapse witness receipt, no external residual witness payload, no calibration/covariance receipt, no defect projection receipt, no comparison law, and no accepted authority route"
        ∷ "It only consolidates HEP-R1, HEP-R2, HEP-R3, the residual queue, and the broad provider request pack into a residual-specific handoff"
        ∷ []
    ; strictBlockerImpact =
        "Residual HEPData empirical compatibility remains blocked until an external provider supplies the residual receipt chain"
        ∷ "The first admissible provider diagnostic is the earliest missing receipt named by the residual first-missing policy"
        ∷ "Local candidate artifacts remain evidence pointers only and cannot discharge provider, calibration, projection, comparison, or authority receipts"
        ∷ []
    }

record HEPDataResidualProviderReceiptRequestPack : Setω where
  field
    residualBridgeWorkerQueue :
      Queue.HEPDataResidualBridgeWorkerQueue

    broadProviderReceiptRequestPack :
      Provider.HEPDataProviderReceiptRequestPack

    providerPayloadRequest :
      HEPDataResidualProviderPayloadRequest

    currentStatus :
      HEPDataResidualProviderReceiptRequestPackStatus

    requiredReceipts :
      List HEPDataResidualProviderRequiredReceipt

    requiredReceiptsAreCanonical :
      requiredReceipts
      ≡
      canonicalHEPDataResidualProviderRequiredReceipts

    firstMissingPolicy :
      List HEPDataResidualProviderFirstMissingReceipt

    firstMissingPolicyIsCanonical :
      firstMissingPolicy
      ≡
      canonicalHEPDataResidualProviderFirstMissingPolicy

    consolidatedRequestBoundary :
      List String

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

canonicalHEPDataResidualProviderReceiptRequestPack :
  HEPDataResidualProviderReceiptRequestPack
canonicalHEPDataResidualProviderReceiptRequestPack =
  record
    { residualBridgeWorkerQueue =
        Queue.canonicalHEPDataResidualBridgeWorkerQueue
    ; broadProviderReceiptRequestPack =
        Provider.canonicalHEPDataProviderReceiptRequestPack
    ; providerPayloadRequest =
        canonicalHEPDataResidualProviderPayloadRequest
    ; currentStatus =
        blockedAwaitingResidualProviderReceiptChain
    ; requiredReceipts =
        canonicalHEPDataResidualProviderRequiredReceipts
    ; requiredReceiptsAreCanonical =
        refl
    ; firstMissingPolicy =
        canonicalHEPDataResidualProviderFirstMissingPolicy
    ; firstMissingPolicyIsCanonical =
        refl
    ; consolidatedRequestBoundary =
        "Residual-specific provider pack consolidates HEP-R queue, HEP-R1 class request, HEP-R2 defect projection diagnostic, HEP-R3 source candidates, and the broad HEPData provider pack"
        ∷ "It narrows the next provider answer to residual/deviation receipt payloads and first-missing typed diagnostics"
        ∷ "It does not modify worker coordination diagrams; workers report node and edge deltas to W0"
        ∷ []
    ; coordinationMapNodeText =
        "rectangle \"HEP-R4\\nresidual provider receipt request pack\\nfirst-missing residual receipt policy\\nconsolidates HEP-R1/R2/R3\\nnon-promoting\" as HEPDATA_HEPR4 #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_RESIDUAL_QUEUE --> HEPDATA_HEPR4 : residual bridge queue consolidated\nHEPDATA_PROVIDER --> HEPDATA_HEPR4 : broad provider chain narrowed to residual receipts\nHEPDATA_HEPR1 --> HEPDATA_HEPR4 : residual observable class fields required\nHEPDATA_HEPR2 --> HEPDATA_HEPR4 : defect projection receipt required\nHEPDATA_HEPR3 --> HEPDATA_HEPR4 : candidate artifacts remain first-missing diagnostics\nHEPDATA_HEPR4 --> Plateau : blocked until exact selected residual observable + baseline + checksum-bound selection + calibration/covariance + defect projection + comparison law + accepted route\nHEPDATA_HEPR4 --> W3 : no accepted-authority promotion\nHEPDATA_HEPR4 --> W4 : no calibration promotion\nHEPDATA_HEPR4 --> W5 : no physical closure promotion\nHEPDATA_HEPR4 --> W8 : no origin receipt promotion"
    }
