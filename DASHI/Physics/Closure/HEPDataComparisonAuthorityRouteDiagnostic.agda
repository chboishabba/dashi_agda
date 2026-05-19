module DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataITIRAuthorityAdapterDiagnostic as Adapter
import DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection as Projection
import DASHI.Physics.Closure.HEPDataObservableSchema as HEP
import DASHI.Physics.Closure.HEPDataObservableSelectionDiagnostic as Selection
import DASHI.Physics.Closure.HEPDataUnitCalibrationRequirementDiagnostic as Calibration

------------------------------------------------------------------------
-- HEP-E: comparison law plus accepted dataset authority route diagnostic.
--
-- HEP-B/C/D/F narrow the source side to typed blockers.  This module records
-- the final current HEP-E boundary: a comparison law and accepted dataset
-- authority route are future receipt shapes only until selection,
-- calibration, projection, and authority-adapter receipts exist together.
-- It constructs no accepted authority token and performs no W3/W8 promotion.

data HEPDataAcceptedDatasetAuthorityToken : Set where

acceptedDatasetAuthorityTokenImpossibleHere :
  HEPDataAcceptedDatasetAuthorityToken →
  ⊥
acceptedDatasetAuthorityTokenImpossibleHere ()

record HEPDataComparisonLawReceipt
  (observable : HEP.HEPDataObservable)
  : Setω where
  field
    selectionReceipt :
      Selection.HEPDataObservableSelectionReceipt

    unitCalibrationReceipt :
      Calibration.HEPDataUnitCalibrationRequirementReceipt observable

    theoremSideProjectionReceipt :
      Projection.TheoremSideMeasurementSurfaceProjectionReceipt

    ObservableCarrier :
      Set

    TheoremCarrier :
      Set

    observableEmbedding :
      ObservableCarrier →
      TheoremCarrier

    theoremComparisonTarget :
      TheoremCarrier

    comparisonPredicate :
      TheoremCarrier →
      TheoremCarrier →
      Set

    comparisonLaw :
      (x : ObservableCarrier) →
      comparisonPredicate (observableEmbedding x) theoremComparisonTarget

    comparisonLawLabel :
      String

    comparisonLawMatchesSchemaTarget :
      comparisonLawLabel
      ≡
      HEP.HEPDataObservableSchemaSurface.comparisonLawTarget
        (HEP.HEPDataObservable.schema observable)

record HEPDataITIRAcceptedAuthorityAdapterReceipt : Setω where
  field
    rawHEPDataAuthorityIdentity :
      String

    cachedArtifactChecksum :
      HEP.HEPDataLocalChecksumOrHash

    localNPZHash :
      String

    sourceCitationTableIdentity :
      String

    derivedProjectionBoundary :
      String

    acceptedAuthorityHandoff :
      HEPDataAcceptedDatasetAuthorityToken

record HEPDataAcceptedDatasetAuthorityRoute
  (observable : HEP.HEPDataObservable)
  : Setω where
  field
    selectedObservableReceipt :
      Selection.HEPDataObservableSelectionReceipt

    unitCalibrationReceipt :
      Calibration.HEPDataUnitCalibrationRequirementReceipt observable

    theoremSideProjectionReceipt :
      Projection.TheoremSideMeasurementSurfaceProjectionReceipt

    comparisonLawReceipt :
      HEPDataComparisonLawReceipt observable

    itirAuthorityAdapterReceipt :
      HEPDataITIRAcceptedAuthorityAdapterReceipt

    acceptedDatasetAuthorityToken :
      HEPDataAcceptedDatasetAuthorityToken

    authorityTokenMatchesAdapterHandoff :
      acceptedDatasetAuthorityToken
      ≡
      HEPDataITIRAcceptedAuthorityAdapterReceipt.acceptedAuthorityHandoff
        itirAuthorityAdapterReceipt

comparisonLawReceiptImpossibleHere :
  {observable : HEP.HEPDataObservable} →
  HEPDataComparisonLawReceipt observable →
  ⊥
comparisonLawReceiptImpossibleHere receipt =
  Selection.selectionReceiptImpossibleHere
    (HEPDataComparisonLawReceipt.selectionReceipt receipt)

itirAuthorityAdapterReceiptImpossibleHere :
  HEPDataITIRAcceptedAuthorityAdapterReceipt →
  ⊥
itirAuthorityAdapterReceiptImpossibleHere receipt =
  acceptedDatasetAuthorityTokenImpossibleHere
    (HEPDataITIRAcceptedAuthorityAdapterReceipt.acceptedAuthorityHandoff receipt)

acceptedDatasetAuthorityRouteImpossibleHere :
  {observable : HEP.HEPDataObservable} →
  HEPDataAcceptedDatasetAuthorityRoute observable →
  ⊥
acceptedDatasetAuthorityRouteImpossibleHere route =
  acceptedDatasetAuthorityTokenImpossibleHere
    (HEPDataAcceptedDatasetAuthorityRoute.acceptedDatasetAuthorityToken route)

data HEPDataComparisonAuthorityRouteStatus : Set where
  blockedAwaitingSelectionCalibrationProjectionAuthorityAdapterReceipts :
    HEPDataComparisonAuthorityRouteStatus

data HEPDataComparisonAuthorityRouteMissingReceipt : Set where
  missingHEPDataObservableSelectionReceipt :
    HEPDataComparisonAuthorityRouteMissingReceipt
  missingHEPDataUnitCalibrationRequirementReceipt :
    HEPDataComparisonAuthorityRouteMissingReceipt
  missingTheoremSideMeasurementSurfaceProjectionReceipt :
    HEPDataComparisonAuthorityRouteMissingReceipt
  missingHEPDataITIRAcceptedAuthorityAdapterReceipt :
    HEPDataComparisonAuthorityRouteMissingReceipt
  missingHEPDataComparisonLawReceipt :
    HEPDataComparisonAuthorityRouteMissingReceipt
  missingAcceptedDatasetAuthorityToken :
    HEPDataComparisonAuthorityRouteMissingReceipt
  missingAcceptedDatasetAuthorityRoute :
    HEPDataComparisonAuthorityRouteMissingReceipt

canonicalHEPDataComparisonAuthorityRouteMissingReceipts :
  List HEPDataComparisonAuthorityRouteMissingReceipt
canonicalHEPDataComparisonAuthorityRouteMissingReceipts =
  missingHEPDataObservableSelectionReceipt
  ∷ missingHEPDataUnitCalibrationRequirementReceipt
  ∷ missingTheoremSideMeasurementSurfaceProjectionReceipt
  ∷ missingHEPDataITIRAcceptedAuthorityAdapterReceipt
  ∷ missingHEPDataComparisonLawReceipt
  ∷ missingAcceptedDatasetAuthorityToken
  ∷ missingAcceptedDatasetAuthorityRoute
  ∷ []

data HEPDataComparisonAuthorityRouteBoundaryToken : Set where
  diagnosticOnlyNoComparisonLawNoAuthorityRoute :
    HEPDataComparisonAuthorityRouteBoundaryToken

record HEPDataComparisonAuthorityRouteDiagnostic : Setω where
  field
    selectionDiagnostic :
      Selection.HEPDataObservableSelectionDiagnostic

    unitCalibrationDiagnostic :
      Calibration.HEPDataUnitCalibrationRequirementDiagnostic

    projectionRejection :
      Projection.HEPDataMeasurementSurfaceProjectionRejection

    authorityAdapterDiagnostic :
      Adapter.HEPDataITIRAuthorityAdapterDiagnostic

    selectionStillBlocked :
      Selection.HEPDataObservableSelectionDiagnostic.selectionStatus
        selectionDiagnostic
      ≡
      Selection.selectionBlockedAwaitingConcreteAuthorizedChecksumCandidate

    unitCalibrationStillBlocked :
      Calibration.HEPDataUnitCalibrationRequirementDiagnostic.currentStatus
        unitCalibrationDiagnostic
      ≡
      Calibration.blockedAwaitingSelectedObservableAndExternalCalibration

    projectionStillRejected :
      Projection.HEPDataMeasurementSurfaceProjectionRejection.currentStatus
        projectionRejection
      ≡
      Projection.rejectedMissingProjectionContract

    authorityAdapterStillAbsent :
      Adapter.HEPDataITIRAuthorityAdapterDiagnostic.adapterStatus
        authorityAdapterDiagnostic
      ≡
      Adapter.genericScaffoldPresentHEPDataAuthorityAdapterAbsent

    currentStatus :
      HEPDataComparisonAuthorityRouteStatus

    comparisonLawConstructible :
      Bool

    acceptedDatasetAuthorityRouteConstructible :
      Bool

    missingReceipts :
      List HEPDataComparisonAuthorityRouteMissingReceipt

    missingReceiptsAreCanonical :
      missingReceipts
      ≡
      canonicalHEPDataComparisonAuthorityRouteMissingReceipts

    futureComparisonLawReceiptName :
      String

    futureAcceptedDatasetAuthorityRouteName :
      String

    exactFutureReceiptFields :
      List String

    currentBlockerSummary :
      List String

    noFabricationBoundary :
      List String

    nonPromotionBoundary :
      List String

    typedBoundaryToken :
      HEPDataComparisonAuthorityRouteBoundaryToken

    coordinationMapNodeText :
      String

    coordinationMapEdgeText :
      String

    coordinationBoardSummary :
      String

    impossibleAcceptedDatasetAuthorityTokenHere :
      HEPDataAcceptedDatasetAuthorityToken →
      ⊥

    impossibleComparisonLawReceiptHere :
      {observable : HEP.HEPDataObservable} →
      HEPDataComparisonLawReceipt observable →
      ⊥

    impossibleAuthorityAdapterReceiptHere :
      HEPDataITIRAcceptedAuthorityAdapterReceipt →
      ⊥

    impossibleAcceptedDatasetAuthorityRouteHere :
      {observable : HEP.HEPDataObservable} →
      HEPDataAcceptedDatasetAuthorityRoute observable →
      ⊥

canonicalHEPDataComparisonAuthorityRouteDiagnostic :
  HEPDataComparisonAuthorityRouteDiagnostic
canonicalHEPDataComparisonAuthorityRouteDiagnostic =
  record
    { selectionDiagnostic =
        Selection.canonicalHEPDataObservableSelectionDiagnostic
    ; unitCalibrationDiagnostic =
        Calibration.canonicalHEPDataUnitCalibrationRequirementDiagnostic
    ; projectionRejection =
        Projection.canonicalHEPDataMeasurementSurfaceProjectionRejection
    ; authorityAdapterDiagnostic =
        Adapter.canonicalHEPDataITIRAuthorityAdapterDiagnostic
    ; selectionStillBlocked =
        refl
    ; unitCalibrationStillBlocked =
        refl
    ; projectionStillRejected =
        refl
    ; authorityAdapterStillAbsent =
        refl
    ; currentStatus =
        blockedAwaitingSelectionCalibrationProjectionAuthorityAdapterReceipts
    ; comparisonLawConstructible =
        false
    ; acceptedDatasetAuthorityRouteConstructible =
        false
    ; missingReceipts =
        canonicalHEPDataComparisonAuthorityRouteMissingReceipts
    ; missingReceiptsAreCanonical =
        refl
    ; futureComparisonLawReceiptName =
        "DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic.HEPDataComparisonLawReceipt"
    ; futureAcceptedDatasetAuthorityRouteName =
        "DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic.HEPDataAcceptedDatasetAuthorityRoute"
    ; exactFutureReceiptFields =
        "selectionReceipt : HEPDataObservableSelectionReceipt from HEP-B"
        ∷ "unitCalibrationReceipt : HEPDataUnitCalibrationRequirementReceipt observable from HEP-C"
        ∷ "theoremSideProjectionReceipt : TheoremSideMeasurementSurfaceProjectionReceipt from HEP-D"
        ∷ "comparison law carriers, embedding, predicate, and proof matching schema comparisonLawTarget"
        ∷ "itirAuthorityAdapterReceipt carrying raw HEPData authority identity, checksum, NPZ hash, source/citation/table identity, projection boundary, and accepted handoff"
        ∷ "acceptedDatasetAuthorityToken : HEPDataAcceptedDatasetAuthorityToken"
        ∷ []
    ; currentBlockerSummary =
        "HEP-B has not supplied a selected observable/table/column/row checksum-bound receipt"
        ∷ "HEP-C has not supplied unit carriers, calibration map, preservation or monotonicity law, and validation authority"
        ∷ "HEP-D explicitly rejects MeasurementSurface -> DashiState projection until semantic, metric, transform, failure, and authority contracts close"
        ∷ "HEP-F finds generic ITIR provenance scaffolding, not a HEPData-specific accepted-authority adapter"
        ∷ "Therefore HEP-E cannot construct a comparison law or accepted dataset authority route"
        ∷ []
    ; noFabricationBoundary =
        "This module constructs no HEPDataAcceptedDatasetAuthorityToken"
        ∷ "This module constructs no HEPDataObservableSelectionReceipt"
        ∷ "This module constructs no HEPDataUnitCalibrationRequirementReceipt"
        ∷ "This module constructs no TheoremSideMeasurementSurfaceProjectionReceipt"
        ∷ "This module constructs no HEPDataITIRAcceptedAuthorityAdapterReceipt"
        ∷ "This module constructs no comparison law receipt and no accepted dataset authority route"
        ∷ []
    ; nonPromotionBoundary =
        "HEP-E is a typed diagnostic and future route shape only"
        ∷ "No fake dataset authority is introduced from local source presence"
        ∷ "No W3 accepted-authority receipt is constructed or promoted"
        ∷ "No W8 origin-promotion receipt is constructed or promoted"
        ∷ []
    ; typedBoundaryToken =
        diagnosticOnlyNoComparisonLawNoAuthorityRoute
    ; coordinationMapNodeText =
        "rectangle \"HEP-E\\ncomparison law + accepted dataset authority route\\ntyped diagnostic\\nblocked on HEP-B/C/D/F receipts\" as HEPDATA_HEPE #fef3c7"
    ; coordinationMapEdgeText =
        "HEPDATA_HEPB --> HEPDATA_HEPE : selected observable receipt required\nHEPDATA_HEPC --> HEPDATA_HEPE : unit calibration receipt required\nHEPDATA_HEPD --> HEPDATA_HEPE : theorem-side projection receipt required\nHEPDATA_HEPF --> HEPDATA_HEPE : accepted authority adapter receipt required\nHEPDATA_HEPE --> W3 : no accepted-authority promotion\nHEPDATA_HEPE --> Plateau : comparison law + accepted dataset route remain unconstructed"
    ; coordinationBoardSummary =
        "HEP-E added DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic: comparison law and accepted dataset authority route are future receipt shapes only; current status is blocked until HEP-B selection, HEP-C calibration, HEP-D projection, and HEP-F authority-adapter receipts exist. No authority token, W3 receipt, or W8 promotion is constructed."
    ; impossibleAcceptedDatasetAuthorityTokenHere =
        acceptedDatasetAuthorityTokenImpossibleHere
    ; impossibleComparisonLawReceiptHere =
        comparisonLawReceiptImpossibleHere
    ; impossibleAuthorityAdapterReceiptHere =
        itirAuthorityAdapterReceiptImpossibleHere
    ; impossibleAcceptedDatasetAuthorityRouteHere =
        acceptedDatasetAuthorityRouteImpossibleHere
    }
