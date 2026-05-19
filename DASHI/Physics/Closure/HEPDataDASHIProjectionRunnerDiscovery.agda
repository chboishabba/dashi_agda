module DASHI.Physics.Closure.HEPDataDASHIProjectionRunnerDiscovery where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection as Projection
import DASHI.Physics.Closure.HEPDataPredictionFreezeProjectionRunRequest as R22
import DASHI.Physics.Closure.HEPDataRatioAdapterTransformReceiptRequest as R21

------------------------------------------------------------------------
-- HEP-R25: DASHI projection-runner discovery diagnostic.
--
-- This module records a local discovery result only.  HEP-R28 now supplies
-- checksum-bound t43/t44 artifacts, so the live runner gap is the executable
-- projection implementation plus freeze/projection digest.  It does not run a
-- prediction, freeze a commit, project against HEPData t43 bins, construct a
-- projection receipt, construct a comparison law, or promote W3/W4/W5/W8.

data HEPDataDASHIProjectionRunnerDiscoveryStatus : Set where
  searchedNoExactT43DASHIProjectionRunnerFound :
    HEPDataDASHIProjectionRunnerDiscoveryStatus

data HEPDataDASHIProjectionRunnerCandidateSurface : Set where
  agdaR21RatioAdapterTransformReceiptRequest :
    HEPDataDASHIProjectionRunnerCandidateSurface
  agdaR22PredictionFreezeProjectionRunRequest :
    HEPDataDASHIProjectionRunnerCandidateSurface
  agdaMeasurementSurfaceProjectionRejection :
    HEPDataDASHIProjectionRunnerCandidateSurface
  pythonHEPDataProgramSurface :
    HEPDataDASHIProjectionRunnerCandidateSurface
  pythonHEPDataSurfaceReport :
    HEPDataDASHIProjectionRunnerCandidateSurface
  pythonHEPDataProjectionContract :
    HEPDataDASHIProjectionRunnerCandidateSurface
  pythonHEPDataConsumer :
    HEPDataDASHIProjectionRunnerCandidateSurface
  localT19T20AbsoluteContextCSV :
    HEPDataDASHIProjectionRunnerCandidateSurface
  localPhistar5076NormalizedArtifactJSON :
    HEPDataDASHIProjectionRunnerCandidateSurface

canonicalHEPDataDASHIProjectionRunnerCandidateSurfaces :
  List HEPDataDASHIProjectionRunnerCandidateSurface
canonicalHEPDataDASHIProjectionRunnerCandidateSurfaces =
  agdaR21RatioAdapterTransformReceiptRequest
  ∷ agdaR22PredictionFreezeProjectionRunRequest
  ∷ agdaMeasurementSurfaceProjectionRejection
  ∷ pythonHEPDataProgramSurface
  ∷ pythonHEPDataSurfaceReport
  ∷ pythonHEPDataProjectionContract
  ∷ pythonHEPDataConsumer
  ∷ localT19T20AbsoluteContextCSV
  ∷ localPhistar5076NormalizedArtifactJSON
  ∷ []

data HEPDataDASHIProjectionRunnerMissingGlue : Set where
  missingLocalT43RatioValueArtifact :
    HEPDataDASHIProjectionRunnerMissingGlue
  missingLocalT44RatioCovarianceArtifact :
    HEPDataDASHIProjectionRunnerMissingGlue
  missingPredictionFixedAtCommitHash :
    HEPDataDASHIProjectionRunnerMissingGlue
  missingPredictionArtifactDigest :
    HEPDataDASHIProjectionRunnerMissingGlue
  missingExecutableT43ProjectionRunner :
    HEPDataDASHIProjectionRunnerMissingGlue
  missingT43T44BinBindingForRunner :
    HEPDataDASHIProjectionRunnerMissingGlue
  missingNonCollapsePreRegistrationBoundary :
    HEPDataDASHIProjectionRunnerMissingGlue
  missingComparisonLawInputFromRunner :
    HEPDataDASHIProjectionRunnerMissingGlue
  missingTheoremSideProjectionReceipt :
    HEPDataDASHIProjectionRunnerMissingGlue

canonicalHEPDataDASHIProjectionRunnerMissingGlue :
  List HEPDataDASHIProjectionRunnerMissingGlue
canonicalHEPDataDASHIProjectionRunnerMissingGlue =
  missingPredictionFixedAtCommitHash
  ∷ missingPredictionArtifactDigest
  ∷ missingExecutableT43ProjectionRunner
  ∷ missingT43T44BinBindingForRunner
  ∷ missingNonCollapsePreRegistrationBoundary
  ∷ missingComparisonLawInputFromRunner
  ∷ missingTheoremSideProjectionReceipt
  ∷ []

data HEPDataDASHIProjectionRunnerBoundary : Set where
  noPredictionResultHere :
    HEPDataDASHIProjectionRunnerBoundary
  noProjectionRunHere :
    HEPDataDASHIProjectionRunnerBoundary
  noProjectionReceiptHere :
    HEPDataDASHIProjectionRunnerBoundary
  noComparisonLawHere :
    HEPDataDASHIProjectionRunnerBoundary
  noPromotionHere :
    HEPDataDASHIProjectionRunnerBoundary

canonicalHEPDataDASHIProjectionRunnerBoundaries :
  List HEPDataDASHIProjectionRunnerBoundary
canonicalHEPDataDASHIProjectionRunnerBoundaries =
  noPredictionResultHere
  ∷ noProjectionRunHere
  ∷ noProjectionReceiptHere
  ∷ noComparisonLawHere
  ∷ noPromotionHere
  ∷ []

data HEPDataDASHIProjectionRunnerReceipt : Set where

projectionRunnerReceiptImpossibleHere :
  HEPDataDASHIProjectionRunnerReceipt →
  ⊥
projectionRunnerReceiptImpossibleHere ()

record HEPDataDASHIProjectionRunnerDiscoveryDiagnostic : Setω where
  field
    status :
      HEPDataDASHIProjectionRunnerDiscoveryStatus

    selectedRatioRoute :
      R21.HEPDataRatioAdapterTransformReceiptRequest

    predictionFreezeProjectionRunRequest :
      R22.HEPDataPredictionFreezeProjectionRunRequestSurface

    projectionContractRejection :
      Projection.HEPDataMeasurementSurfaceProjectionRejection

    r21StillBlocked :
      R21.HEPDataRatioAdapterTransformReceiptRequest.status
        selectedRatioRoute
      ≡
      R21.ratioRouteSelectedButReceiptStillBlocked

    r22StillBlocked :
      R22.HEPDataPredictionFreezeProjectionRunRequestSurface.currentStatus
        predictionFreezeProjectionRunRequest
      ≡
      R22.blockedAwaitingInternalPredictionFreezeAndProjectionRun

    projectionContractStillRejected :
      Projection.HEPDataMeasurementSurfaceProjectionRejection.currentResultState
        projectionContractRejection
      ≡
      Projection.projectionRejected

    exactRunnerExistsHere :
      Bool

    exactRunnerExistsHereIsFalse :
      exactRunnerExistsHere ≡ false

    t43T44RouteSelected :
      Bool

    t43T44RouteSelectedIsTrue :
      t43T44RouteSelected ≡ true

    candidateSurfaces :
      List HEPDataDASHIProjectionRunnerCandidateSurface

    candidateSurfacesAreCanonical :
      candidateSurfaces
      ≡
      canonicalHEPDataDASHIProjectionRunnerCandidateSurfaces

    missingGlue :
      List HEPDataDASHIProjectionRunnerMissingGlue

    missingGlueIsCanonical :
      missingGlue
      ≡
      canonicalHEPDataDASHIProjectionRunnerMissingGlue

    searchedSurfaceNames :
      List String

    candidateSurfaceAssessment :
      List String

    exactNextRunnerBlocker :
      String

    boundary :
      List HEPDataDASHIProjectionRunnerBoundary

    boundaryIsCanonical :
      boundary
      ≡
      canonicalHEPDataDASHIProjectionRunnerBoundaries

    noRunnerReceiptHere :
      HEPDataDASHIProjectionRunnerReceipt →
      ⊥

canonicalHEPDataDASHIProjectionRunnerDiscoveryDiagnostic :
  HEPDataDASHIProjectionRunnerDiscoveryDiagnostic
canonicalHEPDataDASHIProjectionRunnerDiscoveryDiagnostic =
  record
    { status =
        searchedNoExactT43DASHIProjectionRunnerFound
    ; selectedRatioRoute =
        R21.canonicalHEPDataRatioAdapterTransformReceiptRequest
    ; predictionFreezeProjectionRunRequest =
        R22.canonicalHEPDataPredictionFreezeProjectionRunRequestSurface
    ; projectionContractRejection =
        Projection.canonicalHEPDataMeasurementSurfaceProjectionRejection
    ; r21StillBlocked =
        refl
    ; r22StillBlocked =
        refl
    ; projectionContractStillRejected =
        refl
    ; exactRunnerExistsHere =
        false
    ; exactRunnerExistsHereIsFalse =
        refl
    ; t43T44RouteSelected =
        true
    ; t43T44RouteSelectedIsTrue =
        refl
    ; candidateSurfaces =
        canonicalHEPDataDASHIProjectionRunnerCandidateSurfaces
    ; candidateSurfacesAreCanonical =
        refl
    ; missingGlue =
        canonicalHEPDataDASHIProjectionRunnerMissingGlue
    ; missingGlueIsCanonical =
        refl
    ; searchedSurfaceNames =
        "DASHI.Physics.Closure.HEPDataRatioAdapterTransformReceiptRequest"
        ∷ "DASHI.Physics.Closure.HEPDataPredictionFreezeProjectionRunRequest"
        ∷ "DASHI.Physics.Closure.HEPDataMeasurementSurfaceProjectionRejection"
        ∷ "scripts/hepdata_program_surface.py"
        ∷ "scripts/hepdata_surface_report.py"
        ∷ "scripts/hepdata_projection_contract.py"
        ∷ "scripts/hepdata_consumer.py"
        ∷ "scripts/data/hepdata/ins2079374_phistar_mass_50-76_t19.csv"
        ∷ "scripts/data/hepdata/ins2079374_Covariance_phistar_mass_50-76_t20.csv"
        ∷ "scripts/data/hepdata_phistar_50_76_artifact.json"
        ∷ []
    ; candidateSurfaceAssessment =
        "R21 selects t43/t44 as the dimensionless ratio route but leaves predictionFixedAt, projection receipt, and comparison law blocked"
        ∷ "R22 names the freeze/projection-run request and says the internal t43 projection run is missing"
        ∷ "HEPDataMeasurementSurfaceProjectionRejection records the generic MeasurementSurface projection contract rejection"
        ∷ "hepdata_program_surface.py packages validated measurement/report metadata and embeds the projection contract summary"
        ∷ "hepdata_surface_report.py computes report-only metric readiness for a MeasurementSurface"
        ∷ "hepdata_projection_contract.py defines contract and precondition stubs but no DASHI projection implementation"
        ∷ "hepdata_consumer.py loads canonical artifacts into MeasurementSurface values"
        ∷ "local t19/t20 CSV files and phistar_50_76 JSON are absolute/context artifacts, not local t43/t44 ratio-run artifacts"
        ∷ "HEP-R28 now supplies checksum-bound t43/t44 CSV artifacts; this discovery still finds no executable DASHI projection runner"
        ∷ []
    ; exactNextRunnerBlocker =
        "Supply an executable, digest-bound DASHI projection runner that consumes frozen predictionFixedAt plus checksum-bound HEPData t43/t44 bins and emits the R22 comparison-law input and theorem-side projection receipt under pre-registered non-collapse criteria"
    ; boundary =
        canonicalHEPDataDASHIProjectionRunnerBoundaries
    ; boundaryIsCanonical =
        refl
    ; noRunnerReceiptHere =
        projectionRunnerReceiptImpossibleHere
    }

canonicalHEPDataDASHIProjectionRunnerExactBlocker :
  String
canonicalHEPDataDASHIProjectionRunnerExactBlocker =
  HEPDataDASHIProjectionRunnerDiscoveryDiagnostic.exactNextRunnerBlocker
    canonicalHEPDataDASHIProjectionRunnerDiscoveryDiagnostic
