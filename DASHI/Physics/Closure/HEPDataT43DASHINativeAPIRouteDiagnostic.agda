module DASHI.Physics.Closure.HEPDataT43DASHINativeAPIRouteDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataComparisonLawReceiptRequest as R31
import DASHI.Physics.Closure.HEPDataT43PredictionAPIRouteDiagnostic as R33
import DASHI.Physics.Closure.HEPDataT43ProjectionRunnerContract as R29
import DASHI.Physics.Closure.HEPDataT43SudakovBaselinePredictionHook as R34

------------------------------------------------------------------------
-- HEP-R35: DASHI-native t43 phi-star ratio API route diagnostic.
--
-- This module records the current non-promoting state after the R33/R34
-- diagnostics: sibling evidence and the CSS/Sudakov baseline do not supply an
-- accepted sigma_DASHI t43 phi-star ratio API.  The accepted route still has
-- to be constructed from DashiDynamics through a phi-star projection law.
--
-- Governance note: diagrams must add HEP-R35 as a blocker node, but this
-- worker lane intentionally does not edit diagrams, shared docs, or indexes.

data HEPDataT43DASHINativeAPIRouteStatus : Set where
  blockedAwaitingDASHINativeDashiDynamicsPhiStarRatioAPI :
    HEPDataT43DASHINativeAPIRouteStatus

data HEPDataT43DASHINativeAPISourceFinding : Set where
  siblingReposDoNotSupplyAcceptedSigmaDASHIAPI :
    HEPDataT43DASHINativeAPISourceFinding
  cssSudakovBaselineIsNotAcceptedSigmaDASHIAPI :
    HEPDataT43DASHINativeAPISourceFinding
  constructionRequiredViaDashiDynamicsPhiStarProjection :
    HEPDataT43DASHINativeAPISourceFinding

canonicalHEPDataT43DASHINativeAPISourceFindings :
  List HEPDataT43DASHINativeAPISourceFinding
canonicalHEPDataT43DASHINativeAPISourceFindings =
  siblingReposDoNotSupplyAcceptedSigmaDASHIAPI
  ∷ cssSudakovBaselineIsNotAcceptedSigmaDASHIAPI
  ∷ constructionRequiredViaDashiDynamicsPhiStarProjection
  ∷ []

data HEPDataT43DASHINativeAPIMissingField : Set where
  acceptedFunctionPath :
    HEPDataT43DASHINativeAPIMissingField
  DashiDynamicsBackedSigmaSource :
    HEPDataT43DASHINativeAPIMissingField
  massWindowNumeratorBinding5076 :
    HEPDataT43DASHINativeAPIMissingField
  massWindowDenominatorBinding76106 :
    HEPDataT43DASHINativeAPIMissingField
  phiStarBinIntegralProjectionLaw :
    HEPDataT43DASHINativeAPIMissingField
  normalizationUnitSemantics :
    HEPDataT43DASHINativeAPIMissingField
  independenceFromObservedT43Ratios :
    HEPDataT43DASHINativeAPIMissingField
  cleanPredictionFixedAt :
    HEPDataT43DASHINativeAPIMissingField
  projectionCompleteArtifact :
    HEPDataT43DASHINativeAPIMissingField
  comparisonLawReceipt :
    HEPDataT43DASHINativeAPIMissingField

canonicalHEPDataT43DASHINativeAPIMissingFields :
  List HEPDataT43DASHINativeAPIMissingField
canonicalHEPDataT43DASHINativeAPIMissingFields =
  acceptedFunctionPath
  ∷ DashiDynamicsBackedSigmaSource
  ∷ massWindowNumeratorBinding5076
  ∷ massWindowDenominatorBinding76106
  ∷ phiStarBinIntegralProjectionLaw
  ∷ normalizationUnitSemantics
  ∷ independenceFromObservedT43Ratios
  ∷ cleanPredictionFixedAt
  ∷ projectionCompleteArtifact
  ∷ comparisonLawReceipt
  ∷ []

data HEPDataT43DASHINativeAPIBoundary : Set where
  diagnosticOnlyNoAcceptedAPI :
    HEPDataT43DASHINativeAPIBoundary
  noObservedT43RatioBackfill :
    HEPDataT43DASHINativeAPIBoundary
  cssSudakovBaselineCannotPromoteW3 :
    HEPDataT43DASHINativeAPIBoundary
  noProjectionCompleteClaim :
    HEPDataT43DASHINativeAPIBoundary
  noComparisonLawClaim :
    HEPDataT43DASHINativeAPIBoundary
  noW3W4W5W8Promotion :
    HEPDataT43DASHINativeAPIBoundary
  diagramBlockerNodeRequiredButNotEditedHere :
    HEPDataT43DASHINativeAPIBoundary

canonicalHEPDataT43DASHINativeAPIBoundaries :
  List HEPDataT43DASHINativeAPIBoundary
canonicalHEPDataT43DASHINativeAPIBoundaries =
  diagnosticOnlyNoAcceptedAPI
  ∷ noObservedT43RatioBackfill
  ∷ cssSudakovBaselineCannotPromoteW3
  ∷ noProjectionCompleteClaim
  ∷ noComparisonLawClaim
  ∷ noW3W4W5W8Promotion
  ∷ diagramBlockerNodeRequiredButNotEditedHere
  ∷ []

data HEPDataAcceptedT43DASHINativePhiStarRatioAPIReceipt : Set where

acceptedT43DASHINativePhiStarRatioAPIReceiptImpossibleHere :
  HEPDataAcceptedT43DASHINativePhiStarRatioAPIReceipt →
  ⊥
acceptedT43DASHINativePhiStarRatioAPIReceiptImpossibleHere ()

record HEPDataT43DASHINativeAPIRouteDiagnostic : Setω where
  field
    status :
      HEPDataT43DASHINativeAPIRouteStatus

    priorPredictionAPIRouteDiagnostic :
      R33.HEPDataT43PredictionAPIRouteDiagnostic

    sudakovBaselinePredictionHook :
      R34.HEPDataT43SudakovBaselinePredictionHook

    projectionRunnerContract :
      R29.HEPDataT43ProjectionRunnerContract

    comparisonLawReceiptRequest :
      R31.HEPDataComparisonLawReceiptRequest

    acceptedDASHINativeSigmaAPIExistsHere :
      Bool

    acceptedDASHINativeSigmaAPIExistsHereIsFalse :
      acceptedDASHINativeSigmaAPIExistsHere ≡ false

    siblingReposSupplyAcceptedSigmaDASHIAPI :
      Bool

    siblingReposSupplyAcceptedSigmaDASHIAPIIsFalse :
      siblingReposSupplyAcceptedSigmaDASHIAPI ≡ false

    cssSudakovBaselineSuppliesAcceptedSigmaDASHIAPI :
      Bool

    cssSudakovBaselineSuppliesAcceptedSigmaDASHIAPIIsFalse :
      cssSudakovBaselineSuppliesAcceptedSigmaDASHIAPI ≡ false

    constructionRequiredViaDashiDynamicsPhiStarProjectionFlag :
      Bool

    constructionRequiredViaDashiDynamicsPhiStarProjectionFlagIsTrue :
      constructionRequiredViaDashiDynamicsPhiStarProjectionFlag ≡ true

    observedT43RatiosMaySeedPrediction :
      Bool

    observedT43RatiosMaySeedPredictionIsFalse :
      observedT43RatiosMaySeedPrediction ≡ false

    sourceFindings :
      List HEPDataT43DASHINativeAPISourceFinding

    sourceFindingsAreCanonical :
      sourceFindings
      ≡
      canonicalHEPDataT43DASHINativeAPISourceFindings

    missingFields :
      List HEPDataT43DASHINativeAPIMissingField

    missingFieldsAreCanonical :
      missingFields
      ≡
      canonicalHEPDataT43DASHINativeAPIMissingFields

    exactMissingFieldText :
      List String

    requiredConstructionRoute :
      List String

    boundary :
      List HEPDataT43DASHINativeAPIBoundary

    boundaryIsCanonical :
      boundary ≡ canonicalHEPDataT43DASHINativeAPIBoundaries

    diagramBlockerNodeRequired :
      Bool

    diagramBlockerNodeRequiredIsTrue :
      diagramBlockerNodeRequired ≡ true

    futureAcceptedReceiptBlocked :
      HEPDataAcceptedT43DASHINativePhiStarRatioAPIReceipt →
      ⊥

canonicalHEPDataT43DASHINativeAPIRouteDiagnostic :
  HEPDataT43DASHINativeAPIRouteDiagnostic
canonicalHEPDataT43DASHINativeAPIRouteDiagnostic =
  record
    { status =
        blockedAwaitingDASHINativeDashiDynamicsPhiStarRatioAPI
    ; priorPredictionAPIRouteDiagnostic =
        R33.canonicalHEPDataT43PredictionAPIRouteDiagnostic
    ; sudakovBaselinePredictionHook =
        R34.canonicalHEPDataT43SudakovBaselinePredictionHook
    ; projectionRunnerContract =
        R29.canonicalHEPDataT43ProjectionRunnerContract
    ; comparisonLawReceiptRequest =
        R31.canonicalHEPDataComparisonLawReceiptRequest
    ; acceptedDASHINativeSigmaAPIExistsHere =
        false
    ; acceptedDASHINativeSigmaAPIExistsHereIsFalse =
        refl
    ; siblingReposSupplyAcceptedSigmaDASHIAPI =
        false
    ; siblingReposSupplyAcceptedSigmaDASHIAPIIsFalse =
        refl
    ; cssSudakovBaselineSuppliesAcceptedSigmaDASHIAPI =
        false
    ; cssSudakovBaselineSuppliesAcceptedSigmaDASHIAPIIsFalse =
        refl
    ; constructionRequiredViaDashiDynamicsPhiStarProjectionFlag =
        true
    ; constructionRequiredViaDashiDynamicsPhiStarProjectionFlagIsTrue =
        refl
    ; observedT43RatiosMaySeedPrediction =
        false
    ; observedT43RatiosMaySeedPredictionIsFalse =
        refl
    ; sourceFindings =
        canonicalHEPDataT43DASHINativeAPISourceFindings
    ; sourceFindingsAreCanonical =
        refl
    ; missingFields =
        canonicalHEPDataT43DASHINativeAPIMissingFields
    ; missingFieldsAreCanonical =
        refl
    ; exactMissingFieldText =
        "accepted function path : module:function for the accepted DASHI-native t43 phi-star ratio API"
        ∷ "DashiDynamics-backed sigma source : sigma_DASHI must be derived from a DashiDynamics carrier, not from the CSS/Sudakov baseline"
        ∷ "mass-window numerator binding : sigma_DASHI(50 <= M < 76, phi-star bin)"
        ∷ "mass-window denominator binding : sigma_DASHI(76 <= M < 106, phi-star bin)"
        ∷ "phi-star bin integral/projection law : bind each t43 phi-star bin to the DashiDynamics projection used for both mass windows"
        ∷ "normalization/unit semantics : record the unit and normalization convention making the ratio dimensionless and comparable"
        ∷ "independence from observed t43 ratios : the prediction must not read or backfill from the observed HEPData Ratio column"
        ∷ "clean predictionFixedAt : accepted clean freeze identity for the DASHI-native prediction source and inputs"
        ∷ "projectionComplete artifact : digest-bound artifact emitted after running the accepted route over the t43 bins"
        ∷ "comparison-law receipt : accepted receipt consuming the frozen projection before any W3 adequacy claim"
        ∷ []
    ; requiredConstructionRoute =
        "Findings: sibling repos and the CSS/Sudakov baseline do not currently provide an accepted sigma_DASHI t43 phi-star ratio API"
        ∷ "Required route: construct sigma_DASHI through DashiDynamics and a phi-star bin integral/projection law"
        ∷ "Required ratio: sigma_DASHI(50 <= M < 76, bin) / sigma_DASHI(76 <= M < 106, bin)"
        ∷ "Required freeze: bind the accepted function and inputs to a clean predictionFixedAt before projection"
        ∷ "Required artifact: emit projectionComplete with bin bindings, units, normalization semantics, and digest"
        ∷ "Required comparison: obtain a comparison-law receipt before any empirical adequacy or W3/W4/W5/W8 promotion"
        ∷ "Governance: CSS/Sudakov remains baseline only and cannot promote W3"
        ∷ "Governance: diagrams must add HEP-R35 as a blocker node; this module does not edit them"
        ∷ []
    ; boundary =
        canonicalHEPDataT43DASHINativeAPIBoundaries
    ; boundaryIsCanonical =
        refl
    ; diagramBlockerNodeRequired =
        true
    ; diagramBlockerNodeRequiredIsTrue =
        refl
    ; futureAcceptedReceiptBlocked =
        acceptedT43DASHINativePhiStarRatioAPIReceiptImpossibleHere
    }

canonicalHEPDataT43DASHINativeAPIRouteStatus :
  HEPDataT43DASHINativeAPIRouteStatus
canonicalHEPDataT43DASHINativeAPIRouteStatus =
  HEPDataT43DASHINativeAPIRouteDiagnostic.status
    canonicalHEPDataT43DASHINativeAPIRouteDiagnostic
