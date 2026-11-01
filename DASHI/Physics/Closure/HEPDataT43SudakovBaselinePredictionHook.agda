module DASHI.Physics.Closure.HEPDataT43SudakovBaselinePredictionHook where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataT43PredictionAPIRouteDiagnostic as R33

------------------------------------------------------------------------
-- HEP-R34: non-promoting CSS/Sudakov baseline prediction hook.
--
-- This surface records the concrete Python hook that can exercise the
-- digest-bound t43 runner end-to-end:
--
--   DASHI.Physics.Prediction.phi_star_ratio:predict_ratio
--
-- It is deliberately not an accepted DASHI empirical prediction API.  The hook
-- is a deterministic baseline over t43 bin edges; it does not discharge the
-- DashiDynamics -> phi-star ratio projection route, clean freeze receipt,
-- comparison-law receipt, or W3 empirical adequacy.

data HEPDataT43SudakovBaselineHookStatus : Set where
  baselineHookAvailableNonPromoting :
    HEPDataT43SudakovBaselineHookStatus

data HEPDataT43SudakovBaselineHookField : Set where
  pythonModulePath :
    HEPDataT43SudakovBaselineHookField
  callablePath :
    HEPDataT43SudakovBaselineHookField
  acceptsT43BinRecords :
    HEPDataT43SudakovBaselineHookField
  returnsFiniteRatioPerBin :
    HEPDataT43SudakovBaselineHookField
  usesPhiStarBinEdgesOnly :
    HEPDataT43SudakovBaselineHookField
  marksBaselineAsNonPromoting :
    HEPDataT43SudakovBaselineHookField

canonicalHEPDataT43SudakovBaselineHookFields :
  List HEPDataT43SudakovBaselineHookField
canonicalHEPDataT43SudakovBaselineHookFields =
  pythonModulePath
  ∷ callablePath
  ∷ acceptsT43BinRecords
  ∷ returnsFiniteRatioPerBin
  ∷ usesPhiStarBinEdgesOnly
  ∷ marksBaselineAsNonPromoting
  ∷ []

data HEPDataT43SudakovBaselineHookBoundary : Set where
  notAcceptedDASHIPredictionAPI :
    HEPDataT43SudakovBaselineHookBoundary
  noCleanPredictionFreezeReceipt :
    HEPDataT43SudakovBaselineHookBoundary
  noComparisonLawReceipt :
    HEPDataT43SudakovBaselineHookBoundary
  noEmpiricalAdequacyReceipt :
    HEPDataT43SudakovBaselineHookBoundary
  noW3W4W5W8Promotion :
    HEPDataT43SudakovBaselineHookBoundary

canonicalHEPDataT43SudakovBaselineHookBoundaries :
  List HEPDataT43SudakovBaselineHookBoundary
canonicalHEPDataT43SudakovBaselineHookBoundaries =
  notAcceptedDASHIPredictionAPI
  ∷ noCleanPredictionFreezeReceipt
  ∷ noComparisonLawReceipt
  ∷ noEmpiricalAdequacyReceipt
  ∷ noW3W4W5W8Promotion
  ∷ []

data HEPDataAcceptedDASHIPhiStarPredictionAPIReceipt : Set where

acceptedDASHIPhiStarPredictionAPIReceiptImpossibleHere :
  HEPDataAcceptedDASHIPhiStarPredictionAPIReceipt →
  ⊥
acceptedDASHIPhiStarPredictionAPIReceiptImpossibleHere ()

record HEPDataT43SudakovBaselinePredictionHook : Setω where
  field
    status :
      HEPDataT43SudakovBaselineHookStatus

    priorRouteDiagnostic :
      R33.HEPDataT43PredictionAPIRouteDiagnostic

    pythonHookModulePath :
      String

    pythonHookCallablePath :
      String

    runnerCanLoadWithoutExternalPythonPath :
      Bool

    runnerCanLoadWithoutExternalPythonPathIsTrue :
      runnerCanLoadWithoutExternalPythonPath ≡ true

    projectionCompleteCanBeProducedForBaseline :
      Bool

    projectionCompleteCanBeProducedForBaselineIsTrue :
      projectionCompleteCanBeProducedForBaseline ≡ true

    acceptedDASHIPredictionAPIExistsHere :
      Bool

    acceptedDASHIPredictionAPIExistsHereIsFalse :
      acceptedDASHIPredictionAPIExistsHere ≡ false

    fields :
      List HEPDataT43SudakovBaselineHookField

    fieldsAreCanonical :
      fields ≡ canonicalHEPDataT43SudakovBaselineHookFields

    validationCommands :
      List String

    boundary :
      List HEPDataT43SudakovBaselineHookBoundary

    boundaryIsCanonical :
      boundary ≡ canonicalHEPDataT43SudakovBaselineHookBoundaries

    futureAcceptedReceiptBlocked :
      HEPDataAcceptedDASHIPhiStarPredictionAPIReceipt →
      ⊥

canonicalHEPDataT43SudakovBaselinePredictionHook :
  HEPDataT43SudakovBaselinePredictionHook
canonicalHEPDataT43SudakovBaselinePredictionHook =
  record
    { status =
        baselineHookAvailableNonPromoting
    ; priorRouteDiagnostic =
        R33.canonicalHEPDataT43PredictionAPIRouteDiagnostic
    ; pythonHookModulePath =
        "DASHI/Physics/Prediction/phi_star_ratio.py"
    ; pythonHookCallablePath =
        "DASHI.Physics.Prediction.phi_star_ratio:predict_ratio"
    ; runnerCanLoadWithoutExternalPythonPath =
        true
    ; runnerCanLoadWithoutExternalPythonPathIsTrue =
        refl
    ; projectionCompleteCanBeProducedForBaseline =
        true
    ; projectionCompleteCanBeProducedForBaselineIsTrue =
        refl
    ; acceptedDASHIPredictionAPIExistsHere =
        false
    ; acceptedDASHIPredictionAPIExistsHereIsFalse =
        refl
    ; fields =
        canonicalHEPDataT43SudakovBaselineHookFields
    ; fieldsAreCanonical =
        refl
    ; validationCommands =
        "python3 -m py_compile DASHI/Physics/Prediction/__init__.py DASHI/Physics/Prediction/phi_star_ratio.py scripts/run_t43_projection.py"
        ∷ "python3 scripts/run_t43_projection.py --freeze-hash HEP-R34-sudakov-baseline --prediction-api DASHI.Physics.Prediction.phi_star_ratio:predict_ratio --output /tmp/t43_projection_hep_r34.json"
        ∷ []
    ; boundary =
        canonicalHEPDataT43SudakovBaselineHookBoundaries
    ; boundaryIsCanonical =
        refl
    ; futureAcceptedReceiptBlocked =
        acceptedDASHIPhiStarPredictionAPIReceiptImpossibleHere
    }

canonicalHEPDataT43SudakovBaselineHookStatus :
  HEPDataT43SudakovBaselineHookStatus
canonicalHEPDataT43SudakovBaselineHookStatus =
  HEPDataT43SudakovBaselinePredictionHook.status
    canonicalHEPDataT43SudakovBaselinePredictionHook
