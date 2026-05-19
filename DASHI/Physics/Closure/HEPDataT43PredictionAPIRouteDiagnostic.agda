module DASHI.Physics.Closure.HEPDataT43PredictionAPIRouteDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataT43ProjectionRunnerImplementationAttempt as R32

------------------------------------------------------------------------
-- HEP-R33: phi-star ratio prediction API route diagnostic.
--
-- HEP-R32 made the runner able to consume a caller-supplied batch prediction
-- API, but no repo-native API has been accepted for
--   t43 bin -> DASHI ratio 50-76 / 76-106.
-- This diagnostic records that exact remaining route without pretending that
-- generic physics, chi2, or projection surfaces are the needed API.

data HEPDataT43PredictionAPIRouteStatus : Set where
  blockedAwaitingRealDASHIPhiStarRatioPredictionAPI :
    HEPDataT43PredictionAPIRouteStatus

data HEPDataT43PredictionAPICandidateSurface : Set where
  genericProjectionContract :
    HEPDataT43PredictionAPICandidateSurface
  genericMeasurementSurfaceConsumer :
    HEPDataT43PredictionAPICandidateSurface
  chi2TransportDynamicsBridge :
    HEPDataT43PredictionAPICandidateSurface
  physicsClosurePredictionSurfaces :
    HEPDataT43PredictionAPICandidateSurface
  hepR32RunnerPredictionHook :
    HEPDataT43PredictionAPICandidateSurface

canonicalHEPDataT43PredictionAPICandidateSurfaces :
  List HEPDataT43PredictionAPICandidateSurface
canonicalHEPDataT43PredictionAPICandidateSurfaces =
  genericProjectionContract
  ∷ genericMeasurementSurfaceConsumer
  ∷ chi2TransportDynamicsBridge
  ∷ physicsClosurePredictionSurfaces
  ∷ hepR32RunnerPredictionHook
  ∷ []

data HEPDataT43PredictionAPIRequiredField : Set where
  batchFunctionPath :
    HEPDataT43PredictionAPIRequiredField
  acceptsT43BinRecords :
    HEPDataT43PredictionAPIRequiredField
  returnsOneFiniteRatioPerBin :
    HEPDataT43PredictionAPIRequiredField
  bindsMassWindowNumerator5076 :
    HEPDataT43PredictionAPIRequiredField
  bindsMassWindowDenominator76106 :
    HEPDataT43PredictionAPIRequiredField
  independentOfHEPDataOutputValues :
    HEPDataT43PredictionAPIRequiredField
  usableBeforeComparisonLaw :
    HEPDataT43PredictionAPIRequiredField

canonicalHEPDataT43PredictionAPIRequiredFields :
  List HEPDataT43PredictionAPIRequiredField
canonicalHEPDataT43PredictionAPIRequiredFields =
  batchFunctionPath
  ∷ acceptsT43BinRecords
  ∷ returnsOneFiniteRatioPerBin
  ∷ bindsMassWindowNumerator5076
  ∷ bindsMassWindowDenominator76106
  ∷ independentOfHEPDataOutputValues
  ∷ usableBeforeComparisonLaw
  ∷ []

data HEPDataT43PredictionAPIRemainingGap : Set where
  missingAcceptedFunctionPath :
    HEPDataT43PredictionAPIRemainingGap
  missingPhysicsToPhiStarRatioProjection :
    HEPDataT43PredictionAPIRemainingGap
  missingPreComparisonFreezeBinding :
    HEPDataT43PredictionAPIRemainingGap
  missingProjectionCompleteTrueRun :
    HEPDataT43PredictionAPIRemainingGap

canonicalHEPDataT43PredictionAPIRemainingGaps :
  List HEPDataT43PredictionAPIRemainingGap
canonicalHEPDataT43PredictionAPIRemainingGaps =
  missingAcceptedFunctionPath
  ∷ missingPhysicsToPhiStarRatioProjection
  ∷ missingPreComparisonFreezeBinding
  ∷ missingProjectionCompleteTrueRun
  ∷ []

data HEPDataT43PredictionAPIBoundary : Set where
  noPredictionAPIAcceptedHere :
    HEPDataT43PredictionAPIBoundary
  noProjectionCompleteClaim :
    HEPDataT43PredictionAPIBoundary
  noComparisonLawClaim :
    HEPDataT43PredictionAPIBoundary
  noW3W4W5W8Promotion :
    HEPDataT43PredictionAPIBoundary

canonicalHEPDataT43PredictionAPIBoundaries :
  List HEPDataT43PredictionAPIBoundary
canonicalHEPDataT43PredictionAPIBoundaries =
  noPredictionAPIAcceptedHere
  ∷ noProjectionCompleteClaim
  ∷ noComparisonLawClaim
  ∷ noW3W4W5W8Promotion
  ∷ []

data HEPDataAcceptedT43PredictionAPIReceipt : Set where

acceptedT43PredictionAPIReceiptImpossibleHere :
  HEPDataAcceptedT43PredictionAPIReceipt →
  ⊥
acceptedT43PredictionAPIReceiptImpossibleHere ()

record HEPDataT43PredictionAPIRouteDiagnostic : Setω where
  field
    status :
      HEPDataT43PredictionAPIRouteStatus

    runnerImplementationAttempt :
      R32.HEPDataT43ProjectionRunnerImplementationAttempt

    runnerCanConsumePredictionAPI :
      Bool

    runnerCanConsumePredictionAPIIsTrue :
      runnerCanConsumePredictionAPI ≡ true

    acceptedPredictionAPIExistsHere :
      Bool

    acceptedPredictionAPIExistsHereIsFalse :
      acceptedPredictionAPIExistsHere ≡ false

    candidateSurfaces :
      List HEPDataT43PredictionAPICandidateSurface

    candidateSurfacesAreCanonical :
      candidateSurfaces
      ≡
      canonicalHEPDataT43PredictionAPICandidateSurfaces

    requiredFields :
      List HEPDataT43PredictionAPIRequiredField

    requiredFieldsAreCanonical :
      requiredFields
      ≡
      canonicalHEPDataT43PredictionAPIRequiredFields

    exactRequiredAPISignature :
      List String

    remainingGaps :
      List HEPDataT43PredictionAPIRemainingGap

    remainingGapsAreCanonical :
      remainingGaps ≡ canonicalHEPDataT43PredictionAPIRemainingGaps

    boundary :
      List HEPDataT43PredictionAPIBoundary

    boundaryIsCanonical :
      boundary ≡ canonicalHEPDataT43PredictionAPIBoundaries

    futureReceiptBlocked :
      HEPDataAcceptedT43PredictionAPIReceipt →
      ⊥

canonicalHEPDataT43PredictionAPIRouteDiagnostic :
  HEPDataT43PredictionAPIRouteDiagnostic
canonicalHEPDataT43PredictionAPIRouteDiagnostic =
  record
    { status =
        blockedAwaitingRealDASHIPhiStarRatioPredictionAPI
    ; runnerImplementationAttempt =
        R32.canonicalHEPDataT43ProjectionRunnerImplementationAttempt
    ; runnerCanConsumePredictionAPI =
        true
    ; runnerCanConsumePredictionAPIIsTrue =
        refl
    ; acceptedPredictionAPIExistsHere =
        false
    ; acceptedPredictionAPIExistsHereIsFalse =
        refl
    ; candidateSurfaces =
        canonicalHEPDataT43PredictionAPICandidateSurfaces
    ; candidateSurfacesAreCanonical =
        refl
    ; requiredFields =
        canonicalHEPDataT43PredictionAPIRequiredFields
    ; requiredFieldsAreCanonical =
        refl
    ; exactRequiredAPISignature =
        "Python hook shape: module:function"
        ∷ "function input: list of t43 bin records with phiStarLow and phiStarHigh"
        ∷ "function output: list of finite Float ratios with exactly one value per input bin"
        ∷ "ratio meaning: sigma_DASHI(50 <= M < 76, bin) / sigma_DASHI(76 <= M < 106, bin)"
        ∷ "the hook must be fixed before comparison-law evaluation and must not read the t43 observed Ratio column as its prediction"
        ∷ []
    ; remainingGaps =
        canonicalHEPDataT43PredictionAPIRemainingGaps
    ; remainingGapsAreCanonical =
        refl
    ; boundary =
        canonicalHEPDataT43PredictionAPIBoundaries
    ; boundaryIsCanonical =
        refl
    ; futureReceiptBlocked =
        acceptedT43PredictionAPIReceiptImpossibleHere
    }

canonicalHEPDataT43PredictionAPIRouteStatus :
  HEPDataT43PredictionAPIRouteStatus
canonicalHEPDataT43PredictionAPIRouteStatus =
  HEPDataT43PredictionAPIRouteDiagnostic.status
    canonicalHEPDataT43PredictionAPIRouteDiagnostic
