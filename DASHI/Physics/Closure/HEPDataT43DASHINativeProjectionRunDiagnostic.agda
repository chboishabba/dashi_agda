module DASHI.Physics.Closure.HEPDataT43DASHINativeProjectionRunDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataComparisonLawReceiptRequest as R31
import DASHI.Physics.Closure.HEPDataPredictionFreezeIdentityDiagnostic as R26
import DASHI.Physics.Closure.HEPDataT43DASHINativeProjectionReceipt as R36

------------------------------------------------------------------------
-- HEP-R37: dirty diagnostic t43 projection run with sigma_DASHI.
--
-- HEP-R36 supplies a runner-callable internal sigma_DASHI construction hook.
-- This module records the first diagnostic execution of that hook against the
-- checksum-bound t43/t44 artifacts:
--
--   python3 scripts/run_t43_projection.py
--     --freeze-hash HEP-R37-dirty-diagnostic
--     --prediction-api DASHI.Physics.Prediction.sigma_dashi:predict_ratio
--     --output /tmp/t43_projection_hep_r37_dirty.json
--
-- The run emitted projectionComplete = true for 18 bins, but it is not an
-- accepted projection receipt because the freeze hash is synthetic and the
-- worktree is dirty.  It also does not compute or accept a comparison law.

data HEPDataT43DASHINativeProjectionRunStatus : Set where
  dirtyDiagnosticProjectionCompleteNonPromoting :
    HEPDataT43DASHINativeProjectionRunStatus

data HEPDataT43DASHINativeProjectionRunArtifactField : Set where
  diagnosticArtifactPath :
    HEPDataT43DASHINativeProjectionRunArtifactField
  diagnosticFileSHA256 :
    HEPDataT43DASHINativeProjectionRunArtifactField
  projectionDigest :
    HEPDataT43DASHINativeProjectionRunArtifactField
  syntheticFreezeHash :
    HEPDataT43DASHINativeProjectionRunArtifactField
  predictionAPICallable :
    HEPDataT43DASHINativeProjectionRunArtifactField
  projectionCompleteTrue :
    HEPDataT43DASHINativeProjectionRunArtifactField
  eighteenBinBinding :
    HEPDataT43DASHINativeProjectionRunArtifactField
  firstBinDiagnosticValues :
    HEPDataT43DASHINativeProjectionRunArtifactField

canonicalHEPDataT43DASHINativeProjectionRunArtifactFields :
  List HEPDataT43DASHINativeProjectionRunArtifactField
canonicalHEPDataT43DASHINativeProjectionRunArtifactFields =
  diagnosticArtifactPath
  ∷ diagnosticFileSHA256
  ∷ projectionDigest
  ∷ syntheticFreezeHash
  ∷ predictionAPICallable
  ∷ projectionCompleteTrue
  ∷ eighteenBinBinding
  ∷ firstBinDiagnosticValues
  ∷ []

data HEPDataT43DASHINativeProjectionRunRemainingBlocker : Set where
  cleanPredictionFixedAtMissing :
    HEPDataT43DASHINativeProjectionRunRemainingBlocker
  acceptedProjectionArtifactDigestMissing :
    HEPDataT43DASHINativeProjectionRunRemainingBlocker
  covarianceAwareChi2Missing :
    HEPDataT43DASHINativeProjectionRunRemainingBlocker
  comparisonLawReceiptMissing :
    HEPDataT43DASHINativeProjectionRunRemainingBlocker
  empiricalAdequacyReceiptMissing :
    HEPDataT43DASHINativeProjectionRunRemainingBlocker

canonicalHEPDataT43DASHINativeProjectionRunRemainingBlockers :
  List HEPDataT43DASHINativeProjectionRunRemainingBlocker
canonicalHEPDataT43DASHINativeProjectionRunRemainingBlockers =
  cleanPredictionFixedAtMissing
  ∷ acceptedProjectionArtifactDigestMissing
  ∷ covarianceAwareChi2Missing
  ∷ comparisonLawReceiptMissing
  ∷ empiricalAdequacyReceiptMissing
  ∷ []

data HEPDataT43DASHINativeProjectionRunBoundary : Set where
  noAcceptedFreezeHere :
    HEPDataT43DASHINativeProjectionRunBoundary
  noAcceptedProjectionReceiptHere :
    HEPDataT43DASHINativeProjectionRunBoundary
  noChi2ClaimHere :
    HEPDataT43DASHINativeProjectionRunBoundary
  noComparisonLawHere :
    HEPDataT43DASHINativeProjectionRunBoundary
  noEmpiricalAdequacyHere :
    HEPDataT43DASHINativeProjectionRunBoundary
  noW3W4W5W8PromotionHere :
    HEPDataT43DASHINativeProjectionRunBoundary

canonicalHEPDataT43DASHINativeProjectionRunBoundaries :
  List HEPDataT43DASHINativeProjectionRunBoundary
canonicalHEPDataT43DASHINativeProjectionRunBoundaries =
  noAcceptedFreezeHere
  ∷ noAcceptedProjectionReceiptHere
  ∷ noChi2ClaimHere
  ∷ noComparisonLawHere
  ∷ noEmpiricalAdequacyHere
  ∷ noW3W4W5W8PromotionHere
  ∷ []

data HEPDataAcceptedT43DASHINativeProjectionRunReceipt : Set where

acceptedT43DASHINativeProjectionRunReceiptImpossibleHere :
  HEPDataAcceptedT43DASHINativeProjectionRunReceipt →
  ⊥
acceptedT43DASHINativeProjectionRunReceiptImpossibleHere ()

record HEPDataT43DASHINativeProjectionRunDiagnostic : Setω where
  field
    status :
      HEPDataT43DASHINativeProjectionRunStatus

    projectionConstruction :
      R36.HEPDataT43DASHINativeProjectionReceiptRequestSurface

    freezeIdentityDiagnostic :
      R26.HEPDataPredictionFreezeIdentityDiagnostic

    comparisonLawReceiptRequest :
      R31.HEPDataComparisonLawReceiptRequest

    projectionComplete :
      Bool

    projectionCompleteIsTrue :
      projectionComplete ≡ true

    acceptedProjectionRunReceiptExistsHere :
      Bool

    acceptedProjectionRunReceiptExistsHereIsFalse :
      acceptedProjectionRunReceiptExistsHere ≡ false

    diagnosticArtifactPathString :
      String

    diagnosticFileSHA256String :
      String

    projectionDigestString :
      String

    syntheticFreezeHashString :
      String

    predictionAPICallableString :
      String

    nBins :
      Nat

    nBinsIs18 :
      nBins ≡ 18

    firstBinSummary :
      List String

    artifactFields :
      List HEPDataT43DASHINativeProjectionRunArtifactField

    artifactFieldsAreCanonical :
      artifactFields
      ≡
      canonicalHEPDataT43DASHINativeProjectionRunArtifactFields

    remainingBlockers :
      List HEPDataT43DASHINativeProjectionRunRemainingBlocker

    remainingBlockersAreCanonical :
      remainingBlockers
      ≡
      canonicalHEPDataT43DASHINativeProjectionRunRemainingBlockers

    boundaries :
      List HEPDataT43DASHINativeProjectionRunBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataT43DASHINativeProjectionRunBoundaries

    futureAcceptedReceiptBlocked :
      HEPDataAcceptedT43DASHINativeProjectionRunReceipt →
      ⊥

canonicalHEPDataT43DASHINativeProjectionRunDiagnostic :
  HEPDataT43DASHINativeProjectionRunDiagnostic
canonicalHEPDataT43DASHINativeProjectionRunDiagnostic =
  record
    { status =
        dirtyDiagnosticProjectionCompleteNonPromoting
    ; projectionConstruction =
        R36.canonicalHEPDataT43DASHINativeProjectionReceiptRequestSurface
    ; freezeIdentityDiagnostic =
        R26.canonicalHEPDataPredictionFreezeIdentityDiagnostic
    ; comparisonLawReceiptRequest =
        R31.canonicalHEPDataComparisonLawReceiptRequest
    ; projectionComplete =
        true
    ; projectionCompleteIsTrue =
        refl
    ; acceptedProjectionRunReceiptExistsHere =
        false
    ; acceptedProjectionRunReceiptExistsHereIsFalse =
        refl
    ; diagnosticArtifactPathString =
        "/tmp/t43_projection_hep_r37_dirty.json"
    ; diagnosticFileSHA256String =
        "aeab81212b9f341f14d2e7147b4fd3dd64f4fa7d78a4c14beabd1518d853229c"
    ; projectionDigestString =
        "175c4872bd0db2cf108456c62e4c01295333af3c3aec186f07b4a2832cb4d8a6"
    ; syntheticFreezeHashString =
        "HEP-R37-dirty-diagnostic"
    ; predictionAPICallableString =
        "DASHI.Physics.Prediction.sigma_dashi:predict_ratio"
    ; nBins =
        18
    ; nBinsIs18 =
        refl
    ; firstBinSummary =
        "bin0 phiStarLow=0.0 phiStarHigh=0.004"
        ∷ "R_dashi=0.9234826533771504"
        ∷ "R_data=0.036689"
        ∷ "residual=0.8867936533771504"
        ∷ "These values are diagnostic only and do not construct chi2 or comparison law"
        ∷ []
    ; artifactFields =
        canonicalHEPDataT43DASHINativeProjectionRunArtifactFields
    ; artifactFieldsAreCanonical =
        refl
    ; remainingBlockers =
        canonicalHEPDataT43DASHINativeProjectionRunRemainingBlockers
    ; remainingBlockersAreCanonical =
        refl
    ; boundaries =
        canonicalHEPDataT43DASHINativeProjectionRunBoundaries
    ; boundariesAreCanonical =
        refl
    ; futureAcceptedReceiptBlocked =
        acceptedT43DASHINativeProjectionRunReceiptImpossibleHere
    }

canonicalHEPDataT43DASHINativeProjectionRunStatus :
  HEPDataT43DASHINativeProjectionRunStatus
canonicalHEPDataT43DASHINativeProjectionRunStatus =
  HEPDataT43DASHINativeProjectionRunDiagnostic.status
    canonicalHEPDataT43DASHINativeProjectionRunDiagnostic
