module DASHI.Physics.Closure.HEPDataT43ProjectionRunnerImplementationAttempt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataRatioTableArtifactReceipt as R28
import DASHI.Physics.Closure.HEPDataT43ProjectionRunnerContract as R29
import DASHI.Physics.Closure.HEPDataPredictionFreezePolicyRequest as R30

------------------------------------------------------------------------
-- HEP-R32: fail-closed t43 projection runner implementation attempt.
--
-- This module records the concrete script surface for HEP-R29/R30.  The
-- runner can verify the checksum-bound t43/t44 artifacts and emit a
-- diagnostic JSON artifact, but it is not an accepted DASHI projection runner
-- until the real phi-star ratio prediction entry point is wired and a clean
-- predictionFixedAt receipt exists.

data HEPDataT43ProjectionRunnerImplementationStatus : Set where
  failClosedRunnerImplementedPredictionMissing :
    HEPDataT43ProjectionRunnerImplementationStatus

data HEPDataT43ProjectionRunnerScriptArtifact : Set where
  runT43ProjectionPy :
    HEPDataT43ProjectionRunnerScriptArtifact
  assertCleanWorktreeSh :
    HEPDataT43ProjectionRunnerScriptArtifact

canonicalHEPDataT43ProjectionRunnerScriptArtifacts :
  List HEPDataT43ProjectionRunnerScriptArtifact
canonicalHEPDataT43ProjectionRunnerScriptArtifacts =
  runT43ProjectionPy
  ∷ assertCleanWorktreeSh
  ∷ []

data HEPDataT43ProjectionRunnerCapability : Set where
  verifiesT43Digest :
    HEPDataT43ProjectionRunnerCapability
  verifiesT44Digest :
    HEPDataT43ProjectionRunnerCapability
  parsesRatioBins :
    HEPDataT43ProjectionRunnerCapability
  parsesCovarianceShape :
    HEPDataT43ProjectionRunnerCapability
  writesIncompleteProjectionArtifact :
    HEPDataT43ProjectionRunnerCapability
  exitsDistinctlyWhenPredictionMissing :
    HEPDataT43ProjectionRunnerCapability

canonicalHEPDataT43ProjectionRunnerCapabilities :
  List HEPDataT43ProjectionRunnerCapability
canonicalHEPDataT43ProjectionRunnerCapabilities =
  verifiesT43Digest
  ∷ verifiesT44Digest
  ∷ parsesRatioBins
  ∷ parsesCovarianceShape
  ∷ writesIncompleteProjectionArtifact
  ∷ exitsDistinctlyWhenPredictionMissing
  ∷ []

data HEPDataT43ProjectionRunnerRemainingGap : Set where
  missingAcceptedCleanPredictionFixedAt :
    HEPDataT43ProjectionRunnerRemainingGap
  missingRealDASHIPhiStarRatioPrediction :
    HEPDataT43ProjectionRunnerRemainingGap
  missingProjectionCompleteTrueArtifact :
    HEPDataT43ProjectionRunnerRemainingGap
  missingCovarianceAwareChi2Receipt :
    HEPDataT43ProjectionRunnerRemainingGap
  missingComparisonLawReceipt :
    HEPDataT43ProjectionRunnerRemainingGap

canonicalHEPDataT43ProjectionRunnerRemainingGaps :
  List HEPDataT43ProjectionRunnerRemainingGap
canonicalHEPDataT43ProjectionRunnerRemainingGaps =
  missingAcceptedCleanPredictionFixedAt
  ∷ missingRealDASHIPhiStarRatioPrediction
  ∷ missingProjectionCompleteTrueArtifact
  ∷ missingCovarianceAwareChi2Receipt
  ∷ missingComparisonLawReceipt
  ∷ []

data HEPDataT43ProjectionRunnerImplementationBoundary : Set where
  noAcceptedPredictionFixedAtHere :
    HEPDataT43ProjectionRunnerImplementationBoundary
  noProjectionCompleteClaim :
    HEPDataT43ProjectionRunnerImplementationBoundary
  noChi2Claim :
    HEPDataT43ProjectionRunnerImplementationBoundary
  noComparisonLawClaim :
    HEPDataT43ProjectionRunnerImplementationBoundary
  noW3W4W5W8Promotion :
    HEPDataT43ProjectionRunnerImplementationBoundary

canonicalHEPDataT43ProjectionRunnerImplementationBoundaries :
  List HEPDataT43ProjectionRunnerImplementationBoundary
canonicalHEPDataT43ProjectionRunnerImplementationBoundaries =
  noAcceptedPredictionFixedAtHere
  ∷ noProjectionCompleteClaim
  ∷ noChi2Claim
  ∷ noComparisonLawClaim
  ∷ noW3W4W5W8Promotion
  ∷ []

data HEPDataAcceptedProjectionRunnerReceipt : Set where

acceptedProjectionRunnerReceiptImpossibleHere :
  HEPDataAcceptedProjectionRunnerReceipt →
  ⊥
acceptedProjectionRunnerReceiptImpossibleHere ()

record HEPDataT43ProjectionRunnerImplementationAttempt : Setω where
  field
    status :
      HEPDataT43ProjectionRunnerImplementationStatus

    artifactReceipt :
      R28.HEPDataRatioTableArtifactReceipt

    runnerContract :
      R29.HEPDataT43ProjectionRunnerContract

    freezePolicy :
      R30.HEPDataPredictionFreezePolicyRequest

    scripts :
      List HEPDataT43ProjectionRunnerScriptArtifact

    scriptsAreCanonical :
      scripts ≡ canonicalHEPDataT43ProjectionRunnerScriptArtifacts

    scriptPaths :
      List String

    capabilities :
      List HEPDataT43ProjectionRunnerCapability

    capabilitiesAreCanonical :
      capabilities ≡ canonicalHEPDataT43ProjectionRunnerCapabilities

    t43Digest :
      String

    t43DigestMatchesR28 :
      t43Digest
      ≡
      "0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b"

    t44Digest :
      String

    t44DigestMatchesR28 :
      t44Digest
      ≡
      "3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b"

    projectionComplete :
      Bool

    projectionCompleteIsFalse :
      projectionComplete ≡ false

    acceptedProjectionRunnerReceiptExistsHere :
      Bool

    acceptedProjectionRunnerReceiptExistsHereIsFalse :
      acceptedProjectionRunnerReceiptExistsHere ≡ false

    remainingGaps :
      List HEPDataT43ProjectionRunnerRemainingGap

    remainingGapsAreCanonical :
      remainingGaps ≡ canonicalHEPDataT43ProjectionRunnerRemainingGaps

    nonPromotionBoundary :
      List HEPDataT43ProjectionRunnerImplementationBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalHEPDataT43ProjectionRunnerImplementationBoundaries

    futureReceiptBlocked :
      HEPDataAcceptedProjectionRunnerReceipt →
      ⊥

canonicalHEPDataT43ProjectionRunnerImplementationAttempt :
  HEPDataT43ProjectionRunnerImplementationAttempt
canonicalHEPDataT43ProjectionRunnerImplementationAttempt =
  record
    { status =
        failClosedRunnerImplementedPredictionMissing
    ; artifactReceipt =
        R28.canonicalHEPDataRatioTableArtifactReceipt
    ; runnerContract =
        R29.canonicalHEPDataT43ProjectionRunnerContract
    ; freezePolicy =
        R30.canonicalHEPDataPredictionFreezePolicyRequest
    ; scripts =
        canonicalHEPDataT43ProjectionRunnerScriptArtifacts
    ; scriptsAreCanonical =
        refl
    ; scriptPaths =
        "scripts/run_t43_projection.py"
        ∷ "scripts/assert_clean_worktree.sh"
        ∷ []
    ; capabilities =
        canonicalHEPDataT43ProjectionRunnerCapabilities
    ; capabilitiesAreCanonical =
        refl
    ; t43Digest =
        "0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b"
    ; t43DigestMatchesR28 =
        refl
    ; t44Digest =
        "3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b"
    ; t44DigestMatchesR28 =
        refl
    ; projectionComplete =
        false
    ; projectionCompleteIsFalse =
        refl
    ; acceptedProjectionRunnerReceiptExistsHere =
        false
    ; acceptedProjectionRunnerReceiptExistsHereIsFalse =
        refl
    ; remainingGaps =
        canonicalHEPDataT43ProjectionRunnerRemainingGaps
    ; remainingGapsAreCanonical =
        refl
    ; nonPromotionBoundary =
        canonicalHEPDataT43ProjectionRunnerImplementationBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; futureReceiptBlocked =
        acceptedProjectionRunnerReceiptImpossibleHere
    }

canonicalHEPDataT43ProjectionRunnerImplementationStatus :
  HEPDataT43ProjectionRunnerImplementationStatus
canonicalHEPDataT43ProjectionRunnerImplementationStatus =
  HEPDataT43ProjectionRunnerImplementationAttempt.status
    canonicalHEPDataT43ProjectionRunnerImplementationAttempt
