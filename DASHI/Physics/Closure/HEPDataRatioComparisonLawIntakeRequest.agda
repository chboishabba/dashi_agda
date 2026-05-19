module DASHI.Physics.Closure.HEPDataRatioComparisonLawIntakeRequest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataPredictionFreezeProjectionRunRequest as Freeze
import DASHI.Physics.Closure.HEPDataRatioAdapterTransformReceiptRequest as Ratio
import DASHI.Physics.Closure.HEPDataRatioTableArtifactReceipt as Artifacts
import DASHI.Physics.Closure.HEPDataResidualComparisonLawRequest as Comparison

------------------------------------------------------------------------
-- HEP-R27: comparison-law intake frontier.
--
-- This module ties the selected t43/t44 ratio adapter route and the HEP-R22
-- prediction-freeze/projection-run request to the existing residual
-- comparison-law request.  It is only an intake frontier for the next
-- comparison step: comparison may begin only after checksum-bound t43/t44
-- artifacts, predictionFixedAt, projection artifact digest, and bin-binding
-- receipts exist.  HEP-R28 now supplies the checksum-bound t43/t44 artifact
-- receipt, so the remaining live blockers are predictionFixedAt, projection
-- artifact digest, bin-binding, and comparison execution.  No chi2 result,
-- comparison theorem, accepted comparison law, empirical adequacy claim,
-- authority token, or W3 promotion is constructed here.

data HEPDataRatioComparisonLawIntakeStatus : Set where
  blockedAwaitingRatioComparisonIntakeReceipts :
    HEPDataRatioComparisonLawIntakeStatus

data HEPDataRatioComparisonLawIntakeDependency : Set where
  selectedT43T44RatioAdapterRoute :
    HEPDataRatioComparisonLawIntakeDependency
  hepR22PredictionFreezeProjectionRequest :
    HEPDataRatioComparisonLawIntakeDependency
  residualComparisonLawRequest :
    HEPDataRatioComparisonLawIntakeDependency
  checksumBoundHEPR28RatioArtifacts :
    HEPDataRatioComparisonLawIntakeDependency

canonicalHEPDataRatioComparisonLawIntakeDependencies :
  List HEPDataRatioComparisonLawIntakeDependency
canonicalHEPDataRatioComparisonLawIntakeDependencies =
  selectedT43T44RatioAdapterRoute
  ∷ hepR22PredictionFreezeProjectionRequest
  ∷ residualComparisonLawRequest
  ∷ checksumBoundHEPR28RatioArtifacts
  ∷ []

data HEPDataRatioComparisonLawIntakeRequiredReceipt : Set where
  requiredT43ArtifactChecksum :
    HEPDataRatioComparisonLawIntakeRequiredReceipt
  requiredT44ArtifactChecksum :
    HEPDataRatioComparisonLawIntakeRequiredReceipt
  requiredPredictionFixedAt :
    HEPDataRatioComparisonLawIntakeRequiredReceipt
  requiredProjectionArtifactDigest :
    HEPDataRatioComparisonLawIntakeRequiredReceipt
  requiredT43T44ProjectionBinBinding :
    HEPDataRatioComparisonLawIntakeRequiredReceipt

canonicalHEPDataRatioComparisonLawIntakeRequiredReceipts :
  List HEPDataRatioComparisonLawIntakeRequiredReceipt
canonicalHEPDataRatioComparisonLawIntakeRequiredReceipts =
  requiredPredictionFixedAt
  ∷ requiredProjectionArtifactDigest
  ∷ requiredT43T44ProjectionBinBinding
  ∷ []

data HEPDataRatioComparisonLawIntakeBoundary : Set where
  noChi2ComparisonResult :
    HEPDataRatioComparisonLawIntakeBoundary
  noAcceptedComparisonLaw :
    HEPDataRatioComparisonLawIntakeBoundary
  noEmpiricalAdequacyClaim :
    HEPDataRatioComparisonLawIntakeBoundary
  noW3Promotion :
    HEPDataRatioComparisonLawIntakeBoundary

canonicalHEPDataRatioComparisonLawIntakeBoundaries :
  List HEPDataRatioComparisonLawIntakeBoundary
canonicalHEPDataRatioComparisonLawIntakeBoundaries =
  noChi2ComparisonResult
  ∷ noAcceptedComparisonLaw
  ∷ noEmpiricalAdequacyClaim
  ∷ noW3Promotion
  ∷ []

data HEPDataRatioComparisonLawIntakeReceipt : Set where

ratioComparisonLawIntakeReceiptImpossibleHere :
  HEPDataRatioComparisonLawIntakeReceipt →
  ⊥
ratioComparisonLawIntakeReceiptImpossibleHere ()

record HEPDataRatioComparisonLawIntakeRequest : Setω where
  field
    status :
      HEPDataRatioComparisonLawIntakeStatus

    ratioAdapterRequest :
      Ratio.HEPDataRatioAdapterTransformReceiptRequest

    selectedRouteIsT43T44 :
      Ratio.HEPDataRatioAdapterTransformReceiptRequest.selectedRoute
        ratioAdapterRequest
      ≡
      Ratio.selectedRatioT43T44Dimensionless50To76Over76To106

    predictionFreezeProjectionRequest :
      Freeze.HEPDataPredictionFreezeProjectionRunRequestSurface

    residualComparisonLawRequestDiagnostic :
      Comparison.HEPDataResidualComparisonLawRequestDiagnostic

    ratioArtifactReceipt :
      Artifacts.HEPDataRatioTableArtifactReceipt

    dependencies :
      List HEPDataRatioComparisonLawIntakeDependency

    dependenciesAreCanonical :
      dependencies
      ≡
      canonicalHEPDataRatioComparisonLawIntakeDependencies

    requiredReceiptsBeforeComparison :
      List HEPDataRatioComparisonLawIntakeRequiredReceipt

    requiredReceiptsBeforeComparisonAreCanonical :
      requiredReceiptsBeforeComparison
      ≡
      canonicalHEPDataRatioComparisonLawIntakeRequiredReceipts

    exactReceiptNames :
      List String

    comparisonMayBeginOnlyAfter :
      List String

    nonPromotionBoundaries :
      List HEPDataRatioComparisonLawIntakeBoundary

    nonPromotionBoundariesAreCanonical :
      nonPromotionBoundaries
      ≡
      canonicalHEPDataRatioComparisonLawIntakeBoundaries

    futureReceiptBlocked :
      HEPDataRatioComparisonLawIntakeReceipt →
      ⊥

canonicalHEPDataRatioComparisonLawIntakeRequest :
  HEPDataRatioComparisonLawIntakeRequest
canonicalHEPDataRatioComparisonLawIntakeRequest =
  record
    { status =
        blockedAwaitingRatioComparisonIntakeReceipts
    ; ratioAdapterRequest =
        Ratio.canonicalHEPDataRatioAdapterTransformReceiptRequest
    ; selectedRouteIsT43T44 =
        refl
    ; predictionFreezeProjectionRequest =
        Freeze.canonicalHEPDataPredictionFreezeProjectionRunRequestSurface
    ; residualComparisonLawRequestDiagnostic =
        Comparison.canonicalHEPDataResidualComparisonLawRequestDiagnostic
    ; ratioArtifactReceipt =
        Artifacts.canonicalHEPDataRatioTableArtifactReceipt
    ; dependencies =
        canonicalHEPDataRatioComparisonLawIntakeDependencies
    ; dependenciesAreCanonical =
        refl
    ; requiredReceiptsBeforeComparison =
        canonicalHEPDataRatioComparisonLawIntakeRequiredReceipts
    ; requiredReceiptsBeforeComparisonAreCanonical =
        refl
    ; exactReceiptNames =
        "t43ArtifactChecksum : supplied by HEP-R28 artifact receipt"
        ∷ "t44ArtifactChecksum : supplied by HEP-R28 artifact receipt"
        ∷ "predictionFixedAt : immutable commit/hash/time label for the frozen DASHI prediction"
        ∷ "projectionArtifactDigest : digest of the theorem-side projection artifact consumed by comparison"
        ∷ "binBinding : exact binding between t43 ratio bins, t44 covariance bins, and projected DASHI bins"
        ∷ []
    ; comparisonMayBeginOnlyAfter =
        "Comparison cannot begin from the selected t43/t44 ratio adapter route alone"
        ∷ "Comparison cannot begin from the HEP-R22 freeze/projection request alone"
        ∷ "Comparison cannot begin from the residual comparison-law request alone"
        ∷ "HEP-R28 supplies t43/t44 artifact checksums; comparison still waits on predictionFixedAt, projection artifact digest, and bin-binding"
        ∷ []
    ; nonPromotionBoundaries =
        canonicalHEPDataRatioComparisonLawIntakeBoundaries
    ; nonPromotionBoundariesAreCanonical =
        refl
    ; futureReceiptBlocked =
        ratioComparisonLawIntakeReceiptImpossibleHere
    }

canonicalHEPDataRatioComparisonLawIntakeStatus :
  HEPDataRatioComparisonLawIntakeStatus
canonicalHEPDataRatioComparisonLawIntakeStatus =
  blockedAwaitingRatioComparisonIntakeReceipts

canonicalHEPDataRatioComparisonLawIntakeReceiptBlocked :
  HEPDataRatioComparisonLawIntakeReceipt →
  ⊥
canonicalHEPDataRatioComparisonLawIntakeReceiptBlocked =
  HEPDataRatioComparisonLawIntakeRequest.futureReceiptBlocked
    canonicalHEPDataRatioComparisonLawIntakeRequest
