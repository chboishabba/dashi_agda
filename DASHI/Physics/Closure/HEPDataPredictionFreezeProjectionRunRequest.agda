module DASHI.Physics.Closure.HEPDataPredictionFreezeProjectionRunRequest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataDefectProjectionDiagnostic as Projection
import DASHI.Physics.Closure.HEPDataResidualComparisonLawRequest as Comparison

------------------------------------------------------------------------
-- HEP-R22: prediction freeze / projection run request.
--
-- External HEPData anchors for the t43 ratio table and t44 covariance table
-- are now named elsewhere.  The remaining blocker is internal: freeze the
-- DASHI prediction at a commit hash and run the DASHI projection against the
-- t43 bins under a pre-registered non-collapse boundary.
--
-- This module is a receipt request surface only.  It does not run any
-- prediction, claim a prediction result, construct a projection receipt,
-- construct a comparison law, or promote W3.

data HEPDataPredictionFreezeProjectionRunStatus : Set where
  blockedAwaitingInternalPredictionFreezeAndProjectionRun :
    HEPDataPredictionFreezeProjectionRunStatus

data HEPDataPredictionFreezeProjectionRunInternalItem : Set where
  predictionFixedAtCommitHash :
    HEPDataPredictionFreezeProjectionRunInternalItem
  dashiProjectionRunAgainstT43Bins :
    HEPDataPredictionFreezeProjectionRunInternalItem

canonicalHEPDataPredictionFreezeProjectionRunInternalItems :
  List HEPDataPredictionFreezeProjectionRunInternalItem
canonicalHEPDataPredictionFreezeProjectionRunInternalItems =
  predictionFixedAtCommitHash
  ∷ dashiProjectionRunAgainstT43Bins
  ∷ []

data HEPDataPredictionFreezeProjectionRunRequiredField : Set where
  requiredCommitHash :
    HEPDataPredictionFreezeProjectionRunRequiredField
  requiredPredictionArtifactDigest :
    HEPDataPredictionFreezeProjectionRunRequiredField
  requiredT43T44BinBinding :
    HEPDataPredictionFreezeProjectionRunRequiredField
  requiredComparisonLawInput :
    HEPDataPredictionFreezeProjectionRunRequiredField
  requiredNonCollapsePreRegistrationBoundary :
    HEPDataPredictionFreezeProjectionRunRequiredField

canonicalHEPDataPredictionFreezeProjectionRunRequiredFields :
  List HEPDataPredictionFreezeProjectionRunRequiredField
canonicalHEPDataPredictionFreezeProjectionRunRequiredFields =
  requiredCommitHash
  ∷ requiredPredictionArtifactDigest
  ∷ requiredT43T44BinBinding
  ∷ requiredComparisonLawInput
  ∷ requiredNonCollapsePreRegistrationBoundary
  ∷ []

data HEPDataPredictionFreezeProjectionRunReceipt : Set where

predictionFreezeProjectionRunReceiptImpossibleHere :
  HEPDataPredictionFreezeProjectionRunReceipt →
  ⊥
predictionFreezeProjectionRunReceiptImpossibleHere ()

data HEPDataPredictionFreezeProjectionRunBoundary : Set where
  noPredictionRunPerformedHere :
    HEPDataPredictionFreezeProjectionRunBoundary
  noPredictionResultClaimedHere :
    HEPDataPredictionFreezeProjectionRunBoundary
  noProjectionReceiptConstructedHere :
    HEPDataPredictionFreezeProjectionRunBoundary
  noComparisonLawConstructedHere :
    HEPDataPredictionFreezeProjectionRunBoundary
  noW3PromotionHere :
    HEPDataPredictionFreezeProjectionRunBoundary

canonicalHEPDataPredictionFreezeProjectionRunBoundary :
  List HEPDataPredictionFreezeProjectionRunBoundary
canonicalHEPDataPredictionFreezeProjectionRunBoundary =
  noPredictionRunPerformedHere
  ∷ noPredictionResultClaimedHere
  ∷ noProjectionReceiptConstructedHere
  ∷ noComparisonLawConstructedHere
  ∷ noW3PromotionHere
  ∷ []

record HEPDataPredictionFreezeProjectionRunRequestSurface : Setω where
  field
    currentStatus :
      HEPDataPredictionFreezeProjectionRunStatus

    projectionDiagnostic :
      Projection.HEPDataDefectProjectionDiagnostic

    comparisonLawRequestDiagnostic :
      Comparison.HEPDataResidualComparisonLawRequestDiagnostic

    remainingInternalItems :
      List HEPDataPredictionFreezeProjectionRunInternalItem

    remainingInternalItemsAreCanonical :
      remainingInternalItems
      ≡
      canonicalHEPDataPredictionFreezeProjectionRunInternalItems

    requiredReceiptFields :
      List HEPDataPredictionFreezeProjectionRunRequiredField

    requiredReceiptFieldsAreCanonical :
      requiredReceiptFields
      ≡
      canonicalHEPDataPredictionFreezeProjectionRunRequiredFields

    exactRequiredReceiptFields :
      List String

    externalDataSpecifiedBoundary :
      List String

    internalMechanicsBlocker :
      List String

    nonCollapsePreRegistrationBoundary :
      List String

    nonPromotionBoundary :
      List HEPDataPredictionFreezeProjectionRunBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalHEPDataPredictionFreezeProjectionRunBoundary

    futureReceiptBlocked :
      HEPDataPredictionFreezeProjectionRunReceipt →
      ⊥

canonicalHEPDataPredictionFreezeProjectionRunRequestSurface :
  HEPDataPredictionFreezeProjectionRunRequestSurface
canonicalHEPDataPredictionFreezeProjectionRunRequestSurface =
  record
    { currentStatus =
        blockedAwaitingInternalPredictionFreezeAndProjectionRun
    ; projectionDiagnostic =
        Projection.canonicalHEPDataDefectProjectionDiagnostic
    ; comparisonLawRequestDiagnostic =
        Comparison.canonicalHEPDataResidualComparisonLawRequestDiagnostic
    ; remainingInternalItems =
        canonicalHEPDataPredictionFreezeProjectionRunInternalItems
    ; remainingInternalItemsAreCanonical =
        refl
    ; requiredReceiptFields =
        canonicalHEPDataPredictionFreezeProjectionRunRequiredFields
    ; requiredReceiptFieldsAreCanonical =
        refl
    ; exactRequiredReceiptFields =
        "predictionFixedAt : commit hash identifying the frozen DASHI prediction code and inputs"
        ∷ "predictionArtifactDigest : digest of the frozen prediction artifact before comparison to HEPData"
        ∷ "t43/t44 bin binding : exact t43 ratio bins and t44 covariance bins used by the projection run"
        ∷ "comparisonLawInput : typed input surface consumed by the residual comparison-law request"
        ∷ "nonCollapsePreRegistrationBoundary : declaration fixed before looking at projection outcomes"
        ∷ []
    ; externalDataSpecifiedBoundary =
        "HEPData t43 is the phistar mass 50-76 over mass 76-106 ratio table anchor"
        ∷ "HEPData t44 is the covariance table anchor paired to t43"
        ∷ "The remaining HEP-R22 blocker is not external table discovery"
        ∷ []
    ; internalMechanicsBlocker =
        "The current repo has not frozen a prediction at a commit hash for this request"
        ∷ "The current repo has not produced a digest-bound prediction artifact for this request"
        ∷ "The current repo has not run the DASHI projection against the t43 bins"
        ∷ "The current repo has not supplied the comparison-law input generated by such a run"
        ∷ []
    ; nonCollapsePreRegistrationBoundary =
        "Non-collapse criteria must be fixed before inspecting the projection output"
        ∷ "The pre-registration must name the bins or bin relation used to test non-collapse"
        ∷ "The pre-registration must state how the projected DASHI surface is prevented from collapsing to a constant or raw-value equality claim"
        ∷ "Changing the non-collapse criterion after the projection run does not satisfy this request"
        ∷ []
    ; nonPromotionBoundary =
        canonicalHEPDataPredictionFreezeProjectionRunBoundary
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; futureReceiptBlocked =
        predictionFreezeProjectionRunReceiptImpossibleHere
    }

canonicalHEPDataPredictionFreezeProjectionRunStatus :
  HEPDataPredictionFreezeProjectionRunStatus
canonicalHEPDataPredictionFreezeProjectionRunStatus =
  blockedAwaitingInternalPredictionFreezeAndProjectionRun

canonicalHEPDataPredictionFreezeProjectionRunReceiptBlocked :
  HEPDataPredictionFreezeProjectionRunReceipt →
  ⊥
canonicalHEPDataPredictionFreezeProjectionRunReceiptBlocked =
  HEPDataPredictionFreezeProjectionRunRequestSurface.futureReceiptBlocked
    canonicalHEPDataPredictionFreezeProjectionRunRequestSurface
