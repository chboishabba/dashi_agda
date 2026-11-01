module DASHI.Physics.Closure.W4PhysicalCalibrationProviderAttempt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptRequestPack as Request
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as Gate
import DASHI.Physics.Closure.W4PhysicalCalibrationRouteNarrowing as Route

------------------------------------------------------------------------
-- W4 provider-calibration attempt.
--
-- This is a typed diagnostic, not a positive external receipt.  The current
-- repo keeps Candidate256PhysicalCalibrationAuthorityToken constructorless,
-- so any attempted Candidate256PhysicalCalibrationExternalReceipt is blocked
-- before unit, calibration-map, factorization, or dimensional-law fields can
-- legitimately promote the Candidate256 surrogate.

data W4PhysicalCalibrationProviderAttemptKind : Set where
  diagnosticOnlyAwaitingExternalAuthority :
    W4PhysicalCalibrationProviderAttemptKind

record W4PhysicalCalibrationProviderAttempt : Setω where
  field
    requestPack :
      Request.W4PhysicalCalibrationExternalReceiptRequestPack

    attemptKind :
      W4PhysicalCalibrationProviderAttemptKind

    currentExternalStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    currentRouteStatus :
      Route.W4PhysicalCalibrationRouteNarrowingCurrentStatus

    blockedExternalFields :
      List External.Candidate256PhysicalCalibrationExternalBlockedField

    blockedExternalFieldsAreCanonical :
      blockedExternalFields
      ≡
      External.canonicalCandidate256PhysicalCalibrationExternalBlockedFields

    missingRouteIngredients :
      List Route.W4PhysicalCalibrationRouteIngredient

    missingRouteIngredientsAreCanonical :
      missingRouteIngredients
      ≡
      Route.w4PhysicalCalibrationRouteNarrowedIngredients

    authorityTokenImpossibleHere :
      Gate.Candidate256PhysicalCalibrationAuthorityToken →
      ⊥

    externalReceiptImpossibleHere :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    legitimateReceiptConstructionBlocked :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    exactMissingReceiptFields :
      List String

    nonPromotionBoundary :
      List String

    providerDiagnostic :
      List String

canonicalW4PhysicalCalibrationProviderAttempt :
  W4PhysicalCalibrationProviderAttempt
canonicalW4PhysicalCalibrationProviderAttempt =
  record
    { requestPack =
        Request.canonicalW4PhysicalCalibrationExternalReceiptRequestPack
    ; attemptKind =
        diagnosticOnlyAwaitingExternalAuthority
    ; currentExternalStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; currentRouteStatus =
        Route.canonicalW4PhysicalCalibrationRouteNarrowingCurrentStatus
    ; blockedExternalFields =
        External.canonicalCandidate256PhysicalCalibrationExternalBlockedFields
    ; blockedExternalFieldsAreCanonical =
        refl
    ; missingRouteIngredients =
        Route.w4PhysicalCalibrationRouteNarrowedIngredients
    ; missingRouteIngredientsAreCanonical =
        refl
    ; authorityTokenImpossibleHere =
        External.candidate256PhysicalCalibrationAuthorityTokenImpossibleHere
    ; externalReceiptImpossibleHere =
        External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    ; legitimateReceiptConstructionBlocked =
        External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    ; exactMissingReceiptFields =
        Request.W4PhysicalCalibrationProviderPayloadRequest.exactMissingReceiptFields
          Request.canonicalW4PhysicalCalibrationProviderPayloadRequest
    ; nonPromotionBoundary =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.noPromotionBoundary
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; providerDiagnostic =
        "Diagnostic only: no Candidate256PhysicalCalibrationExternalReceipt is constructed"
        ∷ "The blocker is the constructorless Candidate256PhysicalCalibrationAuthorityToken"
        ∷ "The current Nat-valued Candidate256 surrogate remains dimensionless and non-promoting"
        ∷ "A legitimate W4 receipt still needs external authority, physical units, Nat-to-unit calibration, quotient-scale factorization, and dimensional preservation"
        ∷ []
    }

canonicalW4PhysicalCalibrationProviderAttemptIsDiagnostic :
  W4PhysicalCalibrationProviderAttempt.attemptKind
    canonicalW4PhysicalCalibrationProviderAttempt
  ≡
  diagnosticOnlyAwaitingExternalAuthority
canonicalW4PhysicalCalibrationProviderAttemptIsDiagnostic =
  refl

canonicalW4PhysicalCalibrationProviderAttemptBlocksReceipt :
  External.Candidate256PhysicalCalibrationExternalReceipt →
  ⊥
canonicalW4PhysicalCalibrationProviderAttemptBlocksReceipt =
  W4PhysicalCalibrationProviderAttempt.legitimateReceiptConstructionBlocked
    canonicalW4PhysicalCalibrationProviderAttempt
