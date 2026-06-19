module DASHI.Physics.Closure.NSBiaxialCancellationIdentityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Fail-closed receipt for the biaxial cancellation identity.
--
-- This module records the exact algebraic identity
--
--   <S omega, e2> = lambda2 <omega, e2>
--
-- and the biaxial boundary cancellation on
--
--   ∂Ω_K = { lambda2 = 0 }.
--
-- The receipt is explicit and non-promoting: the identity is recorded as
-- a checked surface, the boundary cancellation is recorded as a checked
-- surface, and Clay/global promotion remain false.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSBiaxialCancellationIdentityStatus : Set where
  checkedBiaxialCancellationReceiptRecorded :
    NSBiaxialCancellationIdentityStatus

data NSBiaxialCancellationIdentityStage : Set where
  identityRecorded :
    NSBiaxialCancellationIdentityStage
  biaxialBoundaryRecorded :
    NSBiaxialCancellationIdentityStage
  lambda2ZeroBoundaryRecorded :
    NSBiaxialCancellationIdentityStage
  exactCancellationRecorded :
    NSBiaxialCancellationIdentityStage
  clayFalseRecorded :
    NSBiaxialCancellationIdentityStage
  globalFalseRecorded :
    NSBiaxialCancellationIdentityStage

canonicalNSBiaxialCancellationIdentityStages :
  List NSBiaxialCancellationIdentityStage
canonicalNSBiaxialCancellationIdentityStages =
  identityRecorded
  ∷ biaxialBoundaryRecorded
  ∷ lambda2ZeroBoundaryRecorded
  ∷ exactCancellationRecorded
  ∷ clayFalseRecorded
  ∷ globalFalseRecorded
  ∷ []

data NSBiaxialCancellationIdentityBlocker : Set where
  identityStillOnlyRecorded :
    NSBiaxialCancellationIdentityBlocker
  biaxialBoundaryStillDiagnostic :
    NSBiaxialCancellationIdentityBlocker
  lambda2ZeroStillBoundarySurface :
    NSBiaxialCancellationIdentityBlocker
  exactCancellationStillChecked :
    NSBiaxialCancellationIdentityBlocker
  clayPromotionBlocked :
    NSBiaxialCancellationIdentityBlocker
  globalPromotionBlocked :
    NSBiaxialCancellationIdentityBlocker

canonicalNSBiaxialCancellationIdentityBlockers :
  List NSBiaxialCancellationIdentityBlocker
canonicalNSBiaxialCancellationIdentityBlockers =
  identityStillOnlyRecorded
  ∷ biaxialBoundaryStillDiagnostic
  ∷ lambda2ZeroStillBoundarySurface
  ∷ exactCancellationStillChecked
  ∷ clayPromotionBlocked
  ∷ globalPromotionBlocked
  ∷ []

identityTextValue : String
identityTextValue =
  "<S omega, e2> = lambda2 <omega, e2>"

biaxialBoundaryTextValue : String
biaxialBoundaryTextValue =
  "biaxial boundary cancellation on ∂Ω_K = { lambda2 = 0 }"

lambda2ZeroBoundaryTextValue : String
lambda2ZeroBoundaryTextValue =
  "lambda2 vanishes on the biaxial boundary surface"

exactCancellationTextValue : String
exactCancellationTextValue =
  "exact cancellation: <S omega, e2> collapses to zero when lambda2 = 0"

receiptBoundaryText : List String
receiptBoundaryText =
  "the exact identity <S omega, e2> = lambda2 <omega, e2> is recorded"
  ∷ "the biaxial boundary is recorded as ∂Ω_K = { lambda2 = 0 }"
  ∷ "the exact boundary cancellation is recorded on the lambda2 = 0 surface"
  ∷ "Clay promotion remains false"
  ∷ "global promotion remains false"
  ∷ []

record NSBiaxialCancellationIdentityReceipt : Setω where
  field
    status :
      NSBiaxialCancellationIdentityStatus
    statusIsCanonical :
      status ≡ checkedBiaxialCancellationReceiptRecorded

    stageTrail :
      List NSBiaxialCancellationIdentityStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSBiaxialCancellationIdentityStages

    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSBiaxialCancellationIdentityStages

    blockerTrail :
      List NSBiaxialCancellationIdentityBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSBiaxialCancellationIdentityBlockers

    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSBiaxialCancellationIdentityBlockers

    identityText :
      String
    identityTextIsCanonical :
      identityText ≡ identityTextValue

    biaxialBoundaryText :
      String
    biaxialBoundaryTextIsCanonical :
      biaxialBoundaryText ≡ biaxialBoundaryTextValue

    lambda2ZeroBoundaryText :
      String
    lambda2ZeroBoundaryTextIsCanonical :
      lambda2ZeroBoundaryText ≡ lambda2ZeroBoundaryTextValue

    exactCancellationText :
      String
    exactCancellationTextIsCanonical :
      exactCancellationText ≡ exactCancellationTextValue

    identitySurfaceRecorded :
      Bool
    identitySurfaceRecordedIsTrue :
      identitySurfaceRecorded ≡ true

    biaxialBoundarySurfaceRecorded :
      Bool
    biaxialBoundarySurfaceRecordedIsTrue :
      biaxialBoundarySurfaceRecorded ≡ true

    exactCancellationSurfaceRecorded :
      Bool
    exactCancellationSurfaceRecordedIsTrue :
      exactCancellationSurfaceRecorded ≡ true

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    globalPromoted :
      Bool
    globalPromotedIsFalse :
      globalPromoted ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

data NSBiaxialCancellationIdentityPromotion : Set where

nsBiaxialCancellationIdentityPromotionImpossibleHere :
  NSBiaxialCancellationIdentityPromotion → ⊥
nsBiaxialCancellationIdentityPromotionImpossibleHere ()

canonicalNSBiaxialCancellationIdentityReceipt :
  NSBiaxialCancellationIdentityReceipt
canonicalNSBiaxialCancellationIdentityReceipt =
  record
    { status =
        checkedBiaxialCancellationReceiptRecorded
    ; statusIsCanonical =
        refl
    ; stageTrail =
        canonicalNSBiaxialCancellationIdentityStages
    ; stageTrailIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSBiaxialCancellationIdentityStages
    ; stageCountIsCanonical =
        refl
    ; blockerTrail =
        canonicalNSBiaxialCancellationIdentityBlockers
    ; blockerTrailIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSBiaxialCancellationIdentityBlockers
    ; blockerCountIsCanonical =
        refl
    ; identityText =
        identityTextValue
    ; identityTextIsCanonical =
        refl
    ; biaxialBoundaryText =
        biaxialBoundaryTextValue
    ; biaxialBoundaryTextIsCanonical =
        refl
    ; lambda2ZeroBoundaryText =
        lambda2ZeroBoundaryTextValue
    ; lambda2ZeroBoundaryTextIsCanonical =
        refl
    ; exactCancellationText =
        exactCancellationTextValue
    ; exactCancellationTextIsCanonical =
        refl
    ; identitySurfaceRecorded =
        true
    ; identitySurfaceRecordedIsTrue =
        refl
    ; biaxialBoundarySurfaceRecorded =
        true
    ; biaxialBoundarySurfaceRecordedIsTrue =
        refl
    ; exactCancellationSurfaceRecorded =
        true
    ; exactCancellationSurfaceRecordedIsTrue =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; globalPromoted =
        false
    ; globalPromotedIsFalse =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    }

open NSBiaxialCancellationIdentityReceipt public

canonicalNSBiaxialCancellationIdentityStageTrailIsCanonical :
  stageTrail canonicalNSBiaxialCancellationIdentityReceipt
  ≡ canonicalNSBiaxialCancellationIdentityStages
canonicalNSBiaxialCancellationIdentityStageTrailIsCanonical =
  refl

canonicalNSBiaxialCancellationIdentityBlockerTrailIsCanonical :
  blockerTrail canonicalNSBiaxialCancellationIdentityReceipt
  ≡ canonicalNSBiaxialCancellationIdentityBlockers
canonicalNSBiaxialCancellationIdentityBlockerTrailIsCanonical =
  refl

canonicalNSBiaxialCancellationIdentityTextIsCanonical :
  identityText canonicalNSBiaxialCancellationIdentityReceipt
  ≡ identityTextValue
canonicalNSBiaxialCancellationIdentityTextIsCanonical =
  refl

canonicalNSBiaxialCancellationIdentityBoundaryTextIsCanonical :
  biaxialBoundaryText canonicalNSBiaxialCancellationIdentityReceipt
  ≡ biaxialBoundaryTextValue
canonicalNSBiaxialCancellationIdentityBoundaryTextIsCanonical =
  refl

canonicalNSBiaxialCancellationIdentityLambda2ZeroTextIsCanonical :
  lambda2ZeroBoundaryText canonicalNSBiaxialCancellationIdentityReceipt
  ≡ lambda2ZeroBoundaryTextValue
canonicalNSBiaxialCancellationIdentityLambda2ZeroTextIsCanonical =
  refl

canonicalNSBiaxialCancellationIdentityExactCancellationTextIsCanonical :
  exactCancellationText canonicalNSBiaxialCancellationIdentityReceipt
  ≡ exactCancellationTextValue
canonicalNSBiaxialCancellationIdentityExactCancellationTextIsCanonical =
  refl

canonicalNSBiaxialCancellationIdentityRecordedIsTrue :
  identitySurfaceRecorded canonicalNSBiaxialCancellationIdentityReceipt ≡ true
canonicalNSBiaxialCancellationIdentityRecordedIsTrue =
  refl

canonicalNSBiaxialCancellationIdentityBoundaryRecordedIsTrue :
  biaxialBoundarySurfaceRecorded canonicalNSBiaxialCancellationIdentityReceipt ≡ true
canonicalNSBiaxialCancellationIdentityBoundaryRecordedIsTrue =
  refl

canonicalNSBiaxialCancellationIdentityExactCancellationRecordedIsTrue :
  exactCancellationSurfaceRecorded canonicalNSBiaxialCancellationIdentityReceipt
  ≡ true
canonicalNSBiaxialCancellationIdentityExactCancellationRecordedIsTrue =
  refl

canonicalNSBiaxialCancellationIdentityClayPromotedIsFalse :
  clayPromoted canonicalNSBiaxialCancellationIdentityReceipt ≡ false
canonicalNSBiaxialCancellationIdentityClayPromotedIsFalse =
  refl

canonicalNSBiaxialCancellationIdentityGlobalPromotedIsFalse :
  globalPromoted canonicalNSBiaxialCancellationIdentityReceipt ≡ false
canonicalNSBiaxialCancellationIdentityGlobalPromotedIsFalse =
  refl
