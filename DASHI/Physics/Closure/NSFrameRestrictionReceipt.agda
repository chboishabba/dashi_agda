module DASHI.Physics.Closure.NSFrameRestrictionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NegativeFrameBoundRouteReceipt as Negative

------------------------------------------------------------------------
-- NS W2 frame analysis: restricted vorticity/zero-mean candidate.

data NSFrameRestrictionDomain : Set where
  zeroMeanVelocitySector :
    NSFrameRestrictionDomain

  divergenceFreeLeraySector :
    NSFrameRestrictionDomain

  vorticitySector :
    NSFrameRestrictionDomain

canonicalNSFrameRestrictionDomains :
  List NSFrameRestrictionDomain
canonicalNSFrameRestrictionDomains =
  zeroMeanVelocitySector
  ∷ divergenceFreeLeraySector
  ∷ vorticitySector
  ∷ []

data NSFrameRestrictionStatus : Set where
  unrestrictedWaveletOnlyFrameRejected :
    NSFrameRestrictionStatus

  vorticityZeroMeanRestrictedFrameCandidate :
    NSFrameRestrictionStatus

  restrictedFrameProofOpen :
    NSFrameRestrictionStatus

  clayRegularityPromotionFalse :
    NSFrameRestrictionStatus

canonicalNSFrameRestrictionStatus : List NSFrameRestrictionStatus
canonicalNSFrameRestrictionStatus =
  unrestrictedWaveletOnlyFrameRejected
  ∷ vorticityZeroMeanRestrictedFrameCandidate
  ∷ restrictedFrameProofOpen
  ∷ clayRegularityPromotionFalse
  ∷ []

data NSFrameRestrictionBlocker : Set where
  missingZeroMeanCompletenessProof :
    NSFrameRestrictionBlocker

  missingVorticityEquivalentNormProof :
    NSFrameRestrictionBlocker

  missingRestrictedGramPositiveLowerBound :
    NSFrameRestrictionBlocker

  missingContinuumNSRegularityLift :
    NSFrameRestrictionBlocker

canonicalNSFrameRestrictionBlockers :
  List NSFrameRestrictionBlocker
canonicalNSFrameRestrictionBlockers =
  missingZeroMeanCompletenessProof
  ∷ missingVorticityEquivalentNormProof
  ∷ missingRestrictedGramPositiveLowerBound
  ∷ missingContinuumNSRegularityLift
  ∷ []

data NSFrameRestrictionPromotionReceipt : Set where

nsFrameRestrictionPromotionImpossibleHere :
  NSFrameRestrictionPromotionReceipt →
  ⊥
nsFrameRestrictionPromotionImpossibleHere ()

nsFrameRestrictionDiagnostic : String
nsFrameRestrictionDiagnostic =
  "NS frame restriction diagnostic: the unrestricted Haar wavelet-only union is not a frame on constants; the vorticity/zero-mean restricted frame is candidate/open and carries no Clay or Navier-Stokes regularity promotion"

record NSFrameRestrictionReceipt : Setω where
  field
    negativeRouteReceipt :
      Negative.NegativeFrameBoundRouteReceipt

    unrestrictedFrameOnConstantsRejected :
      Negative.fullHaarWaveletOnlyUnionFrameOnConstants
        negativeRouteReceipt
      ≡
      false

    candidateDepth :
      Nat

    domains :
      List NSFrameRestrictionDomain

    domainsAreCanonical :
      domains ≡ canonicalNSFrameRestrictionDomains

    status :
      List NSFrameRestrictionStatus

    statusIsCanonical :
      status ≡ canonicalNSFrameRestrictionStatus

    diagnostic :
      String

    diagnosticIsCanonical :
      diagnostic ≡ nsFrameRestrictionDiagnostic

    zeroMeanRestrictionRecorded :
      Bool

    zeroMeanRestrictionRecordedIsTrue :
      zeroMeanRestrictionRecorded ≡ true

    vorticityRestrictionRecorded :
      Bool

    vorticityRestrictionRecordedIsTrue :
      vorticityRestrictionRecorded ≡ true

    restrictedFrameCandidateOpen :
      Bool

    restrictedFrameCandidateOpenIsTrue :
      restrictedFrameCandidateOpen ≡ true

    restrictedFrameBoundProved :
      Bool

    restrictedFrameBoundProvedIsFalse :
      restrictedFrameBoundProved ≡ false

    continuumNavierStokesRegularityPromoted :
      Bool

    continuumNavierStokesRegularityPromotedIsFalse :
      continuumNavierStokesRegularityPromoted ≡ false

    clayRegularityPromoted :
      Bool

    clayRegularityPromotedIsFalse :
      clayRegularityPromoted ≡ false

    blockers :
      List NSFrameRestrictionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSFrameRestrictionBlockers

    promotionReceipts :
      List NSFrameRestrictionPromotionReceipt

    promotionReceiptsAreEmpty :
      promotionReceipts ≡ []

    receiptBoundary :
      List String

open NSFrameRestrictionReceipt public

canonicalNSFrameRestrictionReceipt :
  NSFrameRestrictionReceipt
canonicalNSFrameRestrictionReceipt =
  record
    { negativeRouteReceipt =
        Negative.canonicalNegativeFrameBoundRouteReceipt
    ; unrestrictedFrameOnConstantsRejected =
        refl
    ; candidateDepth =
        0
    ; domains =
        canonicalNSFrameRestrictionDomains
    ; domainsAreCanonical =
        refl
    ; status =
        canonicalNSFrameRestrictionStatus
    ; statusIsCanonical =
        refl
    ; diagnostic =
        nsFrameRestrictionDiagnostic
    ; diagnosticIsCanonical =
        refl
    ; zeroMeanRestrictionRecorded =
        true
    ; zeroMeanRestrictionRecordedIsTrue =
        refl
    ; vorticityRestrictionRecorded =
        true
    ; vorticityRestrictionRecordedIsTrue =
        refl
    ; restrictedFrameCandidateOpen =
        true
    ; restrictedFrameCandidateOpenIsTrue =
        refl
    ; restrictedFrameBoundProved =
        false
    ; restrictedFrameBoundProvedIsFalse =
        refl
    ; continuumNavierStokesRegularityPromoted =
        false
    ; continuumNavierStokesRegularityPromotedIsFalse =
        refl
    ; clayRegularityPromoted =
        false
    ; clayRegularityPromotedIsFalse =
        refl
    ; blockers =
        canonicalNSFrameRestrictionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionReceipts =
        []
    ; promotionReceiptsAreEmpty =
        refl
    ; receiptBoundary =
        "This receipt narrows the viable route to zero-mean/vorticity-restricted analysis"
        ∷ "The restricted frame remains candidate/open"
        ∷ "No continuum Navier-Stokes regularity or Clay promotion is constructed"
        ∷ []
    }

nsFrameRestrictionDoesNotPromoteClay :
  clayRegularityPromoted canonicalNSFrameRestrictionReceipt ≡ false
nsFrameRestrictionDoesNotPromoteClay =
  refl
