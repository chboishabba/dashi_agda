module DASHI.Physics.Closure.NegativeFrameBoundRouteReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GramMatrixSpectrumBoundReceipt as Spectrum
import DASHI.Physics.Closure.PentadicCrossTermReceipt as Pentadic

------------------------------------------------------------------------
-- NS W2 frame analysis: negative route for unrestricted lower frame bound.

data NegativeFrameRouteComponent : Set where
  nonpositiveGershgorinLowerBound :
    NegativeFrameRouteComponent

  pentadicAbsoluteSumsAboveOne :
    NegativeFrameRouteComponent

  unrestrictedHaarUnionIncludesConstants :
    NegativeFrameRouteComponent

canonicalNegativeFrameRouteComponents :
  List NegativeFrameRouteComponent
canonicalNegativeFrameRouteComponents =
  nonpositiveGershgorinLowerBound
  ∷ pentadicAbsoluteSumsAboveOne
  ∷ unrestrictedHaarUnionIncludesConstants
  ∷ []

data NegativeFrameRouteStatus : Set where
  unrestrictedFrameBoundRouteNegative :
    NegativeFrameRouteStatus

  fullHaarWaveletOnlyUnionNotFrameOnConstants :
    NegativeFrameRouteStatus

  restrictedVorticityRouteOpen :
    NegativeFrameRouteStatus

canonicalNegativeFrameRouteStatus : List NegativeFrameRouteStatus
canonicalNegativeFrameRouteStatus =
  unrestrictedFrameBoundRouteNegative
  ∷ fullHaarWaveletOnlyUnionNotFrameOnConstants
  ∷ restrictedVorticityRouteOpen
  ∷ []

data NegativeFrameRouteBlocker : Set where
  constantsInvisibleToWaveletOnlyUnion :
    NegativeFrameRouteBlocker

  noPositiveUnrestrictedLowerBound :
    NegativeFrameRouteBlocker

  restrictedZeroMeanFrameProofMissing :
    NegativeFrameRouteBlocker

canonicalNegativeFrameRouteBlockers : List NegativeFrameRouteBlocker
canonicalNegativeFrameRouteBlockers =
  constantsInvisibleToWaveletOnlyUnion
  ∷ noPositiveUnrestrictedLowerBound
  ∷ restrictedZeroMeanFrameProofMissing
  ∷ []

data NegativeFrameRoutePromotionReceipt : Set where

negativeFrameRoutePromotionImpossibleHere :
  NegativeFrameRoutePromotionReceipt →
  ⊥
negativeFrameRoutePromotionImpossibleHere ()

negativeFrameRouteDiagnostic : String
negativeFrameRouteDiagnostic =
  "negative frame-bound route: the full Haar wavelet-only union is not a frame on constants, Gershgorin is nonpositive, and pentadic absolute sums exceed 1; only a zero-mean/vorticity restriction remains candidate/open"

record NegativeFrameBoundRouteReceipt : Setω where
  field
    spectrumReceipt :
      Spectrum.GramMatrixSpectrumBoundReceipt

    gershgorinLowerBoundFailed :
      Spectrum.gershgorinLowerBoundPositive spectrumReceipt ≡ false

    pentadicReceipt :
      Pentadic.PentadicCrossTermReceipt

    pentadicSumsExceedOne :
      Pentadic.absolutePentadicSumsExceedOne pentadicReceipt ≡ true

    witnessDepth :
      Nat

    components :
      List NegativeFrameRouteComponent

    componentsAreCanonical :
      components ≡ canonicalNegativeFrameRouteComponents

    status :
      List NegativeFrameRouteStatus

    statusIsCanonical :
      status ≡ canonicalNegativeFrameRouteStatus

    diagnostic :
      String

    diagnosticIsCanonical :
      diagnostic ≡ negativeFrameRouteDiagnostic

    fullHaarWaveletOnlyUnionFrameOnConstants :
      Bool

    fullHaarWaveletOnlyUnionFrameOnConstantsIsFalse :
      fullHaarWaveletOnlyUnionFrameOnConstants ≡ false

    unrestrictedLowerFrameBoundConstructed :
      Bool

    unrestrictedLowerFrameBoundConstructedIsFalse :
      unrestrictedLowerFrameBoundConstructed ≡ false

    zeroMeanRestrictedRouteCandidate :
      Bool

    zeroMeanRestrictedRouteCandidateIsTrue :
      zeroMeanRestrictedRouteCandidate ≡ true

    zeroMeanRestrictedFrameBoundProved :
      Bool

    zeroMeanRestrictedFrameBoundProvedIsFalse :
      zeroMeanRestrictedFrameBoundProved ≡ false

    navierStokesRegularityPromoted :
      Bool

    navierStokesRegularityPromotedIsFalse :
      navierStokesRegularityPromoted ≡ false

    clayRegularityPromoted :
      Bool

    clayRegularityPromotedIsFalse :
      clayRegularityPromoted ≡ false

    blockers :
      List NegativeFrameRouteBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNegativeFrameRouteBlockers

    promotionReceipts :
      List NegativeFrameRoutePromotionReceipt

    promotionReceiptsAreEmpty :
      promotionReceipts ≡ []

    receiptBoundary :
      List String

open NegativeFrameBoundRouteReceipt public

canonicalNegativeFrameBoundRouteReceipt :
  NegativeFrameBoundRouteReceipt
canonicalNegativeFrameBoundRouteReceipt =
  record
    { spectrumReceipt =
        Spectrum.canonicalGramMatrixSpectrumBoundReceipt
    ; gershgorinLowerBoundFailed =
        refl
    ; pentadicReceipt =
        Pentadic.canonicalPentadicCrossTermReceipt
    ; pentadicSumsExceedOne =
        refl
    ; witnessDepth =
        0
    ; components =
        canonicalNegativeFrameRouteComponents
    ; componentsAreCanonical =
        refl
    ; status =
        canonicalNegativeFrameRouteStatus
    ; statusIsCanonical =
        refl
    ; diagnostic =
        negativeFrameRouteDiagnostic
    ; diagnosticIsCanonical =
        refl
    ; fullHaarWaveletOnlyUnionFrameOnConstants =
        false
    ; fullHaarWaveletOnlyUnionFrameOnConstantsIsFalse =
        refl
    ; unrestrictedLowerFrameBoundConstructed =
        false
    ; unrestrictedLowerFrameBoundConstructedIsFalse =
        refl
    ; zeroMeanRestrictedRouteCandidate =
        true
    ; zeroMeanRestrictedRouteCandidateIsTrue =
        refl
    ; zeroMeanRestrictedFrameBoundProved =
        false
    ; zeroMeanRestrictedFrameBoundProvedIsFalse =
        refl
    ; navierStokesRegularityPromoted =
        false
    ; navierStokesRegularityPromotedIsFalse =
        refl
    ; clayRegularityPromoted =
        false
    ; clayRegularityPromotedIsFalse =
        refl
    ; blockers =
        canonicalNegativeFrameRouteBlockers
    ; blockersAreCanonical =
        refl
    ; promotionReceipts =
        []
    ; promotionReceiptsAreEmpty =
        refl
    ; receiptBoundary =
        "The unrestricted lower-frame route is negative, not merely missing"
        ∷ "The full Haar wavelet-only union cannot frame constants"
        ∷ "A vorticity or zero-mean restriction is recorded only as an open candidate"
        ∷ "No NS regularity or Clay promotion is constructed"
        ∷ []
    }

negativeFrameBoundRouteDoesNotPromoteClay :
  clayRegularityPromoted canonicalNegativeFrameBoundRouteReceipt ≡ false
negativeFrameBoundRouteDoesNotPromoteClay =
  refl
