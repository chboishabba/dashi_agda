module DASHI.Physics.Closure.GramMatrix2x3BoundsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- NS W2 frame analysis: coarse 2x3 Gram-entry bound.

data GramMatrix2x3Input : Set where
  dyadicHaarAtom :
    GramMatrix2x3Input

  triadicHaarAtom :
    GramMatrix2x3Input

  intervalOverlapSupport :
    GramMatrix2x3Input

  coarseScaleEnvelope :
    GramMatrix2x3Input

canonicalGramMatrix2x3Inputs : List GramMatrix2x3Input
canonicalGramMatrix2x3Inputs =
  dyadicHaarAtom
  ∷ triadicHaarAtom
  ∷ intervalOverlapSupport
  ∷ coarseScaleEnvelope
  ∷ []

data GramMatrix2x3Status : Set where
  coarseCrossTermBoundStatusRecorded :
    GramMatrix2x3Status

  signCancellationNotUsed :
    GramMatrix2x3Status

  lowerFrameBoundNotDerived :
    GramMatrix2x3Status

canonicalGramMatrix2x3Status : List GramMatrix2x3Status
canonicalGramMatrix2x3Status =
  coarseCrossTermBoundStatusRecorded
  ∷ signCancellationNotUsed
  ∷ lowerFrameBoundNotDerived
  ∷ []

data GramMatrix2x3Blocker : Set where
  missingUniformSignedCancellation :
    GramMatrix2x3Blocker

  missingSummableAllScaleEnvelope :
    GramMatrix2x3Blocker

  missingPositiveGramLowerBound :
    GramMatrix2x3Blocker

canonicalGramMatrix2x3Blockers : List GramMatrix2x3Blocker
canonicalGramMatrix2x3Blockers =
  missingUniformSignedCancellation
  ∷ missingSummableAllScaleEnvelope
  ∷ missingPositiveGramLowerBound
  ∷ []

data GramMatrix2x3PromotionReceipt : Set where

gramMatrix2x3PromotionImpossibleHere :
  GramMatrix2x3PromotionReceipt →
  ⊥
gramMatrix2x3PromotionImpossibleHere ()

coarseCrossTermDiagnostic : String
coarseCrossTermDiagnostic =
  "coarse Haar cross term bound: |<psi_{2,j,k}, psi_{3,j',k'}>| <= C pm b^{j'/2} a^{-j/2}; recorded only as an absolute envelope, not a cancellation or summability proof"

record GramMatrix2x3BoundsReceipt : Setω where
  field
    sourceDepth :
      Nat

    targetDepth :
      Nat

    inputs :
      List GramMatrix2x3Input

    inputsAreCanonical :
      inputs ≡ canonicalGramMatrix2x3Inputs

    status :
      List GramMatrix2x3Status

    statusIsCanonical :
      status ≡ canonicalGramMatrix2x3Status

    crossTermDiagnostic :
      String

    crossTermDiagnosticIsCanonical :
      crossTermDiagnostic ≡ coarseCrossTermDiagnostic

    coarseCrossTermBoundRecorded :
      Bool

    coarseCrossTermBoundRecordedIsTrue :
      coarseCrossTermBoundRecorded ≡ true

    uniformGramLowerBoundProved :
      Bool

    uniformGramLowerBoundProvedIsFalse :
      uniformGramLowerBoundProved ≡ false

    frameBoundPromoted :
      Bool

    frameBoundPromotedIsFalse :
      frameBoundPromoted ≡ false

    navierStokesRegularityPromoted :
      Bool

    navierStokesRegularityPromotedIsFalse :
      navierStokesRegularityPromoted ≡ false

    clayRegularityPromoted :
      Bool

    clayRegularityPromotedIsFalse :
      clayRegularityPromoted ≡ false

    blockers :
      List GramMatrix2x3Blocker

    blockersAreCanonical :
      blockers ≡ canonicalGramMatrix2x3Blockers

    promotionReceipts :
      List GramMatrix2x3PromotionReceipt

    promotionReceiptsAreEmpty :
      promotionReceipts ≡ []

    receiptBoundary :
      List String

open GramMatrix2x3BoundsReceipt public

canonicalGramMatrix2x3BoundsReceipt :
  GramMatrix2x3BoundsReceipt
canonicalGramMatrix2x3BoundsReceipt =
  record
    { sourceDepth =
        2
    ; targetDepth =
        3
    ; inputs =
        canonicalGramMatrix2x3Inputs
    ; inputsAreCanonical =
        refl
    ; status =
        canonicalGramMatrix2x3Status
    ; statusIsCanonical =
        refl
    ; crossTermDiagnostic =
        coarseCrossTermDiagnostic
    ; crossTermDiagnosticIsCanonical =
        refl
    ; coarseCrossTermBoundRecorded =
        true
    ; coarseCrossTermBoundRecordedIsTrue =
        refl
    ; uniformGramLowerBoundProved =
        false
    ; uniformGramLowerBoundProvedIsFalse =
        refl
    ; frameBoundPromoted =
        false
    ; frameBoundPromotedIsFalse =
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
        canonicalGramMatrix2x3Blockers
    ; blockersAreCanonical =
        refl
    ; promotionReceipts =
        []
    ; promotionReceiptsAreEmpty =
        refl
    ; receiptBoundary =
        "The 2x3 Gram diagnostic records only a coarse cross-term envelope"
        ∷ "No all-scale summability, positive spectrum bound, frame bound, NS regularity theorem, or Clay promotion is constructed"
        ∷ []
    }

gramMatrix2x3DoesNotPromoteClay :
  clayRegularityPromoted canonicalGramMatrix2x3BoundsReceipt ≡ false
gramMatrix2x3DoesNotPromoteClay =
  refl
