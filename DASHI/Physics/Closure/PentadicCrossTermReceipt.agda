module DASHI.Physics.Closure.PentadicCrossTermReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.FrameBoundByOperatorNormReceipt as OpNorm

------------------------------------------------------------------------
-- NS W2 frame analysis: pentadic cross-term obstruction diagnostic.

data PentadicCrossBasePair : Set where
  dyadicPentadic :
    PentadicCrossBasePair

  triadicPentadic :
    PentadicCrossBasePair

canonicalPentadicCrossBasePairs : List PentadicCrossBasePair
canonicalPentadicCrossBasePairs =
  dyadicPentadic
  ∷ triadicPentadic
  ∷ []

data PentadicCrossTermStatus : Set where
  pentadicCrossTermsRecorded :
    PentadicCrossTermStatus

  pentadicRowSumsExceedOne :
    PentadicCrossTermStatus

  gershgorinRowSumsExceedOneStatus :
    PentadicCrossTermStatus

  gershgorinCannotProveFrameLowerBound :
    PentadicCrossTermStatus

  perturbativeFrameRouteRejected :
    PentadicCrossTermStatus

canonicalPentadicCrossTermStatus : List PentadicCrossTermStatus
canonicalPentadicCrossTermStatus =
  pentadicCrossTermsRecorded
  ∷ pentadicRowSumsExceedOne
  ∷ gershgorinRowSumsExceedOneStatus
  ∷ gershgorinCannotProveFrameLowerBound
  ∷ perturbativeFrameRouteRejected
  ∷ []

data PentadicCrossTermBlocker : Set where
  pentadicScaleAccumulationTooLarge :
    PentadicCrossTermBlocker

  missingPentadicCancellationLemma :
    PentadicCrossTermBlocker

  missingThreeBaseSchurBound :
    PentadicCrossTermBlocker

canonicalPentadicCrossTermBlockers : List PentadicCrossTermBlocker
canonicalPentadicCrossTermBlockers =
  pentadicScaleAccumulationTooLarge
  ∷ missingPentadicCancellationLemma
  ∷ missingThreeBaseSchurBound
  ∷ []

data PentadicCrossTermPromotionReceipt : Set where

pentadicCrossTermPromotionImpossibleHere :
  PentadicCrossTermPromotionReceipt →
  ⊥
pentadicCrossTermPromotionImpossibleHere ()

pentadicCrossTermDiagnostic : String
pentadicCrossTermDiagnostic =
  "pentadic cross-term diagnostic: dyadic-pentadic and triadic-pentadic coarse cross terms have Gershgorin row sums exceeding 1 under the coarse bound, so Gershgorin cannot prove a positive W2 frame lower bound"

record PentadicCrossTermReceipt : Setω where
  field
    operatorNormReceipt :
      OpNorm.FrameBoundByOperatorNormReceipt

    operatorNormRouteStillOpen :
      OpNorm.normLessThanOneCertified operatorNormReceipt ≡ false

    pentadicDepth :
      Nat

    crossBasePairs :
      List PentadicCrossBasePair

    crossBasePairsAreCanonical :
      crossBasePairs ≡ canonicalPentadicCrossBasePairs

    status :
      List PentadicCrossTermStatus

    statusIsCanonical :
      status ≡ canonicalPentadicCrossTermStatus

    diagnostic :
      String

    diagnosticIsCanonical :
      diagnostic ≡ pentadicCrossTermDiagnostic

    absolutePentadicSumsExceedOne :
      Bool

    absolutePentadicSumsExceedOneIsTrue :
      absolutePentadicSumsExceedOne ≡ true

    dyadicPentadicCoarseCrossTermsRecorded :
      Bool

    dyadicPentadicCoarseCrossTermsRecordedIsTrue :
      dyadicPentadicCoarseCrossTermsRecorded ≡ true

    triadicPentadicCoarseCrossTermsRecorded :
      Bool

    triadicPentadicCoarseCrossTermsRecordedIsTrue :
      triadicPentadicCoarseCrossTermsRecorded ≡ true

    gershgorinRowSumsExceedOne :
      Bool

    gershgorinRowSumsExceedOneIsTrue :
      gershgorinRowSumsExceedOne ≡ true

    gershgorinCanProveFrameLowerBound :
      Bool

    gershgorinCanProveFrameLowerBoundIsFalse :
      gershgorinCanProveFrameLowerBound ≡ false

    exactPentadicCrossNormComputed :
      Bool

    exactPentadicCrossNormComputedIsFalse :
      exactPentadicCrossNormComputed ≡ false

    perturbativeNormRouteCertified :
      Bool

    perturbativeNormRouteCertifiedIsFalse :
      perturbativeNormRouteCertified ≡ false

    lowerFrameBoundConstructed :
      Bool

    lowerFrameBoundConstructedIsFalse :
      lowerFrameBoundConstructed ≡ false

    navierStokesRegularityPromoted :
      Bool

    navierStokesRegularityPromotedIsFalse :
      navierStokesRegularityPromoted ≡ false

    clayRegularityPromoted :
      Bool

    clayRegularityPromotedIsFalse :
      clayRegularityPromoted ≡ false

    blockers :
      List PentadicCrossTermBlocker

    blockersAreCanonical :
      blockers ≡ canonicalPentadicCrossTermBlockers

    promotionReceipts :
      List PentadicCrossTermPromotionReceipt

    promotionReceiptsAreEmpty :
      promotionReceipts ≡ []

    receiptBoundary :
      List String

open PentadicCrossTermReceipt public

canonicalPentadicCrossTermReceipt :
  PentadicCrossTermReceipt
canonicalPentadicCrossTermReceipt =
  record
    { operatorNormReceipt =
        OpNorm.canonicalFrameBoundByOperatorNormReceipt
    ; operatorNormRouteStillOpen =
        refl
    ; pentadicDepth =
        5
    ; crossBasePairs =
        canonicalPentadicCrossBasePairs
    ; crossBasePairsAreCanonical =
        refl
    ; status =
        canonicalPentadicCrossTermStatus
    ; statusIsCanonical =
        refl
    ; diagnostic =
        pentadicCrossTermDiagnostic
    ; diagnosticIsCanonical =
        refl
    ; absolutePentadicSumsExceedOne =
        true
    ; absolutePentadicSumsExceedOneIsTrue =
        refl
    ; dyadicPentadicCoarseCrossTermsRecorded =
        true
    ; dyadicPentadicCoarseCrossTermsRecordedIsTrue =
        refl
    ; triadicPentadicCoarseCrossTermsRecorded =
        true
    ; triadicPentadicCoarseCrossTermsRecordedIsTrue =
        refl
    ; gershgorinRowSumsExceedOne =
        true
    ; gershgorinRowSumsExceedOneIsTrue =
        refl
    ; gershgorinCanProveFrameLowerBound =
        false
    ; gershgorinCanProveFrameLowerBoundIsFalse =
        refl
    ; exactPentadicCrossNormComputed =
        false
    ; exactPentadicCrossNormComputedIsFalse =
        refl
    ; perturbativeNormRouteCertified =
        false
    ; perturbativeNormRouteCertifiedIsFalse =
        refl
    ; lowerFrameBoundConstructed =
        false
    ; lowerFrameBoundConstructedIsFalse =
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
        canonicalPentadicCrossTermBlockers
    ; blockersAreCanonical =
        refl
    ; promotionReceipts =
        []
    ; promotionReceiptsAreEmpty =
        refl
    ; receiptBoundary =
        "Dyadic-pentadic and triadic-pentadic coarse cross terms are recorded"
        ∷ "Gershgorin row sums exceed 1, so Gershgorin cannot prove the W2 frame lower bound"
        ∷ "Exact pentadic cross norms and an alternative Gram-spectrum bound remain open"
        ∷ "No NS regularity or Clay promotion is constructed"
        ∷ []
    }

pentadicCrossTermDoesNotPromoteNS :
  navierStokesRegularityPromoted canonicalPentadicCrossTermReceipt ≡ false
pentadicCrossTermDoesNotPromoteNS =
  refl
