module DASHI.Physics.Closure.DyadicTriadicOrthogonalityByEquidistributionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.WaveletOrthogonalityProofReceipt as Orthogonality

------------------------------------------------------------------------
-- Dyadic/triadic all-scale orthogonality revision.

data DyadicTriadicCheck : Set where
  scaleZeroCancellationCheck :
    DyadicTriadicCheck

  scaleOneCancellationCheck :
    DyadicTriadicCheck

  coarserScaleCrossTermCheck :
    DyadicTriadicCheck

  fineScaleCancellationCandidateCheck :
    DyadicTriadicCheck

canonicalDyadicTriadicChecks :
  List DyadicTriadicCheck
canonicalDyadicTriadicChecks =
  scaleZeroCancellationCheck
  ∷ scaleOneCancellationCheck
  ∷ coarserScaleCrossTermCheck
  ∷ fineScaleCancellationCandidateCheck
  ∷ []

data DyadicTriadicOrthogonalityStatus : Set where
  allScaleMutualOrthogonalityFalse :
    DyadicTriadicOrthogonalityStatus

  coarserSupportCrossTermsNonzero :
    DyadicTriadicOrthogonalityStatus

  fineScaleCancellationCandidateOnly :
    DyadicTriadicOrthogonalityStatus

  noEquidistributionPromotion :
    DyadicTriadicOrthogonalityStatus

canonicalDyadicTriadicOrthogonalityStatus :
  List DyadicTriadicOrthogonalityStatus
canonicalDyadicTriadicOrthogonalityStatus =
  allScaleMutualOrthogonalityFalse
  ∷ coarserSupportCrossTermsNonzero
  ∷ fineScaleCancellationCandidateOnly
  ∷ noEquidistributionPromotion
  ∷ []

data DyadicTriadicPromotion : Set where

dyadicTriadicPromotionImpossibleHere :
  DyadicTriadicPromotion →
  ⊥
dyadicTriadicPromotionImpossibleHere ()

coarserCrossTermStatement : String
coarserCrossTermStatement =
  "Nonzero dyadic/triadic cross terms occur when one wavelet scale is coarser than the other's support, so all-scale mutual orthogonality is false."

fineScaleCandidateStatement : String
fineScaleCandidateStatement =
  "Fine-scale cancellation by equidistribution remains a candidate mechanism, not a promoted all-scale orthogonality theorem."

record DyadicTriadicOrthogonalityByEquidistributionReceipt : Setω where
  field
    priorOrthogonalityReceipt :
      Orthogonality.WaveletOrthogonalityProofReceipt

    priorLiteralOrthogonalityWasNotProved :
      Orthogonality.literalMutualOrthogonalityProved priorOrthogonalityReceipt
      ≡
      false

    checks :
      List DyadicTriadicCheck

    checksAreCanonical :
      checks ≡ canonicalDyadicTriadicChecks

    status :
      List DyadicTriadicOrthogonalityStatus

    statusIsCanonical :
      status ≡ canonicalDyadicTriadicOrthogonalityStatus

    allScaleMutualOrthogonalityProved :
      Bool

    allScaleMutualOrthogonalityProvedIsFalse :
      allScaleMutualOrthogonalityProved ≡ false

    allScaleMutualOrthogonalityFalseRecorded :
      Bool

    allScaleMutualOrthogonalityFalseRecordedIsTrue :
      allScaleMutualOrthogonalityFalseRecorded ≡ true

    coarserScaleCrossTermsNonzero :
      Bool

    coarserScaleCrossTermsNonzeroIsTrue :
      coarserScaleCrossTermsNonzero ≡ true

    coarserCrossTermEvidence :
      String

    coarserCrossTermEvidenceIsCanonical :
      coarserCrossTermEvidence ≡ coarserCrossTermStatement

    fineScaleEquidistributionCancellationCandidate :
      Bool

    fineScaleEquidistributionCancellationCandidateIsTrue :
      fineScaleEquidistributionCancellationCandidate ≡ true

    fineScaleCancellationPromoted :
      Bool

    fineScaleCancellationPromotedIsFalse :
      fineScaleCancellationPromoted ≡ false

    fineScaleCandidateBoundary :
      String

    fineScaleCandidateBoundaryIsCanonical :
      fineScaleCandidateBoundary ≡ fineScaleCandidateStatement

    equidistributionAllScalePromotion :
      Bool

    equidistributionAllScalePromotionIsFalse :
      equidistributionAllScalePromotion ≡ false

    navierStokesPromoted :
      Bool

    navierStokesPromotedIsFalse :
      navierStokesPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotionFlags :
      List DyadicTriadicPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open DyadicTriadicOrthogonalityByEquidistributionReceipt public

canonicalDyadicTriadicOrthogonalityByEquidistributionReceipt :
  DyadicTriadicOrthogonalityByEquidistributionReceipt
canonicalDyadicTriadicOrthogonalityByEquidistributionReceipt =
  record
    { priorOrthogonalityReceipt =
        Orthogonality.canonicalWaveletOrthogonalityProofReceipt
    ; priorLiteralOrthogonalityWasNotProved =
        refl
    ; checks =
        canonicalDyadicTriadicChecks
    ; checksAreCanonical =
        refl
    ; status =
        canonicalDyadicTriadicOrthogonalityStatus
    ; statusIsCanonical =
        refl
    ; allScaleMutualOrthogonalityProved =
        false
    ; allScaleMutualOrthogonalityProvedIsFalse =
        refl
    ; allScaleMutualOrthogonalityFalseRecorded =
        true
    ; allScaleMutualOrthogonalityFalseRecordedIsTrue =
        refl
    ; coarserScaleCrossTermsNonzero =
        true
    ; coarserScaleCrossTermsNonzeroIsTrue =
        refl
    ; coarserCrossTermEvidence =
        coarserCrossTermStatement
    ; coarserCrossTermEvidenceIsCanonical =
        refl
    ; fineScaleEquidistributionCancellationCandidate =
        true
    ; fineScaleEquidistributionCancellationCandidateIsTrue =
        refl
    ; fineScaleCancellationPromoted =
        false
    ; fineScaleCancellationPromotedIsFalse =
        refl
    ; fineScaleCandidateBoundary =
        fineScaleCandidateStatement
    ; fineScaleCandidateBoundaryIsCanonical =
        refl
    ; equidistributionAllScalePromotion =
        false
    ; equidistributionAllScalePromotionIsFalse =
        refl
    ; navierStokesPromoted =
        false
    ; navierStokesPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "All-scale dyadic/triadic mutual orthogonality is recorded false, not promoted"
        ∷ "Coarser-scale wavelets can see a nonzero average over the other support"
        ∷ "Fine-scale equidistribution cancellation remains only a candidate mechanism"
        ∷ "No Navier-Stokes or Clay promotion follows"
        ∷ []
    }

dyadicTriadicEquidistributionDoesNotPromoteNS :
  navierStokesPromoted
    canonicalDyadicTriadicOrthogonalityByEquidistributionReceipt
  ≡
  false
dyadicTriadicEquidistributionDoesNotPromoteNS =
  refl

dyadicTriadicEquidistributionDoesNotPromoteClay :
  clayPromoted
    canonicalDyadicTriadicOrthogonalityByEquidistributionReceipt
  ≡
  false
dyadicTriadicEquidistributionDoesNotPromoteClay =
  refl
