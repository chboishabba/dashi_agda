module DASHI.Physics.Closure.HaarFrameBoundsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MultiBaseWaveletCompactnessReceipt as MultiBase

------------------------------------------------------------------------
-- Mutual coherence / frame-bound frontier for the 2/3/5 wavelet bridge.

data HaarFrameInput : Set where
  dyadicHaarFamily :
    HaarFrameInput

  triadicHaarFamily :
    HaarFrameInput

  pentadicHaarFamily :
    HaarFrameInput

  pairwiseIntervalOverlapEstimate :
    HaarFrameInput

canonicalHaarFrameInputs : List HaarFrameInput
canonicalHaarFrameInputs =
  dyadicHaarFamily
  ∷ triadicHaarFamily
  ∷ pentadicHaarFamily
  ∷ pairwiseIntervalOverlapEstimate
  ∷ []

data HaarFrameStatus : Set where
  mutualCoherenceBoundRecorded :
    HaarFrameStatus

  lowerFrameBoundOpen :
    HaarFrameStatus

data HaarFrameBlocker : Set where
  missingUniformGramSpectrumBound :
    HaarFrameBlocker

  missingLowerRieszBound :
    HaarFrameBlocker

  missingScaleSummabilityProof :
    HaarFrameBlocker

canonicalHaarFrameBlockers : List HaarFrameBlocker
canonicalHaarFrameBlockers =
  missingUniformGramSpectrumBound
  ∷ missingLowerRieszBound
  ∷ missingScaleSummabilityProof
  ∷ []

data HaarFramePromotion : Set where

haarFramePromotionImpossibleHere :
  HaarFramePromotion →
  ⊥
haarFramePromotionImpossibleHere ()

record HaarFrameBoundsReceipt : Setω where
  field
    multiBaseReceipt :
      MultiBase.MultiBaseWaveletCompactnessReceipt

    frameBoundsPreviouslyOpen :
      MultiBase.frameBoundsProved multiBaseReceipt ≡ false

    inputs :
      List HaarFrameInput

    inputsAreCanonical :
      inputs ≡ canonicalHaarFrameInputs

    status :
      List HaarFrameStatus

    statusIsCanonical :
      status ≡ mutualCoherenceBoundRecorded ∷ lowerFrameBoundOpen ∷ []

    mutualCoherenceEstimate :
      String

    mutualCoherenceEstimateIsCanonical :
      mutualCoherenceEstimate
      ≡
      "pairwise Haar overlaps are controlled by interval overlap, but uniform Gram spectrum bounds across dyadic/triadic/pentadic scales are not proved"

    spanningByStepFunctions :
      Bool

    spanningByStepFunctionsIsTrue :
      spanningByStepFunctions ≡ true

    besselSequenceRecorded :
      Bool

    besselSequenceRecordedIsCandidate :
      besselSequenceRecorded ≡ true

    rieszLowerBoundProved :
      Bool

    rieszLowerBoundProvedIsFalse :
      rieszLowerBoundProved ≡ false

    frameConditionSatisfied :
      Bool

    frameConditionSatisfiedIsFalse :
      frameConditionSatisfied ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List HaarFrameBlocker

    blockersAreCanonical :
      blockers ≡ canonicalHaarFrameBlockers

    promotionFlags :
      List HaarFramePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open HaarFrameBoundsReceipt public

canonicalHaarFrameBoundsReceipt :
  HaarFrameBoundsReceipt
canonicalHaarFrameBoundsReceipt =
  record
    { multiBaseReceipt =
        MultiBase.canonicalMultiBaseWaveletCompactnessReceipt
    ; frameBoundsPreviouslyOpen =
        refl
    ; inputs =
        canonicalHaarFrameInputs
    ; inputsAreCanonical =
        refl
    ; status =
        mutualCoherenceBoundRecorded ∷ lowerFrameBoundOpen ∷ []
    ; statusIsCanonical =
        refl
    ; mutualCoherenceEstimate =
        "pairwise Haar overlaps are controlled by interval overlap, but uniform Gram spectrum bounds across dyadic/triadic/pentadic scales are not proved"
    ; mutualCoherenceEstimateIsCanonical =
        refl
    ; spanningByStepFunctions =
        true
    ; spanningByStepFunctionsIsTrue =
        refl
    ; besselSequenceRecorded =
        true
    ; besselSequenceRecordedIsCandidate =
        refl
    ; rieszLowerBoundProved =
        false
    ; rieszLowerBoundProvedIsFalse =
        refl
    ; frameConditionSatisfied =
        false
    ; frameConditionSatisfiedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalHaarFrameBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The 2/3/5 wavelet system is recorded as a dense spanning candidate"
        ∷ "A lower Riesz/frame bound is not proved"
        ∷ "The p-adic-to-Archimedean Navier-Stokes bridge and Clay promotion remain false"
        ∷ []
    }

haarFrameBoundsDoNotPromoteNS :
  clayNavierStokesPromoted canonicalHaarFrameBoundsReceipt ≡ false
haarFrameBoundsDoNotPromoteNS =
  refl

