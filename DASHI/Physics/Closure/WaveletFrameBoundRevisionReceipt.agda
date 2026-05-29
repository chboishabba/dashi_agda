module DASHI.Physics.Closure.WaveletFrameBoundRevisionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DyadicTriadicOrthogonalityByEquidistributionReceipt as DyTri
import DASHI.Physics.Closure.HaarFrameBoundsReceipt as HaarFrame

------------------------------------------------------------------------
-- Frame-bound revision after dyadic/triadic all-scale orthogonality fails.

data WaveletFrameBoundInput : Set where
  haarFrameBoundFrontier :
    WaveletFrameBoundInput

  dyadicTriadicOrthogonalityRevision :
    WaveletFrameBoundInput

  gramMatrixRoute :
    WaveletFrameBoundInput

  mutualCoherenceRoute :
    WaveletFrameBoundInput

canonicalWaveletFrameBoundInputs :
  List WaveletFrameBoundInput
canonicalWaveletFrameBoundInputs =
  haarFrameBoundFrontier
  ∷ dyadicTriadicOrthogonalityRevision
  ∷ gramMatrixRoute
  ∷ mutualCoherenceRoute
  ∷ []

data WaveletFrameBoundStatus : Set where
  frameBoundsRemainOpen :
    WaveletFrameBoundStatus

  allScaleOrthogonalityShortcutRejected :
    WaveletFrameBoundStatus

  gramAnalysisRequired :
    WaveletFrameBoundStatus

  coherenceAnalysisRequired :
    WaveletFrameBoundStatus

canonicalWaveletFrameBoundStatus :
  List WaveletFrameBoundStatus
canonicalWaveletFrameBoundStatus =
  frameBoundsRemainOpen
  ∷ allScaleOrthogonalityShortcutRejected
  ∷ gramAnalysisRequired
  ∷ coherenceAnalysisRequired
  ∷ []

data WaveletFrameBoundBlocker : Set where
  missingUniformGramSpectrumBound :
    WaveletFrameBoundBlocker

  missingCrossScaleCoherenceSummability :
    WaveletFrameBoundBlocker

  missingLowerFrameInequality :
    WaveletFrameBoundBlocker

canonicalWaveletFrameBoundBlockers :
  List WaveletFrameBoundBlocker
canonicalWaveletFrameBoundBlockers =
  missingUniformGramSpectrumBound
  ∷ missingCrossScaleCoherenceSummability
  ∷ missingLowerFrameInequality
  ∷ []

data WaveletFrameBoundPromotion : Set where

waveletFrameBoundPromotionImpossibleHere :
  WaveletFrameBoundPromotion →
  ⊥
waveletFrameBoundPromotionImpossibleHere ()

revisionStatement : String
revisionStatement =
  "Frame bounds are open after rejecting all-scale dyadic/triadic mutual orthogonality; a Gram-spectrum or cross-scale coherence analysis is required."

record WaveletFrameBoundRevisionReceipt : Setω where
  field
    priorFrameReceipt :
      HaarFrame.HaarFrameBoundsReceipt

    priorFrameBoundsWereOpen :
      HaarFrame.rieszLowerBoundProved priorFrameReceipt ≡ false

    dyadicTriadicRevisionReceipt :
      DyTri.DyadicTriadicOrthogonalityByEquidistributionReceipt

    allScaleOrthogonalityRejected :
      DyTri.allScaleMutualOrthogonalityFalseRecorded
        dyadicTriadicRevisionReceipt
      ≡
      true

    inputs :
      List WaveletFrameBoundInput

    inputsAreCanonical :
      inputs ≡ canonicalWaveletFrameBoundInputs

    status :
      List WaveletFrameBoundStatus

    statusIsCanonical :
      status ≡ canonicalWaveletFrameBoundStatus

    allScaleOrthogonalityShortcutAvailable :
      Bool

    allScaleOrthogonalityShortcutAvailableIsFalse :
      allScaleOrthogonalityShortcutAvailable ≡ false

    frameBoundsProved :
      Bool

    frameBoundsProvedIsFalse :
      frameBoundsProved ≡ false

    frameBoundsOpen :
      Bool

    frameBoundsOpenIsTrue :
      frameBoundsOpen ≡ true

    gramSpectrumAnalysisRequired :
      Bool

    gramSpectrumAnalysisRequiredIsTrue :
      gramSpectrumAnalysisRequired ≡ true

    mutualCoherenceAnalysisRequired :
      Bool

    mutualCoherenceAnalysisRequiredIsTrue :
      mutualCoherenceAnalysisRequired ≡ true

    lowerFrameBoundPromoted :
      Bool

    lowerFrameBoundPromotedIsFalse :
      lowerFrameBoundPromoted ≡ false

    revision :
      String

    revisionIsCanonical :
      revision ≡ revisionStatement

    blockers :
      List WaveletFrameBoundBlocker

    blockersAreCanonical :
      blockers ≡ canonicalWaveletFrameBoundBlockers

    navierStokesPromoted :
      Bool

    navierStokesPromotedIsFalse :
      navierStokesPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotionFlags :
      List WaveletFrameBoundPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open WaveletFrameBoundRevisionReceipt public

canonicalWaveletFrameBoundRevisionReceipt :
  WaveletFrameBoundRevisionReceipt
canonicalWaveletFrameBoundRevisionReceipt =
  record
    { priorFrameReceipt =
        HaarFrame.canonicalHaarFrameBoundsReceipt
    ; priorFrameBoundsWereOpen =
        refl
    ; dyadicTriadicRevisionReceipt =
        DyTri.canonicalDyadicTriadicOrthogonalityByEquidistributionReceipt
    ; allScaleOrthogonalityRejected =
        refl
    ; inputs =
        canonicalWaveletFrameBoundInputs
    ; inputsAreCanonical =
        refl
    ; status =
        canonicalWaveletFrameBoundStatus
    ; statusIsCanonical =
        refl
    ; allScaleOrthogonalityShortcutAvailable =
        false
    ; allScaleOrthogonalityShortcutAvailableIsFalse =
        refl
    ; frameBoundsProved =
        false
    ; frameBoundsProvedIsFalse =
        refl
    ; frameBoundsOpen =
        true
    ; frameBoundsOpenIsTrue =
        refl
    ; gramSpectrumAnalysisRequired =
        true
    ; gramSpectrumAnalysisRequiredIsTrue =
        refl
    ; mutualCoherenceAnalysisRequired =
        true
    ; mutualCoherenceAnalysisRequiredIsTrue =
        refl
    ; lowerFrameBoundPromoted =
        false
    ; lowerFrameBoundPromotedIsFalse =
        refl
    ; revision =
        revisionStatement
    ; revisionIsCanonical =
        refl
    ; blockers =
        canonicalWaveletFrameBoundBlockers
    ; blockersAreCanonical =
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
        "Frame bounds remain open"
        ∷ "The all-scale orthogonality shortcut is rejected by nonzero cross terms"
        ∷ "A Gram-spectrum or mutual-coherence proof is required before any lower frame bound"
        ∷ "No Navier-Stokes or Clay promotion follows"
        ∷ []
    }

waveletFrameBoundRevisionDoesNotPromoteNS :
  navierStokesPromoted canonicalWaveletFrameBoundRevisionReceipt ≡ false
waveletFrameBoundRevisionDoesNotPromoteNS =
  refl

waveletFrameBoundRevisionDoesNotPromoteClay :
  clayPromoted canonicalWaveletFrameBoundRevisionReceipt ≡ false
waveletFrameBoundRevisionDoesNotPromoteClay =
  refl
