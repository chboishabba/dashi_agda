module DASHI.Physics.Closure.FrameBoundByOperatorNormReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.GramMatrixSpectrumBoundReceipt as Spectrum

------------------------------------------------------------------------
-- NS W2 frame analysis: operator-norm perturbation route.

data FrameOperatorNormComponent : Set where
  identityDiagonalPart :
    FrameOperatorNormComponent

  offDiagonalCrossTermOperator :
    FrameOperatorNormComponent

  frameLowerBoundIdentityMinusOffDiagonalNorm :
    FrameOperatorNormComponent

  dyadicTriadicCoarseScaleCrossBlocks :
    FrameOperatorNormComponent

  rankOnePerCoarseTriadicScaleBlock :
    FrameOperatorNormComponent

  normLessThanOneCriterion :
    FrameOperatorNormComponent

  lowerFrameBoundFromInvertibility :
    FrameOperatorNormComponent

canonicalFrameOperatorNormComponents :
  List FrameOperatorNormComponent
canonicalFrameOperatorNormComponents =
  identityDiagonalPart
  ∷ offDiagonalCrossTermOperator
  ∷ frameLowerBoundIdentityMinusOffDiagonalNorm
  ∷ dyadicTriadicCoarseScaleCrossBlocks
  ∷ rankOnePerCoarseTriadicScaleBlock
  ∷ normLessThanOneCriterion
  ∷ lowerFrameBoundFromInvertibility
  ∷ []

data FrameOperatorNormStatus : Set where
  operatorNormRouteOpen :
    FrameOperatorNormStatus

  lowerBoundFormulaRecorded :
    FrameOperatorNormStatus

  dyadicTriadicStructuredBlocksRecorded :
    FrameOperatorNormStatus

  exactOperatorNormStillOpen :
    FrameOperatorNormStatus

  offDiagonalNormNotBoundedBelowOne :
    FrameOperatorNormStatus

  frameBoundNotConstructed :
    FrameOperatorNormStatus

canonicalFrameOperatorNormStatus : List FrameOperatorNormStatus
canonicalFrameOperatorNormStatus =
  operatorNormRouteOpen
  ∷ lowerBoundFormulaRecorded
  ∷ dyadicTriadicStructuredBlocksRecorded
  ∷ exactOperatorNormStillOpen
  ∷ offDiagonalNormNotBoundedBelowOne
  ∷ frameBoundNotConstructed
  ∷ []

data FrameOperatorNormBlocker : Set where
  missingSchurTestWithSummableRows :
    FrameOperatorNormBlocker

  missingCrossBaseOperatorNormEstimate :
    FrameOperatorNormBlocker

  missingNormLessThanOneWitness :
    FrameOperatorNormBlocker

canonicalFrameOperatorNormBlockers : List FrameOperatorNormBlocker
canonicalFrameOperatorNormBlockers =
  missingSchurTestWithSummableRows
  ∷ missingCrossBaseOperatorNormEstimate
  ∷ missingNormLessThanOneWitness
  ∷ []

data FrameOperatorNormPromotionReceipt : Set where

frameOperatorNormPromotionImpossibleHere :
  FrameOperatorNormPromotionReceipt →
  ⊥
frameOperatorNormPromotionImpossibleHere ()

operatorNormRouteDiagnostic : String
operatorNormRouteDiagnostic =
  "operator norm route is open: the candidate lower bound is A = 1 - ||G_off||; dyadic-triadic coarse-scale cross blocks are structured with rank-one contributions per coarse triadic scale, but no exact ||G_off||_op < 1 certificate is available"

frameLowerBoundFormula : String
frameLowerBoundFormula =
  "A = 1 - ||G_off||"

record FrameBoundByOperatorNormReceipt : Setω where
  field
    spectrumReceipt :
      Spectrum.GramMatrixSpectrumBoundReceipt

    spectrumLowerBoundStillOpen :
      Spectrum.uniformSpectrumLowerBoundProved spectrumReceipt ≡ false

    testDepth :
      Nat

    components :
      List FrameOperatorNormComponent

    componentsAreCanonical :
      components ≡ canonicalFrameOperatorNormComponents

    status :
      List FrameOperatorNormStatus

    statusIsCanonical :
      status ≡ canonicalFrameOperatorNormStatus

    diagnostic :
      String

    diagnosticIsCanonical :
      diagnostic ≡ operatorNormRouteDiagnostic

    offDiagonalOperatorNormBoundRecorded :
      Bool

    offDiagonalOperatorNormBoundRecordedIsFalse :
      offDiagonalOperatorNormBoundRecorded ≡ false

    frameLowerBoundFormulaRecorded :
      Bool

    frameLowerBoundFormulaRecordedIsTrue :
      frameLowerBoundFormulaRecorded ≡ true

    lowerBoundFormula :
      String

    lowerBoundFormulaIsCanonical :
      lowerBoundFormula ≡ frameLowerBoundFormula

    dyadicTriadicCoarseBlocksRecorded :
      Bool

    dyadicTriadicCoarseBlocksRecordedIsTrue :
      dyadicTriadicCoarseBlocksRecorded ≡ true

    rankOnePerCoarseTriadicScaleRecorded :
      Bool

    rankOnePerCoarseTriadicScaleRecordedIsTrue :
      rankOnePerCoarseTriadicScaleRecorded ≡ true

    exactOffDiagonalOperatorNormComputed :
      Bool

    exactOffDiagonalOperatorNormComputedIsFalse :
      exactOffDiagonalOperatorNormComputed ≡ false

    normLessThanOneCertified :
      Bool

    normLessThanOneCertifiedIsFalse :
      normLessThanOneCertified ≡ false

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

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    blockers :
      List FrameOperatorNormBlocker

    blockersAreCanonical :
      blockers ≡ canonicalFrameOperatorNormBlockers

    promotionReceipts :
      List FrameOperatorNormPromotionReceipt

    promotionReceiptsAreEmpty :
      promotionReceipts ≡ []

    receiptBoundary :
      List String

open FrameBoundByOperatorNormReceipt public

canonicalFrameBoundByOperatorNormReceipt :
  FrameBoundByOperatorNormReceipt
canonicalFrameBoundByOperatorNormReceipt =
  record
    { spectrumReceipt =
        Spectrum.canonicalGramMatrixSpectrumBoundReceipt
    ; spectrumLowerBoundStillOpen =
        refl
    ; testDepth =
        0
    ; components =
        canonicalFrameOperatorNormComponents
    ; componentsAreCanonical =
        refl
    ; status =
        canonicalFrameOperatorNormStatus
    ; statusIsCanonical =
        refl
    ; diagnostic =
        operatorNormRouteDiagnostic
    ; diagnosticIsCanonical =
        refl
    ; offDiagonalOperatorNormBoundRecorded =
        false
    ; offDiagonalOperatorNormBoundRecordedIsFalse =
        refl
    ; frameLowerBoundFormulaRecorded =
        true
    ; frameLowerBoundFormulaRecordedIsTrue =
        refl
    ; lowerBoundFormula =
        frameLowerBoundFormula
    ; lowerBoundFormulaIsCanonical =
        refl
    ; dyadicTriadicCoarseBlocksRecorded =
        true
    ; dyadicTriadicCoarseBlocksRecordedIsTrue =
        refl
    ; rankOnePerCoarseTriadicScaleRecorded =
        true
    ; rankOnePerCoarseTriadicScaleRecordedIsTrue =
        refl
    ; exactOffDiagonalOperatorNormComputed =
        false
    ; exactOffDiagonalOperatorNormComputedIsFalse =
        refl
    ; normLessThanOneCertified =
        false
    ; normLessThanOneCertifiedIsFalse =
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
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; blockers =
        canonicalFrameOperatorNormBlockers
    ; blockersAreCanonical =
        refl
    ; promotionReceipts =
        []
    ; promotionReceiptsAreEmpty =
        refl
    ; receiptBoundary =
        "The operator-norm perturbation route records the candidate lower bound A = 1 - ||G_off||"
        ∷ "Dyadic-triadic cross blocks are structured at coarse scale with rank-one contributions per coarse triadic scale"
        ∷ "The exact off-diagonal operator norm is still open, and no ||G_off|| < 1 witness is constructed"
        ∷ "No frame, NS regularity, terminal Clay, or Clay promotion is constructed"
        ∷ []
    }

frameBoundByOperatorNormDoesNotPromoteNS :
  navierStokesRegularityPromoted canonicalFrameBoundByOperatorNormReceipt
  ≡
  false
frameBoundByOperatorNormDoesNotPromoteNS =
  refl

frameBoundByOperatorNormDoesNotPromoteClay :
  clayRegularityPromoted canonicalFrameBoundByOperatorNormReceipt ≡ false
frameBoundByOperatorNormDoesNotPromoteClay =
  refl

frameBoundByOperatorNormKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalFrameBoundByOperatorNormReceipt ≡ false
frameBoundByOperatorNormKeepsTerminalFalse =
  refl
