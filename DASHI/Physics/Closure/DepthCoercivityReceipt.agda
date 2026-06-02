module DASHI.Physics.Closure.DepthCoercivityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Bounded depth-coercivity receipt.
--
-- This is a bounded receipt only.  It records a finite-depth coercivity
-- surface and explicitly separates embedding-constant divergence from any
-- spectral gap shrinkage claim.  The first excitation at K=0 is not promoted
-- here; it remains a theorem obligation with its operator/domain hypotheses.

data DepthCoercivityStatus : Set where
  boundedDepthCoercivityRecordedNoPromotion :
    DepthCoercivityStatus

data BoundedDepth : Set where
  depthZero :
    BoundedDepth

  depthOne :
    BoundedDepth

  depthTwo :
    BoundedDepth

canonicalBoundedDepthWindow :
  List BoundedDepth
canonicalBoundedDepthWindow =
  depthZero
  ∷ depthOne
  ∷ depthTwo
  ∷ []

data DepthCoercivityFact : Set where
  finiteDepthWindowFixed :
    DepthCoercivityFact

  coerciveLowerBoundRecordedOnWindow :
    DepthCoercivityFact

  depthEmbeddingConstantTrackedSeparately :
    DepthCoercivityFact

  embeddingConstantDivergenceNotGapShrinkage :
    DepthCoercivityFact

  firstExcitationAtKZeroLeftAsTheoremObligation :
    DepthCoercivityFact

canonicalDepthCoercivityFacts :
  List DepthCoercivityFact
canonicalDepthCoercivityFacts =
  finiteDepthWindowFixed
  ∷ coerciveLowerBoundRecordedOnWindow
  ∷ depthEmbeddingConstantTrackedSeparately
  ∷ embeddingConstantDivergenceNotGapShrinkage
  ∷ firstExcitationAtKZeroLeftAsTheoremObligation
  ∷ []

data DepthCoercivityPromotion : Set where

depthCoercivityPromotionImpossibleHere :
  DepthCoercivityPromotion →
  ⊥
depthCoercivityPromotionImpossibleHere ()

depthCoercivityStatement : String
depthCoercivityStatement =
  "Bounded depth coercivity is recorded on the finite window K = 0,1,2.  The depth embedding constant may diverge with depth, but that bookkeeping is not a spectral-gap shrinkage theorem.  A first-excitation statement at K=0 remains a separate operator/domain theorem obligation."

record DepthCoercivityReceipt : Set where
  field
    status :
      DepthCoercivityStatus

    statusIsCanonical :
      status ≡ boundedDepthCoercivityRecordedNoPromotion

    boundedDepthWindow :
      List BoundedDepth

    boundedDepthWindowIsCanonical :
      boundedDepthWindow ≡ canonicalBoundedDepthWindow

    boundedCoerciveLowerBoundRecorded :
      Bool

    boundedCoerciveLowerBoundRecordedIsTrue :
      boundedCoerciveLowerBoundRecorded ≡ true

    depthEmbeddingConstantTracked :
      Bool

    depthEmbeddingConstantTrackedIsTrue :
      depthEmbeddingConstantTracked ≡ true

    embeddingConstantMayDivergeWithDepth :
      Bool

    embeddingConstantMayDivergeWithDepthIsTrue :
      embeddingConstantMayDivergeWithDepth ≡ true

    embeddingConstantDivergenceIsGapShrinkage :
      Bool

    embeddingConstantDivergenceIsGapShrinkageIsFalse :
      embeddingConstantDivergenceIsGapShrinkage ≡ false

    firstExcitationAtKZeroUnconditionallyProved :
      Bool

    firstExcitationAtKZeroUnconditionallyProvedIsFalse :
      firstExcitationAtKZeroUnconditionallyProved ≡ false

    firstExcitationAtKZeroTheoremObligationRecorded :
      Bool

    firstExcitationAtKZeroTheoremObligationRecordedIsTrue :
      firstExcitationAtKZeroTheoremObligationRecorded ≡ true

    continuumGapPromoted :
      Bool

    continuumGapPromotedIsFalse :
      continuumGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    facts :
      List DepthCoercivityFact

    factsAreCanonical :
      facts ≡ canonicalDepthCoercivityFacts

    statement :
      String

    statementIsCanonical :
      statement ≡ depthCoercivityStatement

    promotionFlags :
      List DepthCoercivityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open DepthCoercivityReceipt public

canonicalDepthCoercivityReceipt :
  DepthCoercivityReceipt
canonicalDepthCoercivityReceipt =
  record
    { status =
        boundedDepthCoercivityRecordedNoPromotion
    ; statusIsCanonical =
        refl
    ; boundedDepthWindow =
        canonicalBoundedDepthWindow
    ; boundedDepthWindowIsCanonical =
        refl
    ; boundedCoerciveLowerBoundRecorded =
        true
    ; boundedCoerciveLowerBoundRecordedIsTrue =
        refl
    ; depthEmbeddingConstantTracked =
        true
    ; depthEmbeddingConstantTrackedIsTrue =
        refl
    ; embeddingConstantMayDivergeWithDepth =
        true
    ; embeddingConstantMayDivergeWithDepthIsTrue =
        refl
    ; embeddingConstantDivergenceIsGapShrinkage =
        false
    ; embeddingConstantDivergenceIsGapShrinkageIsFalse =
        refl
    ; firstExcitationAtKZeroUnconditionallyProved =
        false
    ; firstExcitationAtKZeroUnconditionallyProvedIsFalse =
        refl
    ; firstExcitationAtKZeroTheoremObligationRecorded =
        true
    ; firstExcitationAtKZeroTheoremObligationRecordedIsTrue =
        refl
    ; continuumGapPromoted =
        false
    ; continuumGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; facts =
        canonicalDepthCoercivityFacts
    ; factsAreCanonical =
        refl
    ; statement =
        depthCoercivityStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Coercivity is recorded only on the bounded depth window K = 0,1,2"
        ∷ "The embedding constant is tracked separately and may diverge with depth"
        ∷ "Embedding-constant divergence is not identified with spectral gap shrinkage"
        ∷ "First excitation at K=0 remains a theorem obligation, not an unconditional proof"
        ∷ "No continuum-gap, Clay Yang-Mills, or terminal Clay promotion follows"
        ∷ []
    }

depthCoercivityKeepsFirstExcitationConditional :
  firstExcitationAtKZeroUnconditionallyProved
    canonicalDepthCoercivityReceipt
  ≡
  false
depthCoercivityKeepsFirstExcitationConditional =
  refl

depthCoercivitySeparatesEmbeddingDivergenceFromGapShrinkage :
  embeddingConstantDivergenceIsGapShrinkage
    canonicalDepthCoercivityReceipt
  ≡
  false
depthCoercivitySeparatesEmbeddingDivergenceFromGapShrinkage =
  refl

depthCoercivityKeepsClayFalse :
  clayYangMillsPromoted canonicalDepthCoercivityReceipt
  ≡
  false
depthCoercivityKeepsClayFalse =
  refl
