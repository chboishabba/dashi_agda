module DASHI.Reasoning.TernaryComparisonSynthesisExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Make the local comparison/synthesis reading of the existing 3/6/9/27
-- carriers explicit without replacing any of them.
--
--   T x T = diagonal agreement (3) + directed disagreement (6)
--   synthesis choice adds one ternary coordinate
--   (T x T) x T = T^3 = 27.
--
-- A synthesis rule is total when it supplies one ternary synthesis coordinate
-- for every ordered comparison. Disagreement is retained in the first two
-- coordinates; synthesis does not erase the boundary that produced it.
--
-- Counterposition, reversal and strict inversion remain separate operations,
-- reusing the repository's existing exact counterposition-not-inverse theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.CounterpositionOrderedJoinExact as Counter
import DASHI.Interop.PNFHyperfabric369 as PNF

Comparison9 : Set
Comparison9 = Base.TriTruth × Base.TriTruth

data Agreement3 : Set where
  agreeLow agreeMid agreeHigh : Agreement3

data DirectedDisagreement6 : Set where
  lowToMid
    midToLow
    lowToHigh
    highToLow
    midToHigh
    highToMid : DirectedDisagreement6

ComparisonClass9 : Set
ComparisonClass9 = Agreement3 ⊎ DirectedDisagreement6

classifyComparison : Comparison9 → ComparisonClass9
classifyComparison (Base.tri-low , Base.tri-low) = inj₁ agreeLow
classifyComparison (Base.tri-low , Base.tri-mid) = inj₂ lowToMid
classifyComparison (Base.tri-low , Base.tri-high) = inj₂ lowToHigh
classifyComparison (Base.tri-mid , Base.tri-low) = inj₂ midToLow
classifyComparison (Base.tri-mid , Base.tri-mid) = inj₁ agreeMid
classifyComparison (Base.tri-mid , Base.tri-high) = inj₂ midToHigh
classifyComparison (Base.tri-high , Base.tri-low) = inj₂ highToLow
classifyComparison (Base.tri-high , Base.tri-mid) = inj₂ highToMid
classifyComparison (Base.tri-high , Base.tri-high) = inj₁ agreeHigh

forgetComparisonClass : ComparisonClass9 → Comparison9
forgetComparisonClass (inj₁ agreeLow) =
  Base.tri-low , Base.tri-low
forgetComparisonClass (inj₁ agreeMid) =
  Base.tri-mid , Base.tri-mid
forgetComparisonClass (inj₁ agreeHigh) =
  Base.tri-high , Base.tri-high
forgetComparisonClass (inj₂ lowToMid) =
  Base.tri-low , Base.tri-mid
forgetComparisonClass (inj₂ midToLow) =
  Base.tri-mid , Base.tri-low
forgetComparisonClass (inj₂ lowToHigh) =
  Base.tri-low , Base.tri-high
forgetComparisonClass (inj₂ highToLow) =
  Base.tri-high , Base.tri-low
forgetComparisonClass (inj₂ midToHigh) =
  Base.tri-mid , Base.tri-high
forgetComparisonClass (inj₂ highToMid) =
  Base.tri-high , Base.tri-mid

forgetAfterClassifyComparison :
  (comparison : Comparison9) →
  forgetComparisonClass (classifyComparison comparison) ≡ comparison
forgetAfterClassifyComparison (Base.tri-low , Base.tri-low) = refl
forgetAfterClassifyComparison (Base.tri-low , Base.tri-mid) = refl
forgetAfterClassifyComparison (Base.tri-low , Base.tri-high) = refl
forgetAfterClassifyComparison (Base.tri-mid , Base.tri-low) = refl
forgetAfterClassifyComparison (Base.tri-mid , Base.tri-mid) = refl
forgetAfterClassifyComparison (Base.tri-mid , Base.tri-high) = refl
forgetAfterClassifyComparison (Base.tri-high , Base.tri-low) = refl
forgetAfterClassifyComparison (Base.tri-high , Base.tri-mid) = refl
forgetAfterClassifyComparison (Base.tri-high , Base.tri-high) = refl

classifyAfterForgetComparison :
  (comparisonClass : ComparisonClass9) →
  classifyComparison (forgetComparisonClass comparisonClass)
  ≡ comparisonClass
classifyAfterForgetComparison (inj₁ agreeLow) = refl
classifyAfterForgetComparison (inj₁ agreeMid) = refl
classifyAfterForgetComparison (inj₁ agreeHigh) = refl
classifyAfterForgetComparison (inj₂ lowToMid) = refl
classifyAfterForgetComparison (inj₂ midToLow) = refl
classifyAfterForgetComparison (inj₂ lowToHigh) = refl
classifyAfterForgetComparison (inj₂ highToLow) = refl
classifyAfterForgetComparison (inj₂ midToHigh) = refl
classifyAfterForgetComparison (inj₂ highToMid) = refl

------------------------------------------------------------------------
-- Directed reversal is an involution on the six disagreement edges.
------------------------------------------------------------------------

reverseDisagreement : DirectedDisagreement6 → DirectedDisagreement6
reverseDisagreement lowToMid = midToLow
reverseDisagreement midToLow = lowToMid
reverseDisagreement lowToHigh = highToLow
reverseDisagreement highToLow = lowToHigh
reverseDisagreement midToHigh = highToMid
reverseDisagreement highToMid = midToHigh

reverseDisagreementInvolutive :
  (edge : DirectedDisagreement6) →
  reverseDisagreement (reverseDisagreement edge) ≡ edge
reverseDisagreementInvolutive lowToMid = refl
reverseDisagreementInvolutive midToLow = refl
reverseDisagreementInvolutive lowToHigh = refl
reverseDisagreementInvolutive highToLow = refl
reverseDisagreementInvolutive midToHigh = refl
reverseDisagreementInvolutive highToMid = refl

------------------------------------------------------------------------
-- Synthesis is a third coordinate, not deletion of the comparison boundary.
------------------------------------------------------------------------

SynthesisChoice27 : Set
SynthesisChoice27 = Tower.LevelTwoCode

makeSynthesisChoice :
  Base.TriTruth →
  Base.TriTruth →
  Base.TriTruth →
  SynthesisChoice27
makeSynthesisChoice left right synthesis =
  left , (right , synthesis)

comparisonOfSynthesis : SynthesisChoice27 → Comparison9
comparisonOfSynthesis (left , (right , synthesis)) =
  left , right

synthesisCoordinate : SynthesisChoice27 → Base.TriTruth
synthesisCoordinate (left , (right , synthesis)) =
  synthesis

comparisonBoundaryRetained :
  (left right synthesis : Base.TriTruth) →
  comparisonOfSynthesis (makeSynthesisChoice left right synthesis)
  ≡ (left , right)
comparisonBoundaryRetained left right synthesis = refl

synthesisCoordinateRetained :
  (left right synthesis : Base.TriTruth) →
  synthesisCoordinate (makeSynthesisChoice left right synthesis)
  ≡ synthesis
synthesisCoordinateRetained left right synthesis = refl

record TotalSynthesisRule : Set where
  constructor totalSynthesisRule
  field
    synthesize : Base.TriTruth → Base.TriTruth → Base.TriTruth

open TotalSynthesisRule public

applySynthesisRule :
  TotalSynthesisRule → Comparison9 → SynthesisChoice27
applySynthesisRule rule (left , right) =
  makeSynthesisChoice left right (synthesize rule left right)

everyComparisonReceivesSynthesis :
  (rule : TotalSynthesisRule) →
  (comparison : Comparison9) →
  comparisonOfSynthesis (applySynthesisRule rule comparison)
  ≡ comparison
everyComparisonReceivesSynthesis rule (left , right) = refl

------------------------------------------------------------------------
-- Existing counterposition theorem: counterposition is context indexed and
-- need not equal strict inversion.
------------------------------------------------------------------------

existingPartialCounterpositionIsNotFullInverse :
  Counter.counterUnder Counter.rejectThird BT.allPositive
  ≡ Counter.counterUnder Counter.invertAll BT.allPositive
  → ⊥
existingPartialCounterpositionIsNotFullInverse =
  Counter.partialCounterpositionIsNotFullInverse

------------------------------------------------------------------------
-- Dimension bridge to the already-existing PNF hyperfabric.
------------------------------------------------------------------------

comparisonDimension : Nat
comparisonDimension = 3 * 3

synthesisChoiceDimension : Nat
synthesisChoiceDimension = 3 * 3 * 3

comparisonDimensionIsNine : comparisonDimension ≡ 9
comparisonDimensionIsNine = refl

synthesisChoiceDimensionIsTwentySeven :
  synthesisChoiceDimension ≡ 27
synthesisChoiceDimensionIsTwentySeven = refl

comparisonMatchesPNFNonary :
  comparisonDimension ≡ PNF.nonaryDimension
comparisonMatchesPNFNonary = refl

synthesisMatchesPNFDialecticAtom :
  synthesisChoiceDimension ≡ PNF.dialecticDiscussionAtomDimension
synthesisMatchesPNFDialecticAtom = refl

record TernaryComparisonSynthesisBoundary : Set where
  field
    diagonalPlusDirectedSixConstructed : Bool
    diagonalPlusDirectedSixConstructedIsTrue :
      diagonalPlusDirectedSixConstructed ≡ true

    synthesisTotalityIsRuleIndexed : Bool
    synthesisTotalityIsRuleIndexedIsTrue :
      synthesisTotalityIsRuleIndexed ≡ true

    synthesisErasesComparisonBoundary : Bool
    synthesisErasesComparisonBoundaryIsFalse :
      synthesisErasesComparisonBoundary ≡ false

    counterpositionIdentifiedWithStrictInverse : Bool
    counterpositionIdentifiedWithStrictInverseIsFalse :
      counterpositionIdentifiedWithStrictInverse ≡ false

canonicalTernaryComparisonSynthesisBoundary :
  TernaryComparisonSynthesisBoundary
canonicalTernaryComparisonSynthesisBoundary =
  record
    { diagonalPlusDirectedSixConstructed = true
    ; diagonalPlusDirectedSixConstructedIsTrue = refl
    ; synthesisTotalityIsRuleIndexed = true
    ; synthesisTotalityIsRuleIndexedIsTrue = refl
    ; synthesisErasesComparisonBoundary = false
    ; synthesisErasesComparisonBoundaryIsFalse = refl
    ; counterpositionIdentifiedWithStrictInverse = false
    ; counterpositionIdentifiedWithStrictInverseIsFalse = refl
    }
