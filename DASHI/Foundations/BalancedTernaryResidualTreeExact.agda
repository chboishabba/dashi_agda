module DASHI.Foundations.BalancedTernaryResidualTreeExact where

open import DASHI.Core.Prelude
open import DASHI.Core.Optional public

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.BalancedTernaryAmplitudeClosureExact as Amp

------------------------------------------------------------------------
-- A stage state has two simultaneous charts:
--
-- * a local sheet chart retaining the ordered triad constituents;
-- * a global balanced-ternary radix chart retaining carry/debt structure.
--
-- A coarse fallback changes the visible node but not the retained state.
------------------------------------------------------------------------

record RetainedStageTreeState : Set where
  constructor retained-stage-tree-state
  field
    lowerConstituent upperConstituent : BT.TriadPattern
    localJoinedAmplitude : Amp.JoinedAmplitude13
    localJoinedAmplitudeExact :
      Amp.joinAmplitude lowerConstituent upperConstituent
      ≡ localJoinedAmplitude

    globalAddress : BT.BalancedTernaryAddress
    projectedValue : Nat
    projectedValueExact :
      BT.BalancedTernaryAddress.representedValue globalAddress
      ≡ projectedValue

    visibleAncestorValue : Nat
    residualConstituent : Optional BT.TriadPattern
    coarseProjectionRetainsResidual : Bool
    coarseProjectionRetainsResidualIsTrue :
      coarseProjectionRetainsResidual ≡ true

open RetainedStageTreeState public

stageFiveRetainedTree : RetainedStageTreeState
stageFiveRetainedTree =
  retained-stage-tree-state
    BT.allPositive
    BT.twoPositiveOneOpen
    Amp.joinedPos5 refl
    BT.fiveBalancedAddress 5 refl
    3 (some BT.twoPositiveOneOpen)
    true refl

stageSixRetainedTree : RetainedStageTreeState
stageSixRetainedTree =
  retained-stage-tree-state
    BT.allPositive
    BT.allPositive
    Amp.joinedPos6 refl
    BT.sixBalancedAddress 6 refl
    6 none
    true refl

stageFiveLocalChartIsThreeJoinTwo :
  Amp.triadAmplitude (lowerConstituent stageFiveRetainedTree)
    ≡ Amp.ampPos3
  × Amp.triadAmplitude (upperConstituent stageFiveRetainedTree)
    ≡ Amp.ampPos2
stageFiveLocalChartIsThreeJoinTwo = refl , refl

stageFiveGlobalChartIsOneNegNeg :
  BT.BalancedTernaryAddress.digitsHighToLow
    (globalAddress stageFiveRetainedTree)
  ≡ BT.pos ∷ BT.neg ∷ BT.neg ∷ []
stageFiveGlobalChartIsOneNegNeg = refl

stageFiveVisibleFallbackIsThree :
  visibleAncestorValue stageFiveRetainedTree ≡ 3
stageFiveVisibleFallbackIsThree = refl

stageFiveResidualIsStillPresent :
  residualConstituent stageFiveRetainedTree
  ≡ some BT.twoPositiveOneOpen
stageFiveResidualIsStillPresent = refl

stageFiveProjectionDoesNotEraseTwo :
  residualConstituent stageFiveRetainedTree ≡ none → ⊥
stageFiveProjectionDoesNotEraseTwo ()

stageSixLocalChartIsTwoClosedTriads :
  lowerConstituent stageSixRetainedTree ≡ BT.allPositive
  × upperConstituent stageSixRetainedTree ≡ BT.allPositive
stageSixLocalChartIsTwoClosedTriads = refl , refl

stageSixGlobalChartIsOneNegZero :
  BT.BalancedTernaryAddress.digitsHighToLow
    (globalAddress stageSixRetainedTree)
  ≡ BT.pos ∷ BT.neg ∷ BT.zeroDigit ∷ []
stageSixGlobalChartIsOneNegZero = refl

record RetainedTreeAuthorityBoundary : Set where
  constructor retained-tree-authority-boundary
  field
    localAndRadixChartsRetainedTogether : Bool
    localAndRadixChartsRetainedTogetherIsTrue :
      localAndRadixChartsRetainedTogether ≡ true
    visibleFallbackErasesResidualChild : Bool
    visibleFallbackErasesResidualChildIsFalse :
      visibleFallbackErasesResidualChild ≡ false
    localConstituentChartIdentifiedWithRadixChart : Bool
    localConstituentChartIdentifiedWithRadixChartIsFalse :
      localConstituentChartIdentifiedWithRadixChart ≡ false

canonicalRetainedTreeAuthorityBoundary : RetainedTreeAuthorityBoundary
canonicalRetainedTreeAuthorityBoundary =
  retained-tree-authority-boundary true refl false refl false refl
