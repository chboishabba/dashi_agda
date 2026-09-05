module DASHI.Physics.Materials.RezaParetoWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Materials.RezaTestedAlloyTradeoffMatrixExact as Matrix

------------------------------------------------------------------------
-- Theorem-valued finite comparison surface over source-owned tested examples.
------------------------------------------------------------------------

record StrictlyBetterTensile (x y : Matrix.AlloyExample) : Set where
  constructor strictly-better-tensile
  field
    witness : Matrix.tensileKsi x > Matrix.tensileKsi y

record StrictlyBetterBurn (x y : Matrix.AlloyExample) : Set where
  constructor strictly-better-burn
  field
    witness : Matrix.burnThresholdPsi x > Matrix.burnThresholdPsi y

record PairwiseNonDominance (x y : Matrix.AlloyExample) : Set where
  constructor pairwise-nondominance
  field
    xBetterBurn : StrictlyBetterBurn x y
    yBetterTensile : StrictlyBetterTensile y x

nonDominanceFromOpposedStrictAdvantages :
  {x y : Matrix.AlloyExample} →
  Matrix.burnThresholdPsi x > Matrix.burnThresholdPsi y →
  Matrix.tensileKsi y > Matrix.tensileKsi x →
  PairwiseNonDominance x y
nonDominanceFromOpposedStrictAdvantages burn> tensile> =
  pairwise-nondominance
    (strictly-better-burn burn>)
    (strictly-better-tensile tensile>)

------------------------------------------------------------------------
-- Concrete source arithmetic frontier.
-- Example 1 vs Example 2 is source-numerically:
--   burn:    10000 > 7000
--   tensile:   187 > 170
-- We deliberately do not fake those Nat proofs with hand-written Peano chains.
------------------------------------------------------------------------

record ConcreteComparisonFrontier : Set where
  constructor concrete-comparison-frontier
  field
    leftLabel rightLabel : String
    burnComparison : String
    tensileComparison : String
    natInequalityProofsOwned : Bool
    natInequalityProofsOwnedIsFalse : natInequalityProofsOwned ≡ false
    theoremConstructorReady : Bool
    theoremConstructorReadyIsTrue : theoremConstructorReady ≡ true

example1Vs2Frontier : ConcreteComparisonFrontier
example1Vs2Frontier = concrete-comparison-frontier
  "Example 1"
  "Example 2"
  "10000 > 7000"
  "187 > 170"
  false refl
  true refl

record RezaParetoBoundary : Set where
  constructor reza-pareto-boundary
  field
    sourceNumericReceiptEqualsConstructedNatInequalityProof : Bool
    sourceNumericReceiptEqualsConstructedNatInequalityProofIsFalse :
      sourceNumericReceiptEqualsConstructedNatInequalityProof ≡ false
    lowerBoundExampleMayEnterExactDominanceTest : Bool
    lowerBoundExampleMayEnterExactDominanceTestIsFalse :
      lowerBoundExampleMayEnterExactDominanceTest ≡ false
    opposedStrictAdvantagesSufficeForNonDominance : Bool
    opposedStrictAdvantagesSufficeForNonDominanceIsTrue :
      opposedStrictAdvantagesSufficeForNonDominance ≡ true

canonicalRezaParetoBoundary : RezaParetoBoundary
canonicalRezaParetoBoundary = reza-pareto-boundary false refl false refl true refl
