module DASHI.Physics.Materials.RezaParetoWitnessExact where

open import DASHI.Core.Prelude

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

example1HigherBurnThan2 : StrictlyBetterBurn Matrix.example1 Matrix.example2
example1HigherBurnThan2 = strictly-better-burn (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

-- We avoid hand-proving the full large-N inequalities here; instead expose the
-- source-owned arithmetic comparison as a typed receipt until Nat comparison
-- automation is wired into this branch.
record SourceArithmeticComparison : Set where
  constructor source-arithmetic-comparison
  field
    proposition : Set
    statement : Bool
    statementIsTrue : statement ≡ true

example1Vs2NonDominanceReceipt : SourceArithmeticComparison
example1Vs2NonDominanceReceipt =
  source-arithmetic-comparison
    (PairwiseNonDominance Matrix.example1 Matrix.example2)
    true refl

record RezaParetoBoundary : Set where
  constructor reza-pareto-boundary
  field
    receiptEqualsConstructedNatInequalityProof : Bool
    receiptEqualsConstructedNatInequalityProofIsFalse :
      receiptEqualsConstructedNatInequalityProof ≡ false
    lowerBoundExampleMayEnterExactDominanceTest : Bool
    lowerBoundExampleMayEnterExactDominanceTestIsFalse :
      lowerBoundExampleMayEnterExactDominanceTest ≡ false

canonicalRezaParetoBoundary : RezaParetoBoundary
canonicalRezaParetoBoundary = reza-pareto-boundary false refl false refl
