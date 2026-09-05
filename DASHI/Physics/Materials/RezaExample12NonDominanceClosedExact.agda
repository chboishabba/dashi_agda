module DASHI.Physics.Materials.RezaExample12NonDominanceClosedExact where

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Materials.RezaTestedAlloyTradeoffMatrixExact as Matrix
import DASHI.Physics.Materials.RezaParetoWitnessExact as Pareto

------------------------------------------------------------------------
-- EXACT FINITE ARITHMETIC CLOSURE FOR TESTED EXAMPLES 1 AND 2
--
-- Source-owned coordinates:
--   Example 1: tensile 170 ksi, burn threshold 10000 psi
--   Example 2: tensile 187 ksi, burn threshold  7000 psi
--
-- Nat strict inequality m > n is represented by suc n ≤ m.
------------------------------------------------------------------------

example1BurnGreaterThan2 :
  Matrix.burnThresholdPsi Matrix.example1 >
  Matrix.burnThresholdPsi Matrix.example2
example1BurnGreaterThan2 =
  toWitness {a? = NatP._≤?_ 7001 10000} _

example2TensileGreaterThan1 :
  Matrix.tensileKsi Matrix.example2 >
  Matrix.tensileKsi Matrix.example1
example2TensileGreaterThan1 =
  toWitness {a? = NatP._≤?_ 171 187} _

example1Vs2NonDominance :
  Pareto.PairwiseNonDominance Matrix.example1 Matrix.example2
example1Vs2NonDominance =
  Pareto.nonDominanceFromOpposedStrictAdvantages
    example1BurnGreaterThan2
    example2TensileGreaterThan1

record RezaExample12ClosureBoundary : Set where
  constructor reza-example12-closure-boundary
  field
    sourceNumbersNowHaveConstructedNatProofs : Bool
    sourceNumbersNowHaveConstructedNatProofsIsTrue :
      sourceNumbersNowHaveConstructedNatProofs ≡ true
    example1DominatesExample2 : Bool
    example1DominatesExample2IsFalse : example1DominatesExample2 ≡ false
    example2DominatesExample1 : Bool
    example2DominatesExample1IsFalse : example2DominatesExample1 ≡ false
    lowerBoundExample4UsedInThisExactComparison : Bool
    lowerBoundExample4UsedInThisExactComparisonIsFalse :
      lowerBoundExample4UsedInThisExactComparison ≡ false

canonicalRezaExample12ClosureBoundary : RezaExample12ClosureBoundary
canonicalRezaExample12ClosureBoundary =
  reza-example12-closure-boundary true refl false refl false refl false refl
