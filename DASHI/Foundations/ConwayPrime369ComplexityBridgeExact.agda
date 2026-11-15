module DASHI.Foundations.ConwayPrime369ComplexityBridgeExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Foundations.ConwayChainedArrowFiniteBridgeExact as Conway
import DASHI.Foundations.PrimorialFactorAddressConcrete as Prime
import DASHI.Cognition.RecursiveFibreTower as Fibre

-- A syntax tree is an *intensional* witness: its size is not its value.
-- A Karp reduction must account for the binary length of its materialised
-- output, not only the number of nodes in the input expression.
data GrowthCode : Set where
  literal : Nat → GrowthCode
  arrow3 : Nat → Nat → Nat → GrowthCode
  factorialIter : Nat → Nat → GrowthCode
  primeDigits : Prime.PrimorialDigits4 → GrowthCode

evaluate : GrowthCode → Nat
evaluate (literal n) = n
evaluate (arrow3 a b c) = Conway.three a b c
evaluate (factorialIter seed height) =
  Conway.factorialTower seed height
evaluate (primeDigits d) = Prime.primeExponentProduct4 d

-- Complexity must distinguish syntax description, printed numeral,
-- encoded factor-address, and executable reduction/runtime budgets.
record RepresentationCost : Set where
  constructor representationCost
  field
    syntaxNodes : Nat
    emittedBits : Nat
    verifierSteps : Nat
    decoderSteps : Nat

-- These are different complexity quantities, without a polynomiality claim.
record CostedRepresentation (code : GrowthCode) : Set where
  constructor costedRepresentation
  field
    cost : RepresentationCost
    generatedValue : Nat
    evaluationFaithful : generatedValue ≡ evaluate code

-- Prime-exponent vector is already a concrete repository representation.
-- 3, 6, 9 are deliberately coordinates here, NOT Conway arrow ranks.
digits369 : Prime.PrimorialDigits4
digits369 = Prime.primorialDigits4 3 6 9 0

digits369Decode : Prime.primorialDecode4 digits369 ≡ 69
digits369Decode = refl

digits369FactorProduct :
  Prime.primeExponentProduct4 digits369
    ≡ Prime.pow 2 3 * (Prime.pow 3 6 *
       (Prime.pow 5 9 * Prime.pow 7 0))
digits369FactorProduct = refl

-- C3^3 means three independent ternary positions, giving 27 combinations.
-- Tetration height two gives 3^3 = 27 by coincidence of arithmetic value,
-- but these are typed differently and have different growth recurrences.
threeAxisC3Cardinality : 3 * (3 * 3) ≡ 27
threeAxisC3Cardinality = refl

tetrationHeightTwoCardinality : Fibre.tetration 3 2 ≡ 27
tetrationHeightTwoCardinality = refl

conwayHeightTwoCardinality : Conway.three 3 2 2 ≡ 27
conwayHeightTwoCardinality = refl

primeDigits369AsGrowthCode : evaluate (primeDigits digits369)
  ≡ Prime.primeExponentProduct4 digits369
primeDigits369AsGrowthCode = refl

-- Concrete small same-value representations require explicit equality.
-- No structural equivalence of a C3 cube and tetrational fibre is inferred.
conwayCubeNumericCoincidence :
  Conway.three 3 2 2 ≡ 3 * (3 * 3)
conwayCubeNumericCoincidence = refl

record ReductionBoundary : Set where
  constructor reductionBoundary
  field
    syntaxSizeIsEmittedBitCost : Bool
    syntaxSizeIsEmittedBitCostIsFalse :
      syntaxSizeIsEmittedBitCost ≡ false
    representationCoincidenceProvesKarpReduction : Bool
    representationCoincidenceProvesKarpReductionIsFalse :
      representationCoincidenceProvesKarpReduction ≡ false
    c3CardinalityEqualityProvesIsomorphism : Bool
    c3CardinalityEqualityProvesIsomorphismIsFalse :
      c3CardinalityEqualityProvesIsomorphism ≡ false

canonicalReductionBoundary : ReductionBoundary
canonicalReductionBoundary =
  reductionBoundary false refl false refl false refl
