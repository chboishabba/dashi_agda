module DASHI.Analysis.RiemannG21OddTaylorOrderBudgetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Radius-degree bookkeeping for the odd determinant Taylor transfer.
--
-- The six-scaled cubic truncation has terms of radius degree 1 and 3.
-- The first omitted odd Taylor term has radius degree 5.
--
-- Consequently:
--
--   cubic determinant signal:
--     r1 r2 (r2^2-r1^2) Delta       total degree 4,
--
--   truncation x remainder terms:   total degree >= 6,
--   remainder x remainder terms:    total degree >= 10.
--
-- Thus the determinant-level relative error is expected to begin two powers
-- of the sample-radius scale above the signal.  This module records the exact
-- degree arithmetic only; analytic constants and a common small-radius bound
-- remain separate obligations.
------------------------------------------------------------------------

data OddResponseTerm : Set where
  linearTerm cubicTerm remainderTerm : OddResponseTerm

radiusDegree : OddResponseTerm → Nat
radiusDegree linearTerm = 1
radiusDegree cubicTerm = 3
radiusDegree remainderTerm = 5

determinantProductDegree : OddResponseTerm → OddResponseTerm → Nat
determinantProductDegree left right = radiusDegree left + radiusDegree right

linearCubicDegree : determinantProductDegree linearTerm cubicTerm ≡ 4
linearCubicDegree = refl

cubicLinearDegree : determinantProductDegree cubicTerm linearTerm ≡ 4
cubicLinearDegree = refl

linearRemainderDegree : determinantProductDegree linearTerm remainderTerm ≡ 6
linearRemainderDegree = refl

remainderLinearDegree : determinantProductDegree remainderTerm linearTerm ≡ 6
remainderLinearDegree = refl

cubicRemainderDegree : determinantProductDegree cubicTerm remainderTerm ≡ 8
cubicRemainderDegree = refl

remainderCubicDegree : determinantProductDegree remainderTerm cubicTerm ≡ 8
remainderCubicDegree = refl

remainderRemainderDegree : determinantProductDegree remainderTerm remainderTerm ≡ 10
remainderRemainderDegree = refl

signalDegree : Nat
signalDegree = 4

lowestErrorDegree : Nat
lowestErrorDegree = 6

relativeErrorDegreeGap : Nat
relativeErrorDegreeGap = lowestErrorDegree ∸ signalDegree

relativeErrorDegreeGapIsTwo : relativeErrorDegreeGap ≡ 2
relativeErrorDegreeGapIsTwo = refl

record OddTaylorOrderBudget : Set where
  constructor oddTaylorOrderBudget
  field
    signalRadiusDegree : Nat
    firstErrorRadiusDegree : Nat
    relativeRadiusDegreeGap : Nat

    signalRadiusDegreeIsFour : signalRadiusDegree ≡ 4
    firstErrorRadiusDegreeIsSix : firstErrorRadiusDegree ≡ 6
    relativeRadiusDegreeGapIsTwo : relativeRadiusDegreeGap ≡ 2

    analyticConstantsControlled : Bool
    analyticConstantsControlledIsFalse : analyticConstantsControlled ≡ false
    commonSmallRadiusChosen : Bool
    commonSmallRadiusChosenIsFalse : commonSmallRadiusChosen ≡ false

    reading : String

canonicalOddTaylorOrderBudget : OddTaylorOrderBudget
canonicalOddTaylorOrderBudget =
  oddTaylorOrderBudget
    4 6 2 refl refl refl false refl false refl
