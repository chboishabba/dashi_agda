module DASHI.Physics.YangMills.BalabanClayT4NaiveNormalizedSineSquareCounterexampleExact where

-- Original-source negative control: expanding the Wilson hat momentum
-- atom into four ordinary interval squares, *without* tracking that both
-- factors are the same sine value, can destroy strict positivity.
--
-- The source regular cell has three inner axes [-1,1] and one outer.
-- Generic four-corner interval product [-1,1]*[-1,1] = [-1,1],
-- even though the true square is nonnegative. This invalidates using
-- naive normalizeHatMomentum + generic multiplyInterval to certify
-- the propagator denominator on rank-one regular boxes.
--
-- Refined square (dependency-aware) is a sound remedy, but physical
-- sine enclosures and actual diagram sources still have to be admitted.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4RefinedSineSquareRegularBoxesExact as Refined

originalInner : Eval.RationalInterval
originalInner = Refined.sourceSineBox Grid.negativeInner

rawSquare : Eval.RationalInterval
rawSquare = Typed.multiplyInterval originalInner originalInner

rawSquareLowerIsNegativeOne :
  Eval.lower rawSquare ≡ ℚ.- 1ℚ
rawSquareLowerIsNegativeOne = refl

rawSquareUpperIsOne :
  Eval.upper rawSquare ≡ 1ℚ
rawSquareUpperIsOne = refl

refinedSquareLowerIsZero :
  Eval.lower (Refined.refinedSquare originalInner) ≡ 0ℚ
refinedSquareLowerIsZero = refl

naiveComponent : Grid.IntervalCell → Eval.RationalInterval
naiveComponent c =
  Typed.multiplyInterval
    (Canonical.singletonInterval Canonical.fourRational)
    (Typed.multiplyInterval (Refined.sourceSineBox c)
      (Refined.sourceSineBox c))

-- Rank-one source cell: 3 inner, 1 positive outer.
rankOne : Grid.GridCell4
rankOne = Grid.gridCell4
  Grid.positiveOuter Grid.negativeInner
  Grid.negativeInner Grid.negativeInner

naiveRankOneDenominator : Eval.RationalInterval
naiveRankOneDenominator =
  Typed.addInterval
    (Typed.addInterval
      (naiveComponent Grid.positiveOuter)
      (naiveComponent Grid.negativeInner))
    (Typed.addInterval
      (naiveComponent Grid.negativeInner)
      (naiveComponent Grid.negativeInner))

-- This lower bound is <= 0, so original Typed.divideInterval cannot
-- accept it as a strictly-positive source denominator.
naiveRankOneCannotProvePositiveByItsLower :
  Eval.lower naiveRankOneDenominator ≤ 0ℚ
naiveRankOneCannotProvePositiveByItsLower = ℚP.≤ᵇ⇒≤ tt

refinedRankOneHasPositiveLower :
  0ℚ < Eval.lower (Refined.sourceWilsonDenominatorBox rankOne)
refinedRankOneHasPositiveLower =
  Refined.sourceStrictPositiveAtRegularBox rankOne refl

-- This no-go is about the SPECIFIC interval-extension algorithm,
-- not a singularity of the underlying physical Wilson propagator.
