module DASHI.Physics.YangMills.BalabanLiteralPositiveDivisionNumeratorCongruenceExact where

-- Actual typed positive-denominator division. The denominator and its
-- positive certificate are FIXED. Endpoint-equivalent numerator intervals
-- must give endpoint-equivalent typed quotient intervals.
-- This is NOT an unlawful total division backend or a claim about
-- independent denominator positivity proofs.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (0ℚ; _<_)
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanLiteralRationalEndpointSemiringExact as End

typedPositiveDivideNumeratorEndpointStable :
  ∀ {a b}
  (denominator : Eval.RationalInterval)
  (denominatorPositive : 0ℚ < Eval.lower denominator) →
  End.SameEndpoints a b →
  End.SameEndpoints
    (Typed.divideInterval a denominator denominatorPositive)
    (Typed.divideInterval b denominator denominatorPositive)
typedPositiveDivideNumeratorEndpointStable
  {a = Eval.interval aLower aUpper aOrdered}
  {b = Eval.interval bLower bUpper bOrdered}
  denominator positive (End.sameEndpoints lowerEqual upperEqual)
  rewrite lowerEqual | upperEqual = End.sameEndpoints refl refl

-- This lemma cannot be applied to the source's UNINDEXED total
-- Eval.RationalIntervalArithmetic.divideInterval without choosing a
-- nonpositive-denominator policy and establishing that policy's soundness.
-- Nor does it prove coherent transfer between distinct positive
-- denominator witnesses: the selected typed division is partial.
