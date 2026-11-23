{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayCMP102NativeMasterSignedParitySpecializationExact where

------------------------------------------------------------------------
-- YM CMP102 finite signed-row cancellation on the ACTUAL master Bishop
-- factorial Cauchy owner.  No duplicate parity reindexing or new sum.
--
-- The source specializes existing all-degree even exponential coefficient
-- at x = 1, y = -1, and composes with original Bishop expTerm(0,m)=0.
-- The two original rows use positive even and negative odd factorial
-- coefficients, with the right endpoint included exactly once.
--
-- This is NOT the #1444 shifted-CMP109 a/b coefficient attachment:
-- that branch's row identifiers are absent from this master-based tree.
-- No analytic limit, quaternion norm or physical CMP102 claim follows.
-- Sources: Cauchy/binomial, Bishop/Bridges, Murray/Csimma pinned backend,
-- DASHI existing unsigned factorial parity and exponent sources.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopConvergentDoubleTailExact as Double
import DASHI.Foundations.BishopUnsignedFactorialCauchyParitySplitExact as Unsigned
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as Cong
import DASHI.Foundations.BishopExponentialPositiveOrderExact as Positive

originalEvenExponentialRow originalOddExponentialRow : Nat → R.ℝ
originalEvenExponentialRow n =
  Row.cauchyCoefficient
    (Unsigned.evenExp R.1ℝ)
    (Unsigned.evenExp (R.- R.1ℝ)) (suc n)
originalOddExponentialRow n =
  Row.cauchyCoefficient
    (Unsigned.oddExp R.1ℝ)
    (Unsigned.oddExp (R.- R.1ℝ)) n

-- Original degree m = 2(n+1) finite exponential Cauchy row.
originalSignedEvenOddRowZero : ∀ n →
  R._≃_
    (R._+_
      (originalEvenExponentialRow n)
      (originalOddExponentialRow n))
    R.0ℝ
originalSignedEvenOddRowZero n =
  RP.≃-trans
    (Unsigned.unsignedEvenExponentialCoefficientSuccessor
      R.1ℝ (R.- R.1ℝ) n)
    (RP.≃-trans
      (Cong.expTermCongruent
        (RP.+-inverseʳ R.1ℝ)
        (Double.double (suc n)))
      (Positive.expTermZeroAtPositive
        (suc (Double.double n))))

-- This directly establishes cancellation of the real original x=1,
-- y=-1 even/odd exponential rows (all n), WITHOUT identifying them
-- with the shifted native CMP109 A/B coefficient pair on #1444.
-- The latter is the remaining SAME-SOURCE interface and must retain
-- the original singleton/endpoint and bounded Fin index geometry.
