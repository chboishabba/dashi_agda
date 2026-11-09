module DASHI.Analysis.BishopOriginalFiniteLogSecondQuotientPositiveExact where

------------------------------------------------------------------------
-- K04d P0.01: NATIVE ORDER OF THE EXACT SECOND QUOTIENT
--
-- The original second quotient polynomial T_n(x,h) and the
-- original finite log second-quotient S_N(x,h) have nonnegative
-- coefficients on any TWO nonnegative endpoints x and x+h.
--
-- In particular, no h>=0 condition is needed for S_N>=0;
-- the *endpoints* matter. The original LOG coefficients are
-- the pinned reciprocals 1/(n+1) and are genuinely nonnegative.
--
-- This supplies the sign used in the uniform modulus proof.
-- It does not claim the upper majorant on S_N.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as NatRecip

originalPowerZeroStepQuotientNonnegative :
  (x : R.ℝ) →
  R.NonNegative x →
  (n : Nat) →
  R.NonNegative (Power.powerDifferenceQuotient x R.0ℝ n)
originalPowerZeroStepQuotientNonnegative x xNN zero = RP.nonNeg0
originalPowerZeroStepQuotientNonnegative x xNN (suc n) =
  RP.nonNegx,y⇒nonNegx+y
    (RP.nonNegx,y⇒nonNegx*y
      (originalPowerZeroStepQuotientNonnegative x xNN n)
      (RP.nonNeg-cong
        (RP.≃-symm (RP.+-identityʳ x)) xNN))
    (Seq.nonNegx⇒nonNegxⁿ n xNN)

originalPowerSecondQuotientNonnegative :
  (x h : R.ℝ) →
  R.NonNegative x →
  R.NonNegative (R._+_ x h) →
  (n : Nat) →
  R.NonNegative (Second.sourcePowerSecondQuotient x h n)
originalPowerSecondQuotientNonnegative x h xNN yNN zero =
  RP.nonNeg0
originalPowerSecondQuotientNonnegative x h xNN yNN (suc n) =
  RP.nonNegx,y⇒nonNegx+y
    (RP.nonNegx,y⇒nonNegx*y
      (originalPowerSecondQuotientNonnegative x h xNN yNN n)
      yNN)
    (originalPowerZeroStepQuotientNonnegative x xNN n)

originalFiniteLogSecondQuotientNonnegative :
  (x h : R.ℝ) →
  R.NonNegative x →
  R.NonNegative (R._+_ x h) →
  (n : Nat) →
  R.NonNegative (Second.sourceFiniteLogSecondQuotient x h n)
originalFiniteLogSecondQuotientNonnegative x h xNN yNN zero =
  RP.nonNeg0
originalFiniteLogSecondQuotientNonnegative x h xNN yNN (suc n) =
  RP.nonNegx,y⇒nonNegx+y
    (originalFiniteLogSecondQuotientNonnegative x h xNN yNN n)
    (RP.nonNegx,y⇒nonNegx*y
      (NatRecip.reciprocalNonnegative n)
      (originalPowerSecondQuotientNonnegative
        x h xNN yNN (suc n)))
