module DASHI.Analysis.BishopOriginalFiniteLogQuotientRadiusDominanceExact where

------------------------------------------------------------------------
-- K04d P0.03: ORIGINAL FINITE LOG QUOTIENT RADIUS DOMINANCE.
--
-- On any two nonnegative Bishop endpoints x,y=x+h bounded by r,
-- the literal original power quotient Q_k(x,h) and original
-- finite LOG quotient q_L,N(x,h) are both nonnegative and <=
-- their same-stage values with both endpoints equal to r.
--
--    0 <= q_L,N(x,h) <= q_L,N(r,0) = P_N(r).
--
-- No derivative-limit exchange, integration or nonzero division.
-- This proves a stagewise common bound for the original negative
-- logarithm increment:
--    |Delta_N(x,h)| <= |h| * P_N(r)
-- after the source signed-increment normalization is consumed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExplicitQuotientExact as Explicit
import DASHI.Analysis.BishopOriginalNegativeLogFiniteDerivativeExact as LogFinite
import DASHI.Analysis.BishopOriginalFiniteLogQuotientUniformModulusExact as Modulus
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip

sourcePowerQuotientNonnegative :
  (x h : R.ℝ) →
  R.NonNegative x →
  R.NonNegative (R._+_ x h) →
  (n : Nat) →
  R.NonNegative (Power.powerDifferenceQuotient x h n)
sourcePowerQuotientNonnegative x h xNN yNN zero = RP.nonNeg0
sourcePowerQuotientNonnegative x h xNN yNN (suc n) =
  RP.nonNegx,y⇒nonNegx+y
    (RP.nonNegx,y⇒nonNegx*y
      (sourcePowerQuotientNonnegative x h xNN yNN n)
      yNN)
    (Seq.nonNegx⇒nonNegxⁿ n xNN)

sourcePowerQuotientRadiusDominance :
  (x h radius : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  (n : Nat) →
  R._≤_
    (Power.powerDifferenceQuotient x h n)
    (Power.powerDifferenceQuotient radius R.0ℝ n)
sourcePowerQuotientRadiusDominance
    x h radius xNN yNN xInside yInside zero =
  RP.≤-refl
sourcePowerQuotientRadiusDominance
    x h radius xNN yNN xInside yInside (suc n) =
  let
    rNN = Modulus.sourceRadiusNonnegative x radius xNN xInside
    rpNN = RP.nonNeg-cong
      (RP.≃-symm (RP.+-identityʳ radius)) rNN
    yBelowRPlusZero =
      RP.≤-respʳ-≃
        (RP.≃-symm (RP.+-identityʳ radius))
        yInside
    productOrder =
      RP.≤-trans
        (RP.*-monoˡ-≤-nonNeg
          yBelowRPlusZero
          (sourcePowerQuotientNonnegative x h xNN yNN n))
        (RP.*-monoʳ-≤-nonNeg
          (sourcePowerQuotientRadiusDominance
            x h radius xNN yNN xInside yInside n)
          rpNN)
    powerOrder = Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
      n xInside xNN
  in
  RP.+-mono-≤ productOrder powerOrder

sourceFiniteLogQuotientNonnegative :
  (x h : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (n : Nat) →
  R.NonNegative (Explicit.originalSourceFiniteLogQuotient n x h)
sourceFiniteLogQuotientNonnegative x h xNN yNN zero =
  RP.nonNeg0
sourceFiniteLogQuotientNonnegative x h xNN yNN (suc n) =
  RP.nonNegx,y⇒nonNegx+y
    (sourceFiniteLogQuotientNonnegative x h xNN yNN n)
    (RP.nonNegx,y⇒nonNegx*y
      (Recip.reciprocalNonnegative n)
      (sourcePowerQuotientNonnegative x h xNN yNN (suc n)))

originalSourceFiniteLogQuotientRadiusDominance :
  (x h radius : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  (n : Nat) →
  R._≤_
    (Explicit.originalSourceFiniteLogQuotient n x h)
    (Explicit.originalSourceFiniteLogQuotient n radius R.0ℝ)
originalSourceFiniteLogQuotientRadiusDominance
    x h radius xNN yNN xInside yInside zero =
  RP.≤-refl
originalSourceFiniteLogQuotientRadiusDominance
    x h radius xNN yNN xInside yInside (suc n) =
  RP.+-mono-≤
    (originalSourceFiniteLogQuotientRadiusDominance
      x h radius xNN yNN xInside yInside n)
    (RP.*-monoˡ-≤-nonNeg
      (sourcePowerQuotientRadiusDominance
        x h radius xNN yNN xInside yInside (suc n))
      (Recip.reciprocalNonnegative n))
