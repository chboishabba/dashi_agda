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
import DASHI.Analysis.BishopOriginalFiniteLogExpQuotientDefectSplitExact as Delta
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import DASHI.Analysis.BishopOriginalShiftedFactorialUniformModulusExact as Shift
import DASHI.Analysis.BishopOriginalExpOriginDividedDifferenceSeriesExact as Origin
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
open import Data.Rational.Unnormalised using (1ℚᵘ)
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

------------------------------------------------------------------------
-- The original negative LOG increment's absolute value is bounded
-- by an actual, stagewise-uniform original LOG derivative at r.
-- The source proof does NOT assume h>=0.
------------------------------------------------------------------------

originalNegativeLogIncrementAbsoluteIsStepTimesQuotient :
  (n : Nat) (x h : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  R._≃_
    (R.∣ Delta.sourceOriginalNegativeLogDelta n x h ∣)
    (R._*_
      (R.∣ h ∣)
      (Explicit.originalSourceFiniteLogQuotient n x h))
originalNegativeLogIncrementAbsoluteIsStepTimesQuotient
    n x h xNN yNN =
  let
    q = Explicit.originalSourceFiniteLogQuotient n x h
    open RP.ℝ-Solver
    negativeFactor :
      R._≃_ (R._*_ (R.-_ R.1ℝ) q) (R.-_ q)
    negativeFactor =
      solve 1
        (λ qq → (⊝ Κ 1ℚᵘ) ⊗ qq ⊜ ⊝ qq)
        RP.≃-refl q
  in
  RP.≃-trans
    (RP.∣-∣-cong
      (Delta.originalSourceNegativeLogDeltaIsFiniteQuotient
        n x h))
    (RP.≃-trans
      (RP.∣x*y∣≃∣x∣*∣y∣ h (R._*_ (R.-_ R.1ℝ) q))
      (RP.*-cong
        RP.≃-refl
        (RP.≃-trans
          (RP.∣-∣-cong negativeFactor)
          (RP.≃-trans
            (RP.∣-x∣≃∣x∣ {x = q})
            (RP.nonNegx⇒∣x∣≃x
              (sourceFiniteLogQuotientNonnegative
                x h xNN yNN n))))))

originalNegativeLogIncrementUniformRadiusBound :
  (n : Nat) (radius x h : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  R._≤_
    (R.∣ Delta.sourceOriginalNegativeLogDelta n x h ∣)
    (R._*_
      (R.∣ h ∣)
      (Geo.negativeLogDerivativePolynomial radius n))
originalNegativeLogIncrementUniformRadiusBound
    n radius x h xNN yNN xInside yInside =
  RP.≤-respˡ-≃
    (originalNegativeLogIncrementAbsoluteIsStepTimesQuotient
      n x h xNN yNN)
    (RP.≤-respʳ-≃
      (RP.*-cong RP.≃-refl
        (Second.originalFiniteLogQuotientAtZeroIsDerivativePolynomial
          radius n))
      (RP.*-monoˡ-≤-nonNeg
        (originalSourceFiniteLogQuotientRadiusDominance
          x h radius xNN yNN xInside yInside n)
        (RP.nonNeg∣x∣ h)))

------------------------------------------------------------------------
-- Original shifted-factorial quotient controlled by an explicit
-- COMMON mesh radius, not an independent epsilon at every vertex.
------------------------------------------------------------------------

originalFiniteLogRadiusDerivativeNonnegative :
  (radius : R.ℝ) →
  R.NonNegative radius →
  (n : Nat) →
  R.NonNegative (Geo.negativeLogDerivativePolynomial radius n)
originalFiniteLogRadiusDerivativeNonnegative radius radiusNN n =
  RP.nonNeg-cong
    (Second.originalFiniteLogQuotientAtZeroIsDerivativePolynomial
      radius n)
    (sourceFiniteLogQuotientNonnegative
      radius R.0ℝ radiusNN
      (RP.nonNeg-cong
        (RP.≃-symm (RP.+-identityʳ radius)) radiusNN)
      n)

originalFiniteLogShiftedFactorialStagewiseMeshBound :
  (n : Nat) (radius x h : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  let
    p = Geo.negativeLogDerivativePolynomial radius n
    rho = R._*_ (R.∣ h ∣) p
    delta = Delta.sourceOriginalNegativeLogDelta n x h
  in
  R._≤_
    (R.∣ R._-_
      (Origin.originalExpOriginQuotient delta)
      R.1ℝ ∣)
    (R._-_ (Exp.bishopExp rho) R.1ℝ)
originalFiniteLogShiftedFactorialStagewiseMeshBound
    n radius x h xNN yNN xInside yInside =
  let
    p = Geo.negativeLogDerivativePolynomial radius n
    rho = R._*_ (R.∣ h ∣) p
    delta = Delta.sourceOriginalNegativeLogDelta n x h
    radiusNN = Modulus.sourceRadiusNonnegative
      x radius xNN xInside
    rhoNN = RP.nonNegx,y⇒nonNegx*y
      (RP.nonNeg∣x∣ h)
      (originalFiniteLogRadiusDerivativeNonnegative
        radius radiusNN n)
  in
  Shift.originalShiftedFactorialExpQuotientUniformModulus
    rho rhoNN delta
    (originalNegativeLogIncrementUniformRadiusBound
      n radius x h xNN yNN xInside yInside)
