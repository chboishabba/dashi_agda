module DASHI.Analysis.BishopOriginalFiniteLogExpQuotientTriangleExact where

------------------------------------------------------------------------
-- K04d P0.03: ORIGINAL COMPOSITE QUOTIENT DEFECT -- TWO-TERM BOUND.
--
-- From the actual source identity
--
--   q_E - E' = -F_N * (h*S_N*Q(delta) + P_N*(Q(delta)-1))
--
-- construct the original Bishop real absolute triangle, and
-- control each term by the original common compact radius:
--
--   |q_E - E'|
--    <= |F_N| * [ (|h|*S_N(r,0))*|Q(delta)|
--                  + P_N(r)*|Q(delta)-1| ].
--
-- Every term is the real source finite log/exponential quotient.
-- The shifted-factorial last term has already been bounded by
-- exp_B(|h| P_N(r))-1 in the RadiusDominance owner.
-- The still stronger bound |Q(delta)|<=exp_B(|h|P_N(r))
-- can be applied afterwards, without a new quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalFiniteLogQuotientUniformModulusExact as Modulus
import DASHI.Analysis.BishopOriginalFiniteLogSecondQuotientPositiveExact as Positive
import DASHI.Analysis.BishopOriginalFiniteLogQuotientRadiusDominanceExact as Radius
import DASHI.Analysis.BishopOriginalFiniteLogExpQuotientDefectSplitExact as Split
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo

sourceTriangleFirstTerm :
  (n : Nat) (x h : R.ℝ) → R.ℝ
sourceTriangleFirstTerm n x h =
  R._*_
    (R._*_ h (Second.sourceFiniteLogSecondQuotient x h n))
    (Split.sourceOriginalExpShiftedFactorial n x h)

sourceTriangleSecondTerm :
  (n : Nat) (x h : R.ℝ) → R.ℝ
sourceTriangleSecondTerm n x h =
  R._*_
    (Geo.negativeLogDerivativePolynomial x n)
    (R._-_ (Split.sourceOriginalExpShiftedFactorial n x h) R.1ℝ)

originalFiniteLogErrorQuotientAbsoluteTriangle :
  (n : Nat) (x h : R.ℝ) →
  let
    f = Finite.originalNegativeLogFiniteExponential x n
    a = sourceTriangleFirstTerm n x h
    b = sourceTriangleSecondTerm n x h
  in
  R._≤_
    (R.∣ Split.sourceOriginalErrorSlopeDefect n x h ∣)
    (R._*_
      (R.∣ f ∣)
      (R._+_ (R.∣ a ∣) (R.∣ b ∣)))
originalFiniteLogErrorQuotientAbsoluteTriangle n x h =
  let
    f = Finite.originalNegativeLogFiniteExponential x n
    a = sourceTriangleFirstTerm n x h
    b = sourceTriangleSecondTerm n x h
    open RP.ℝ-Solver
    sameSource =
      Split.originalFiniteLogErrorQuotientDefectSplit n x h
    absDefectIsFactor =
      RP.≃-trans
        (RP.∣-∣-cong sameSource)
        (RP.≃-trans
          (RP.∣x*y∣≃∣x∣*∣y∣ (R.-_ f) (R._+_ a b))
          (RP.*-cong
            (RP.∣-x∣≃∣x∣ {x = f})
            RP.≃-refl))
  in
  RP.≤-respˡ-≃
    absDefectIsFactor
    (RP.*-monoˡ-≤-nonNeg
      (RP.∣x+y∣≤∣x∣+∣y∣ a b)
      (RP.nonNeg∣x∣ f))

originalFiniteLogErrorFirstTermRadiusBound :
  (n : Nat) (radius x h : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  R._≤_
    (R.∣ sourceTriangleFirstTerm n x h ∣)
    (R._*_
      (R._*_
        (R.∣ h ∣)
        (Second.sourceFiniteLogSecondQuotient radius R.0ℝ n))
      (R.∣ Split.sourceOriginalExpShiftedFactorial n x h ∣))
originalFiniteLogErrorFirstTermRadiusBound
    n radius x h xNN yNN xInside yInside =
  let
    s = Second.sourceFiniteLogSecondQuotient x h n
    q = Split.sourceOriginalExpShiftedFactorial n x h
    absFactor =
      RP.≃-trans
        (RP.∣x*y∣≃∣x∣*∣y∣ (R._*_ h s) q)
        (RP.*-cong
          (RP.≃-trans
            (RP.∣x*y∣≃∣x∣*∣y∣ h s)
            (RP.*-cong RP.≃-refl
              (RP.nonNegx⇒∣x∣≃x
                (Positive.originalFiniteLogSecondQuotientNonnegative
                  x h xNN yNN n))))
          RP.≃-refl)
    factorBound =
      RP.*-monoʳ-≤-nonNeg
        (RP.*-monoˡ-≤-nonNeg
          (Modulus.sourceFiniteLogSecondQuotientMonotone
            x h radius xNN yNN xInside yInside n)
          (RP.nonNeg∣x∣ h))
        (RP.nonNeg∣x∣ q)
  in
  RP.≤-respˡ-≃ absFactor factorBound

originalFiniteLogErrorSecondTermRadiusBound :
  (n : Nat) (radius x h : R.ℝ) →
  (xNN : R.NonNegative x) →
  (xInside : R._≤_ x radius) →
  R._≤_
    (R.∣ sourceTriangleSecondTerm n x h ∣)
    (R._*_
      (Geo.negativeLogDerivativePolynomial radius n)
      (R.∣ R._-_
        (Split.sourceOriginalExpShiftedFactorial n x h)
        R.1ℝ ∣))
originalFiniteLogErrorSecondTermRadiusBound
    n radius x h xNN xInside =
  let
    p = Geo.negativeLogDerivativePolynomial x n
    defect = R._-_ (Split.sourceOriginalExpShiftedFactorial n x h) R.1ℝ
    absFactor =
      RP.≃-trans
        (RP.∣x*y∣≃∣x∣*∣y∣ p defect)
        (RP.*-cong
          (RP.nonNegx⇒∣x∣≃x
            (Radius.originalFiniteLogRadiusDerivativeNonnegative
              x xNN n))
          RP.≃-refl)
  in
  RP.≤-respˡ-≃ absFactor
    (RP.*-monoʳ-≤-nonNeg
      (Radius.originalFiniteLogDerivativeRadiusDominance
        x radius xNN xInside n)
      (RP.nonNeg∣x∣ defect))

originalFiniteLogErrorQuotientRadiusTriangle :
  (n : Nat) (radius x h : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  let
    f = Finite.originalNegativeLogFiniteExponential x n
    q = Split.sourceOriginalExpShiftedFactorial n x h
    s = Second.sourceFiniteLogSecondQuotient radius R.0ℝ n
    p = Geo.negativeLogDerivativePolynomial radius n
  in
  R._≤_
    (R.∣ Split.sourceOriginalErrorSlopeDefect n x h ∣)
    (R._*_
      (R.∣ f ∣)
      (R._+_
        (R._*_ (R._*_ (R.∣ h ∣) s) (R.∣ q ∣))
        (R._*_ p (R.∣ R._-_ q R.1ℝ ∣))))
originalFiniteLogErrorQuotientRadiusTriangle
    n radius x h xNN yNN xInside yInside =
  RP.≤-trans
    (originalFiniteLogErrorQuotientAbsoluteTriangle n x h)
    (RP.*-monoˡ-≤-nonNeg
      (RP.+-mono-≤
        (originalFiniteLogErrorFirstTermRadiusBound
          n radius x h xNN yNN xInside yInside)
        (originalFiniteLogErrorSecondTermRadiusBound
          n radius x h xNN xInside))
      (RP.nonNeg∣x∣
        (Finite.originalNegativeLogFiniteExponential x n)))
