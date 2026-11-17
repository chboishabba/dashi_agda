module DASHI.Moonshine.JInvariantEllipticStandardJValuesCompilerExact where

------------------------------------------------------------------------
-- SAME ORIGINAL STANDARD-j AT THE TWO ELLIPTIC FIXED POINTS
--
-- This composes the repository's actual Eisenstein transformation theorem,
-- normalized discriminant and standard-j quotient. No duplicate j
-- function, numerical approximation, or asserted special-value input.
--
-- The evidence record below contains explicit outstanding point, field,
-- normalization and nonvanishing requirements. The results are genuine
-- consequences, but a literal Bishop-complex instance is still OPEN.
--
-- Source: Serre, A Course in Arithmetic (1973); Miyake, Modular Forms
-- (2006). The formal provenance is the existing DASHI owner chain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality
  using (cong; trans; subst)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as E
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as D
import DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact as N
import DASHI.Moonshine.JSameWeightQuotientInvariantExact as Q
import DASHI.Moonshine.JInvariantAnalyticNormalizedKleinAdapterExact as J
import DASHI.Moonshine.JInvariantEllipticFixedPointCompilerExact as Fixed

record EllipticValueFieldEvidence
    (M : E.EisensteinAnalyticModel)
    (A : D.DiscriminantAlgebra M)
    (Norm : N.WeightCompatibleNormalization M)
    (Div : Q.QuotientCancellationAlgebra M)
    (W : Fixed.EllipticFixedPointEvidence M) : Set₁ where
  field
    scalar1728 : E.Scalar M

    zeroCube : D.cube M (E.zero M) ≡ E.zero M

    subtractSquareZero :
      (x : E.Scalar M) →
      D._-ˢ_ A x (D.square M (E.zero M)) ≡ x

    -- Actual normalized Delta nonvanishing at the literal points.
    deltaSafeAtI :
      Q.DenominatorSafe Div
        (N.normalizedDelta M A Norm (Fixed.iPoint W))

    deltaSafeAtOmega :
      Q.DenominatorSafe Div
        (N.normalizedDelta M A Norm (Fixed.omegaPoint W))

    zeroNumeratorQuotient :
      (denominator : E.Scalar M) →
      Q.DenominatorSafe Div denominator →
      Q._/ˢ_ Div (E.zero M) denominator ≡ E.zero M

    -- A concrete field proves this from normalize(x)=x/1728
    -- and cancellation with the required denominator witness.
    normalizedSelfQuotient :
      (x : E.Scalar M) →
      Q.DenominatorSafe Div (N.normalize Norm x) →
      Q._/ˢ_ Div x (N.normalize Norm x) ≡ scalar1728

open EllipticValueFieldEvidence public

jAtOmegaIsZero :
  (M : E.EisensteinAnalyticModel) →
  (A : D.DiscriminantAlgebra M) →
  (Norm : N.WeightCompatibleNormalization M) →
  (Div : Q.QuotientCancellationAlgebra M) →
  (W : Fixed.EllipticFixedPointEvidence M) →
  (F : EllipticValueFieldEvidence M A Norm Div W) →
  J.standardJ M A Norm Div (Fixed.omegaPoint W) ≡ E.zero M
jAtOmegaIsZero M A Norm Div W F =
  trans
    (cong
      (λ value →
        Q._/ˢ_ Div (D.cube M value)
          (N.normalizedDelta M A Norm (Fixed.omegaPoint W)))
      (Fixed.e4AtOmegaIsZero M W))
    (trans
      (cong
        (λ value →
          Q._/ˢ_ Div value
            (N.normalizedDelta M A Norm (Fixed.omegaPoint W)))
        (zeroCube F))
      (zeroNumeratorQuotient F
        (N.normalizedDelta M A Norm (Fixed.omegaPoint W))
        (deltaSafeAtOmega F)))

deltaAtIIsNormalizedNumerator :
  (M : E.EisensteinAnalyticModel) →
  (A : D.DiscriminantAlgebra M) →
  (Norm : N.WeightCompatibleNormalization M) →
  (Div : Q.QuotientCancellationAlgebra M) →
  (W : Fixed.EllipticFixedPointEvidence M) →
  (F : EllipticValueFieldEvidence M A Norm Div W) →
  N.normalizedDelta M A Norm (Fixed.iPoint W)
    ≡ N.normalize Norm (D.cube M (D.E4 M (Fixed.iPoint W)))
deltaAtIIsNormalizedNumerator M A Norm Div W F =
  cong (N.normalize Norm)
    (trans
      (cong
        (λ value →
          D._-ˢ_ A
            (D.cube M (D.E4 M (Fixed.iPoint W)))
            (D.square M value))
        (Fixed.e6AtIIsZero M W))
      (subtractSquareZero F
        (D.cube M (D.E4 M (Fixed.iPoint W)))))

jAtIIs1728 :
  (M : E.EisensteinAnalyticModel) →
  (A : D.DiscriminantAlgebra M) →
  (Norm : N.WeightCompatibleNormalization M) →
  (Div : Q.QuotientCancellationAlgebra M) →
  (W : Fixed.EllipticFixedPointEvidence M) →
  (F : EllipticValueFieldEvidence M A Norm Div W) →
  J.standardJ M A Norm Div (Fixed.iPoint W) ≡ scalar1728 F
jAtIIs1728 M A Norm Div W F =
  let
    x = D.cube M (D.E4 M (Fixed.iPoint W))
    denominatorEquality =
      deltaAtIIsNormalizedNumerator M A Norm Div W F
    safeNormalized =
      subst (Q.DenominatorSafe Div)
        denominatorEquality (deltaSafeAtI F)
  in
  trans
    (cong (Q._/ˢ_ Div x) denominatorEquality)
    (normalizedSelfQuotient F x safeNormalized)

------------------------------------------------------------------------
-- Exact remaining original-source obligations:
-- * concrete Bishop parameter points i and omega and their S,ST actions;
-- * factor^6(i) != 1 and factor^4(omega) != 1 with scalar cancellation;
-- * normalization == division by the actual rational 1728;
-- * nonzero discriminant at the two selected points;
-- * q-series/lattice same-object theorem on the same Bishop carrier.
-- No theta, CM class-polynomial, or -163 theorem is asserted here.
------------------------------------------------------------------------
