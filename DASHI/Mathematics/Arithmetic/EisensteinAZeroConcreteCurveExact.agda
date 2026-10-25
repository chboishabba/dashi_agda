module DASHI.Mathematics.Arithmetic.EisensteinAZeroConcreteCurveExact where

------------------------------------------------------------------------
-- CONCRETE A=0 SHORT-WEIERSTRASS FIXTURE
--
-- A literal inhabitant of the existing rational short-Weierstrass carrier:
--
--   E : y^2 = x^3 + 1.
--
-- This turns the generic A=0/j-expression/scalar-extension results into one
-- same-object repository fixture.  It remains below full CM authority: no
-- rational point-group endomorphism ring, Hecke character or elliptic
-- L-function identification is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Biology.EisensteinNineRingInterferenceExact as E
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EisensteinJZeroCubicSymmetryExact as Cubic
import DASHI.Mathematics.Arithmetic.EisensteinAZeroEllipticScalarExtensionExact as Scalar
import DASHI.Mathematics.Arithmetic.EisensteinAZeroJInvariantExact as J

------------------------------------------------------------------------
-- 1. Nonsingular curve y^2 = x^3 + 1.
------------------------------------------------------------------------

aZeroBOneDiscriminant :
  (- Elliptic.sixteen) *
    (Elliptic.four * 0ℚ * 0ℚ * 0ℚ
      + Elliptic.twentySeven * E.qOne * E.qOne)
  ≡ - (Elliptic.sixteen * Elliptic.twentySeven)
aZeroBOneDiscriminant = ℚRing.solve []

minusSixteenTimesTwentySevenNonzero :
  - (Elliptic.sixteen * Elliptic.twentySeven) ≡ 0ℚ → ⊥
minusSixteenTimesTwentySevenNonzero ()

curveY2EqualsX3PlusOne : Elliptic.ShortWeierstrassCurve
curveY2EqualsX3PlusOne =
  Elliptic.shortWeierstrass 0ℚ E.qOne
    (λ discriminantZero →
      minusSixteenTimesTwentySevenNonzero
        (trans aZeroBOneDiscriminant discriminantZero))
  where
    trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans refl second = second

concreteACoefficientZero :
  Elliptic.aCoefficient curveY2EqualsX3PlusOne ≡ 0ℚ
concreteACoefficientZero = refl

concreteBCoefficientOne :
  Elliptic.bCoefficient curveY2EqualsX3PlusOne ≡ E.qOne
concreteBCoefficientOne = refl

------------------------------------------------------------------------
-- 2. Concrete j-expression result.
------------------------------------------------------------------------

concreteJExpressionZero :
  J.shortWeierstrassJExpression curveY2EqualsX3PlusOne ≡ 0ℚ
concreteJExpressionZero =
  J.aZeroShortJExpressionIsZero concreteACoefficientZero

------------------------------------------------------------------------
-- 3. Literal rational point (0,1), embedded into the same Eisenstein cubic.
------------------------------------------------------------------------

zeroOnePoint :
  Scalar.OnShortWeierstrass curveY2EqualsX3PlusOne 0ℚ E.qOne
zeroOnePoint = ℚRing.solve []

embeddedZeroOnePoint :
  Cubic.OnJZeroCubic
    (Scalar.embedQ (Elliptic.bCoefficient curveY2EqualsX3PlusOne))
    (Scalar.embedQ 0ℚ)
    (Scalar.embedQ E.qOne)
embeddedZeroOnePoint =
  Scalar.aZeroShortPointEmbeds concreteACoefficientZero zeroOnePoint

rotatedEmbeddedZeroOnePoint :
  Cubic.OnJZeroCubic
    (Scalar.embedQ (Elliptic.bCoefficient curveY2EqualsX3PlusOne))
    (Cubic.rotateX (Scalar.embedQ 0ℚ))
    (Scalar.embedQ E.qOne)
rotatedEmbeddedZeroOnePoint =
  Scalar.omegaActionPreservesEmbeddedAZeroPoint
    concreteACoefficientZero zeroOnePoint

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record EisensteinAZeroConcreteCurveBoundary : Set where
  constructor eisenstein-a-zero-concrete-curve-boundary
  field
    concreteNonsingularAZeroCurvePaid : Bool
    concreteJExpressionZeroPaid : Bool
    concreteRationalPointEmbeddedPaid : Bool
    scalarExtendedC3PreservationPaid : Bool
    rationalPointGroupLawPaid : Bool
    fullCMEndomorphismRingPaid : Bool
    heckeCharacterPaid : Bool
    ellipticLSeriesIdentifiedWithChiMinus3 : Bool

open EisensteinAZeroConcreteCurveBoundary public

canonicalBoundary : EisensteinAZeroConcreteCurveBoundary
canonicalBoundary =
  eisenstein-a-zero-concrete-curve-boundary
    true
    true
    true
    true
    false
    false
    false
    false
