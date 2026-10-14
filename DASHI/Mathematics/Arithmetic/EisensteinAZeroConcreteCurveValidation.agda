module DASHI.Mathematics.Arithmetic.EisensteinAZeroConcreteCurveValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (0ℚ)

import DASHI.Biology.EisensteinNineRingInterferenceExact as E
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EisensteinJZeroCubicSymmetryExact as Cubic
import DASHI.Mathematics.Arithmetic.EisensteinAZeroEllipticScalarExtensionExact as Scalar
import DASHI.Mathematics.Arithmetic.EisensteinAZeroJInvariantExact as J
import DASHI.Mathematics.Arithmetic.EisensteinAZeroConcreteCurveExact as Concrete

concreteCurveHasAZero :
  Elliptic.aCoefficient Concrete.curveY2EqualsX3PlusOne ≡ 0ℚ
concreteCurveHasAZero = refl

concreteCurveHasJExpressionZero :
  J.shortWeierstrassJExpression Concrete.curveY2EqualsX3PlusOne ≡ 0ℚ
concreteCurveHasJExpressionZero = Concrete.concreteJExpressionZero

concreteRationalPointEmbeds :
  Cubic.OnJZeroCubic
    (Scalar.embedQ (Elliptic.bCoefficient Concrete.curveY2EqualsX3PlusOne))
    (Scalar.embedQ 0ℚ)
    (Scalar.embedQ E.qOne)
concreteRationalPointEmbeds = Concrete.embeddedZeroOnePoint

concreteC3ImageStaysOnScalarExtendedCubic :
  Cubic.OnJZeroCubic
    (Scalar.embedQ (Elliptic.bCoefficient Concrete.curveY2EqualsX3PlusOne))
    (Cubic.rotateX (Scalar.embedQ 0ℚ))
    (Scalar.embedQ E.qOne)
concreteC3ImageStaysOnScalarExtendedCubic = Concrete.rotatedEmbeddedZeroOnePoint

cmStillNotPromoted :
  Concrete.fullCMEndomorphismRingPaid Concrete.canonicalBoundary ≡ false
cmStillNotPromoted = refl
