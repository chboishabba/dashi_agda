module DASHI.Mathematics.Arithmetic.EisensteinAZeroEllipticScalarExtensionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Biology.EisensteinNineRingInterferenceExact as E
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EisensteinJZeroCubicSymmetryExact as Cubic
import DASHI.Mathematics.Arithmetic.EisensteinAZeroEllipticScalarExtensionExact as Bridge

embedOneIsOne : Bridge.embedQ E.qOne ≡ E.one
embedOneIsOne = refl

rationalAZeroPointEmbedsIntoSameCubic :
  ∀ {curve x y} →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  Bridge.OnShortWeierstrass curve x y →
  Cubic.OnJZeroCubic
    (Bridge.embedQ (Elliptic.bCoefficient curve))
    (Bridge.embedQ x)
    (Bridge.embedQ y)
rationalAZeroPointEmbedsIntoSameCubic = Bridge.aZeroShortPointEmbeds

embeddedCubicReflectsRationalAZeroPoint :
  ∀ {curve x y} →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  Cubic.OnJZeroCubic
    (Bridge.embedQ (Elliptic.bCoefficient curve))
    (Bridge.embedQ x)
    (Bridge.embedQ y) →
  Bridge.OnShortWeierstrass curve x y
embeddedCubicReflectsRationalAZeroPoint = Bridge.embeddedCubicReflectsAZeroShortPoint

omegaActionNeedNotStayRational :
  (q : ℚ) →
  Cubic.rotateX (Bridge.embedQ E.qOne) ≡ Bridge.embedQ q →
  ⊥
omegaActionNeedNotStayRational = Bridge.rotateEmbeddedOneNotEmbedded

jInvariantFormulaStillNotManufactured :
  Bridge.jInvariantZeroFormulaPaid Bridge.canonicalBoundary ≡ false
jInvariantFormulaStillNotManufactured = refl

heckeCharacterStillNotManufactured :
  Bridge.heckeCharacterPaid Bridge.canonicalBoundary ≡ false
heckeCharacterStillNotManufactured = refl
