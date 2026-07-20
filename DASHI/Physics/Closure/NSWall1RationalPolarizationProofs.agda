module DASHI.Physics.Closure.NSWall1RationalPolarizationProofs where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ)

open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier
open import DASHI.Physics.Closure.NSWall1CanonicalPolarizations
open import DASHI.Physics.Closure.NSWall1RationalScalarInstance

------------------------------------------------------------------------
-- The six canonical packet polarizations are exactly transverse over ℚ.
------------------------------------------------------------------------

rationalTransverse100 :
  vecDot rationalScalarAlgebra
    (integerWaveVector rationalScalarAlgebra p100)
    (canonicalPolarization100 rationalScalarAlgebra)
  ≡ 0ℚ
rationalTransverse100 = refl

rationalTransverse010 :
  vecDot rationalScalarAlgebra
    (integerWaveVector rationalScalarAlgebra p010)
    (canonicalPolarization010 rationalScalarAlgebra)
  ≡ 0ℚ
rationalTransverse010 = refl

rationalTransverse001 :
  vecDot rationalScalarAlgebra
    (integerWaveVector rationalScalarAlgebra p001)
    (canonicalPolarization001 rationalScalarAlgebra)
  ≡ 0ℚ
rationalTransverse001 = refl

rationalTransverse110 :
  vecDot rationalScalarAlgebra
    (integerWaveVector rationalScalarAlgebra p110)
    (canonicalPolarization110 rationalScalarAlgebra)
  ≡ 0ℚ
rationalTransverse110 = refl

rationalTransverse101 :
  vecDot rationalScalarAlgebra
    (integerWaveVector rationalScalarAlgebra p101)
    (canonicalPolarization101 rationalScalarAlgebra)
  ≡ 0ℚ
rationalTransverse101 = refl

rationalTransverse011 :
  vecDot rationalScalarAlgebra
    (integerWaveVector rationalScalarAlgebra p011)
    (canonicalPolarization011 rationalScalarAlgebra)
  ≡ 0ℚ
rationalTransverse011 = refl

rationalCanonicalPolarizationLaws :
  CanonicalPolarizationLaws rationalScalarAlgebra
rationalCanonicalPolarizationLaws = record
  { transverse100 = rationalTransverse100
  ; transverse010 = rationalTransverse010
  ; transverse001 = rationalTransverse001
  ; transverse110 = rationalTransverse110
  ; transverse101 = rationalTransverse101
  ; transverse011 = rationalTransverse011
  }
