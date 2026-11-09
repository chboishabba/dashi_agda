module DASHI.Foundations.BishopMachinOriginalCayleyRationalPointAlgebraExact where

------------------------------------------------------------------------
-- K05-PI/P1: EXACT rational Gaussian Cayley calculations at the
-- ORIGINAL Bishop-Machin arguments 1/5 and 1/239.
--
-- This discharges the finite *denominator-equation arithmetic*
-- at both Machin points on the existing rational Q[i] carrier.
-- It does NOT identify exp_B(2i atan_B(t)) with those values:
-- original analytic composition and limit remain separately OPEN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _/_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Foundations.BishopMachinOriginalCayleyFormalSeriesExact as Formal

oneFifth : ℚ
oneFifth = + 1 / 5

oneTwoHundredThirtyNinth : ℚ
oneTwoHundredThirtyNinth = + 1 / 239

cayleyNumeratorAt : ℚ → CD.RationalComplex
cayleyNumeratorAt t =
  CD._+c_ CD.oneC
    (CD._*c_ Formal.imaginaryUnit (CD.complex t 0ℚ))

cayleyDenominatorAt : ℚ → CD.RationalComplex
cayleyDenominatorAt t =
  CD._-c_ CD.oneC
    (CD._*c_ Formal.imaginaryUnit (CD.complex t 0ℚ))

-- Rational complex solutions to (1-it) z = 1+it.
cayleyAtOneFifth : CD.RationalComplex
cayleyAtOneFifth =
  CD.complex (+ 12 / 13) (+ 5 / 13)

cayleyAtOneTwoHundredThirtyNinth : CD.RationalComplex
cayleyAtOneTwoHundredThirtyNinth =
  CD.complex (+ 28560 / 28561) (+ 239 / 28561)

originalCayleyFiveDenominatorEquation :
  CD._*c_ (cayleyDenominatorAt oneFifth)
    cayleyAtOneFifth
  ≡ cayleyNumeratorAt oneFifth
originalCayleyFiveDenominatorEquation =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

originalCayley239DenominatorEquation :
  CD._*c_ (cayleyDenominatorAt oneTwoHundredThirtyNinth)
    cayleyAtOneTwoHundredThirtyNinth
  ≡ cayleyNumeratorAt oneTwoHundredThirtyNinth
originalCayley239DenominatorEquation =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

-- No hidden analytic evaluation field: the point values are
-- explicitly identified with the selected source rational Q[i]
-- values, and multiplication verifies the original Cayley law.
originalCayleyFiveRealCoordinate :
  CD.re cayleyAtOneFifth ≡ (+ 12 / 13)
originalCayleyFiveRealCoordinate = refl

originalCayleyFiveImaginaryCoordinate :
  CD.im cayleyAtOneFifth ≡ (+ 5 / 13)
originalCayleyFiveImaginaryCoordinate = refl

originalCayley239RealCoordinate :
  CD.re cayleyAtOneTwoHundredThirtyNinth
  ≡ (+ 28560 / 28561)
originalCayley239RealCoordinate = refl

originalCayley239ImaginaryCoordinate :
  CD.im cayleyAtOneTwoHundredThirtyNinth
  ≡ (+ 239 / 28561)
originalCayley239ImaginaryCoordinate = refl
