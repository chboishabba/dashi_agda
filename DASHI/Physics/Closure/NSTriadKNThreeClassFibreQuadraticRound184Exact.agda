module DASHI.Physics.Closure.NSTriadKNThreeClassFibreQuadraticRound184Exact where

------------------------------------------------------------------------
-- ROUND184 / UNIVERSAL THREE-CLASS QUADRATIC RECOMBINATION
--
-- Round183 proves that the Gram debt between arbitrary partner-compressed
-- cells need not be nonpositive.  The physical Bony geometry, however, has
-- only three partner-invariant blocks after LH and HL are merged:
--
--   FL = LH ∪ HL,   HH = HH -> low,   CC = comparable.
--
-- We therefore do NOT need to pay every cross-class Gram term with a sign.
-- A single three-vector Cauchy estimate recombines the already-summed class
-- vectors with the universal constant 3:
--
--   ||S_FL + S_HH + S_CC||²
--     <= 3 (||S_FL||² + ||S_HH||² + ||S_CC||²).
--
-- Hence arbitrary-data Package A only needs a cardinality-free L² estimate
-- INSIDE each physical class.  Cross-class interference costs a fixed constant,
-- independent of the Fourier cutoff, shell count, or fibre cardinality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178

F = R178.F

threeClassTotal :
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
threeClassTotal farLow highHigh comparable =
  C3.complex3Add (C3.complex3Add farLow highHigh) comparable

threeClassQuadraticBound :
  (farLow highHigh comparable : C3.Complex3 F) →
  L2.complex3NormSquared (threeClassTotal farLow highHigh comparable)
  ≤ R178.three *
      (L2.complex3NormSquared farLow
       + L2.complex3NormSquared highHigh
       + L2.complex3NormSquared comparable)
threeClassQuadraticBound = R178.threeVectorSumNormSquaredBound

threeClassPaidQuadraticBound :
  (farLow highHigh comparable : C3.Complex3 F)
  (farLowMass highHighMass comparableMass : ℚ) →
  L2.complex3NormSquared farLow ≤ farLowMass →
  L2.complex3NormSquared highHigh ≤ highHighMass →
  L2.complex3NormSquared comparable ≤ comparableMass →
  L2.complex3NormSquared (threeClassTotal farLow highHigh comparable)
  ≤ R178.three * (farLowMass + highHighMass + comparableMass)
threeClassPaidQuadraticBound
    farLow highHigh comparable
    farLowMass highHighMass comparableMass
    farLowBound highHighBound comparableBound =
  let
    classMassBound :
      L2.complex3NormSquared farLow
        + L2.complex3NormSquared highHigh
        + L2.complex3NormSquared comparable
      ≤ farLowMass + highHighMass + comparableMass
    classMassBound =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤ farLowBound highHighBound)
        comparableBound

    scaledClassMassBound :
      R178.three *
        (L2.complex3NormSquared farLow
         + L2.complex3NormSquared highHigh
         + L2.complex3NormSquared comparable)
      ≤ R178.three * (farLowMass + highHighMass + comparableMass)
    scaledClassMassBound =
      let instance threeNNI = nonNegative R178.threeNN
      in ℚP.*-monoˡ-≤-nonNeg R178.three classMassBound
  in
  ℚP.≤-trans
    (threeClassQuadraticBound farLow highHigh comparable)
    scaledClassMassBound

-- No physical class estimate is smuggled into this theorem.  Its content is
-- exactly that cross-class Gram debt can be discarded in favour of one fixed
-- three-class constant AFTER each class has been summed with its signs intact.
round184CrossClassGramSignRequired : Bool
round184CrossClassGramSignRequired = false

round184UniversalClassCountConstant : Bool
round184UniversalClassCountConstant = true

round184WithinClassQuadraticPaymentStillRequired : Bool
round184WithinClassQuadraticPaymentStillRequired = true

round184PackageAClosed : Bool
round184PackageAClosed = false

round184ClayPromotion : Bool
round184ClayPromotion = false
