module DASHI.Moonshine.JInvariantQExponentCartesianNormalizationValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as Q
import DASHI.Moonshine.JInvariantQExponentCartesianNormalizationExact as P

------------------------------------------------------------------------
-- RED owner: normalize the literal q exponent on the existing constructed-real
-- and ConcreteComplex carriers.  No order, trig, or analytic input is allowed.
------------------------------------------------------------------------

qExponentCartesianRegression :
  (C : Complex.ConstructedComplexPackage) →
  (N : Ring.ConstructedRealRingNormalisationLaws
    (Real.real (Complex.realPackage C))) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  Q.qExponent C tau
  ≡ Complex.complex
      (Real.neg (Real.real (Complex.realPackage C))
        (Real._*_ (Real.real (Complex.realPackage C))
          (P.twoPi C)
          (Complex.im tau)))
      (Real._*_ (Real.real (Complex.realPackage C))
        (P.twoPi C)
        (Complex.re tau))
qExponentCartesianRegression = P.qExponentCartesianExact

qExponentRealPartRegression :
  (C : Complex.ConstructedComplexPackage) →
  (N : Ring.ConstructedRealRingNormalisationLaws
    (Real.real (Complex.realPackage C))) →
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) →
  Complex.re (Q.qExponent C tau)
  ≡ Real.neg (Real.real (Complex.realPackage C))
      (Real._*_ (Real.real (Complex.realPackage C))
        (P.twoPi C)
        (Complex.im tau))
qExponentRealPartRegression = P.qExponentRealPartExact
