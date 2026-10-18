module DASHI.Moonshine.JInvariantQBishopExponentTransportCompilerValidation where

import Real as BishopReal

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as Q
import DASHI.Moonshine.JInvariantQBishopExponentTransportCompilerExact as P

exponentAgreementRegression :
  ∀ {C : Complex.ConstructedComplexPackage}
    (N : Ring.ConstructedRealRingNormalisationLaws
      (Real.real (Complex.realPackage C)))
    (tau : Complex.ComplexPair (Real.real (Complex.realPackage C)))
    {piB imagB : BishopReal.ℝ}
    (transport : P.QBishopExponentMagnitudeTransport C tau piB imagB) →
  P.toLegacy transport
    (BishopReal.-_
      (P.qExponentMagnitude piB imagB))
  ≡
  Complex.re (Q.qExponent C tau)
exponentAgreementRegression =
  P.compileExponentAgreement
