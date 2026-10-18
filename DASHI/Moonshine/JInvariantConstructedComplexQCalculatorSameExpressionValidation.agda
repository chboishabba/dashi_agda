module DASHI.Moonshine.JInvariantConstructedComplexQCalculatorSameExpressionValidation where

open import DASHI.Core.Prelude

import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Moonshine.JInvariantConstructedComplexQCalculatorSameExpressionExact as P

qSyntaxRegression :
  P.qOfCalculatorExpr ≡ P.qOfCalculatorExpr
qSyntaxRegression = refl

sameExpressionRegression :
  (C : Complex.ConstructedComplexPackage) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  P.evalQOfCalculator C tau ≡ P.qOf C tau
sameExpressionRegression = P.evalQOfCalculatorIsQOf

boundaryRegression :
  P.JConstructedComplexQCalculatorBoundary.sameExpressionPaid
    P.canonicalJConstructedComplexQCalculatorBoundary
  ≡ true
boundaryRegression = refl
