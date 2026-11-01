module DASHI.Moonshine.JInvariantConstructedComplexQCalculatorSameExpressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Foundations.ElementarySingleOperator as EML
import DASHI.Foundations.ElementaryCalculator as Calc
import DASHI.Foundations.ElementaryCalculatorSemantics as Sem
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Series

------------------------------------------------------------------------
-- CONSTRUCTED-COMPLEX q <-> EXISTING CALCULATOR AST SAME-EXPRESSION WELD
--
-- The theorem-bearing q producer is already
--
--   qOf C tau = expC (scaleNatC 2 (i * piC) * tau).
--
-- Rather than demand a global complex logarithm merely to reuse the EML
-- lowering, interpret one actual CalculatorExpr through the repository's
-- independent named calculator semantics.  The AST below deliberately mirrors
-- the association used by qOf, including scaleNatC 2 = z + (z + 0).
--
-- This pays an exact expression/semantic weld for q only.  It does not make
-- the full exp/log/sub backend a complex-analytic model and it imports no
-- convergence, modularity, Klein-j, or RH authority.
------------------------------------------------------------------------

qOf :
  (C : Complex.ConstructedComplexPackage) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
qOf = Series.qOf

zeroCalculatorExpr : Calc.CalculatorExpr
zeroCalculatorExpr = Calc.calcSubtract Calc.constantOne Calc.constantOne

iPiCalculatorExpr : Calc.CalculatorExpr
iPiCalculatorExpr = Calc.calcMultiply Calc.constantI Calc.constantPi

twoIPiCalculatorExpr : Calc.CalculatorExpr
twoIPiCalculatorExpr =
  Calc.calcAdd
    iPiCalculatorExpr
    (Calc.calcAdd iPiCalculatorExpr zeroCalculatorExpr)

qOfCalculatorExpr : Calc.CalculatorExpr
qOfCalculatorExpr =
  Calc.calcExp
    (Calc.calcMultiply twoIPiCalculatorExpr (Calc.variable 0))

------------------------------------------------------------------------
-- A carrier-only ExpLogSubModel is sufficient to instantiate the independent
-- calculator semantic evaluator.  Its log/sub backend is NOT promoted to the
-- analytic complex logarithm; qOfCalculatorExpr never asks for log.
------------------------------------------------------------------------

complexCarrierModel :
  (C : Complex.ConstructedComplexPackage) -> EML.ExpLogSubModel
complexCarrierModel C =
  let
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C
  in record
    { EML.Carrier = Complex.ComplexPair R
    ; EML.one = Complex.oneC
    ; EML.exp = Complex.expC CE
    ; EML.log = λ z -> z
    ; EML.sub = Complex._-C_
    }

constructedComplexCalculatorSemantics :
  (C : Complex.ConstructedComplexPackage) ->
  Sem.CalculatorSemanticModel (complexCarrierModel C)
constructedComplexCalculatorSemantics C =
  let
    R = Real.real (Complex.realPackage C)
    CE = Complex.complexExponential C
    zero = Complex.zeroC {R = R}
    one = Complex.oneC {R = R}
    piC = Complex.complex (Complex.pi CE) (Real.zero R)
  in record
    { Sem.integerS = λ _ -> zero
    ; Sem.rationalS = λ _ -> zero
    ; Sem.piS = piC
    ; Sem.eS = zero
    ; Sem.iS = Complex.imaginaryUnit
    ; Sem.minusOneS = zero
    ; Sem.oneS = one
    ; Sem.twoS = Complex._+C_ one one
    ; Sem.expS = Complex.expC CE
    ; Sem.logS = λ z -> z
    ; Sem.inverseS = λ z -> z
    ; Sem.halfS = λ z -> z
    ; Sem.negateS = λ z -> Complex._-C_ zero z
    ; Sem.sqrtS = λ z -> z
    ; Sem.squareS = λ z -> Complex._*C_ z z
    ; Sem.sigmoidS = λ z -> z
    ; Sem.sinS = λ z -> z
    ; Sem.cosS = λ z -> z
    ; Sem.tanS = λ z -> z
    ; Sem.arcSinS = λ z -> z
    ; Sem.arcCosS = λ z -> z
    ; Sem.arcTanS = λ z -> z
    ; Sem.sinhS = λ z -> z
    ; Sem.coshS = λ z -> z
    ; Sem.tanhS = λ z -> z
    ; Sem.arcSinhS = λ z -> z
    ; Sem.arcCoshS = λ z -> z
    ; Sem.arcTanhS = λ z -> z
    ; Sem.addS = Complex._+C_
    ; Sem.subtractS = Complex._-C_
    ; Sem.multiplyS = Complex._*C_
    ; Sem.divideS = λ x y -> x
    ; Sem.logBaseS = λ x y -> x
    ; Sem.powerS = λ x y -> x
    ; Sem.averageS = λ x y -> x
    ; Sem.hypotenuseS = λ x y -> x
    }

qEnvironment :
  (C : Complex.ConstructedComplexPackage) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  EML.Env (complexCarrierModel C)
qEnvironment C tau zero = tau
qEnvironment C tau (suc n) = Complex.zeroC

evalQOfCalculator :
  (C : Complex.ConstructedComplexPackage) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C)) ->
  Complex.ComplexPair (Real.real (Complex.realPackage C))
evalQOfCalculator C tau =
  Sem.evalSemanticCalculator
    (constructedComplexCalculatorSemantics C)
    (qEnvironment C tau)
    qOfCalculatorExpr

------------------------------------------------------------------------
-- The only normalization required is 1 - 1 = 0 in both complex coordinates.
------------------------------------------------------------------------

complexOneMinusOneIsZero :
  (C : Complex.ConstructedComplexPackage) ->
  Complex._-C_
    (Complex.oneC {R = Real.real (Complex.realPackage C)})
    Complex.oneC
  ≡ Complex.zeroC
complexOneMinusOneIsZero C =
  let R = Real.real (Complex.realPackage C)
  in
  cong₂ Complex.complex
    (Real.subSelf R (Real.one R))
    (Real.subSelf R (Real.zero R))

------------------------------------------------------------------------
-- Exact same-expression theorem.
------------------------------------------------------------------------

evalQOfCalculatorIsQOf :
  (C : Complex.ConstructedComplexPackage) ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  evalQOfCalculator C tau ≡ qOf C tau
evalQOfCalculatorIsQOf C tau
  rewrite complexOneMinusOneIsZero C = refl

------------------------------------------------------------------------
-- The original pretty calculator expression still compiles through EML; this
-- exact qOf-normal-form AST is a semantic witness, not a replacement compiler.
------------------------------------------------------------------------

qOfCalculatorLowered : EML.ExpLogSubExpr
qOfCalculatorLowered = Calc.lowerCalculator qOfCalculatorExpr

qOfCalculatorCompiled : EML.EMLExpr
qOfCalculatorCompiled = Calc.compileCalculator qOfCalculatorExpr

qOfCalculatorCompilationCanonical :
  qOfCalculatorCompiled ≡ EML.compileEML qOfCalculatorLowered
qOfCalculatorCompilationCanonical = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameExpressionCreatesGlobalComplexLog : Set where
data SameExpressionCreatesKleinJ : Set where
data SameExpressionCreatesQSeriesConvergence : Set where
data SameExpressionCreatesRH : Set where

sameExpressionDoesNotCreateGlobalComplexLog :
  SameExpressionCreatesGlobalComplexLog -> ⊥
sameExpressionDoesNotCreateGlobalComplexLog ()

sameExpressionDoesNotCreateKleinJ : SameExpressionCreatesKleinJ -> ⊥
sameExpressionDoesNotCreateKleinJ ()

sameExpressionDoesNotCreateQSeriesConvergence :
  SameExpressionCreatesQSeriesConvergence -> ⊥
sameExpressionDoesNotCreateQSeriesConvergence ()

sameExpressionDoesNotCreateRH : SameExpressionCreatesRH -> ⊥
sameExpressionDoesNotCreateRH ()

record JConstructedComplexQCalculatorBoundary : Set where
  constructor j-constructed-complex-q-calculator-boundary
  field
    existingQOfReused : Bool
    existingCalculatorASTReused : Bool
    namedCalculatorSemanticsReused : Bool
    sameExpressionPaid : Bool
    fullComplexLogModelPaid : Bool
    kleinJPaidByThisWeld : Bool
    qSeriesConvergencePaidByThisWeld : Bool
    rhPaidByThisWeld : Bool
    nextResidual : String
open JConstructedComplexQCalculatorBoundary public

canonicalJConstructedComplexQCalculatorBoundary :
  JConstructedComplexQCalculatorBoundary
canonicalJConstructedComplexQCalculatorBoundary =
  j-constructed-complex-q-calculator-boundary
    true true true true
    false false false false
    "reuse the exact q same-expression theorem inside the existing constructed-complex Klein-j/Eisenstein and Riemann carrier adapters; keep Gamma/zeta/xi and all convergence authority in their existing analytic owners"
