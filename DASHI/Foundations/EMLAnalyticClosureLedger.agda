module DASHI.Foundations.EMLAnalyticClosureLedger where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain
open import DASHI.Foundations.ElementaryCalculator
open import DASHI.Foundations.ElementaryCalculatorSemantics

------------------------------------------------------------------------
-- Operation-indexed analytic closure.  The structural compiler is complete;
-- concrete scalar models promote calculator fragments only after supplying the
-- exact domain proof and semantic identity for each generated expression.

data AnalyticPrimitiveClass : Set where
  positiveRealArithmetic : AnalyticPrimitiveClass
  complexConstants : AnalyticPrimitiveClass
  directTrigonometric : AnalyticPrimitiveClass
  directHyperbolic : AnalyticPrimitiveClass
  principalInverseTrigonometric : AnalyticPrimitiveClass
  principalInverseHyperbolic : AnalyticPrimitiveClass

zeroCalculator : CalculatorExpr
zeroCalculator = integer (integerLiteral positiveLiteral zero)

record PrimitiveClosureWitness
  (M : ExpLogSubModel)
  (S : CalculatorSemanticModel M)
  (P : AnalyticEMLCompilerPackage M)
  (primitive : CalculatorExpr)
  : Set₁ where

  field
    environment : Env M
    sourceDefined :
      DefinedSource M (admissibility P) environment
        (lowerCalculator primitive)
    compilationDefined :
      CompilationDefined M (admissibility P) environment
        (lowerCalculator primitive)
    semanticIdentity :
      evalSource M environment (lowerCalculator primitive)
      ≡ evalSemanticCalculator S environment primitive

open PrimitiveClosureWitness public

record ArithmeticClosurePackage
  (M : ExpLogSubModel)
  (S : CalculatorSemanticModel M)
  (P : AnalyticEMLCompilerPackage M)
  : Set₁ where

  field
    zeroClosed : PrimitiveClosureWitness M S P zeroCalculator
    minusOneClosed : PrimitiveClosureWitness M S P constantMinusOne
    additionClosed : ∀ x y → PrimitiveClosureWitness M S P (calcAdd x y)
    multiplicationClosed : ∀ x y → PrimitiveClosureWitness M S P (calcMultiply x y)
    divisionClosed : ∀ x y → PrimitiveClosureWitness M S P (calcDivide x y)
    powerClosed : ∀ x y → PrimitiveClosureWitness M S P (calcPower x y)

open ArithmeticClosurePackage public

record ComplexConstantClosurePackage
  (M : ExpLogSubModel)
  (S : CalculatorSemanticModel M)
  (P : AnalyticEMLCompilerPackage M)
  : Set₁ where

  field
    eClosed : PrimitiveClosureWitness M S P constantE
    iClosed : PrimitiveClosureWitness M S P constantI
    piClosed : PrimitiveClosureWitness M S P constantPi

open ComplexConstantClosurePackage public

record DirectTranscendentalClosurePackage
  (M : ExpLogSubModel)
  (S : CalculatorSemanticModel M)
  (P : AnalyticEMLCompilerPackage M)
  : Set₁ where

  field
    sineClosed : ∀ x → PrimitiveClosureWitness M S P (calcSin x)
    cosineClosed : ∀ x → PrimitiveClosureWitness M S P (calcCos x)
    tangentClosed : ∀ x → PrimitiveClosureWitness M S P (calcTan x)
    sinhClosed : ∀ x → PrimitiveClosureWitness M S P (calcSinh x)
    coshClosed : ∀ x → PrimitiveClosureWitness M S P (calcCosh x)
    tanhClosed : ∀ x → PrimitiveClosureWitness M S P (calcTanh x)

open DirectTranscendentalClosurePackage public

record PrincipalInverseClosurePackage
  (M : ExpLogSubModel)
  (S : CalculatorSemanticModel M)
  (P : AnalyticEMLCompilerPackage M)
  : Set₁ where

  field
    arcsineClosed : ∀ x → PrimitiveClosureWitness M S P (calcArcSin x)
    arccosineClosed : ∀ x → PrimitiveClosureWitness M S P (calcArcCos x)
    arctangentClosed : ∀ x → PrimitiveClosureWitness M S P (calcArcTan x)
    arsinhClosed : ∀ x → PrimitiveClosureWitness M S P (calcArcSinh x)
    arcoshClosed : ∀ x → PrimitiveClosureWitness M S P (calcArcCosh x)
    artanhClosed : ∀ x → PrimitiveClosureWitness M S P (calcArcTanh x)

open PrincipalInverseClosurePackage public

record CompleteCalculatorAnalyticClosure
  (M : ExpLogSubModel)
  (S : CalculatorSemanticModel M)
  (P : AnalyticEMLCompilerPackage M)
  : Set₁ where

  field
    arithmetic : ArithmeticClosurePackage M S P
    constants : ComplexConstantClosurePackage M S P
    direct : DirectTranscendentalClosurePackage M S P
    inverse : PrincipalInverseClosurePackage M S P

open CompleteCalculatorAnalyticClosure public

primitiveCompiledCorrect :
  ∀ {M : ExpLogSubModel}
    {S : CalculatorSemanticModel M}
    {P : AnalyticEMLCompilerPackage M}
    {primitive : CalculatorExpr} →
  (witness : PrimitiveClosureWitness M S P primitive) →
  evalEML M (environment witness) (compileCalculator primitive)
  ≡ evalSemanticCalculator S (environment witness) primitive
primitiveCompiledCorrect {P = P} witness
  rewrite analyticCompileCorrect P
    (environment witness)
    (compilationDefined witness) =
  semanticIdentity witness
