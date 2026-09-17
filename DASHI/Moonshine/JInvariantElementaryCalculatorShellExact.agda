module DASHI.Moonshine.JInvariantElementaryCalculatorShellExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Foundations.ElementarySingleOperator as EML
import DASHI.Foundations.ElementaryCalculator as Calc

------------------------------------------------------------------------
-- FINITE ELEMENTARY j/q CALCULATOR SHELL
--
-- This file pays only a representation theorem: a finite elementary q-series
-- head can be expressed in the existing scientific-calculator syntax and
-- compiled through the existing exp/log/sub/1 -> EML pipeline.
--
-- It does NOT prove that the variable is an upper-half-plane tau, that the
-- expression converges to Klein j, or that modularity/replicability follows.
------------------------------------------------------------------------

tauVariable : Calc.CalculatorExpr
tauVariable = Calc.variable 0

twoPiITauExpr : Calc.CalculatorExpr
twoPiITauExpr =
  Calc.calcMultiply
    (Calc.calcMultiply Calc.constantTwo Calc.constantPi)
    (Calc.calcMultiply Calc.constantI tauVariable)

qCoordinateExpr : Calc.CalculatorExpr
qCoordinateExpr = Calc.calcExp twoPiITauExpr

positiveIntegerExpr : Nat -> Calc.CalculatorExpr
positiveIntegerExpr n =
  Calc.integer (Calc.integerLiteral Calc.positiveLiteral n)

qInverseExpr : Calc.CalculatorExpr
qInverseExpr = Calc.calcInverse qCoordinateExpr

jConstant744 : Calc.CalculatorExpr
jConstant744 = positiveIntegerExpr 744

jCoefficient196884 : Calc.CalculatorExpr
jCoefficient196884 = positiveIntegerExpr 196884

finiteJHeadExpr : Calc.CalculatorExpr
finiteJHeadExpr =
  Calc.calcAdd
    (Calc.calcAdd qInverseExpr jConstant744)
    (Calc.calcMultiply jCoefficient196884 qCoordinateExpr)

finiteJHeadLowered : EML.ExpLogSubExpr
finiteJHeadLowered = Calc.lowerCalculator finiteJHeadExpr

finiteJHeadCompiled : EML.EMLExpr
finiteJHeadCompiled = Calc.compileCalculator finiteJHeadExpr

qCoordinateLoweringIsExponential :
  Calc.lowerCalculator qCoordinateExpr
  ≡ EML.expE (Calc.lowerCalculator twoPiITauExpr)
qCoordinateLoweringIsExponential = refl

finiteJHeadCompilationIsCanonical :
  finiteJHeadCompiled ≡ EML.compileEML finiteJHeadLowered
finiteJHeadCompilationIsCanonical = refl

------------------------------------------------------------------------
-- The existing calculator theorem can transport meaning once a concrete
-- analytic model supplies its branch/domain laws.  We retain that dependency
-- instead of pretending syntax establishes analytic j authority.
------------------------------------------------------------------------

compileFiniteJHeadCorrect :
  ∀ {M : EML.ExpLogSubModel} ->
  EML.EMLCompilerLaws M ->
  Calc.CalculatorMeaning M ->
  (rho : EML.Env M) ->
  EML.evalEML M rho finiteJHeadCompiled
  ≡ Calc.CalculatorMeaning.meaning _ rho finiteJHeadExpr
compileFiniteJHeadCorrect laws meaning rho =
  Calc.calculatorMeaningCompiles laws meaning rho finiteJHeadExpr

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteQSyntaxIsKleinJ : Set where
data EMLCompilationProvesQSeriesConvergence : Set where
data EMLCompilationProvesModularity : Set where
data EMLCompilationProvesRH : Set where

finiteQSyntaxDoesNotCreateKleinJ : FiniteQSyntaxIsKleinJ -> ⊥
finiteQSyntaxDoesNotCreateKleinJ ()

emlCompilationDoesNotProveQSeriesConvergence :
  EMLCompilationProvesQSeriesConvergence -> ⊥
emlCompilationDoesNotProveQSeriesConvergence ()

emlCompilationDoesNotProveModularity : EMLCompilationProvesModularity -> ⊥
emlCompilationDoesNotProveModularity ()

emlCompilationDoesNotProveRH : EMLCompilationProvesRH -> ⊥
emlCompilationDoesNotProveRH ()

record JElementaryCalculatorShellBoundary : Set where
  constructor j-elementary-calculator-shell-boundary
  field
    qElementarySyntaxConstructed : Bool
    finiteJHeadSyntaxConstructed : Bool
    expLogSubLoweringReused : Bool
    singleOperatorCompilerReused : Bool
    kleinJSameObjectPaid : Bool
    qSeriesConvergencePaidHere : Bool
    modularityPaidHere : Bool
    rhPaidHere : Bool
    nextResidual : String
open JElementaryCalculatorShellBoundary public

canonicalJElementaryCalculatorShellBoundary : JElementaryCalculatorShellBoundary
canonicalJElementaryCalculatorShellBoundary =
  j-elementary-calculator-shell-boundary
    true true true true
    false false false false
    "attach the finite calculator shell to the existing theorem-bearing j q-expansion owner with an explicit same-expression/same-domain receipt; retain convergence and modular authority in that analytic owner"
