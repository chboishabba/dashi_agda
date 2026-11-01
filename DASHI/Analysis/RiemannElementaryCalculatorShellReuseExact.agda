module DASHI.Analysis.RiemannElementaryCalculatorShellReuseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact as Carrier
import DASHI.Moonshine.JInvariantConstructedComplexQCalculatorSameExpressionExact as Q

------------------------------------------------------------------------
-- RH / ELEMENTARY CALCULATOR SHELL REUSE
--
-- This owner does one narrow cross-lane job:
--
-- * retain the genuine CompletedRiemannZeta.functionalEquation unchanged;
-- * reuse the existing whole-carrier attachment from the constructed complex
--   package into the selected Riemann AnalyticSubstrate;
-- * expose the new exact calculator-AST <-> qOf theorem on that same donor
--   constructed-complex carrier.
--
-- No theorem below says that q is part of xi's definition, that xi factors
-- through the calculator, or that EML compilation proves RH.
------------------------------------------------------------------------

functionalEquationRetained :
  (analytic : Analytic.AnalyticSubstrate) ->
  (s : Analytic.ComplexAnalyticCarrier.Complex
    (Analytic.AnalyticSubstrate.carrier analytic)) ->
  Analytic.ComplexAnalyticCarrier.apply
    (Analytic.AnalyticSubstrate.carrier analytic)
    (Analytic.CompletedRiemannZeta.xi
      (Analytic.AnalyticSubstrate.completed analytic)) s
  ≡
  Analytic.ComplexAnalyticCarrier.apply
    (Analytic.AnalyticSubstrate.carrier analytic)
    (Analytic.CompletedRiemannZeta.xi
      (Analytic.AnalyticSubstrate.completed analytic))
    (Analytic.CompletedRiemannZeta.oneMinus
      (Analytic.AnalyticSubstrate.completed analytic) s)
functionalEquationRetained analytic s =
  Analytic.CompletedRiemannZeta.functionalEquation
    (Analytic.AnalyticSubstrate.completed analytic) s

record RiemannQCalculatorAttachment
    (analytic : Analytic.AnalyticSubstrate)
    (C : Complex.ConstructedComplexPackage)
    (F : Carrier.ConstructedComplexAnalyticFunctionLayer C) : Set₁ where
  constructor riemann-q-calculator-attachment
  field
    carrierRealization : Carrier.CanonicalConstructedCarrierRealization analytic C F
open RiemannQCalculatorAttachment public

rhComplexCarrierIsQDonorCarrier :
  ∀ {analytic C F} ->
  RiemannQCalculatorAttachment analytic C F ->
  Analytic.ComplexAnalyticCarrier.Complex
    (Analytic.AnalyticSubstrate.carrier analytic)
  ≡ Complex.ComplexPair (Real.real (Complex.realPackage C))
rhComplexCarrierIsQDonorCarrier A =
  Carrier.complexCarrierIdentityFromWholeCarrier (carrierRealization A)

qSameExpressionOnAttachedDonor :
  ∀ {analytic C F} ->
  RiemannQCalculatorAttachment analytic C F ->
  (tau : Complex.ComplexPair (Real.real (Complex.realPackage C))) ->
  Q.evalQOfCalculator C tau ≡ Q.qOf C tau
qSameExpressionOnAttachedDonor A tau = Q.evalQOfCalculatorIsQOf _ tau

------------------------------------------------------------------------
-- Explicit non-factorability / authority firewalls.
------------------------------------------------------------------------

data QShellIsCompletedXiDefinition : Set where
data CompletedXiFactorsThroughCalculator : Set where
data FunctionalEquationFactorsThroughQShell : Set where
data CalculatorShellCreatesRiemannHypothesis : Set where

qShellDoesNotBecomeCompletedXiDefinition : QShellIsCompletedXiDefinition -> ⊥
qShellDoesNotBecomeCompletedXiDefinition ()

completedXiDoesNotFactorThroughCalculator : CompletedXiFactorsThroughCalculator -> ⊥
completedXiDoesNotFactorThroughCalculator ()

functionalEquationDoesNotFactorThroughQShell : FunctionalEquationFactorsThroughQShell -> ⊥
functionalEquationDoesNotFactorThroughQShell ()

calculatorShellDoesNotCreateRiemannHypothesis :
  CalculatorShellCreatesRiemannHypothesis -> ⊥
calculatorShellDoesNotCreateRiemannHypothesis ()

record RiemannElementaryCalculatorShellBoundary : Set where
  constructor riemann-elementary-calculator-shell-boundary
  field
    completedFunctionalEquationReused : Bool
    constructedComplexCarrierAdapterReused : Bool
    calculatorQSameExpressionReused : Bool
    qAndRiemannCarrierCanShareLiteralDonorCarrier : Bool
    qShellIsCompletedXiDefinition : Bool
    completedXiFactorsThroughCalculator : Bool
    functionalEquationFactorsThroughQShell : Bool
    rhDerivedByCalculatorShell : Bool
    nextResidual : String
open RiemannElementaryCalculatorShellBoundary public

canonicalRiemannElementaryCalculatorShellBoundary :
  RiemannElementaryCalculatorShellBoundary
canonicalRiemannElementaryCalculatorShellBoundary =
  riemann-elementary-calculator-shell-boundary
    true true true true
    false false false false
    "only compile elementary factors that are already explicit in a theorem-bearing RH owner; retain Gamma, zeta, xi, analytic continuation, zero classification, and the functional equation as independent analytic authority"
