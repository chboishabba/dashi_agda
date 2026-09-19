module DASHI.Analysis.RiemannElementaryCalculatorShellReuseValidation where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannElementaryCalculatorShellReuseExact as P

functionalEquationReuseRegression :
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
functionalEquationReuseRegression = P.functionalEquationRetained

boundaryRegression :
  P.RiemannElementaryCalculatorShellBoundary.rhDerivedByCalculatorShell
    P.canonicalRiemannElementaryCalculatorShellBoundary
  ≡ false
boundaryRegression = refl
