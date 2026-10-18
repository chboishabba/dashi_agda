module DASHI.Analysis.RiemannAnalyticCoordinateObserverDescentValidation where

import DASHI.Foundations.HyperformChartGluingExact as Glue
import DASHI.Foundations.ProofRelevantPredicateObserverDescentExact as Predicate

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate
import DASHI.Analysis.RiemannAnalyticCoordinateObserverDescentExact as R3

criticalPredicateFactorsThroughRealPart :
  ∀ {analytic}
    (refinement : Coordinate.AnalyticCoordinateTerminalRefinement analytic) →
  Predicate.PredicateFactorsThroughObserver
    (R3.realPartObserver analytic)
    (Analytic.CompletedRiemannZeta.criticalLine
      (Analytic.AnalyticSubstrate.completed analytic))
criticalPredicateFactorsThroughRealPart =
  R3.criticalLineFactorsThroughRealPart

sameRealPartTransportsCriticality :
  ∀ {analytic}
    (refinement : Coordinate.AnalyticCoordinateTerminalRefinement analytic)
    (left right :
      Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)) →
  Glue.observe (R3.realPartObserver analytic) left
    ≡ Glue.observe (R3.realPartObserver analytic) right →
  Analytic.CompletedRiemannZeta.criticalLine
    (Analytic.AnalyticSubstrate.completed analytic) left →
  Analytic.CompletedRiemannZeta.criticalLine
    (Analytic.AnalyticSubstrate.completed analytic) right
sameRealPartTransportsCriticality =
  R3.criticalLineConstantOnRealPartFibre
