module DASHI.Analysis.RiemannAnalyticCoordinateObserverDescentExact where

------------------------------------------------------------------------
-- LITERAL RH R3 AS A SHARED PROOF-RELEVANT COORDINATE OBSERVER
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- The existing terminal coordinate package already proves, on one exact
-- AnalyticSubstrate,
--
--   criticalLine(s)  <->  realPart(s) = half
--
-- and separately proves that every zero in the published verified region has
-- realPart = half.  This owner exposes the common information geometry:
--
--   Complex --realPart--> Real
--                    |
--                    +-- coarse predicate r = half
--
-- The critical-line predicate genuinely descends through this observer, while
-- the published verified region lands in the same coarse predicate.  Therefore
-- the low-region theorem and the critical-line refinement share one theorem-
-- bearing coordinate instead of separate carrier interpretations.
--
-- The actual coordinate refinement remains an input.  No numeric-height
-- interpretation, high contradiction, cover, or RH is manufactured here.
------------------------------------------------------------------------

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.HyperformChartGluingExact as Glue
import DASHI.Foundations.ProofRelevantPredicateObserverDescentExact as Predicate

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate

realPartObserver :
  (analytic : Analytic.AnalyticSubstrate) →
  Glue.ObserverWithFibre
    (Analytic.ComplexAnalyticCarrier.Complex
      (Analytic.AnalyticSubstrate.carrier analytic))
    (Analytic.ComplexAnalyticCarrier.Real
      (Analytic.AnalyticSubstrate.carrier analytic))
realPartObserver analytic = record
  { Glue.observe =
      Analytic.ComplexAnalyticCarrier.realPart
        (Analytic.AnalyticSubstrate.carrier analytic)
  }

halfCoordinatePredicate :
  ∀ {analytic} →
  Coordinate.AnalyticCoordinateTerminalRefinement analytic →
  Analytic.ComplexAnalyticCarrier.Real
    (Analytic.AnalyticSubstrate.carrier analytic) →
  Set
halfCoordinatePredicate refinement r =
  r ≡ Coordinate.half refinement

criticalLineFactorsThroughRealPart :
  ∀ {analytic} →
  (refinement : Coordinate.AnalyticCoordinateTerminalRefinement analytic) →
  Predicate.PredicateFactorsThroughObserver
    (realPartObserver analytic)
    (Analytic.CompletedRiemannZeta.criticalLine
      (Analytic.AnalyticSubstrate.completed analytic))
criticalLineFactorsThroughRealPart refinement = record
  { Predicate.coarsePredicate =
      halfCoordinatePredicate refinement
  ; Predicate.forward =
      Coordinate.criticalLineImpliesHalf refinement
  ; Predicate.backward =
      Coordinate.halfImpliesCriticalLine refinement
  }

criticalLineConstantOnRealPartFibre :
  ∀ {analytic}
    (refinement : Coordinate.AnalyticCoordinateTerminalRefinement analytic)
    (left right :
      Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)) →
  Glue.observe (realPartObserver analytic) left
    ≡ Glue.observe (realPartObserver analytic) right →
  Analytic.CompletedRiemannZeta.criticalLine
    (Analytic.AnalyticSubstrate.completed analytic) left →
  Analytic.CompletedRiemannZeta.criticalLine
    (Analytic.AnalyticSubstrate.completed analytic) right
criticalLineConstantOnRealPartFibre refinement =
  Predicate.predicateTransportAcrossObserverFibre
    (criticalLineFactorsThroughRealPart refinement)

zeroRealPartObserver :
  (analytic : Analytic.AnalyticSubstrate) →
  Glue.ObserverWithFibre
    (Universal.AnalyticNontrivialZero analytic)
    (Analytic.ComplexAnalyticCarrier.Real
      (Analytic.AnalyticSubstrate.carrier analytic))
zeroRealPartObserver analytic = record
  { Glue.observe = λ rho →
      Analytic.ComplexAnalyticCarrier.realPart
        (Analytic.AnalyticSubstrate.carrier analytic)
        (Universal.point rho)
  }

publishedVerifiedRegionLandsAtHalf :
  ∀ {analytic}
    (refinement : Coordinate.AnalyticCoordinateTerminalRefinement analytic)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  Coordinate.WithinPublishedVerifiedHeight refinement rho →
  halfCoordinatePredicate refinement
    (Glue.observe (zeroRealPartObserver analytic) rho)
publishedVerifiedRegionLandsAtHalf refinement rho =
  Coordinate.publishedVerifiedHeightHasHalfRealPart refinement rho

publishedVerifiedRegionCriticalViaSharedCoordinate :
  ∀ {analytic}
    (refinement : Coordinate.AnalyticCoordinateTerminalRefinement analytic)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  Coordinate.WithinPublishedVerifiedHeight refinement rho →
  Universal.analyticCritical rho
publishedVerifiedRegionCriticalViaSharedCoordinate refinement rho within =
  Coordinate.halfImpliesCriticalLine refinement
    (Universal.point rho)
    (publishedVerifiedRegionLandsAtHalf refinement rho within)

record AnalyticCoordinateObserverDescentBoundary : Set where
  constructor analytic-coordinate-observer-descent-boundary
  field
    criticalLinePredicateFactorsThroughRealPart : Bool
    criticalLineIsConstantOnRealPartFibres : Bool
    verifiedRegionLandsInSameHalfCoordinate : Bool
    lowAndCriticalConsumersShareCoordinate : Bool
    numericVerifiedHeightInterpretationPaidHere : Bool
    highContradictionPaidHere : Bool
    verifiedRegionOrHighCoverPaidHere : Bool
    rhDerived : Bool

open AnalyticCoordinateObserverDescentBoundary public

canonicalAnalyticCoordinateObserverDescentBoundary :
  AnalyticCoordinateObserverDescentBoundary
canonicalAnalyticCoordinateObserverDescentBoundary =
  analytic-coordinate-observer-descent-boundary
    true true true true false false false false
