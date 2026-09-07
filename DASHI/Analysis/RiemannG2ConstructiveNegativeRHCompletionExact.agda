module DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as High
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability

------------------------------------------------------------------------
-- CONSTRUCTIVE NEGATIVE RH COMPLETION
--
-- The direct high contradiction does not need double-negation elimination.  For
-- an arbitrary high zero it already gives
--
--   (criticalLine rho -> bottom) -> bottom,
--
-- i.e. double-negated criticality.  The canonical Low region is definitionally
-- the exact Platt--Trudgian verified-region predicate; its same-carrier theorem
-- gives positive criticality and hence double-negated criticality.
--
-- Package that result as the natural constructive endpoint of the analytic
-- high/low route.  The final conversion to prize-facing positive RH is then a
-- separate predicate-stability refinement rather than a hidden logical premise
-- inside the harmonic analysis.
------------------------------------------------------------------------

Not : Set -> Set
Not P = P -> ⊥

DoubleNegatedRiemannHypothesisFor :
  Analytic.AnalyticSubstrate -> Set
DoubleNegatedRiemannHypothesisFor analytic =
  (s : Analytic.ComplexAnalyticCarrier.Complex
    (Analytic.AnalyticSubstrate.carrier analytic)) ->
  Analytic.CompletedRiemannZeta.nontrivialZero
    (Analytic.AnalyticSubstrate.completed analytic) s ->
  Not (Not
    (Analytic.CompletedRiemannZeta.criticalLine
      (Analytic.AnalyticSubstrate.completed analytic) s))

record DirectOneLeafNegativeRHInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    lowTransport :
      Low.PlattTrudgianVerifiedRegionTransport analytic

    HighRegion : Universal.AnalyticNontrivialZero analytic -> Set

    verifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion lowTransport rho ⊎ HighRegion rho

    highProducer :
      High.UniformIndependentComplementHighProducer analytic HighRegion

    completionReference : String

open DirectOneLeafNegativeRHInput public

lowDoubleNegCritical :
  forall {analytic} ->
  (input : DirectOneLeafNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Low.CanonicalLowRegion (lowTransport input) rho ->
  Not (Not (Universal.analyticCritical rho))
lowDoubleNegCritical input rho low notCritical =
  notCritical
    (Low.canonicalLowCritical (lowTransport input) rho low)

highDoubleNegCritical :
  forall {analytic} ->
  (input : DirectOneLeafNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  HighRegion input rho ->
  Not (Not (Universal.analyticCritical rho))
highDoubleNegCritical input rho high =
  High.uniformHighContradiction (highProducer input) rho high

allDoubleNegCritical :
  forall {analytic} ->
  (input : DirectOneLeafNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Not (Not (Universal.analyticCritical rho))
allDoubleNegCritical input rho with verifiedOrHighCover input rho
... | inj₁ low = lowDoubleNegCritical input rho low
... | inj₂ high = highDoubleNegCritical input rho high

compileDirectOneLeafNegativeRH :
  forall {analytic} ->
  DirectOneLeafNegativeRHInput analytic ->
  DoubleNegatedRiemannHypothesisFor analytic
compileDirectOneLeafNegativeRH input s hz =
  allDoubleNegCritical input
    (Universal.analytic-nontrivial-zero s hz)

------------------------------------------------------------------------
-- LOGICAL FINAL STEP: exact predicate refinement turns negative RH into RH.
------------------------------------------------------------------------

negativeRHPlusPredicateRefinementImpliesRH :
  forall {analytic} ->
  Stability.CriticalLinePredicateRefinement analytic ->
  DoubleNegatedRiemannHypothesisFor analytic ->
  Analytic.RiemannHypothesisFor analytic
negativeRHPlusPredicateRefinementImpliesRH refinement negativeRH s hz =
  Stability.compileCriticalLineStable refinement s (negativeRH s hz)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ConstructiveNegativeRHBoundary : Set where
  constructor constructive-negative-rh-boundary
  field
    highAnalyticContradictionNeedsCriticalPredicateStability : Bool
    highAnalyticContradictionNeedsCriticalPredicateStabilityIsFalse :
      highAnalyticContradictionNeedsCriticalPredicateStability ≡ false

    arbitraryLowPredicatePrimitive : Bool
    arbitraryLowPredicatePrimitiveIsFalse :
      arbitraryLowPredicatePrimitive ≡ false

    separateLowSubsetVerifiedRegionProofPrimitive : Bool
    separateLowSubsetVerifiedRegionProofPrimitiveIsFalse :
      separateLowSubsetVerifiedRegionProofPrimitive ≡ false

    canonicalLowPositiveCriticalityCompilesDoubleNegatedCriticality : Bool
    canonicalLowPositiveCriticalityCompilesDoubleNegatedCriticalityIsTrue :
      canonicalLowPositiveCriticalityCompilesDoubleNegatedCriticality ≡ true

    uniformHighContradictionCompilesDoubleNegatedCriticality : Bool
    uniformHighContradictionCompilesDoubleNegatedCriticalityIsTrue :
      uniformHighContradictionCompilesDoubleNegatedCriticality ≡ true

    directHighLowRouteCompilesDoubleNegatedRH : Bool
    directHighLowRouteCompilesDoubleNegatedRHIsTrue :
      directHighLowRouteCompilesDoubleNegatedRH ≡ true

    positiveRHRequiresExactCriticalPredicateRefinement : Bool
    positiveRHRequiresExactCriticalPredicateRefinementIsTrue :
      positiveRHRequiresExactCriticalPredicateRefinement ≡ true

    globalExcludedMiddleIntroducedHere : Bool
    globalExcludedMiddleIntroducedHereIsFalse :
      globalExcludedMiddleIntroducedHere ≡ false

    negativeRHInputInhabitedHere : Bool
    negativeRHInputInhabitedHereIsFalse :
      negativeRHInputInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalConstructiveNegativeRHBoundary :
  ConstructiveNegativeRHBoundary
canonicalConstructiveNegativeRHBoundary =
  constructive-negative-rh-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "The constructive endpoint is now smaller again. Low is definitionally the exact Platt--Trudgian verified-region predicate, so no arbitrary Low carrier or separate Low-subset-verification theorem remains on the canonical path. The same-carrier verified-region criticality theorem and the verified-region-or-High cover combine with the uniform high contradiction to prove double-negated RH without critical-line stability. Only the final conversion to positive RH needs the exact critical-predicate refinement. No excluded-middle axiom or substantive input is fabricated here."
