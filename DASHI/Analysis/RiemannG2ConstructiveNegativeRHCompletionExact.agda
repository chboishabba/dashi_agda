module DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannG2UniformLiteralPhaseHighProducerExact as High
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability

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
    lowTransport : Low.PlattTrudgianVerifiedRegionTransport analytic
    HighRegion : Universal.AnalyticNontrivialZero analytic -> Set
    verifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion lowTransport rho ⊎ HighRegion rho
    highProducer : High.UniformLiteralPhaseHighProducer analytic HighRegion
    completionReference : String

open DirectOneLeafNegativeRHInput public

lowDoubleNegCritical :
  forall {analytic} ->
  (input : DirectOneLeafNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Low.CanonicalLowRegion (lowTransport input) rho ->
  Not (Not (Universal.analyticCritical rho))
lowDoubleNegCritical input rho low notCritical =
  notCritical (Low.canonicalLowCritical (lowTransport input) rho low)

highDoubleNegCritical :
  forall {analytic} ->
  (input : DirectOneLeafNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  HighRegion input rho ->
  Not (Not (Universal.analyticCritical rho))
highDoubleNegCritical input rho high =
  High.uniformLiteralPhaseHighContradiction (highProducer input) rho high

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
  allDoubleNegCritical input (Universal.analytic-nontrivial-zero s hz)

negativeRHPlusPredicateRefinementImpliesRH :
  forall {analytic} ->
  Stability.CriticalLinePredicateRefinement analytic ->
  DoubleNegatedRiemannHypothesisFor analytic ->
  Analytic.RiemannHypothesisFor analytic
negativeRHPlusPredicateRefinementImpliesRH refinement negativeRH s hz =
  Stability.compileCriticalLineStable refinement s (negativeRH s hz)

record ConstructiveNegativeRHBoundary : Set where
  constructor constructive-negative-rh-boundary
  field
    highAnalyticContradictionNeedsCriticalPredicateStability : Bool
    highAnalyticContradictionNeedsCriticalPredicateStabilityIsFalse :
      highAnalyticContradictionNeedsCriticalPredicateStability ≡ false
    arbitraryLowPredicatePrimitive : Bool
    arbitraryLowPredicatePrimitiveIsFalse : arbitraryLowPredicatePrimitive ≡ false
    separateLowSubsetVerifiedRegionProofPrimitive : Bool
    separateLowSubsetVerifiedRegionProofPrimitiveIsFalse :
      separateLowSubsetVerifiedRegionProofPrimitive ≡ false
    canonicalLowPositiveCriticalityCompilesDoubleNegatedCriticality : Bool
    canonicalLowPositiveCriticalityCompilesDoubleNegatedCriticalityIsTrue :
      canonicalLowPositiveCriticalityCompilesDoubleNegatedCriticality ≡ true
    uniformLiteralPhaseContradictionCompilesDoubleNegatedCriticality : Bool
    uniformLiteralPhaseContradictionCompilesDoubleNegatedCriticalityIsTrue :
      uniformLiteralPhaseContradictionCompilesDoubleNegatedCriticality ≡ true
    opaqueCanonicalMarginProducerPrimitiveAtClayBoundary : Bool
    opaqueCanonicalMarginProducerPrimitiveAtClayBoundaryIsFalse :
      opaqueCanonicalMarginProducerPrimitiveAtClayBoundary ≡ false
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
    negativeRHInputInhabitedHereIsFalse : negativeRHInputInhabitedHere ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    highestAlphaReading : String

canonicalConstructiveNegativeRHBoundary : ConstructiveNegativeRHBoundary
canonicalConstructiveNegativeRHBoundary =
  constructive-negative-rh-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Low verified-region transport plus the verified-or-High cover and the uniform literal phase high contradiction compile to double-negated RH without critical-line stability. The high theorem family now targets the actual ClusterResponse through its direct producer. Only positive RH needs the exact critical-predicate refinement; no excluded-middle axiom or substantive theorem is fabricated here."
