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

------------------------------------------------------------------------
-- CONSTRUCTIVE NEGATIVE RH COMPLETION
--
-- The direct high contradiction does not need double-negation elimination.  The
-- canonical high input is now the literal phase-visible theorem family itself:
-- for each arbitrary high off-line zero, an unpaid final context, exact literal
-- near model, and independent phase+far+Gamma strict margin.
--
-- The canonical Low region is definitionally the exact Platt--Trudgian
-- verified-region predicate.  Low positive criticality and high contradiction
-- compile to double-negated RH.  Only the final conversion to prize-facing
-- positive RH consumes the critical-predicate refinement.
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
    lowTransport : Low.PlattTrudgianVerifiedRegionTransport analytic
    HighRegion : Universal.AnalyticNontrivialZero analytic -> Set
    verifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion lowTransport rho ⊎ HighRegion rho

    highProducer :
      High.UniformLiteralPhaseHighProducer analytic HighRegion

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
  High.uniformLiteralPhaseHighContradiction
    (highProducer input) rho high

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
    "The constructive Clay-strength endpoint now consumes the literal phase-visible high theorem family directly. For each arbitrary high off-line zero, the high input exposes the unpaid final context, exact literal near model, and independent phase+far+Gamma strict margin; that compiles to contradiction and hence double-negated criticality. Low is definitionally the Platt--Trudgian verified region. Verified-region transport plus the verified-or-High cover and the literal high family compile to double-negated RH with no critical-line stability. Only positive RH needs the exact critical-predicate refinement. No opaque canonical-margin producer, excluded-middle axiom, or substantive theorem is fabricated here."
