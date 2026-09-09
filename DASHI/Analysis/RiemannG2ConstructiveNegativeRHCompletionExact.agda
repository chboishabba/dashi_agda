module DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannG2UniformHighContradictionExact as High
import DASHI.Analysis.RiemannG2UniformLiteralPhaseHighProducerExact as LiteralHigh
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

------------------------------------------------------------------------
-- CANONICAL GENERIC HIGH INPUT
------------------------------------------------------------------------

record GenericHighNegativeRHInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    lowTransport : Low.PlattTrudgianVerifiedRegionTransport analytic
    HighRegion : Universal.AnalyticNontrivialZero analytic -> Set
    verifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion lowTransport rho ⊎ HighRegion rho
    highProducer : High.UniformHighContradictionProducer analytic HighRegion
    completionReference : String

open GenericHighNegativeRHInput public

lowDoubleNegCritical :
  forall {analytic} ->
  (input : GenericHighNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Low.CanonicalLowRegion (lowTransport input) rho ->
  Not (Not (Universal.analyticCritical rho))
lowDoubleNegCritical input rho low notCritical =
  notCritical (Low.canonicalLowCritical (lowTransport input) rho low)

highDoubleNegCritical :
  forall {analytic} ->
  (input : GenericHighNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  HighRegion input rho ->
  Not (Not (Universal.analyticCritical rho))
highDoubleNegCritical input rho high =
  High.contradictionForOffLineHigh (highProducer input) rho high

allDoubleNegCritical :
  forall {analytic} ->
  (input : GenericHighNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Not (Not (Universal.analyticCritical rho))
allDoubleNegCritical input rho with verifiedOrHighCover input rho
... | inj₁ low = lowDoubleNegCritical input rho low
... | inj₂ high = highDoubleNegCritical input rho high

compileGenericHighNegativeRH :
  forall {analytic} ->
  GenericHighNegativeRHInput analytic ->
  DoubleNegatedRiemannHypothesisFor analytic
compileGenericHighNegativeRH input s hz =
  allDoubleNegCritical input (Universal.analytic-nontrivial-zero s hz)

------------------------------------------------------------------------
-- LITERAL-PHASE COMPATIBILITY INPUT
------------------------------------------------------------------------

record DirectOneLeafNegativeRHInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    literalLowTransport : Low.PlattTrudgianVerifiedRegionTransport analytic
    LiteralHighRegion : Universal.AnalyticNontrivialZero analytic -> Set
    literalVerifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion literalLowTransport rho ⊎ LiteralHighRegion rho
    literalHighProducer :
      LiteralHigh.UniformLiteralPhaseHighProducer analytic LiteralHighRegion
    literalCompletionReference : String

open DirectOneLeafNegativeRHInput public

compileLiteralInputToGeneric :
  forall {analytic} ->
  DirectOneLeafNegativeRHInput analytic ->
  GenericHighNegativeRHInput analytic
compileLiteralInputToGeneric input = record
  { lowTransport = literalLowTransport input
  ; HighRegion = LiteralHighRegion input
  ; verifiedOrHighCover = literalVerifiedOrHighCover input
  ; highProducer = High.fromLiteralPhaseProducer (literalHighProducer input)
  ; completionReference = literalCompletionReference input
  }

compileDirectOneLeafNegativeRH :
  forall {analytic} ->
  DirectOneLeafNegativeRHInput analytic ->
  DoubleNegatedRiemannHypothesisFor analytic
compileDirectOneLeafNegativeRH input =
  compileGenericHighNegativeRH (compileLiteralInputToGeneric input)

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
    terminalNegativeRHCompilerRequiresLiteralPhaseImplementation : Bool
    terminalNegativeRHCompilerRequiresLiteralPhaseImplementationIsFalse :
      terminalNegativeRHCompilerRequiresLiteralPhaseImplementation ≡ false
    literalPhaseProducerCompilesGenericHighInput : Bool
    literalPhaseProducerCompilesGenericHighInputIsTrue :
      literalPhaseProducerCompilesGenericHighInput ≡ true
    arbitraryLowPredicatePrimitive : Bool
    arbitraryLowPredicatePrimitiveIsFalse : arbitraryLowPredicatePrimitive ≡ false
    separateLowSubsetVerifiedRegionProofPrimitive : Bool
    separateLowSubsetVerifiedRegionProofPrimitiveIsFalse :
      separateLowSubsetVerifiedRegionProofPrimitive ≡ false
    canonicalLowPositiveCriticalityCompilesDoubleNegatedCriticality : Bool
    canonicalLowPositiveCriticalityCompilesDoubleNegatedCriticalityIsTrue :
      canonicalLowPositiveCriticalityCompilesDoubleNegatedCriticality ≡ true
    genericUniformHighContradictionCompilesDoubleNegatedCriticality : Bool
    genericUniformHighContradictionCompilesDoubleNegatedCriticalityIsTrue :
      genericUniformHighContradictionCompilesDoubleNegatedCriticality ≡ true
    genericHighLowRouteCompilesDoubleNegatedRH : Bool
    genericHighLowRouteCompilesDoubleNegatedRHIsTrue :
      genericHighLowRouteCompilesDoubleNegatedRH ≡ true
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
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "The canonical high/low compiler now consumes only a uniform high contradiction family, not a literal-phase implementation. Low verified-region transport plus the verified-or-High cover and any same-carrier high contradiction producer compile to double-negated RH without critical-line stability. Literal phase remains a compatibility producer; certified finite-upper producers can feed the same high interface. Only positive RH needs the exact critical-predicate refinement, with no excluded-middle axiom or RH theorem fabricated here."
