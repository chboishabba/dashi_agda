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
    genericLowTransport : Low.PlattTrudgianVerifiedRegionTransport analytic
    GenericHighRegion : Universal.AnalyticNontrivialZero analytic -> Set
    genericVerifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion genericLowTransport rho ⊎ GenericHighRegion rho
    genericHighProducer :
      High.UniformHighContradictionProducer analytic GenericHighRegion
    genericCompletionReference : String

open GenericHighNegativeRHInput public

genericLowDoubleNegCritical :
  forall {analytic} ->
  (input : GenericHighNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Low.CanonicalLowRegion (genericLowTransport input) rho ->
  Not (Not (Universal.analyticCritical rho))
genericLowDoubleNegCritical input rho low notCritical =
  notCritical (Low.canonicalLowCritical (genericLowTransport input) rho low)

genericHighDoubleNegCritical :
  forall {analytic} ->
  (input : GenericHighNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  GenericHighRegion input rho ->
  Not (Not (Universal.analyticCritical rho))
genericHighDoubleNegCritical input rho high =
  High.contradictionForOffLineHigh (genericHighProducer input) rho high

genericAllDoubleNegCritical :
  forall {analytic} ->
  (input : GenericHighNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Not (Not (Universal.analyticCritical rho))
genericAllDoubleNegCritical input rho with genericVerifiedOrHighCover input rho
... | inj₁ low = genericLowDoubleNegCritical input rho low
... | inj₂ high = genericHighDoubleNegCritical input rho high

compileGenericHighNegativeRH :
  forall {analytic} ->
  GenericHighNegativeRHInput analytic ->
  DoubleNegatedRiemannHypothesisFor analytic
compileGenericHighNegativeRH input s hz =
  genericAllDoubleNegCritical input (Universal.analytic-nontrivial-zero s hz)

------------------------------------------------------------------------
-- LITERAL-PHASE COMPATIBILITY INPUT
--
-- Preserve the existing public field/projection names so downstream Clay and
-- regression owners remain source-compatible.
------------------------------------------------------------------------

record DirectOneLeafNegativeRHInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    lowTransport : Low.PlattTrudgianVerifiedRegionTransport analytic
    HighRegion : Universal.AnalyticNontrivialZero analytic -> Set
    verifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion lowTransport rho ⊎ HighRegion rho
    highProducer : LiteralHigh.UniformLiteralPhaseHighProducer analytic HighRegion
    completionReference : String

open DirectOneLeafNegativeRHInput public

compileLiteralInputToGeneric :
  forall {analytic} ->
  DirectOneLeafNegativeRHInput analytic ->
  GenericHighNegativeRHInput analytic
compileLiteralInputToGeneric input = record
  { genericLowTransport = lowTransport input
  ; GenericHighRegion = HighRegion input
  ; genericVerifiedOrHighCover = verifiedOrHighCover input
  ; genericHighProducer = High.fromLiteralPhaseProducer (highProducer input)
  ; genericCompletionReference = completionReference input
  }

lowDoubleNegCritical :
  forall {analytic} ->
  (input : DirectOneLeafNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Low.CanonicalLowRegion (lowTransport input) rho ->
  Not (Not (Universal.analyticCritical rho))
lowDoubleNegCritical input =
  genericLowDoubleNegCritical (compileLiteralInputToGeneric input)

highDoubleNegCritical :
  forall {analytic} ->
  (input : DirectOneLeafNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  HighRegion input rho ->
  Not (Not (Universal.analyticCritical rho))
highDoubleNegCritical input =
  genericHighDoubleNegCritical (compileLiteralInputToGeneric input)

allDoubleNegCritical :
  forall {analytic} ->
  (input : DirectOneLeafNegativeRHInput analytic) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  Not (Not (Universal.analyticCritical rho))
allDoubleNegCritical input =
  genericAllDoubleNegCritical (compileLiteralInputToGeneric input)

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

    uniformLiteralPhaseContradictionCompilesDoubleNegatedCriticality : Bool
    uniformLiteralPhaseContradictionCompilesDoubleNegatedCriticalityIsTrue :
      uniformLiteralPhaseContradictionCompilesDoubleNegatedCriticality ≡ true

    genericUniformHighContradictionCompilesDoubleNegatedCriticality : Bool
    genericUniformHighContradictionCompilesDoubleNegatedCriticalityIsTrue :
      genericUniformHighContradictionCompilesDoubleNegatedCriticality ≡ true

    opaqueCanonicalMarginProducerPrimitiveAtClayBoundary : Bool
    opaqueCanonicalMarginProducerPrimitiveAtClayBoundaryIsFalse :
      opaqueCanonicalMarginProducerPrimitiveAtClayBoundary ≡ false

    directHighLowRouteCompilesDoubleNegatedRH : Bool
    directHighLowRouteCompilesDoubleNegatedRHIsTrue :
      directHighLowRouteCompilesDoubleNegatedRH ≡ true

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
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "The canonical high/low compiler consumes only a uniform high contradiction family, not a literal-phase implementation. Existing literal-phase callers retain their original DirectOneLeafNegativeRHInput field names and compile through a compatibility adapter. Low verified-region transport plus the verified-or-High cover and any same-carrier uniform high contradiction producer compile to double-negated RH without critical-line stability. Certified finite-upper and direct phase routes can therefore share one terminal spine. Only positive RH needs the exact critical-predicate refinement; no excluded-middle axiom or RH theorem is fabricated here."
