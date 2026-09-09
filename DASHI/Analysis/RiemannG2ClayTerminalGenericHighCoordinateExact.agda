module DASHI.Analysis.RiemannG2ClayTerminalGenericHighCoordinateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate
import DASHI.Analysis.RiemannG2UniformHighContradictionExact as High
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative

------------------------------------------------------------------------
-- GENERIC-HIGH + SHARED-COORDINATE CLAY TERMINAL
--
-- This is the least implementation-aware prize-facing wrapper currently needed:
--
--   one same-AnalyticSubstrate coordinate refinement
--   + verified-region-or-High cover
--   + implementation-neutral uniform high contradiction
--   -> double-negated RH
--   -> positive RH through the same coordinate refinement.
--
-- The terminal wrapper does not know whether the high contradiction came from
-- a direct literal-phase theorem, a certified finite upper, or another future
-- same-object producer.
------------------------------------------------------------------------

record GenericHighCoordinateClayInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    coordinate : Coordinate.AnalyticCoordinateTerminalRefinement analytic

    HighRegion : Universal.AnalyticNontrivialZero analytic -> Set

    verifiedOrHighCover :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      Low.CanonicalLowRegion
        (Coordinate.compilePlattTrudgianVerifiedRegionTransport coordinate)
        rho
      ⊎ HighRegion rho

    highProducer : High.UniformHighContradictionProducer analytic HighRegion

    terminalReference : String

open GenericHighCoordinateClayInput public

compileGenericNegativeInput :
  forall {analytic} ->
  GenericHighCoordinateClayInput analytic ->
  Negative.GenericHighNegativeRHInput analytic
compileGenericNegativeInput input = record
  { Negative.genericLowTransport =
      Coordinate.compilePlattTrudgianVerifiedRegionTransport (coordinate input)
  ; Negative.GenericHighRegion = HighRegion input
  ; Negative.genericVerifiedOrHighCover = verifiedOrHighCover input
  ; Negative.genericHighProducer = highProducer input
  ; Negative.genericCompletionReference = terminalReference input
  }

compiledDoubleNegatedRH :
  forall {analytic} ->
  GenericHighCoordinateClayInput analytic ->
  Negative.DoubleNegatedRiemannHypothesisFor analytic
compiledDoubleNegatedRH input =
  Negative.compileGenericHighNegativeRH (compileGenericNegativeInput input)

compileGenericHighCoordinateClayToRH :
  forall {analytic} ->
  GenericHighCoordinateClayInput analytic ->
  Analytic.RiemannHypothesisFor analytic
compileGenericHighCoordinateClayToRH input =
  Negative.negativeRHPlusPredicateRefinementImpliesRH
    (Coordinate.compileCriticalLinePredicateRefinement (coordinate input))
    (compiledDoubleNegatedRH input)

record GenericHighCoordinateClayBoundary : Set where
  constructor generic-high-coordinate-clay-boundary
  field
    terminalClayWrapperRequiresLiteralPhaseImplementation : Bool
    terminalClayWrapperRequiresLiteralPhaseImplementationIsFalse :
      terminalClayWrapperRequiresLiteralPhaseImplementation ≡ false

    terminalClayWrapperRequiresCertifiedUpperImplementation : Bool
    terminalClayWrapperRequiresCertifiedUpperImplementationIsFalse :
      terminalClayWrapperRequiresCertifiedUpperImplementation ≡ false

    oneSameCarrierCoordinateRefinementCompilesLowAndStability : Bool
    oneSameCarrierCoordinateRefinementCompilesLowAndStabilityIsTrue :
      oneSameCarrierCoordinateRefinementCompilesLowAndStability ≡ true

    verifiedRegionOrHighCoverStillRequired : Bool
    verifiedRegionOrHighCoverStillRequiredIsTrue :
      verifiedRegionOrHighCoverStillRequired ≡ true

    genericUniformHighContradictionStillRequired : Bool
    genericUniformHighContradictionStillRequiredIsTrue :
      genericUniformHighContradictionStillRequired ≡ true

    highLowCompilesDoubleNegatedRHBeforeStability : Bool
    highLowCompilesDoubleNegatedRHBeforeStabilityIsTrue :
      highLowCompilesDoubleNegatedRHBeforeStability ≡ true

    theseInputsCompileRiemannHypothesisFor : Bool
    theseInputsCompileRiemannHypothesisForIsTrue :
      theseInputsCompileRiemannHypothesisFor ≡ true

    inputsInhabitedHere : Bool
    inputsInhabitedHereIsFalse : inputsInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalGenericHighCoordinateClayBoundary : GenericHighCoordinateClayBoundary
canonicalGenericHighCoordinateClayBoundary =
  generic-high-coordinate-clay-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The canonical Clay wrapper now consumes one shared same-AnalyticSubstrate coordinate refinement, one verified-region-or-High cover, and one implementation-neutral uniform high contradiction producer. Direct literal-phase and proof-carrying certified-upper routes are interchangeable producer families below this interface. The wrapper compiles double-negated RH before using coordinate stability for positive RH; none of the substantive inputs or RH is inhabited here."
