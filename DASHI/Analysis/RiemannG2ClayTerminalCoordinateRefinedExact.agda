module DASHI.Analysis.RiemannG2ClayTerminalCoordinateRefinedExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannG2UniformLiteralPhaseHighProducerExact as High
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate
import DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact as Clay

------------------------------------------------------------------------
-- COORDINATE-REFINED CLAY TERMINAL INPUT
--
-- Do not ask the terminal caller to supply a low verified-region transport and
-- a critical-line predicate refinement independently.  They are compiled from
-- one theorem-bearing same-AnalyticSubstrate coordinate refinement.
------------------------------------------------------------------------

record CoordinateRefinedClayInput
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

    highProducer : High.UniformLiteralPhaseHighProducer analytic HighRegion

    terminalReference : String

open CoordinateRefinedClayInput public

compileClayTerminalInput :
  forall {analytic} ->
  CoordinateRefinedClayInput analytic ->
  Clay.ClayTerminalOneLeafInput analytic
compileClayTerminalInput input = record
  { Clay.lowTransport =
      Coordinate.compilePlattTrudgianVerifiedRegionTransport (coordinate input)
  ; Clay.HighRegion = HighRegion input
  ; Clay.verifiedOrHighCover = verifiedOrHighCover input
  ; Clay.highProducer = highProducer input
  ; Clay.criticalLineRefinement =
      Coordinate.compileCriticalLinePredicateRefinement (coordinate input)
  ; Clay.terminalReference = terminalReference input
  }

compileCoordinateRefinedClayToRH :
  forall {analytic} ->
  CoordinateRefinedClayInput analytic ->
  Analytic.RiemannHypothesisFor analytic
compileCoordinateRefinedClayToRH input =
  Clay.compileClayTerminalOneLeafToRH (compileClayTerminalInput input)

record CoordinateRefinedClayBoundary : Set where
  constructor coordinate-refined-clay-boundary
  field
    separateLowTransportPrimitive : Bool
    separateLowTransportPrimitiveIsFalse :
      separateLowTransportPrimitive ≡ false

    separateCriticalPredicateRefinementPrimitive : Bool
    separateCriticalPredicateRefinementPrimitiveIsFalse :
      separateCriticalPredicateRefinementPrimitive ≡ false

    oneSameCarrierCoordinateRefinementCompilesBoth : Bool
    oneSameCarrierCoordinateRefinementCompilesBothIsTrue :
      oneSameCarrierCoordinateRefinementCompilesBoth ≡ true

    verifiedRegionOrHighCoverStillRequired : Bool
    verifiedRegionOrHighCoverStillRequiredIsTrue :
      verifiedRegionOrHighCoverStillRequired ≡ true

    uniformHighProducerStillRequired : Bool
    uniformHighProducerStillRequiredIsTrue :
      uniformHighProducerStillRequired ≡ true

    theseInputsCompileRiemannHypothesisFor : Bool
    theseInputsCompileRiemannHypothesisForIsTrue :
      theseInputsCompileRiemannHypothesisFor ≡ true

    coordinateRefinementInhabitedHere : Bool
    coordinateRefinementInhabitedHereIsFalse :
      coordinateRefinementInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalCoordinateRefinedClayBoundary : CoordinateRefinedClayBoundary
canonicalCoordinateRefinedClayBoundary =
  coordinate-refined-clay-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "At the Clay boundary, consume one theorem-bearing same-AnalyticSubstrate coordinate refinement, one verified-region-or-High cover, and the uniform high literal-phase producer. The coordinate compiler supplies both the Platt--Trudgian low transport and the exact critical-line predicate refinement/stability. This removes duplicated carrier interpretation but does not inhabit the coordinate theorem, high producer, cover, or RH."
