module DASHI.Analysis.RiemannG2ClayTerminalMinimalLocatedR3StarExact where

------------------------------------------------------------------------
-- MINIMAL CONSTRUCTIVE R3★ TERMINAL
--
-- This is the preferred low-side terminal surface.  It consumes exactly:
--
--   * one located analytic-coordinate realization over a minimal height carrier,
--   * one uniform high contradiction producer on T_high < |Im rho|.
--
-- The low/high cover is compiler output from locatedness.  No Dec(V), arbitrary
-- cover, complete-real package, rational density, reciprocal, or Archimedean
-- package appears at this boundary.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₂)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located
import DASHI.Analysis.RiemannG2UniformHighContradictionExact as High
import DASHI.Analysis.RiemannG2ClayTerminalGenericHighCoordinateExact as Generic

record ClayTerminalMinimalLocatedR3StarInput
    (analytic : Analytic.AnalyticSubstrate) : Set₂ where
  field
    r3Star :
      Located.LocatedAnalyticCoordinateRealization analytic

    highProducer :
      High.UniformHighContradictionProducer
        analytic
        (Located.LocatedHighRegion
          (Located.carrierAttachment r3Star))

    terminalReference : String

open ClayTerminalMinimalLocatedR3StarInput public

compileMinimalLocatedR3StarToGenericClay :
  ∀ {analytic} →
  ClayTerminalMinimalLocatedR3StarInput analytic →
  Generic.GenericHighCoordinateClayInput analytic
compileMinimalLocatedR3StarToGenericClay input = record
  { Generic.coordinate =
      Located.compileCoordinateTerminalRefinement (r3Star input)
  ; Generic.HighRegion =
      Located.LocatedHighRegion
        (Located.carrierAttachment (r3Star input))
  ; Generic.verifiedOrHighCover =
      Located.locatedVerifiedOrHigh
        (Located.carrierAttachment (r3Star input))
  ; Generic.highProducer =
      highProducer input
  ; Generic.terminalReference =
      terminalReference input
  }

compileClayTerminalMinimalLocatedR3StarToRH :
  ∀ {analytic} →
  ClayTerminalMinimalLocatedR3StarInput analytic →
  Analytic.RiemannHypothesisFor analytic
compileClayTerminalMinimalLocatedR3StarToRH input =
  Generic.compileGenericHighCoordinateClayToRH
    (compileMinimalLocatedR3StarToGenericClay input)

record ClayTerminalMinimalLocatedR3StarBoundary : Set where
  constructor clay-terminal-minimal-located-r3star-boundary
  field
    exactVerifiedRegionDecisionRequired : Bool
    arbitraryLowHighCoverRequired : Bool
    completeRealCapabilityPackageRequired : Bool
    minimalLocatedHeightCarrierSuffices : Bool
    uniformHighProducerStillRequired : Bool
    sameCarrierLowTheoremStillRequired : Bool
    theseInputsCompileRH : Bool
    inputsInhabitedHere : Bool
    rhDerivedHere : Bool

open ClayTerminalMinimalLocatedR3StarBoundary public

canonicalClayTerminalMinimalLocatedR3StarBoundary :
  ClayTerminalMinimalLocatedR3StarBoundary
canonicalClayTerminalMinimalLocatedR3StarBoundary =
  clay-terminal-minimal-located-r3star-boundary
    false false false true true true true false false
