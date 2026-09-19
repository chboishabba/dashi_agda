module DASHI.Analysis.RiemannG2ClayTerminalLocatedR3StarExact where

------------------------------------------------------------------------
-- PREFERRED CONSTRUCTIVE THREE-PROGRAM TERMINAL SURFACE
--
-- This replaces exact Dec(V) by a located overlapping partition:
--
--   T_high < |Im rho|   ⊎   |Im rho| < T_PT.
--
-- The right branch is the published low theorem.  The left branch is the high
-- input for R1+R2.  No equality-at-threshold decision is required.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAnalyticLocatedVerifiedHeightExact as Located
import DASHI.Analysis.RiemannG2UniformHighContradictionExact as High
import DASHI.Analysis.RiemannG2ClayTerminalGenericHighCoordinateExact as Generic

record ClayTerminalLocatedR3StarInput
    (analytic : Analytic.AnalyticSubstrate) : Set₂ where
  field
    r3Star :
      Located.LocatedAnalyticCoordinateRealization analytic

    highProducer :
      High.UniformHighContradictionProducer
        analytic
        (Located.LocatedHighRegion
          (Located.carrierAttachment r3Star)
          (Located.heightWindow r3Star))

    terminalReference : String

open ClayTerminalLocatedR3StarInput public

compileLocatedR3StarToGenericClay :
  ∀ {analytic} →
  ClayTerminalLocatedR3StarInput analytic →
  Generic.GenericHighCoordinateClayInput analytic
compileLocatedR3StarToGenericClay input = record
  { Generic.coordinate =
      Located.compileCoordinateTerminalRefinement (r3Star input)
  ; Generic.HighRegion =
      Located.LocatedHighRegion
        (Located.carrierAttachment (r3Star input))
        (Located.heightWindow (r3Star input))
  ; Generic.verifiedOrHighCover =
      Located.locatedVerifiedOrHigh
        (Located.carrierAttachment (r3Star input))
        (Located.heightWindow (r3Star input))
  ; Generic.highProducer =
      highProducer input
  ; Generic.terminalReference =
      terminalReference input
  }

compileClayTerminalLocatedR3StarToRH :
  ∀ {analytic} →
  ClayTerminalLocatedR3StarInput analytic →
  Analytic.RiemannHypothesisFor analytic
compileClayTerminalLocatedR3StarToRH input =
  Generic.compileGenericHighCoordinateClayToRH
    (compileLocatedR3StarToGenericClay input)

record ClayTerminalLocatedR3StarBoundary : Set where
  constructor clay-terminal-located-r3star-boundary
  field
    exactVerifiedRegionDecisionPrimitive : Bool
    arbitraryCoverPrimitive : Bool
    locatedOverlappingSplitUsed : Bool
    strictThresholdSeparationSufficesForCover : Bool
    highProducerReceivesConcreteOrdinateLowerRegion : Bool
    publishedLowTheoremStillRequired : Bool
    theseInputsCompileRH : Bool
    inputsInhabitedHere : Bool
    rhDerivedHere : Bool

open ClayTerminalLocatedR3StarBoundary public

canonicalClayTerminalLocatedR3StarBoundary :
  ClayTerminalLocatedR3StarBoundary
canonicalClayTerminalLocatedR3StarBoundary =
  clay-terminal-located-r3star-boundary
    false false true true true true true false false
