module DASHI.Analysis.RiemannG2ClayTerminalR3StarExact where

------------------------------------------------------------------------
-- THREE-PROGRAM TERMINAL SURFACE
--
-- R1 + R2 compile below this module to an implementation-neutral uniform high
-- contradiction producer.  R3★ owns the entire terminal low/coordinate side,
-- including decidability of its exact verified-region predicate.  Therefore the
-- old arbitrary R4 cover disappears from this canonical public surface.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAnalyticCoordinateVerifiedRegionRealizationExact as R3Star
import DASHI.Analysis.RiemannG2UniformHighContradictionExact as High
import DASHI.Analysis.RiemannG2VerifiedRegionComplementHighCoverExact as Complement
import DASHI.Analysis.RiemannG2ClayTerminalGenericHighCoordinateExact as GenericClay

record ClayTerminalR3StarInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    r3Star :
      R3Star.AnalyticCoordinateVerifiedRegionRealization analytic

    highProducer :
      High.UniformHighContradictionProducer
        analytic
        (R3Star.VerifiedRegionComplementHigh r3Star)

    terminalReference : String

open ClayTerminalR3StarInput public

compileR3StarToComplementHighClay :
  ∀ {analytic} →
  ClayTerminalR3StarInput analytic →
  Complement.ComplementHighCoordinateClayInput analytic
compileR3StarToComplementHighClay input = record
  { Complement.coordinate =
      R3Star.coordinate (r3Star input)
  ; Complement.verifiedRegionDecidable =
      R3Star.compileDecidablePublishedVerifiedRegion (r3Star input)
  ; Complement.highProducer =
      highProducer input
  ; Complement.terminalReference =
      terminalReference input
  }

compileR3StarToGenericClay :
  ∀ {analytic} →
  ClayTerminalR3StarInput analytic →
  GenericClay.GenericHighCoordinateClayInput analytic
compileR3StarToGenericClay input =
  Complement.compileComplementHighCoordinateClayInput
    (compileR3StarToComplementHighClay input)

compileClayTerminalR3StarToRH :
  ∀ {analytic} →
  ClayTerminalR3StarInput analytic →
  Analytic.RiemannHypothesisFor analytic
compileClayTerminalR3StarToRH input =
  Complement.compileComplementHighCoordinateClayToRH
    (compileR3StarToComplementHighClay input)

record ClayTerminalR3StarBoundary : Set where
  constructor clay-terminal-r3star-boundary
  field
    arbitraryHighRegionPrimitiveAtCanonicalTerminalSurface : Bool
    arbitraryVerifiedOrHighCoverPrimitiveAtCanonicalTerminalSurface : Bool
    r4PrimeAbsorbedIntoR3Star : Bool
    implementationNeutralHighProducerStillRequired : Bool
    directR1R2MayCompileBelowHighProducerInterface : Bool
    r3StarStillRequiresActualCarrierRealization : Bool
    theseInputsCompileRH : Bool
    inputsInhabitedHere : Bool
    rhDerivedHere : Bool

open ClayTerminalR3StarBoundary public

canonicalClayTerminalR3StarBoundary : ClayTerminalR3StarBoundary
canonicalClayTerminalR3StarBoundary =
  clay-terminal-r3star-boundary
    false false true true true true true false false
