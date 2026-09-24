module DASHI.Analysis.RiemannG2VerifiedRegionComplementHighCoverExact where

------------------------------------------------------------------------
-- R4 AS DECIDABLE VERIFIED-REGION COMPLEMENT
--
-- The generic Clay wrapper accepts an arbitrary High predicate together with
--
--   verifiedRegion rho ⊎ High rho.
--
-- For the least-privilege canonical partition, choose High definitionally as
-- the complement of the exact verified-region predicate.  Then R4 is no longer
-- an unrelated cover theorem: it compiles from a decision procedure for that
-- same theorem-facing low predicate.
--
-- This does not manufacture the decision procedure.  In particular, source
-- metadata or a numerical height literal does not decide a predicate on an
-- abstract analytic carrier.  The exact numeric/carrier interpretation remains
-- a substantive input.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate
import DASHI.Analysis.RiemannG2UniformHighContradictionExact as High
import DASHI.Analysis.RiemannG2ClayTerminalGenericHighCoordinateExact as Clay
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative

VerifiedRegionComplementHigh :
  ∀ {analytic} →
  Coordinate.AnalyticCoordinateTerminalRefinement analytic →
  Universal.AnalyticNontrivialZero analytic →
  Set
VerifiedRegionComplementHigh coordinate rho =
  Coordinate.WithinPublishedVerifiedHeight coordinate rho → ⊥

record DecidablePublishedVerifiedRegion
    {analytic : Analytic.AnalyticSubstrate}
    (coordinate : Coordinate.AnalyticCoordinateTerminalRefinement analytic)
    : Set₁ where
  field
    decidePublishedVerifiedRegion :
      (rho : Universal.AnalyticNontrivialZero analytic) →
      Dec (Coordinate.WithinPublishedVerifiedHeight coordinate rho)

open DecidablePublishedVerifiedRegion public

verifiedOrComplementHighCover :
  ∀ {analytic}
    (coordinate : Coordinate.AnalyticCoordinateTerminalRefinement analytic) →
  DecidablePublishedVerifiedRegion coordinate →
  (rho : Universal.AnalyticNontrivialZero analytic) →
  Coordinate.WithinPublishedVerifiedHeight coordinate rho
    ⊎ VerifiedRegionComplementHigh coordinate rho
verifiedOrComplementHighCover coordinate decidable rho
  with decidePublishedVerifiedRegion decidable rho
... | yes within = inj₁ within
... | no outside = inj₂ outside

record ComplementHighCoordinateClayInput
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    coordinate :
      Coordinate.AnalyticCoordinateTerminalRefinement analytic

    verifiedRegionDecidable :
      DecidablePublishedVerifiedRegion coordinate

    highProducer :
      High.UniformHighContradictionProducer
        analytic
        (VerifiedRegionComplementHigh coordinate)

    terminalReference : String

open ComplementHighCoordinateClayInput public

compileComplementHighCoordinateClayInput :
  ∀ {analytic} →
  ComplementHighCoordinateClayInput analytic →
  Clay.GenericHighCoordinateClayInput analytic
compileComplementHighCoordinateClayInput input = record
  { Clay.coordinate = coordinate input
  ; Clay.HighRegion =
      VerifiedRegionComplementHigh (coordinate input)
  ; Clay.verifiedOrHighCover =
      verifiedOrComplementHighCover
        (coordinate input)
        (verifiedRegionDecidable input)
  ; Clay.highProducer = highProducer input
  ; Clay.terminalReference = terminalReference input
  }

compiledComplementHighDoubleNegatedRH :
  ∀ {analytic} →
  ComplementHighCoordinateClayInput analytic →
  Negative.DoubleNegatedRiemannHypothesisFor analytic
compiledComplementHighDoubleNegatedRH input =
  Clay.compiledDoubleNegatedRH
    (compileComplementHighCoordinateClayInput input)

compileComplementHighCoordinateClayToRH :
  ∀ {analytic} →
  ComplementHighCoordinateClayInput analytic →
  Analytic.RiemannHypothesisFor analytic
compileComplementHighCoordinateClayToRH input =
  Clay.compileGenericHighCoordinateClayToRH
    (compileComplementHighCoordinateClayInput input)

record VerifiedRegionComplementHighBoundary : Set where
  constructor verified-region-complement-high-boundary
  field
    canonicalHighMayBeChosenAsVerifiedRegionComplement : Bool
    coverCompilesFromVerifiedRegionDecidability : Bool
    separateArbitraryCoverTheoremRequiredOnComplementRoute : Bool
    numericCarrierInterpretationAutomaticallyDecidable : Bool
    uniformHighContradictionStillRequired : Bool
    rhDerivedHere : Bool

open VerifiedRegionComplementHighBoundary public

canonicalVerifiedRegionComplementHighBoundary :
  VerifiedRegionComplementHighBoundary
canonicalVerifiedRegionComplementHighBoundary =
  verified-region-complement-high-boundary
    true true false false true false
