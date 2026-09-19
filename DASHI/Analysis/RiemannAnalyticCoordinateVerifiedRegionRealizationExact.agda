module DASHI.Analysis.RiemannAnalyticCoordinateVerifiedRegionRealizationExact where

------------------------------------------------------------------------
-- R3★ = SAME-CARRIER COORDINATE + VERIFIED-REGION REALIZATION
--
-- The terminal low-side debt is best exposed as one package rather than a
-- coordinate record plus a logically unrelated R4 cover:
--
--   * criticalLine(s) <-> realPart(s) = half,
--   * stability of equality to half,
--   * the exact published verified-region predicate on the same zero carrier,
--   * verified region -> realPart(point rho) = half,
--   * decidability of that same verified-region predicate.
--
-- The last field is deliberately an input.  AnalyticSubstrate.Real currently
-- carries no order/comparison structure, so no numeric-height decision theorem
-- can be manufactured from the abstract carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Nullary using (Dec)
open import Data.Sum using (_⊎_)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate
import DASHI.Analysis.RiemannG2VerifiedRegionComplementHighCoverExact as Complement

record AnalyticCoordinateVerifiedRegionRealization
    (analytic : Analytic.AnalyticSubstrate) : Set₁ where
  field
    coordinate :
      Coordinate.AnalyticCoordinateTerminalRefinement analytic

    decideWithinPublishedVerifiedHeight :
      (rho : Universal.AnalyticNontrivialZero analytic) →
      Dec (Coordinate.WithinPublishedVerifiedHeight coordinate rho)

open AnalyticCoordinateVerifiedRegionRealization public

compileDecidablePublishedVerifiedRegion :
  ∀ {analytic} →
  (realization : AnalyticCoordinateVerifiedRegionRealization analytic) →
  Complement.DecidablePublishedVerifiedRegion (coordinate realization)
compileDecidablePublishedVerifiedRegion realization = record
  { Complement.decidePublishedVerifiedRegion =
      decideWithinPublishedVerifiedHeight realization
  }

VerifiedRegionComplementHigh :
  ∀ {analytic} →
  AnalyticCoordinateVerifiedRegionRealization analytic →
  Universal.AnalyticNontrivialZero analytic →
  Set
VerifiedRegionComplementHigh realization =
  Complement.VerifiedRegionComplementHigh (coordinate realization)

verifiedOrComplementHighCover :
  ∀ {analytic}
    (realization : AnalyticCoordinateVerifiedRegionRealization analytic)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  Coordinate.WithinPublishedVerifiedHeight
      (coordinate realization) rho
    ⊎ VerifiedRegionComplementHigh realization rho
verifiedOrComplementHighCover realization =
  Complement.verifiedOrComplementHighCover
    (coordinate realization)
    (compileDecidablePublishedVerifiedRegion realization)

record AnalyticCoordinateVerifiedRegionRealizationBoundary : Set where
  constructor analytic-coordinate-verified-region-realization-boundary
  field
    coordinateAndVerifiedRegionDecisionShareOnePackage : Bool
    complementCoverCompilesFromR3Star : Bool
    standaloneArbitraryR4CoverRequiredOnCanonicalRoute : Bool
    abstractAnalyticRealAlreadyProvidesDecidableOrder : Bool
    numericHeightCarrierRealizationStillRequired : Bool
    r3StarInhabitedHere : Bool
    rhDerived : Bool

open AnalyticCoordinateVerifiedRegionRealizationBoundary public

canonicalAnalyticCoordinateVerifiedRegionRealizationBoundary :
  AnalyticCoordinateVerifiedRegionRealizationBoundary
canonicalAnalyticCoordinateVerifiedRegionRealizationBoundary =
  analytic-coordinate-verified-region-realization-boundary
    true true false false true false false
