module DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact where

------------------------------------------------------------------------
-- EXACT ANALYTIC-SUBSTRATE WELD TO A MINIMAL LOCATED HEIGHT CARRIER
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁; Set₂)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannLocatedHeightCarrierExact as Height
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate

cast : ∀ {A B : Set} → A ≡ B → A → B
cast refl value = value

record AnalyticLocatedHeightCarrierAttachment
    (analytic : Analytic.AnalyticSubstrate)
    (heightCarrier : Height.LocatedHeightCarrier) : Set₁ where
  field
    realCarrierIdentity :
      Analytic.ComplexAnalyticCarrier.Real
        (Analytic.AnalyticSubstrate.carrier analytic)
      ≡ Height.Carrier heightCarrier

open AnalyticLocatedHeightCarrierAttachment public

ordinateMagnitude :
  ∀ {analytic heightCarrier} →
  AnalyticLocatedHeightCarrierAttachment analytic heightCarrier →
  Universal.AnalyticNontrivialZero analytic →
  Height.Carrier heightCarrier
ordinateMagnitude {analytic} {heightCarrier} attachment rho =
  Height.abs heightCarrier
    (cast
      (realCarrierIdentity attachment)
      (Analytic.ComplexAnalyticCarrier.imaginaryPart
        (Analytic.AnalyticSubstrate.carrier analytic)
        (Universal.point rho)))

LocatedVerifiedRegion :
  ∀ {analytic heightCarrier} →
  AnalyticLocatedHeightCarrierAttachment analytic heightCarrier →
  Universal.AnalyticNontrivialZero analytic →
  Set
LocatedVerifiedRegion {heightCarrier = heightCarrier} attachment rho =
  Height._<_ heightCarrier
    (ordinateMagnitude attachment rho)
    (Height.publishedHeight heightCarrier)

LocatedHighRegion :
  ∀ {analytic heightCarrier} →
  AnalyticLocatedHeightCarrierAttachment analytic heightCarrier →
  Universal.AnalyticNontrivialZero analytic →
  Set
LocatedHighRegion {heightCarrier = heightCarrier} attachment rho =
  Height._<_ heightCarrier
    (Height.highStart heightCarrier)
    (ordinateMagnitude attachment rho)

locatedVerifiedOrHigh :
  ∀ {analytic heightCarrier}
    (attachment :
      AnalyticLocatedHeightCarrierAttachment analytic heightCarrier)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  LocatedVerifiedRegion attachment rho
    ⊎ LocatedHighRegion attachment rho
locatedVerifiedOrHigh {heightCarrier = heightCarrier} attachment rho =
  Height.locatedBetweenThresholds heightCarrier
    (ordinateMagnitude attachment rho)

record LocatedAnalyticCoordinateRealization
    (analytic : Analytic.AnalyticSubstrate) : Set₂ where
  field
    heightCarrier : Height.LocatedHeightCarrier

    carrierAttachment :
      AnalyticLocatedHeightCarrierAttachment analytic heightCarrier

    half :
      Analytic.ComplexAnalyticCarrier.Real
        (Analytic.AnalyticSubstrate.carrier analytic)

    criticalLineImpliesHalf :
      (s : Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)) →
      Analytic.CompletedRiemannZeta.criticalLine
        (Analytic.AnalyticSubstrate.completed analytic) s →
      Analytic.ComplexAnalyticCarrier.realPart
        (Analytic.AnalyticSubstrate.carrier analytic) s
      ≡ half

    halfImpliesCriticalLine :
      (s : Analytic.ComplexAnalyticCarrier.Complex
        (Analytic.AnalyticSubstrate.carrier analytic)) →
      Analytic.ComplexAnalyticCarrier.realPart
        (Analytic.AnalyticSubstrate.carrier analytic) s
      ≡ half →
      Analytic.CompletedRiemannZeta.criticalLine
        (Analytic.AnalyticSubstrate.completed analytic) s

    equalityToHalfStable :
      (r : Analytic.ComplexAnalyticCarrier.Real
        (Analytic.AnalyticSubstrate.carrier analytic)) →
      ((r ≡ half → ⊥) → ⊥) →
      r ≡ half

    publishedLocatedRegionHasHalfRealPart :
      (rho : Universal.AnalyticNontrivialZero analytic) →
      LocatedVerifiedRegion carrierAttachment rho →
      Analytic.ComplexAnalyticCarrier.realPart
        (Analytic.AnalyticSubstrate.carrier analytic)
        (Universal.point rho)
      ≡ half

    sourceReference : String

open LocatedAnalyticCoordinateRealization public

compileCoordinateTerminalRefinement :
  ∀ {analytic} →
  (realization : LocatedAnalyticCoordinateRealization analytic) →
  Coordinate.AnalyticCoordinateTerminalRefinement analytic
compileCoordinateTerminalRefinement realization = record
  { Coordinate.half = half realization
  ; Coordinate.criticalLineImpliesHalf =
      criticalLineImpliesHalf realization
  ; Coordinate.halfImpliesCriticalLine =
      halfImpliesCriticalLine realization
  ; Coordinate.equalityToHalfStable =
      equalityToHalfStable realization
  ; Coordinate.WithinPublishedVerifiedHeight =
      LocatedVerifiedRegion (carrierAttachment realization)
  ; Coordinate.publishedVerifiedHeightHasHalfRealPart =
      publishedLocatedRegionHasHalfRealPart realization
  ; Coordinate.sourceReference = sourceReference realization
  ; Coordinate.refinementReference =
      "RiemannAnalyticLocatedHeightCarrierRealizationExact"
  }

record AnalyticLocatedHeightCarrierBoundary : Set where
  constructor analytic-located-height-carrier-boundary
  field
    fullConstructiveRealPackageRequired : Bool
    realCarrierSameObjectWeldRequired : Bool
    locatedCoverCompilerOwned : Bool
    criticalCoordinateStillRequired : Bool
    publishedLowTheoremStillRequired : Bool
    rhDerivedHere : Bool

open AnalyticLocatedHeightCarrierBoundary public

canonicalAnalyticLocatedHeightCarrierBoundary :
  AnalyticLocatedHeightCarrierBoundary
canonicalAnalyticLocatedHeightCarrierBoundary =
  analytic-located-height-carrier-boundary
    false true true true true false
