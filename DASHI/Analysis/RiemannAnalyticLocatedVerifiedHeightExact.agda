module DASHI.Analysis.RiemannAnalyticLocatedVerifiedHeightExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE LOCATED LOW/HIGH SPLIT ON THE ACTUAL ANALYTIC ORDINATE
--
-- Exact decidability of x <= T for constructive reals is the wrong primitive.
-- The repository already owns the stronger constructive pattern needed here:
-- strict-order cotransitivity on a constructive complete ordered field.
--
-- Choose two rational coordinates
--
--   T_high < T_PT.
--
-- Then for every ordinate magnitude y,
--
--   T_high < y  ⊎  y < T_PT.
--
-- The right branch lies strictly inside the published verified height; the left
-- branch is the high regime supplied to the uniform high contradiction
-- producer.  The regimes may overlap.  This is deliberate and removes any need
-- to decide equality at the published threshold.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannAnalyticCoordinateTerminalRefinementExact as Coordinate
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.ConstructiveRealCapabilityHierarchyExact as Capability
import DASHI.Analysis.ConstructiveCompleteRealPackageExact as Package

cast : ∀ {A B : Set} → A ≡ B → A → B
cast refl x = x

record AnalyticConstructiveRealCarrierAttachment
    (analytic : Analytic.AnalyticSubstrate)
    (realPackage : Package.ConstructiveCompleteRealPackage) : Set₁ where
  field
    realCarrierIdentity :
      Analytic.ComplexAnalyticCarrier.Real
        (Analytic.AnalyticSubstrate.carrier analytic)
      ≡
      Package.packageCarrier realPackage

open AnalyticConstructiveRealCarrierAttachment public

record RationalLocatedHeightWindow
    (realPackage : Package.ConstructiveCompleteRealPackage) : Set₁ where
  private
    R = Spine.real (Package.backend realPackage)
    rationals = Package.rationals realPackage
  field
    highStartRational : Capability.Q rationals
    publishedHeightRational : Capability.Q rationals

    highStartBelowPublishedHeightRational :
      Capability._<Q_ rationals
        highStartRational
        publishedHeightRational

    encodeNatAsRational : Nat → Capability.Q rationals

    publishedHeightRationalIsPlattTrudgianHeight :
      publishedHeightRational
      ≡
      encodeNatAsRational Low.publishedVerifiedHeight

open RationalLocatedHeightWindow public

highStartReal :
  ∀ {realPackage} →
  RationalLocatedHeightWindow realPackage →
  Package.packageCarrier realPackage
highStartReal {realPackage} window =
  Capability.fromQ
    (Package.rationals realPackage)
    (highStartRational window)

publishedHeightReal :
  ∀ {realPackage} →
  RationalLocatedHeightWindow realPackage →
  Package.packageCarrier realPackage
publishedHeightReal {realPackage} window =
  Capability.fromQ
    (Package.rationals realPackage)
    (publishedHeightRational window)

highStartBelowPublishedHeight :
  ∀ {realPackage}
    (window : RationalLocatedHeightWindow realPackage) →
  Spine._<_
    (Spine.real (Package.backend realPackage))
    (highStartReal window)
    (publishedHeightReal window)
highStartBelowPublishedHeight {realPackage} window =
  Capability.rationalLtPreserved
    (Package.rationals realPackage)
    (highStartBelowPublishedHeightRational window)

analyticOrdinateMagnitude :
  ∀ {analytic realPackage} →
  AnalyticConstructiveRealCarrierAttachment analytic realPackage →
  Universal.AnalyticNontrivialZero analytic →
  Package.packageCarrier realPackage
analyticOrdinateMagnitude {analytic} {realPackage} attachment rho =
  Spine.abs
    (Spine.real (Package.backend realPackage))
    (cast
      (realCarrierIdentity attachment)
      (Analytic.ComplexAnalyticCarrier.imaginaryPart
        (Analytic.AnalyticSubstrate.carrier analytic)
        (Universal.point rho)))

LocatedVerifiedRegion :
  ∀ {analytic realPackage} →
  AnalyticConstructiveRealCarrierAttachment analytic realPackage →
  RationalLocatedHeightWindow realPackage →
  Universal.AnalyticNontrivialZero analytic →
  Set
LocatedVerifiedRegion {realPackage = realPackage} attachment window rho =
  Spine._<_
    (Spine.real (Package.backend realPackage))
    (analyticOrdinateMagnitude attachment rho)
    (publishedHeightReal window)

LocatedHighRegion :
  ∀ {analytic realPackage} →
  AnalyticConstructiveRealCarrierAttachment analytic realPackage →
  RationalLocatedHeightWindow realPackage →
  Universal.AnalyticNontrivialZero analytic →
  Set
LocatedHighRegion {realPackage = realPackage} attachment window rho =
  Spine._<_
    (Spine.real (Package.backend realPackage))
    (highStartReal window)
    (analyticOrdinateMagnitude attachment rho)

locatedHighOrVerified :
  ∀ {analytic realPackage}
    (attachment : AnalyticConstructiveRealCarrierAttachment analytic realPackage)
    (window : RationalLocatedHeightWindow realPackage)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  LocatedHighRegion attachment window rho
    ⊎ LocatedVerifiedRegion attachment window rho
locatedHighOrVerified {realPackage = realPackage} attachment window rho =
  Capability.ltCotransitive
    (Package.constructiveField realPackage)
    (highStartBelowPublishedHeight window)
    (analyticOrdinateMagnitude attachment rho)

locatedVerifiedOrHigh :
  ∀ {analytic realPackage}
    (attachment : AnalyticConstructiveRealCarrierAttachment analytic realPackage)
    (window : RationalLocatedHeightWindow realPackage)
    (rho : Universal.AnalyticNontrivialZero analytic) →
  LocatedVerifiedRegion attachment window rho
    ⊎ LocatedHighRegion attachment window rho
locatedVerifiedOrHigh attachment window rho
  with locatedHighOrVerified attachment window rho
... | inj₁ high = inj₂ high
... | inj₂ low = inj₁ low

record LocatedAnalyticCoordinateRealization
    (analytic : Analytic.AnalyticSubstrate) : Set₂ where
  field
    realPackage : Package.ConstructiveCompleteRealPackage

    carrierAttachment :
      AnalyticConstructiveRealCarrierAttachment analytic realPackage

    heightWindow :
      RationalLocatedHeightWindow realPackage

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
      LocatedVerifiedRegion carrierAttachment heightWindow rho →
      Analytic.ComplexAnalyticCarrier.realPart
        (Analytic.AnalyticSubstrate.carrier analytic)
        (Universal.point rho)
      ≡ half

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
      LocatedVerifiedRegion
        (carrierAttachment realization)
        (heightWindow realization)
  ; Coordinate.publishedVerifiedHeightHasHalfRealPart =
      publishedLocatedRegionHasHalfRealPart realization
  ; Coordinate.sourceReference =
      "Platt--Trudgian verified-height theorem realized on a constructive ordered-real ordinate with an interior strict low region"
  ; Coordinate.refinementReference =
      "RiemannAnalyticLocatedVerifiedHeightExact"
  }

compileCanonicalLowTransport :
  ∀ {analytic} →
  LocatedAnalyticCoordinateRealization analytic →
  Low.PlattTrudgianVerifiedRegionTransport analytic
compileCanonicalLowTransport realization =
  Coordinate.compilePlattTrudgianVerifiedRegionTransport
    (compileCoordinateTerminalRefinement realization)

record LocatedVerifiedHeightBoundary : Set where
  constructor located-verified-height-boundary
  field
    exactRealThresholdDecidabilityRequired : Bool
    strictOrderCotransitivityConstructsCover : Bool
    lowAndHighMayOverlap : Bool
    publishedThresholdIsRationallyRepresented : Bool
    analyticRealCarrierMustBeSameObjectAsConstructiveReal : Bool
    publishedLowCriticalityStillRequiresSourceTransport : Bool
    rhDerivedHere : Bool

open LocatedVerifiedHeightBoundary public

canonicalLocatedVerifiedHeightBoundary : LocatedVerifiedHeightBoundary
canonicalLocatedVerifiedHeightBoundary =
  located-verified-height-boundary
    false true true true true true false
