module DASHI.Analysis.RiemannAnalyticLocatedLowCriticalityCompilerExact where

------------------------------------------------------------------------
-- PUBLISHED LOW CRITICALITY + COORDINATE CORE -> LOCATED R3★ REALIZATION
--
-- Keep source authority and coordinate representation separate:
--
--   source theorem: located verified zero -> analytic critical-line truth
--   coordinate theorem: critical-line truth -> realPart = half
--
-- Their composition supplies the half-real theorem consumed by the existing
-- terminal coordinate record.  The source layer is therefore not required to
-- speak in DASHI's chosen real-coordinate equality directly.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁; Set₂)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannLocatedHeightCarrierExact as Height
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located

record LocatedCriticalCoordinateCore
    (analytic : Analytic.AnalyticSubstrate)
    (heightCarrier : Height.LocatedHeightCarrier)
    (attachment :
      Located.AnalyticLocatedHeightCarrierAttachment analytic heightCarrier)
    : Set₁ where
  field
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

open LocatedCriticalCoordinateCore public

record PublishedLocatedLowCriticality
    {analytic : Analytic.AnalyticSubstrate}
    {heightCarrier : Height.LocatedHeightCarrier}
    (attachment :
      Located.AnalyticLocatedHeightCarrierAttachment analytic heightCarrier)
    : Set₁ where
  field
    verifiedLocatedZeroCritical :
      (rho : Universal.AnalyticNontrivialZero analytic) →
      Located.LocatedVerifiedRegion attachment rho →
      Universal.analyticCritical rho

    sourceReference : String
    sameSubstrateReference : String

open PublishedLocatedLowCriticality public

compileLocatedAnalyticCoordinateRealization :
  ∀ {analytic heightCarrier}
    {attachment :
      Located.AnalyticLocatedHeightCarrierAttachment analytic heightCarrier} →
  LocatedCriticalCoordinateCore analytic heightCarrier attachment →
  PublishedLocatedLowCriticality attachment →
  Located.LocatedAnalyticCoordinateRealization analytic
compileLocatedAnalyticCoordinateRealization
    {heightCarrier = heightCarrier}
    {attachment = attachment}
    coordinate low = record
  { Located.heightCarrier = heightCarrier
  ; Located.carrierAttachment = attachment
  ; Located.half = half coordinate
  ; Located.criticalLineImpliesHalf =
      criticalLineImpliesHalf coordinate
  ; Located.halfImpliesCriticalLine =
      halfImpliesCriticalLine coordinate
  ; Located.equalityToHalfStable =
      equalityToHalfStable coordinate
  ; Located.publishedLocatedRegionHasHalfRealPart =
      λ rho verified →
        criticalLineImpliesHalf coordinate
          (Universal.point rho)
          (verifiedLocatedZeroCritical low rho verified)
  ; Located.sourceReference =
      sourceReference low
  }

record LocatedLowCriticalityCompilerBoundary : Set where
  constructor located-low-criticality-compiler-boundary
  field
    sourceMustStateRealPartEqualityDirectly : Bool
    sourceMayStateSameSubstrateCriticality : Bool
    criticalityToHalfIsCoordinateCompilerWork : Bool
    sameSubstratePublishedTheoremStillRequired : Bool
    rhDerivedHere : Bool

open LocatedLowCriticalityCompilerBoundary public

canonicalLocatedLowCriticalityCompilerBoundary :
  LocatedLowCriticalityCompilerBoundary
canonicalLocatedLowCriticalityCompilerBoundary =
  located-low-criticality-compiler-boundary
    false true true true false
