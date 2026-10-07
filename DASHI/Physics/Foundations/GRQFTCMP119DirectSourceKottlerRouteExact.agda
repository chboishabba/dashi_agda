{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119DirectSourceKottlerRouteExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_; _*_; _+_; _-_)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.GRQFTCMP119NambuBuriedVacuumReadoutExact as Readout
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTSourceAmplitudeDrivenIsraelKottlerExact as Geometry

------------------------------------------------------------------------
-- DIRECT SOURCE VACUUM -> COSMOLOGICAL STRESS -> KOTTLER ROUTE
--
-- This is the shortest static geometry route discovered by archaeology.
-- It does NOT require the independently useful R136/pinned-stress route.
--
-- The literal Section-2 source, specialized to the already-used LocalizedAction
-- realization, owns a vacuum term at every scale.  The existing projector gives
-- its rational amplitude.  The normalized cosmological stress shape is then
-- simply the existing vacuumStressAt amplitude.  Geometry consumes those same
-- literal amplitudes through the source-driven Israel/Kottler inversion.
------------------------------------------------------------------------

record SourceAmplitudePair
    {Density Background Fluctuation : Set}
    (source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction) : Set where
  constructor source-amplitude-pair
  field
    interiorScale exteriorScale : Nat

  interiorAmplitude : ℚ
  interiorAmplitude = Readout.sourceVacuumAmplitudeAt source interiorScale

  exteriorAmplitude : ℚ
  exteriorAmplitude = Readout.sourceVacuumAmplitudeAt source exteriorScale

open SourceAmplitudePair public

sourceAmplitudePair :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction} →
  Nat → Nat → SourceAmplitudePair source
sourceAmplitudePair interior exterior =
  source-amplitude-pair interior exterior

sourceInteriorVacuumStress :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction} →
  SourceAmplitudePair source → Stress.RationalTensor4
sourceInteriorVacuumStress pair =
  Vacuum.vacuumStressAt (interiorAmplitude pair)

sourceExteriorVacuumStress :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction} →
  SourceAmplitudePair source → Stress.RationalTensor4
sourceExteriorVacuumStress pair =
  Vacuum.vacuumStressAt (exteriorAmplitude pair)

sourceInteriorStressUsesLiteralVacuumAmplitude :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction}
    (pair : SourceAmplitudePair source) →
  sourceInteriorVacuumStress pair
    ≡ Vacuum.vacuumStressAt
        (Readout.sourceVacuumAmplitudeAt source (interiorScale pair))
sourceInteriorStressUsesLiteralVacuumAmplitude pair = refl

sourceExteriorStressUsesLiteralVacuumAmplitude :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction}
    (pair : SourceAmplitudePair source) →
  sourceExteriorVacuumStress pair
    ≡ Vacuum.vacuumStressAt
        (Readout.sourceVacuumAmplitudeAt source (exteriorScale pair))
sourceExteriorStressUsesLiteralVacuumAmplitude pair = refl

sourceDrivenMass :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction} →
  SourceAmplitudePair source → ℚ → ℚ → ℚ
sourceDrivenMass pair radius exteriorLapseRoot =
  Geometry.sourceExteriorMass radius exteriorLapseRoot
    (exteriorAmplitude pair)

record DirectSourceKottlerAdmissibility
    {Density Background Fluctuation : Set}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction}
    (pair : SourceAmplitudePair source) : Set where
  constructor direct-source-kottler-admissibility
  field
    radius interiorLapseRoot exteriorLapseRoot : ℚ

    positiveRadius : 0ℚ < radius
    positiveInteriorLapseRoot : 0ℚ < interiorLapseRoot
    positiveExteriorLapseRoot : 0ℚ < exteriorLapseRoot

    interiorAmplitudeMatchesRoot :
      Geometry.sourceInteriorRootResidual
        radius interiorLapseRoot (interiorAmplitude pair)
      ≡ 0ℚ

    positiveMass :
      0ℚ < sourceDrivenMass pair radius exteriorLapseRoot

    outwardExteriorMargin :
      0ℚ <
        Geometry.sourceDrivenOutwardMarginIdentity
          radius exteriorLapseRoot
          (Geometry.sourceExteriorScaledAmplitude
            radius (exteriorAmplitude pair))
          |>Margin

    positiveNECDECMargin :
      0ℚ < Geometry.sourceDrivenNECDECMargin
        radius interiorLapseRoot exteriorLapseRoot
        (Geometry.sourceExteriorScaledAmplitude
          radius (exteriorAmplitude pair))

-- Agda has no pipeline operator here; expose the actual margin separately and
-- use it in a second, compiler-friendly admissibility surface below.
sourceOutwardMargin :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction} →
  SourceAmplitudePair source → ℚ → ℚ → ℚ
sourceOutwardMargin pair radius y =
  let scaled = Geometry.sourceExteriorScaledAmplitude radius (exteriorAmplitude pair)
  in
  scaled -
    (Geometry.three * sourceDrivenMass pair radius y)

record DirectSourceKottlerCandidate
    {Density Background Fluctuation : Set}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction}
    (pair : SourceAmplitudePair source) : Set where
  constructor direct-source-kottler-candidate
  field
    radius interiorLapseRoot exteriorLapseRoot : ℚ
    positiveRadius : 0ℚ < radius
    positiveInteriorLapseRoot : 0ℚ < interiorLapseRoot
    positiveExteriorLapseRoot : 0ℚ < exteriorLapseRoot
    interiorAmplitudeMatchesRoot :
      Geometry.sourceInteriorRootResidual
        radius interiorLapseRoot (interiorAmplitude pair) ≡ 0ℚ
    positiveMass : 0ℚ < sourceDrivenMass pair radius exteriorLapseRoot
    outward : 0ℚ < sourceOutwardMargin pair radius exteriorLapseRoot
    necDecCompatible :
      0ℚ < Geometry.sourceDrivenNECDECMargin
        radius interiorLapseRoot exteriorLapseRoot
        (Geometry.sourceExteriorScaledAmplitude radius (exteriorAmplitude pair))

record DirectSourceKottlerBoundary : Set where
  constructor direct-source-kottler-boundary
  field
    literalVacuumAmplitudeReadoutUsed : Bool
    sourceVacuumStressConstructedDirectly : Bool
    sameLiteralAmplitudesFeedGeometry : Bool
    exactFixtureFractionsRequired : Bool
    pinnedR136NotRequiredForStaticGeometryConstruction : Bool
    pinnedR136StillUsefulAsIndependentStressCrossCheck : Bool
    physicalSourceAdmissibilityStillRequired : Bool

canonicalDirectSourceKottlerBoundary : DirectSourceKottlerBoundary
canonicalDirectSourceKottlerBoundary =
  direct-source-kottler-boundary true true true false true true true
