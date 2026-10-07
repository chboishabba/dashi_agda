{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119DirectSourceKottlerRouteExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.GRQFTCMP119NambuBuriedVacuumReadoutExact as Readout
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTSourceAmplitudeDrivenIsraelKottlerExact as Geometry
import DASHI.Physics.Foundations.GRQFTKottlerRepulsionParameterWindowExact as Window

------------------------------------------------------------------------
-- DIRECT SOURCE VACUUM -> COSMOLOGICAL STRESS -> KOTTLER ROUTE
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

sourceOutwardMargin :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction} →
  SourceAmplitudePair source → ℚ → ℚ → ℚ
sourceOutwardMargin pair radius y =
  Window.outwardAccelerationMargin
    (sourceDrivenMass pair radius y)
    (Geometry.sourceExteriorScaledAmplitude radius (exteriorAmplitude pair))

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
