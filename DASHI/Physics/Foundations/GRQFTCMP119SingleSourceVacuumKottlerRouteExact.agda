{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119SingleSourceVacuumKottlerRouteExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.GRQFTCMP119NambuBuriedVacuumReadoutExact as Readout
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTSingleVacuumIsraelKottlerExact as Geometry
import DASHI.Physics.Foundations.GRQFTRationalSquareIsraelDesignExact as Design

record SingleSourceVacuum
    {Density Background Fluctuation : Set}
    (source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction) : Set₁ where
  constructor single-source-vacuum
  field
    scale : Nat

  sourceAmplitude : ℚ
  sourceAmplitude = Readout.sourceVacuumAmplitudeAt source scale

open SingleSourceVacuum public

singleSourceVacuumStress :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction} →
  SingleSourceVacuum source → Stress.RationalTensor4
singleSourceVacuumStress selected =
  Vacuum.vacuumStressAt (sourceAmplitude selected)

record SingleSourceVacuumKottlerCandidate
    {Density Background Fluctuation : Set}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction}
    (selected : SingleSourceVacuum source) : Set₁ where
  constructor single-source-vacuum-kottler-candidate
  field
    radius interiorLapseRoot exteriorLapseRoot : ℚ

    positiveRadius : 0ℚ < radius
    positiveInteriorLapseRoot : 0ℚ < interiorLapseRoot
    positiveExteriorLapseRoot : 0ℚ < exteriorLapseRoot

    sourceAmplitudeMatchesInteriorGeometry :
      sourceAmplitude selected
      ≡ Geometry.sameVacuumAmplitude radius interiorLapseRoot

    positiveMetricMass :
      0ℚ < Geometry.sameVacuumMass
        radius interiorLapseRoot exteriorLapseRoot

    outwardExteriorAcceleration :
      0ℚ < Geometry.sameVacuumOutwardScaled
        radius interiorLapseRoot exteriorLapseRoot

    necDecCompatible :
      0ℚ < Geometry.sameVacuumNECDECMargin
        radius interiorLapseRoot exteriorLapseRoot

    secViolated :
      0ℚ < Geometry.sameVacuumSECViolationMargin
        radius interiorLapseRoot exteriorLapseRoot

  sameSourceAmplitudeFeedsInteriorExterior :
    Design.lambdaOutFromSquareLapse
      (Geometry.sameVacuumMass radius interiorLapseRoot exteriorLapseRoot)
      radius exteriorLapseRoot
    ≡ sourceAmplitude selected
  sameSourceAmplitudeFeedsInteriorExterior =
    let open SingleSourceVacuumKottlerCandidate in
    Agda.Builtin.Equality.trans
      Geometry.fixtureExteriorLambdaIsSame
      (Agda.Builtin.Equality.sym sourceAmplitudeMatchesInteriorGeometry)

record SingleSourceVacuumKottlerBoundary : Set where
  constructor single-source-vacuum-kottler-boundary
  field
    literalSourceVacuumReadoutUsed : Bool
    oneLiteralSourceScaleFeedsBothVacuumRegions : Bool
    sameVacuumStressRayUsedOnBothSides : Bool
    secondSourceVacuumScaleRequired : Bool
    exactFixtureAmplitudeRequired : Bool
    oneScaleGeometricAdmissibilityStillRequired : Bool

canonicalSingleSourceVacuumKottlerBoundary :
  SingleSourceVacuumKottlerBoundary
canonicalSingleSourceVacuumKottlerBoundary =
  single-source-vacuum-kottler-boundary
    true true true false false true
