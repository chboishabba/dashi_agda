{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119SingleSourceVacuumKottlerRouteExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _<_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravityLocalizedVacuumReadoutExact as Readout
import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTSingleVacuumIsraelKottlerExact as Geometry

------------------------------------------------------------------------
-- SINGLE-SOURCE VACUUM / KOTTLER CANDIDATE ROUTE
--
-- sourceAmplitude is the corrected constant/remainder coordinate of the
-- selected vacuum-sector LocalizedAction.  The geometry below is exact algebra
-- on that scalar, but remains a candidate until the published vacuum-constant
-- encoding and normalization-to-gravity metric-response receipts are supplied.
------------------------------------------------------------------------

record SingleSourceVacuum
    {Density Background Fluctuation : Set}
    (source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction) : Set₁ where
  constructor single-source-vacuum
  field scale : Nat
  sourceAmplitude : ℚ
  sourceAmplitude = Readout.localizedVacuumValue source scale
open SingleSourceVacuum public

singleSourceVacuumStress :
  ∀ {Density Background Fluctuation}
    {source : Source.CMP119Section2SourceNativeState
      Density Background Fluctuation
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
      T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction} →
  SingleSourceVacuum source → Stress.RationalTensor4
singleSourceVacuumStress selected = Vacuum.vacuumStressAt (sourceAmplitude selected)

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
    sourceAmplitudeMatchesInteriorScaledGeometry :
      (sourceAmplitude selected * radius * radius)
      ≡ Geometry.three * (1ℚ - interiorLapseRoot * interiorLapseRoot)
    positiveMetricMass :
      0ℚ < Geometry.sameVacuumMass radius interiorLapseRoot exteriorLapseRoot
    outwardExteriorAcceleration :
      0ℚ < Geometry.sameVacuumOutwardScaled radius interiorLapseRoot exteriorLapseRoot
    necDecCompatible :
      0ℚ < Geometry.sameVacuumNECDECMargin radius interiorLapseRoot exteriorLapseRoot
    secViolated :
      0ℚ < Geometry.sameVacuumSECViolationMargin radius interiorLapseRoot exteriorLapseRoot

  sameSourceAmplitudeFeedsInteriorExterior :
    (sourceAmplitude selected * radius * radius) * radius
    ≡ Geometry.sameVacuumExteriorScaledAmplitude radius interiorLapseRoot exteriorLapseRoot
  sameSourceAmplitudeFeedsInteriorExterior
    rewrite sourceAmplitudeMatchesInteriorScaledGeometry
          | Geometry.sameScaledAmplitudeOnBothSides radius interiorLapseRoot exteriorLapseRoot =
    solve (radius ∷ interiorLapseRoot ∷ [])

record SingleSourceVacuumKottlerBoundary : Set where
  constructor single-source-vacuum-kottler-boundary
  field
    constantRemainderCoordinateUsed : Bool
    plaquetteProjectorUsedAsVacuumConstant : Bool
    publishedVacuumConstantEncodingRequired : Bool
    oneLiteralSourceScaleFeedsBothVacuumRegions : Bool
    sameVacuumStressRayUsedOnBothSides : Bool
    denominatorClearedSameAmplitudeIdentityConstructed : Bool
    secondSourceVacuumScaleRequired : Bool
    exactFixtureAmplitudeRequired : Bool
    oneScaleGeometricAdmissibilityStillRequired : Bool
    actionReadoutAloneProvesPhysicalCosmologicalAmplitude : Bool
    physicalMetricAmplitudeWeldStillRequired : Bool

canonicalSingleSourceVacuumKottlerBoundary : SingleSourceVacuumKottlerBoundary
canonicalSingleSourceVacuumKottlerBoundary =
  single-source-vacuum-kottler-boundary
    true false true true true true false false true false true

literalSourceVacuumReadoutUsed : Bool
literalSourceVacuumReadoutUsed = false

formalConstantCoordinateReadoutUsed : Bool
formalConstantCoordinateReadoutUsed = true

publishedVacuumConstantEncodingRequired : Bool
publishedVacuumConstantEncodingRequired =
  Readout.publishedVacuumConstantEncodingStillRequired
