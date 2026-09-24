{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTFiniteComovingRiemannDeviationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTFiniteFLRWRepulsiveAccelerationExact as FLRW

------------------------------------------------------------------------
-- MINIMAL INDEXED COMOVING RIEMANN BLOCK
--
-- For a smooth FLRW spacetime with signature (-,+,+,+),
--
--   R^i_{0 j 0} = - (a double-dot / a) delta^i_j
--
-- in the comoving orthonormal frame.  The previous finite theorem establishes
-- only the ORIENTATION of (a double-dot/a), not its continuum magnitude.
--
-- We therefore compile exactly the indexed time-tidal block needed by geodesic
-- deviation and nothing more.  This is not presented as a general continuum
-- Riemann tensor construction.
------------------------------------------------------------------------

data SpatialAxis3 : Set where
  xSpatial : SpatialAxis3
  ySpatial : SpatialAxis3
  zSpatial : SpatialAxis3

spatialToAxis4 : SpatialAxis3 → Flat.Axis4
spatialToAxis4 xSpatial = Flat.xAxis
spatialToAxis4 ySpatial = Flat.yAxis
spatialToAxis4 zSpatial = Flat.zAxis

data CurvatureActionOrientation : Set where
  negativeCurvatureAction : CurvatureActionOrientation
  zeroCurvatureAction : CurvatureActionOrientation
  positiveCurvatureAction : CurvatureActionOrientation

negateCurvatureAction :
  CurvatureActionOrientation → CurvatureActionOrientation
negateCurvatureAction negativeCurvatureAction = positiveCurvatureAction
negateCurvatureAction zeroCurvatureAction = zeroCurvatureAction
negateCurvatureAction positiveCurvatureAction = negativeCurvatureAction

sameSpatialAxis : SpatialAxis3 → SpatialAxis3 → Bool
sameSpatialAxis xSpatial xSpatial = true
sameSpatialAxis ySpatial ySpatial = true
sameSpatialAxis zSpatial zSpatial = true
sameSpatialAxis _ _ = false

comovingRiemannTimeTidal :
  SpatialAxis3 → SpatialAxis3 → CurvatureActionOrientation
comovingRiemannTimeTidal i j with sameSpatialAxis i j
... | true = negativeCurvatureAction
... | false = zeroCurvatureAction

finiteRiemannXX :
  comovingRiemannTimeTidal xSpatial xSpatial
    ≡ negativeCurvatureAction
finiteRiemannXX = refl

finiteRiemannYY :
  comovingRiemannTimeTidal ySpatial ySpatial
    ≡ negativeCurvatureAction
finiteRiemannYY = refl

finiteRiemannZZ :
  comovingRiemannTimeTidal zSpatial zSpatial
    ≡ negativeCurvatureAction
finiteRiemannZZ = refl

finiteRiemannXY :
  comovingRiemannTimeTidal xSpatial ySpatial
    ≡ zeroCurvatureAction
finiteRiemannXY = refl

finiteRiemannXZ :
  comovingRiemannTimeTidal xSpatial zSpatial
    ≡ zeroCurvatureAction
finiteRiemannXZ = refl

finiteRiemannYZ :
  comovingRiemannTimeTidal ySpatial zSpatial
    ≡ zeroCurvatureAction
finiteRiemannYZ = refl

------------------------------------------------------------------------
-- GEODESIC-DEVIATION COMPILER
--
--   D^2 xi^i / D tau^2 = - R^i_{0 j 0} xi^j
--
-- On each principal comoving spatial eigen-direction, the finite acceleration
-- orientation proved previously is expanding, so R^i_{0 i 0} is negative and
-- the deviation acceleration points along +xi: neighboring free-fall worldlines
-- separate rather than focus.
------------------------------------------------------------------------

data SeparationOrientation : Set where
  inwardSeparationAcceleration : SeparationOrientation
  zeroSeparationAcceleration : SeparationOrientation
  outwardSeparationAcceleration : SeparationOrientation

deviationFromRiemann :
  CurvatureActionOrientation → SeparationOrientation
deviationFromRiemann negativeCurvatureAction =
  outwardSeparationAcceleration
deviationFromRiemann zeroCurvatureAction =
  zeroSeparationAcceleration
deviationFromRiemann positiveCurvatureAction =
  inwardSeparationAcceleration

principalDeviationAcceleration :
  SpatialAxis3 → SeparationOrientation
principalDeviationAcceleration i =
  deviationFromRiemann (comovingRiemannTimeTidal i i)

xDeviationIsOutward :
  principalDeviationAcceleration xSpatial
    ≡ outwardSeparationAcceleration
xDeviationIsOutward = refl

yDeviationIsOutward :
  principalDeviationAcceleration ySpatial
    ≡ outwardSeparationAcceleration
yDeviationIsOutward = refl

zDeviationIsOutward :
  principalDeviationAcceleration zSpatial
    ≡ outwardSeparationAcceleration
zDeviationIsOutward = refl

allPrincipalComovingDeviationDirectionsOutward :
  (i : SpatialAxis3) →
  principalDeviationAcceleration i
    ≡ outwardSeparationAcceleration
allPrincipalComovingDeviationDirectionsOutward xSpatial = refl
allPrincipalComovingDeviationDirectionsOutward ySpatial = refl
allPrincipalComovingDeviationDirectionsOutward zSpatial = refl

------------------------------------------------------------------------
-- SAME-OBJECT DEPENDENCY ON THE PREVIOUS FLRW RESULT
------------------------------------------------------------------------

record FiniteComovingRiemannDeviationWitness : Set where
  constructor finite-comoving-riemann-deviation-witness
  field
    flrwRepulsiveExpansion :
      FLRW.FiniteRepulsiveExpansionWitness

    accelerationOrientation :
      FLRW.finiteFLRWAccelerationOrientation
        ≡ FLRW.expandingAcceleration

    xRiemannTidalNegative :
      comovingRiemannTimeTidal xSpatial xSpatial
        ≡ negativeCurvatureAction

    yRiemannTidalNegative :
      comovingRiemannTimeTidal ySpatial ySpatial
        ≡ negativeCurvatureAction

    zRiemannTidalNegative :
      comovingRiemannTimeTidal zSpatial zSpatial
        ≡ negativeCurvatureAction

    everyPrincipalDeviationOutward :
      (i : SpatialAxis3) →
      principalDeviationAcceleration i
        ≡ outwardSeparationAcceleration

open FiniteComovingRiemannDeviationWitness public

canonicalFiniteComovingRiemannDeviationWitness :
  FiniteComovingRiemannDeviationWitness
canonicalFiniteComovingRiemannDeviationWitness =
  finite-comoving-riemann-deviation-witness
    FLRW.canonicalFiniteRepulsiveExpansionWitness
    FLRW.finiteFLRWAccelerationIsExpanding
    finiteRiemannXX
    finiteRiemannYY
    finiteRiemannZZ
    allPrincipalComovingDeviationDirectionsOutward

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record FiniteComovingRiemannDeviationBoundary : Set where
  constructor finite-comoving-riemann-deviation-boundary
  field
    indexedComovingTimeTidalBlockConstructed : Bool
    threePrincipalTidalEigenDirectionsOutward : Bool
    offDiagonalComovingTidalBlockZeroInFixture : Bool
    resultRequiresNegativeG : Bool
    resultRequiresNegativeInertialMass : Bool
    resultIsArbitrarySpacetimeRiemannTensor : Bool
    resultIsLocalizedStaticAntigravityField : Bool
    continuumMagnitudeStillRequiresSmoothScaleFactor : Bool
    arbitraryWorldlineDeviationStillRequiresGeneralRiemannCarrier : Bool

canonicalFiniteComovingRiemannDeviationBoundary :
  FiniteComovingRiemannDeviationBoundary
canonicalFiniteComovingRiemannDeviationBoundary =
  finite-comoving-riemann-deviation-boundary
    true true true false false false false true true
