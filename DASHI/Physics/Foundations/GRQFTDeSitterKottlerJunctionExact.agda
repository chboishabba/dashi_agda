{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- STATIC SPHERICAL JUNCTION: de Sitter-like INTERIOR -> KOTTLER EXTERIOR
--
-- Use the standard lapse functions in G=c=1 units:
--
--   f_in(r)  = 1 - Lambda_in r^2 / 3
--   f_out(r) = 1 - 2M/r - Lambda_out r^2 / 3.
--
-- A shell-free Darmois match at r=R requires both f and f' continuity.
-- Those two equations force incompatible Lambda jumps unless M=0.
------------------------------------------------------------------------

fInterior :
  (radius lambdaIn : ℚ) → ℚ
fInterior radius lambdaIn =
  1ℚ - lambdaIn * radius * radius / (Int.+ 3 / 1)

fExterior :
  (radius mass lambdaOut : ℚ) → ℚ
fExterior radius mass lambdaOut =
  1ℚ
  - (Int.+ 2 / 1) * mass / radius
  - lambdaOut * radius * radius / (Int.+ 3 / 1)

fInteriorPrime :
  (radius lambdaIn : ℚ) → ℚ
fInteriorPrime radius lambdaIn =
  - ((Int.+ 2 / 1) * lambdaIn * radius / (Int.+ 3 / 1))

fExteriorPrime :
  (radius mass lambdaOut : ℚ) → ℚ
fExteriorPrime radius mass lambdaOut =
  (Int.+ 2 / 1) * mass / (radius * radius)
  - (Int.+ 2 / 1) * lambdaOut * radius / (Int.+ 3 / 1)

------------------------------------------------------------------------
-- Algebraic jump conditions.
--
-- f continuity implies:
--   Lambda_in - Lambda_out = 6 M / R^3.
--
-- f' continuity implies:
--   Lambda_in - Lambda_out = -3 M / R^3.
--
-- Hence for nonzero M they cannot both hold.
------------------------------------------------------------------------

metricContinuityLambdaJump :
  (mass radius : ℚ) → ℚ
metricContinuityLambdaJump mass radius =
  (Int.+ 6 / 1) * mass / (radius * radius * radius)

derivativeContinuityLambdaJump :
  (mass radius : ℚ) → ℚ
derivativeContinuityLambdaJump mass radius =
  - ((Int.+ 3 / 1) * mass / (radius * radius * radius))

fixtureMass : ℚ
fixtureMass = Int.+ 1 / 4

fixtureRadius : ℚ
fixtureRadius = Int.+ 2 / 1

fixtureMetricLambdaJumpIsThreeSixteenths :
  metricContinuityLambdaJump fixtureMass fixtureRadius
    ≡ Int.+ 3 / 16
fixtureMetricLambdaJumpIsThreeSixteenths = solve []

fixtureDerivativeLambdaJumpIsMinusThreeThirtySeconds :
  derivativeContinuityLambdaJump fixtureMass fixtureRadius
    ≡ - (Int.+ 3 / 32)
fixtureDerivativeLambdaJumpIsMinusThreeThirtySeconds = solve []

fixtureDarmoisJumpContradiction :
  metricContinuityLambdaJump fixtureMass fixtureRadius
    ≡ derivativeContinuityLambdaJump fixtureMass fixtureRadius → ⊥
fixtureDarmoisJumpContradiction ()

------------------------------------------------------------------------
-- STATIC OUTWARD-ACCELERATING EXTERIOR FIXTURE
--
-- Choose Lambda_out = 3/16:
--
--   acceleration at R=2:
--     -M/R^2 + Lambda_out R/3
--       = -1/16 + 1/8 = +1/16.
--
-- It also keeps f_out(R)=1/2 > 0, so the boundary lies in the static patch.
--
-- Metric continuity then forces Lambda_in = 3/8.
------------------------------------------------------------------------

lambdaOut : ℚ
lambdaOut = Int.+ 3 / 16

lambdaIn : ℚ
lambdaIn = Int.+ 3 / 8

radialAcceleration :
  (radius mass lambda : ℚ) → ℚ
radialAcceleration radius mass lambda =
  - (mass / (radius * radius))
  + lambda * radius / (Int.+ 3 / 1)

fixtureExteriorAccelerationIsOneSixteenth :
  radialAcceleration fixtureRadius fixtureMass lambdaOut
    ≡ Int.+ 1 / 16
fixtureExteriorAccelerationIsOneSixteenth = solve []

fixtureExteriorLapseIsOneHalf :
  fExterior fixtureRadius fixtureMass lambdaOut
    ≡ Int.+ 1 / 2
fixtureExteriorLapseIsOneHalf = solve []

fixtureInteriorLapseIsOneHalf :
  fInterior fixtureRadius lambdaIn
    ≡ Int.+ 1 / 2
fixtureInteriorLapseIsOneHalf = solve []

fixtureMetricContinuous :
  fInterior fixtureRadius lambdaIn
    ≡ fExterior fixtureRadius fixtureMass lambdaOut
fixtureMetricContinuous = solve []

------------------------------------------------------------------------
-- EXTRINSIC-CURVATURE / DERIVATIVE JUMP
--
-- At the same matched boundary:
--
--   f'_in  = -1/2
--   f'_out = -1/8
--   [f']   = +3/8.
--
-- Thus the induced metric can be continuous while the radial derivative is
-- not: a thin shell / surface stress is required.
------------------------------------------------------------------------

fixtureInteriorPrimeIsMinusHalf :
  fInteriorPrime fixtureRadius lambdaIn
    ≡ - (Int.+ 1 / 2)
fixtureInteriorPrimeIsMinusHalf = solve []

fixtureExteriorPrimeIsMinusOneEighth :
  fExteriorPrime fixtureRadius fixtureMass lambdaOut
    ≡ - (Int.+ 1 / 8)
fixtureExteriorPrimeIsMinusOneEighth = solve []

fixtureDerivativeJump :
  ℚ
fixtureDerivativeJump =
  fExteriorPrime fixtureRadius fixtureMass lambdaOut
  - fInteriorPrime fixtureRadius lambdaIn

fixtureDerivativeJumpIsThreeEighths :
  fixtureDerivativeJump ≡ Int.+ 3 / 8
fixtureDerivativeJumpIsThreeEighths = solve []

fixtureDerivativeNotContinuous :
  fInteriorPrime fixtureRadius lambdaIn
    ≡ fExteriorPrime fixtureRadius fixtureMass lambdaOut → ⊥
fixtureDerivativeNotContinuous ()

------------------------------------------------------------------------
-- ISRAEL-SHELL SIGN DIAGNOSTIC
--
-- For a static spherical shell with continuous f, the angular extrinsic
-- curvature is continuous because it depends on sqrt(f)/R.  The remaining
-- jump is carried by the time-time extrinsic curvature, proportional to
--
--   [f']/(2 sqrt(f)).
--
-- Since f(R)=1/2>0 and [f']=3/8>0, the normalized surface tangential-pressure
-- numerator is positive.  We retain only this exact rational sign carrier;
-- the sqrt(f) and 8*pi normalization are deliberately not manufactured.
------------------------------------------------------------------------

data SurfaceTangentialStressOrientation : Set where
  negativeSurfaceTension : SurfaceTangentialStressOrientation
  zeroSurfaceTangentialStress : SurfaceTangentialStressOrientation
  positiveSurfacePressure : SurfaceTangentialStressOrientation

fixtureSurfaceTangentialStressOrientation :
  SurfaceTangentialStressOrientation
fixtureSurfaceTangentialStressOrientation =
  positiveSurfacePressure

record DeSitterKottlerJunctionWitness : Set where
  constructor de-sitter-kottler-junction-witness
  field
    mass :
      fixtureMass ≡ Int.+ 1 / 4

    radius :
      fixtureRadius ≡ Int.+ 2 / 1

    interiorLambda :
      lambdaIn ≡ Int.+ 3 / 8

    exteriorLambda :
      lambdaOut ≡ Int.+ 3 / 16

    lapseMatched :
      fInterior fixtureRadius lambdaIn
        ≡ fExterior fixtureRadius fixtureMass lambdaOut

    lapseStaticPositive :
      fExterior fixtureRadius fixtureMass lambdaOut
        ≡ Int.+ 1 / 2

    exteriorAccelerationOutward :
      radialAcceleration fixtureRadius fixtureMass lambdaOut
        ≡ Int.+ 1 / 16

    derivativeJump :
      fixtureDerivativeJump ≡ Int.+ 3 / 8

    surfaceStressOrientation :
      SurfaceTangentialStressOrientation
    surfaceStressIsPositivePressure :
      surfaceStressOrientation ≡ positiveSurfacePressure

open DeSitterKottlerJunctionWitness public

canonicalDeSitterKottlerJunctionWitness :
  DeSitterKottlerJunctionWitness
canonicalDeSitterKottlerJunctionWitness =
  de-sitter-kottler-junction-witness
    refl
    refl
    refl
    refl
    fixtureMetricContinuous
    fixtureExteriorLapseIsOneHalf
    fixtureExteriorAccelerationIsOneSixteenth
    fixtureDerivativeJumpIsThreeEighths
    positiveSurfacePressure
    refl

record DeSitterKottlerJunctionBoundary : Set where
  constructor de-sitter-kottler-junction-boundary
  field
    shellFreeNonzeroMassDarmoisMatchAvailable : Bool
    inducedMetricContinuityConstructed : Bool
    boundaryInsideStaticPatch : Bool
    outwardExteriorAccelerationConstructed : Bool
    derivativeJumpNonzero : Bool
    thinSurfaceLayerRequired : Bool
    positiveSurfacePressureOrientationRequired : Bool
    exactIsraelNormalizationSolved : Bool
    SIUnitsCalibrated : Bool

canonicalDeSitterKottlerJunctionBoundary :
  DeSitterKottlerJunctionBoundary
canonicalDeSitterKottlerJunctionBoundary =
  de-sitter-kottler-junction-boundary
    false true true true true true true false false
