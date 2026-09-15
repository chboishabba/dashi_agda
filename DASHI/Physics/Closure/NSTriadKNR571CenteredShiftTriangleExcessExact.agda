module DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact where

------------------------------------------------------------------------
-- R571 GATE-A / A2 CENTERED SHIFT TRIANGLE-EXCESS GEOMETRY
--
-- Timestamp: 2026-09-15 AEST.
--
-- For the literal centered Fourier shifts
--
--   p = k + y,
--   q = k - y,
--
-- this owner proves the exact integer/Fourier identities
--
--   p + q = 2 k,
--   |2 k|^2 = 4 |k|^2,
--   Plucker(p,q) = 4 Plucker(k,y).
--
-- These are the same-object polynomial coordinates needed by the A2
-- triangle-excess reduction.  They do NOT by themselves prove the scalar
-- square-root/radius statement modeNorm(2k) = 2 modeNorm(k), nor an ordered
-- denominator bound, nor the final |y|^2 curvature estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _+_; _-_; _*_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Add
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plane

module RingZ = NR IntRS.ring

two : ℤ
two = + 2

four : ℤ
four = + 4

plusMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
plusMode center displacement = Z3.addMode center displacement

minusMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
minusMode center displacement =
  Z3.addMode center (Z3.negateMode displacement)

doubledCenter : Z3.FourierMode → Z3.FourierMode
doubledCenter center = Z3.addMode center center

centeredShiftSumIsDoubledCenter :
  (center displacement : Z3.FourierMode) →
  Z3.addMode
    (plusMode center displacement)
    (minusMode center displacement)
  ≡ doubledCenter center
centeredShiftSumIsDoubledCenter
    (Z3.mode kx ky kz) (Z3.mode yx yy yz) =
  Add.modeExt
    (RingZ.solve 2
      (λ k y → (((k + y) + (k - y)) , k + k))
      refl kx yx)
    (RingZ.solve 2
      (λ k y → (((k + y) + (k - y)) , k + k))
      refl ky yy)
    (RingZ.solve 2
      (λ k y → (((k + y) + (k - y)) , k + k))
      refl kz yz)

doubledCenterNormSquaredScalesByFour :
  (center : Z3.FourierMode) →
  Plane.modeNormSquared (doubledCenter center)
  ≡ four * Plane.modeNormSquared center
doubledCenterNormSquaredScalesByFour (Z3.mode kx ky kz) =
  RingZ.solve 3
    (λ x y z →
      ( ((x + x) * (x + x)
          + (y + y) * (y + y)
          + (z + z) * (z + z))
      , (+ 4) * (x * x + y * y + z * z)))
    refl kx ky kz

centeredShiftOutputNormSquaredScalesByFour :
  (center displacement : Z3.FourierMode) →
  Plane.modeNormSquared
    (Z3.addMode
      (plusMode center displacement)
      (minusMode center displacement))
  ≡ four * Plane.modeNormSquared center
centeredShiftOutputNormSquaredScalesByFour center displacement =
  trans
    (cong Plane.modeNormSquared
      (centeredShiftSumIsDoubledCenter center displacement))
    (doubledCenterNormSquaredScalesByFour center)

centeredShiftPluckerScalesByFour :
  (center displacement : Z3.FourierMode) →
  Plane.pluckerNormSquared
    (plusMode center displacement)
    (minusMode center displacement)
  ≡ four * Plane.pluckerNormSquared center displacement
centeredShiftPluckerScalesByFour
    (Z3.mode kx ky kz) (Z3.mode yx yy yz) =
  RingZ.solve 6
    (λ kx ky kz yx yy yz →
      ( (((kx + yx) * (ky - yy) - (ky + yy) * (kx - yx))
          * ((kx + yx) * (ky - yy) - (ky + yy) * (kx - yx)))
        + (((kx + yx) * (kz - yz) - (kz + yz) * (kx - yx))
          * ((kx + yx) * (kz - yz) - (kz + yz) * (kx - yx)))
        + (((ky + yy) * (kz - yz) - (kz + yz) * (ky - yy))
          * ((ky + yy) * (kz - yz) - (kz + yz) * (ky - yy)))
      , (+ 4) *
          ( ((kx * yy - ky * yx) * (kx * yy - ky * yx))
          + ((kx * yz - kz * yx) * (kx * yz - kz * yx))
          + ((ky * yz - kz * yy) * (ky * yz - kz * yy)))))
    refl kx ky kz yx yy yz

r571A2CenteredShiftModeSumClosed : Bool
r571A2CenteredShiftModeSumClosed = true

r571A2CenteredShiftSquaredOutputScalingClosed : Bool
r571A2CenteredShiftSquaredOutputScalingClosed = true

r571A2CenteredShiftPluckerScalingClosed : Bool
r571A2CenteredShiftPluckerScalingClosed = true

r571A2CenteredShiftScalarRadiusDoublingClosed : Bool
r571A2CenteredShiftScalarRadiusDoublingClosed = false

r571A2OrderedRadialDenominatorPaymentClosed : Bool
r571A2OrderedRadialDenominatorPaymentClosed = false

r571A2UniformCurvatureEstimateClosed : Bool
r571A2UniformCurvatureEstimateClosed = false

r571A2ClosesR568 : Bool
r571A2ClosesR568 = false

r571A2CenteredShiftModeSumClosedIsTrue :
  r571A2CenteredShiftModeSumClosed ≡ true
r571A2CenteredShiftModeSumClosedIsTrue = refl

r571A2CenteredShiftSquaredOutputScalingClosedIsTrue :
  r571A2CenteredShiftSquaredOutputScalingClosed ≡ true
r571A2CenteredShiftSquaredOutputScalingClosedIsTrue = refl

r571A2CenteredShiftPluckerScalingClosedIsTrue :
  r571A2CenteredShiftPluckerScalingClosed ≡ true
r571A2CenteredShiftPluckerScalingClosedIsTrue = refl

r571A2CenteredShiftScalarRadiusDoublingClosedIsFalse :
  r571A2CenteredShiftScalarRadiusDoublingClosed ≡ false
r571A2CenteredShiftScalarRadiusDoublingClosedIsFalse = refl
