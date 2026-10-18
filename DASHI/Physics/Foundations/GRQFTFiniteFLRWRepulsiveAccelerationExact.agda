{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTFiniteFLRWRepulsiveAccelerationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Geometry.NonconstantWarpedLorentzianModel as Geometry
import DASHI.Physics.Foundations.GRQFTFiniteDefocusingSolutionWitnessExact as Witness

------------------------------------------------------------------------
-- FINITE FLRW-LIKE COMOVING ACCELERATION ORIENTATION
--
-- Standard smooth FLRW kinematics gives
--
--     (a double-dot)/a = H-dot + H^2.
--
-- The finite warped carrier stores only normalized sign/depth information, not
-- a real-valued scale factor.  We therefore compile only the ORIENTATION of
-- this quantity for the exact fixture:
--
--     H-dot = 0
--     H^2   = positiveCurvature
--
-- hence the comoving separation-acceleration orientation is positive.
--
-- This is stronger than a bare active-stress sign but weaker than a general
-- vector-valued geodesic-deviation theorem.
------------------------------------------------------------------------

data ScaleAccelerationOrientation : Set where
  contractingAcceleration : ScaleAccelerationOrientation
  zeroScaleAcceleration : ScaleAccelerationOrientation
  expandingAcceleration : ScaleAccelerationOrientation

zeroHdotFLRWAccelerationOrientation :
  Geometry.CurvatureCoefficient →
  ScaleAccelerationOrientation
zeroHdotFLRWAccelerationOrientation Geometry.zeroCurvature =
  zeroScaleAcceleration
zeroHdotFLRWAccelerationOrientation Geometry.positiveCurvature =
  expandingAcceleration

finiteFLRWAccelerationOrientation :
  ScaleAccelerationOrientation
finiteFLRWAccelerationOrientation =
  zeroHdotFLRWAccelerationOrientation
    Geometry.warpedSectionalCurvature

finiteFLRWAccelerationIsExpanding :
  finiteFLRWAccelerationOrientation ≡ expandingAcceleration
finiteFLRWAccelerationIsExpanding = refl

------------------------------------------------------------------------
-- SAME-OBJECT COMPOSITION WITH THE DEFOCUSING WITNESS
------------------------------------------------------------------------

record FiniteRepulsiveExpansionWitness : Set where
  constructor finite-repulsive-expansion-witness
  field
    defocusingSolution :
      Witness.FiniteDefocusingSolutionWitness

    hubbleDerivativeZero :
      Geometry.hubbleDerivative ≡ Geometry.zeroUnit

    hubbleSquarePositive :
      Geometry.warpedSectionalCurvature ≡ Geometry.positiveCurvature

    comovingScaleAccelerationPositive :
      finiteFLRWAccelerationOrientation ≡ expandingAcceleration

open FiniteRepulsiveExpansionWitness public

canonicalFiniteRepulsiveExpansionWitness :
  FiniteRepulsiveExpansionWitness
canonicalFiniteRepulsiveExpansionWitness =
  finite-repulsive-expansion-witness
    Witness.canonicalFiniteDefocusingSolutionWitness
    Geometry.constantHubbleReceipt
    Geometry.computedPositiveCurvature
    finiteFLRWAccelerationIsExpanding

------------------------------------------------------------------------
-- INTERPRETATION BOUNDARY
------------------------------------------------------------------------

record FiniteFLRWRepulsiveAccelerationBoundary : Set where
  constructor finite-flrw-repulsive-acceleration-boundary
  field
    positiveComovingAccelerationOrientationConstructed : Bool
    sameObjectAlsoHasPositiveGCoupling : Bool
    sameObjectAlsoHasNegativePressureTension : Bool
    sameObjectAlsoHasPositiveRaychaudhuriCurvatureContribution : Bool
    resultUsesNegativeNewtonG : Bool
    resultUsesNegativeInertialMass : Bool
    finiteSignDepthAccelerationEqualsContinuumMagnitudePrediction : Bool
    comovingFLRWAccelerationEqualsArbitraryLocalTestMassTrajectory : Bool
    fullIndexedRiemannDeviationOperatorStillNeededForGeneralTrajectory : Bool

canonicalFiniteFLRWRepulsiveAccelerationBoundary :
  FiniteFLRWRepulsiveAccelerationBoundary
canonicalFiniteFLRWRepulsiveAccelerationBoundary =
  finite-flrw-repulsive-acceleration-boundary
    true true true true false false false false true
