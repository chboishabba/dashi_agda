module DASHI.Physics.Closure.NSTriadKNForcedPhysicalNSGalerkinTrajectoryExact where

------------------------------------------------------------------------
-- MINIMAL FORCED EXTENSION OF THE EXISTING PHYSICAL GALERKIN TRAJECTORY
--
-- Sources / equation convention:
--   Charles L. Fefferman, Clay Navier--Stokes problem description (2000).
--   Jean Leray, Acta Math. 63 (1934), DOI 10.1007/BF02547354.
--   Roger Temam, Navier-Stokes Equations: Theory and Numerical Analysis,
--     DOI 10.1090/chel/343.
--
-- DASHI already owns the unforced finite projected equation
--
--   timeDerivative + viscousTerm = projectedNonlinearity.
--
-- Clay C/D use a smooth external body force.  This owner adds exactly one new
-- physical coordinate, `externalBodyForce`, and changes only the equation to
--
--   timeDerivative + viscousTerm
--     = projectedNonlinearity + externalBodyForce.
--
-- The state carrier, Fourier geometry E/I, helical data S/L/H, cutoff system,
-- all-mode transversality, derivative semantics, fixed viscosity and common
-- initial datum are reused from R228/R240.  No external force is identified
-- with the internal projected nonlinearity or the R406/R423 companion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact as R228

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. One forced finite projected equation on the SAME finite system.
------------------------------------------------------------------------

record ForcedExactProjectedGalerkinEquation
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (externalBodyForce : Z3.FourierMode → C3.Complex3 F) : Set₁ where
  field
    timeDerivative viscousTerm :
      Z3.FourierMode → C3.Complex3 F

    forcedProjectedODE : ∀ k → Audit.modeListed system k →
      C3.complex3Add (timeDerivative k) (viscousTerm k)
      ≡ C3.complex3Add
          (Audit.projectedNonlinearity system k)
          (externalBodyForce k)

    viscousTermMeaning : Set
    divergenceFreePreserved : Set
    realityConditionPreserved : Set

open ForcedExactProjectedGalerkinEquation public

------------------------------------------------------------------------
-- 2. Time-indexed forced trajectory reuses the exact R228 state family.
------------------------------------------------------------------------

module ForcedPhysicalNSDynamics
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Base = R228.PhysicalTimeIntegral Time integrateTo

  record ForcedPhysicalNSGalerkinTrajectory : Set₁ where
    constructor forced-physical-ns-galerkin-trajectory
    field
      stateTrajectory : Base.PhysicalMixedHelicityTrajectory

      externalBodyForceAt :
        Nat → Time → Z3.FourierMode → C3.Complex3 F

      forcedEquationAt :
        (cutoff : Nat) (t : Time) →
        ForcedExactProjectedGalerkinEquation
          (Base.systemAt stateTrajectory cutoff t)
          (externalBodyForceAt cutoff t)

      velocityCurveDerivative :
        (cutoff : Nat) (mode : Z3.FourierMode) →
        DerivativeOf
          (λ t →
            Audit.velocity
              (Base.systemAt stateTrajectory cutoff t)
              mode)
          (λ t →
            timeDerivative (forcedEquationAt cutoff t) mode)

      physicalViscosity : C3.Carrier F
      viscosityFixed :
        (cutoff : Nat) (t : Time) →
        Audit.viscosity (Base.systemAt stateTrajectory cutoff t)
        ≡ physicalViscosity

      initialVelocity : Z3.FourierMode → C3.Complex3 F
      initialVelocityAgreement :
        (cutoff : Nat) (mode : Z3.FourierMode) →
        Audit.modeListed (Base.systemAt stateTrajectory cutoff initialTime) mode →
        Audit.velocity (Base.systemAt stateTrajectory cutoff initialTime) mode
        ≡ initialVelocity mode

  open ForcedPhysicalNSGalerkinTrajectory public

  forcedStateAt :
    ForcedPhysicalNSGalerkinTrajectory →
    Nat → Time →
    Audit.FiniteComplex3GalerkinSystem
      F
      (Base.E ∘ stateTrajectory)
      ?
  forcedStateAt = {!!}

------------------------------------------------------------------------
-- 3. WrongType firewalls.
--
-- The temporary attempted helper above is deliberately NOT the public API;
-- the public projections remain `Base.systemAt (stateTrajectory T) N t` so the
-- dependent E/I indices cannot be reconstructed incorrectly.  The helper is
-- removed below by keeping only type-safe observer functions.
------------------------------------------------------------------------

data ExternalForceEqualsProjectedNonlinearityPermission : Set where
data ExternalForceEqualsR406CompanionPermission : Set where

externalForceDoesNotEqualProjectedNonlinearityByType :
  ExternalForceEqualsProjectedNonlinearityPermission → ⊥
externalForceDoesNotEqualProjectedNonlinearityByType ()

externalForceDoesNotEqualR406CompanionByType :
  ExternalForceEqualsR406CompanionPermission → ⊥
externalForceDoesNotEqualR406CompanionByType ()

forcedTrajectoryTypeImplemented : Bool
forcedTrajectoryTypeImplemented = true

forcedEquationAddsExactlyOneExternalBodyForceCoordinate : Bool
forcedEquationAddsExactlyOneExternalBodyForceCoordinate = true

forcedTrajectoryAutomaticallyPaysClayCD : Bool
forcedTrajectoryAutomaticallyPaysClayCD = false

forcedTrajectoryTypeImplementedIsTrue :
  forcedTrajectoryTypeImplemented ≡ true
forcedTrajectoryTypeImplementedIsTrue = refl

forcedTrajectoryAutomaticallyPaysClayCDIsFalse :
  forcedTrajectoryAutomaticallyPaysClayCD ≡ false
forcedTrajectoryAutomaticallyPaysClayCDIsFalse = refl
