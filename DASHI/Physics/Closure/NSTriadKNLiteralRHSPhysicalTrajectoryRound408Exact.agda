module DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact where

------------------------------------------------------------------------
-- ROUND408 / CONSTRUCT THE ACTUAL ROUND240 TRAJECTORY WITH LITERAL ROUND30 RHS
--
-- R407 constructed the projected equation whose timeDerivative is
-- definitionally Round30's literal Navier--Stokes coefficient.  Here we remove
-- the remaining equation-selection freedom from the live Round240 trajectory.
-- The physical Round30 wrapper is constructed from the SAME Round228 state,
-- so its `finiteSystem` is definitionally the live state system; no carrier
-- equality or caller-selected equation is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNCanonicalLiteralProjectedODERound407Exact as R407

F : C3.RealField _
F = Rational.rationalRealField

module LiteralDynamics
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Base = Dyn.Base

  record LiteralStateSupport : Set₁ where
    field
      stateTrajectory : Base.PhysicalMixedHelicityTrajectory

      retainedModeNonzero :
        (cutoff : Nat) (time : Time) (mode : Z3.FourierMode) →
        mode Cube.∈ Audit.modes (Base.systemAt stateTrajectory cutoff time) →
        Z3.NonZeroMode mode

      physicalViscosity : C3.Carrier F
      viscosityFixed :
        (cutoff : Nat) (time : Time) →
        Audit.viscosity (Base.systemAt stateTrajectory cutoff time)
        ≡ physicalViscosity

      initialVelocity : Z3.FourierMode → C3.Complex3 F
      initialVelocityAgreement :
        (cutoff : Nat) (mode : Z3.FourierMode) →
        Audit.modeListed (Base.systemAt stateTrajectory cutoff initialTime) mode →
        Audit.velocity (Base.systemAt stateTrajectory cutoff initialTime) mode
        ≡ initialVelocity mode

  open LiteralStateSupport public

  physicalSystemAt :
    (S : LiteralStateSupport) →
    (cutoff : Nat) (time : Time) →
    R30.PhysicalFiniteComplex3GalerkinSystem F
  physicalSystemAt S cutoff time = record
    { R30.physicalEmbedding = Base.E (stateTrajectory S)
    ; R30.physicalInverseSquare = Base.I (stateTrajectory S)
    ; R30.finiteSystem = Base.systemAt (stateTrajectory S) cutoff time
    ; R30.viscosity = Audit.viscosity (Base.systemAt (stateTrajectory S) cutoff time)
    ; R30.retainedModeNonzero = retainedModeNonzero S cutoff time
    ; R30.retainedVelocityTransverse = λ mode member →
        Base.velocityTransverse (stateTrajectory S) cutoff time mode
    }

  canonicalEquationAt :
    (S : LiteralStateSupport) →
    (cutoff : Nat) (time : Time) →
    Audit.ExactProjectedGalerkinEquation
      (Base.systemAt (stateTrajectory S) cutoff time)
  canonicalEquationAt S cutoff time =
    R407.canonicalLiteralProjectedEquation (physicalSystemAt S cutoff time)

  record LiteralRHSTrajectoryData : Set₁ where
    field
      support : LiteralStateSupport

      velocityDerivativeIsLiteralRHS :
        (cutoff : Nat) (mode : Z3.FourierMode) →
        DerivativeOf
          (λ time →
            Audit.velocity
              (Base.systemAt (stateTrajectory support) cutoff time)
              mode)
          (λ time →
            R30.literalViscousQuadraticCoefficient
              (physicalSystemAt support cutoff time) mode)

  open LiteralRHSTrajectoryData public

  literalPhysicalTrajectory :
    LiteralRHSTrajectoryData → Dyn.PhysicalNSGalerkinTrajectory
  literalPhysicalTrajectory D =
    Dyn.physical-ns-galerkin-trajectory
      (stateTrajectory S)
      (canonicalEquationAt S)
      (velocityDerivativeIsLiteralRHS D)
      (physicalViscosity S)
      (viscosityFixed S)
      (initialVelocity S)
      (initialVelocityAgreement S)
    where
      S = support D

  literalTrajectoryEquationDerivativeIsRound30 :
    (D : LiteralRHSTrajectoryData) →
    (cutoff : Nat) (time : Time) (mode : Z3.FourierMode) →
    Audit.timeDerivative
      (Dyn.equationAt (literalPhysicalTrajectory D) cutoff time) mode
    ≡ R30.literalViscousQuadraticCoefficient
         (physicalSystemAt (support D) cutoff time) mode
  literalTrajectoryEquationDerivativeIsRound30 D cutoff time mode = refl

round408ActualRound240TrajectoryConstructed : Bool
round408ActualRound240TrajectoryConstructed = true

round408CanonicalEquationSelectionClosed : Bool
round408CanonicalEquationSelectionClosed = true

round408LiteralDerivativeAuthoritySameObject : Bool
round408LiteralDerivativeAuthoritySameObject = true

round408IntroducesNoNewAnalyticEstimate : Bool
round408IntroducesNoNewAnalyticEstimate = true

round408ActualScalarFluxDerivativeStillOpen : Bool
round408ActualScalarFluxDerivativeStillOpen = true

round408ActualRound240TrajectoryConstructedIsTrue :
  round408ActualRound240TrajectoryConstructed ≡ true
round408ActualRound240TrajectoryConstructedIsTrue = refl
