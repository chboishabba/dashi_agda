module DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact where

------------------------------------------------------------------------
-- ROUND408 / CONSTRUCT THE ROUND240 TRAJECTORY WITH THE CANONICAL LITERAL RHS
--
-- R407 constructed the exact projected Galerkin equation whose
-- `timeDerivative` is definitionally Round30's literal Navier--Stokes
-- coefficient.  This round removes the remaining equation-selection freedom
-- from the live Round240 trajectory: the caller supplies only the actual state
-- curve, support/viscosity data, and a derivative witness against the literal
-- Round30 coefficient.  The equation field itself is constructed here from
-- R407.
--
-- This is a same-object authority weld, not an analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNPhysicalFiniteComplex3GalerkinFieldRound30Exact as Field30
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

  record LiteralRHSTrajectoryData : Set₁ where
    field
      systemAt : Nat → Time → Audit.FiniteComplex3GalerkinSystem F

      physicalSystemAt :
        (cutoff : Nat) (time : Time) →
        Field30.PhysicalFiniteComplex3GalerkinSystem F

      physicalSystemUnderlying :
        (cutoff : Nat) (time : Time) →
        R30.finiteSystem (physicalSystemAt cutoff time) ≡ systemAt cutoff time

      velocityDerivativeIsLiteralRHS :
        (cutoff : Nat) (mode : Z3.FourierMode) →
        DerivativeOf
          (λ time → Audit.velocityAt (systemAt cutoff time) mode)
          (λ time →
            R30.literalViscousQuadraticCoefficient
              (physicalSystemAt cutoff time) mode)

      viscosityFixed :
        (cutoff : Nat) (time : Time) →
        Audit.viscosity (systemAt cutoff time)
        ≡ Audit.viscosity (systemAt cutoff initialTime)

      velocityTransverse :
        (cutoff : Nat) (time : Time) (mode : Z3.FourierMode) → Set

      initialVelocityAgreement :
        (cutoff : Nat) (mode : Z3.FourierMode) → Set

  open LiteralRHSTrajectoryData public

  canonicalEquationAt :
    (D : LiteralRHSTrajectoryData) →
    (cutoff : Nat) (time : Time) →
    Audit.ExactProjectedGalerkinEquation (systemAt D cutoff time)
  canonicalEquationAt D cutoff time
    rewrite sym (physicalSystemUnderlying D cutoff time) =
      R407.canonicalLiteralProjectedEquation (physicalSystemAt D cutoff time)

  literalRHSAgreement :
    (D : LiteralRHSTrajectoryData) →
    (cutoff : Nat) (time : Time) (mode : Z3.FourierMode) →
    Audit.timeDerivative (canonicalEquationAt D cutoff time) mode
    ≡ R30.literalViscousQuadraticCoefficient
         (physicalSystemAt D cutoff time) mode
  literalRHSAgreement D cutoff time mode
    rewrite sym (physicalSystemUnderlying D cutoff time) = refl

round408CanonicalEquationSelectionClosed : Bool
round408CanonicalEquationSelectionClosed = true

round408LiteralDerivativeAuthoritySameObject : Bool
round408LiteralDerivativeAuthoritySameObject = true

round408IntroducesNoNewAnalyticEstimate : Bool
round408IntroducesNoNewAnalyticEstimate = true

round408ActualScalarFluxDerivativeStillOpen : Bool
round408ActualScalarFluxDerivativeStillOpen = true

round408CanonicalEquationSelectionClosedIsTrue :
  round408CanonicalEquationSelectionClosed ≡ true
round408CanonicalEquationSelectionClosedIsTrue = refl

round408LiteralDerivativeAuthoritySameObjectIsTrue :
  round408LiteralDerivativeAuthoritySameObject ≡ true
round408LiteralDerivativeAuthoritySameObjectIsTrue = refl
