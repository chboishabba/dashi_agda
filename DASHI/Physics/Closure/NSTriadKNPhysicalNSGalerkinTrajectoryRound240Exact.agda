module DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact where

------------------------------------------------------------------------
-- ROUND240 / AUTHORITY CORRECTION: ROUND228 NEEDS AN ACTUAL NS TRAJECTORY
--
-- Round228's `PhysicalMixedHelicityTrajectory` is a time-indexed family of
-- finite Galerkin STATES.  The underlying `FiniteComplex3GalerkinSystem` is
-- static data: velocity, cutoff, modes, viscosity, etc.  The exact projected
-- ODE lives in the separate `ExactProjectedGalerkinEquation` record.
--
-- Therefore a theorem quantified over the bare Round228 trajectory can range
-- over arbitrary time-indexed transverse states.  That is too broad for the
-- intended Navier--Stokes PDE estimate.
--
-- This file installs the stronger consumer object without breaking R223--228.
-- It requires, on the SAME state family:
--
--   1. an exact projected Galerkin equation at every (N,t);
--   2. an externally owned derivative semantics witnessing that the ODE's
--      `timeDerivative` is literally the derivative of the actual velocity
--      curve t |-> u_N(t,k);
--   3. one viscosity shared across all cutoffs and times;
--   4. one initial Fourier datum shared by all cutoffs on their listed modes.
--
-- The derivative relation is a MODULE PARAMETER, not a caller-defined field
-- whose meaning could be weakened inside the trajectory record.
--
-- A forgetful map returns the original Round228 state trajectory, so all
-- mixed-helicity algebra remains reusable.  The corrected spacetime-budget
-- target is now attached only to an actual NS Galerkin trajectory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact as R228

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalNSDynamics
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Base = R228.PhysicalTimeIntegral Time integrateTo

  record PhysicalNSGalerkinTrajectory : Set₁ where
    constructor physical-ns-galerkin-trajectory
    field
      stateTrajectory : Base.PhysicalMixedHelicityTrajectory

      equationAt :
        (cutoff : Nat) (t : Time) →
        Audit.ExactProjectedGalerkinEquation
          (Base.systemAt stateTrajectory cutoff t)

      velocityCurveDerivative :
        (cutoff : Nat) (mode : Z3.FourierMode) →
        DerivativeOf
          (λ t →
            Audit.velocity
              (Base.systemAt stateTrajectory cutoff t)
              mode)
          (λ t →
            Audit.ExactProjectedGalerkinEquation.timeDerivative
              (equationAt cutoff t)
              mode)

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

  open PhysicalNSGalerkinTrajectory public

  forgetDynamics :
    PhysicalNSGalerkinTrajectory →
    Base.PhysicalMixedHelicityTrajectory
  forgetDynamics = stateTrajectory

  mixedHelicityMass :
    PhysicalNSGalerkinTrajectory → Nat → Time → ℚ
  mixedHelicityMass T = Base.mixedHelicityMass (forgetDynamics T)

  record PhysicalNSMixedHelicitySpacetimeBudget
      (T : PhysicalNSGalerkinTrajectory) : Set where
    constructor physical-ns-mixed-helicity-spacetime-budget
    field
      cutoffIndependentBound : Time → ℚ
      integratedMixedHelicityBound :
        (cutoff : Nat) (terminal : Time) →
        integrateTo (mixedHelicityMass T cutoff) terminal
        ≤ cutoffIndependentBound terminal

  open PhysicalNSMixedHelicitySpacetimeBudget public

  correctedBudgetForgetsToRound228 :
    (T : PhysicalNSGalerkinTrajectory) →
    PhysicalNSMixedHelicitySpacetimeBudget T →
    Base.PhysicalMixedHelicitySpacetimeBudget (forgetDynamics T)
  correctedBudgetForgetsToRound228 T B = record
    { cutoffIndependentBound = cutoffIndependentBound B
    ; integratedMixedHelicityBound = integratedMixedHelicityBound B
    }

round240Round228TrajectoryOwnsProjectedODE : Bool
round240Round228TrajectoryOwnsProjectedODE = false

round240Round228TrajectoryOwnsActualTimeDerivativeSemantics : Bool
round240Round228TrajectoryOwnsActualTimeDerivativeSemantics = false

round240CorrectedTrajectoryOwnsProjectedODE : Bool
round240CorrectedTrajectoryOwnsProjectedODE = true

round240CorrectedTrajectoryOwnsActualTimeDerivativeSemantics : Bool
round240CorrectedTrajectoryOwnsActualTimeDerivativeSemantics = true

round240CorrectedTrajectoryOwnsFixedViscosity : Bool
round240CorrectedTrajectoryOwnsFixedViscosity = true

round240CorrectedTrajectoryOwnsCommonInitialDatum : Bool
round240CorrectedTrajectoryOwnsCommonInitialDatum = true

round240OldMixedHelicityAlgebraReusableByForgetting : Bool
round240OldMixedHelicityAlgebraReusableByForgetting = true

round240CorrectedPhysicalSpacetimeBudgetClosed : Bool
round240CorrectedPhysicalSpacetimeBudgetClosed = false

round240PackageAClosed : Bool
round240PackageAClosed = false

round240ClayPromotion : Bool
round240ClayPromotion = false

round240Round228TrajectoryOwnsProjectedODEIsFalse :
  round240Round228TrajectoryOwnsProjectedODE ≡ false
round240Round228TrajectoryOwnsProjectedODEIsFalse = refl

round240Round228TrajectoryOwnsActualTimeDerivativeSemanticsIsFalse :
  round240Round228TrajectoryOwnsActualTimeDerivativeSemantics ≡ false
round240Round228TrajectoryOwnsActualTimeDerivativeSemanticsIsFalse = refl

round240CorrectedTrajectoryOwnsProjectedODEIsTrue :
  round240CorrectedTrajectoryOwnsProjectedODE ≡ true
round240CorrectedTrajectoryOwnsProjectedODEIsTrue = refl

round240CorrectedTrajectoryOwnsActualTimeDerivativeSemanticsIsTrue :
  round240CorrectedTrajectoryOwnsActualTimeDerivativeSemantics ≡ true
round240CorrectedTrajectoryOwnsActualTimeDerivativeSemanticsIsTrue = refl

round240OldMixedHelicityAlgebraReusableByForgettingIsTrue :
  round240OldMixedHelicityAlgebraReusableByForgetting ≡ true
round240OldMixedHelicityAlgebraReusableByForgettingIsTrue = refl

round240CorrectedPhysicalSpacetimeBudgetClosedIsFalse :
  round240CorrectedPhysicalSpacetimeBudgetClosed ≡ false
round240CorrectedPhysicalSpacetimeBudgetClosedIsFalse = refl

round240ClayPromotionIsFalse : round240ClayPromotion ≡ false
round240ClayPromotionIsFalse = refl
