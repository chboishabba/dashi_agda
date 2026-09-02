module DASHI.Physics.Closure.NSTriadKNLiteralTrajectoryMixedCellDerivativeRound427Exact where

------------------------------------------------------------------------
-- ROUND427 / ROUND408 LITERAL NS TRAJECTORY -> ACTUAL R224 CELL DERIVATIVE
--
-- R408 supplies, for every retained mode, the actual derivative of the live
-- Galerkin velocity curve and identifies it with the literal Round30 RHS.
-- R426 says two modal derivative witnesses are sufficient to differentiate the
-- literal plus-minus mixed-helicity cell by the projected cross product rule.
--
-- This file composes those owners on the SAME live trajectory.  The tangent is
-- not caller-selected: it is R292.cellTangent evaluated on the literal R30 RHS
-- of R408's physicalSystemAt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCellDampedTangentRound292Exact as R292
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426

F : C3.RealField _
F = Rational.rationalRealField

module LiteralCellDynamics
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (C : R426.ProjectedCrossDerivativeCalculus Time DerivativeOf) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Base = Live.Base
  module Cell = R426.ActualMixedCell Time DerivativeOf C

  liveVelocity :
    (D : Live.LiteralRHSTrajectoryData) →
    Nat → Time → Z3.FourierMode → C3.Complex3 F
  liveVelocity D cutoff time mode =
    Audit.velocity
      (Base.systemAt
        (Live.stateTrajectory (Live.support D)) cutoff time)
      mode

  literalRHSTangent :
    (D : Live.LiteralRHSTrajectoryData) →
    Nat → Time → Z3.FourierMode → C3.Complex3 F
  literalRHSTangent D cutoff time mode =
    R30.literalViscousQuadraticCoefficient
      (Live.physicalSystemAt (Live.support D) cutoff time)
      mode

  literalMixedCellCurve :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    Nat → Physical.PhysicalTriadIncidence →
    Time → C3.Complex3 F
  literalMixedCellCurve D S cutoff tau =
    Cell.literalMixedCellCurve
      {E = Base.E (Live.stateTrajectory (Live.support D))}
      {I = Base.I (Live.stateTrajectory (Live.support D))}
      S (liveVelocity D cutoff) tau

  literalMixedCellTangentCurve :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    Nat → Physical.PhysicalTriadIncidence →
    Time → C3.Complex3 F
  literalMixedCellTangentCurve D S cutoff tau =
    Cell.literalMixedCellTangentCurve
      {E = Base.E (Live.stateTrajectory (Live.support D))}
      {I = Base.I (Live.stateTrajectory (Live.support D))}
      S (liveVelocity D cutoff) (literalRHSTangent D cutoff) tau

  round408BuildsActualMixedCellDerivative :
    (D : Live.LiteralRHSTrajectoryData) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (tau : Physical.PhysicalTriadIncidence) →
    DerivativeOf
      (literalMixedCellCurve D S cutoff tau)
      (literalMixedCellTangentCurve D S cutoff tau)
  round408BuildsActualMixedCellDerivative D S cutoff tau =
    Cell.modalDerivativesBuildLiteralMixedCellDerivative
      {E = Base.E (Live.stateTrajectory (Live.support D))}
      {I = Base.I (Live.stateTrajectory (Live.support D))}
      S
      (liveVelocity D cutoff)
      (literalRHSTangent D cutoff)
      tau
      (Live.velocityDerivativeIsLiteralRHS D cutoff (Physical.p tau))
      (Live.velocityDerivativeIsLiteralRHS D cutoff (Physical.q tau))

round427UsesActualRound408VelocityDerivative : Bool
round427UsesActualRound408VelocityDerivative = true

round427MixedCellIsLiteralR224Carrier : Bool
round427MixedCellIsLiteralR224Carrier = true

round427TangentIsR292OnLiteralRound30RHS : Bool
round427TangentIsR292OnLiteralRound30RHS = true

round427ActualPlusMinusCellDifferentiationClosedModuloStandardCalculus : Bool
round427ActualPlusMinusCellDifferentiationClosedModuloStandardCalculus = true

round427NewNavierStokesEstimateIntroduced : Bool
round427NewNavierStokesEstimateIntroduced = false
