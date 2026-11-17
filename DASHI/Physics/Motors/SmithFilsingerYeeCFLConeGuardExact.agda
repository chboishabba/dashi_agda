module DASHI.Physics.Motors.SmithFilsingerYeeCFLConeGuardExact where

-- F02 explicit logical firewall: Yee CFL stability != continuum light cone.
-- The physical speed of the numerical stencil is dx/dt, which can be
-- GREATER than c when dt is made smaller at fixed dx.
-- At 3D uniform spacing, c*dt*sqrt(3)<=dx is a stability requirement,
-- not a derivation of physical propagation support <= c*dt.
--
-- No original source geometry, light cone, discrete Maxwell update or
-- ionosphere Green operator is claimed.

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port

-- Integer units: c=1, dt=1, dx=4.
-- Stable one-dimensional Courant inequality 1<=4 holds; a one-cell
-- stencil dependency can be 4 distance units away after one time step.
-- Thus "numerical dependency contained in physical cone" is FALSE.
stencilCanSatisfyCourantStability : Bound._≤_ 1 4
stencilCanSatisfyCourantStability =
  Bound.s≤s Bound.z≤n

stencilNeighborIsOutsidePhysicalFront :
  Bound._≤_ 4 1 → Port.Contradiction
stencilNeighborIsOutsidePhysicalFront (Bound.s≤s ())

-- Physical front speed is an INDEPENDENT quantitative admission.
-- A bound on maximum numerical graph-distance in N steps is a statement
-- about the scheme's dependency support, not about real electromagnetic
-- energy/information propagation in an arbitrary material.
record CalibratedPhysicalCone (distance speed elapsed : Nat) : Set where
  constructor calibratedPhysicalCone
  field
    measuredOrProvenMaxwellFront :
      Bound._≤_ distance (speed * elapsed)

physicalFrontBoundRequiresAdmission :
  (distance speed elapsed : Nat) →
  CalibratedPhysicalCone distance speed elapsed →
  Bound._≤_ distance (speed * elapsed)
physicalFrontBoundRequiresAdmission d c t proof =
  CalibratedPhysicalCone.measuredOrProvenMaxwellFront proof

-- The actual F02 target requires the Maxwell retarded propagator support
-- theorem, not an arbitrary Cell.clock index or CFL mesh restriction.
