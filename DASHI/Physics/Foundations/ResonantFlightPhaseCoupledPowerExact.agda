module DASHI.Physics.Foundations.ResonantFlightPhaseCoupledPowerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ResonantFlightPowerSignExact as Sign
import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque369
import DASHI.Algebra.BalancedTernary as BT
import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Reasoning.TernarySynthesisCellComplexExact as Cells

------------------------------------------------------------------------
-- Phase-coupled power: torque and velocity are retained as separate
-- phase-indexed observables so their phase relation can be reasoned about
-- without collapsing everything into a single scalar sample.
------------------------------------------------------------------------

record PhaseCoupledPower : Set₁ where
  constructor phase-coupled-power
  field
    Phase Torque Velocity Power : Set
    torque : Phase → Torque
    velocity : Phase → Velocity
    instantaneousPower : Phase → Power
    sign : Phase → Sign.PowerSign

open PhaseCoupledPower public

data CouplingRegime : Set where
  direct resonant parametric regenerative reversal : CouplingRegime

record PhaseCouplingClassifier : Set₁ where
  constructor phase-coupling-classifier
  field
    Phase : Set
    regime : Phase → CouplingRegime

open PhaseCouplingClassifier public

record PhaseOffsetRelation : Set₁ where
  constructor phase-offset-relation
  field
    Phase Offset : Set
    offset : Phase → Phase → Offset

open PhaseOffsetRelation public

------------------------------------------------------------------------
-- Shared torque geometry.
--
-- Geometry may itself vary with oscillation phase.  The existing torque value
-- remains untouched; this merely exposes the same 369 / pants / C3 orientation
-- observers at each phase sample.
------------------------------------------------------------------------

phaseOrientedTorque :
  (power : PhaseCoupledPower) →
  (geometry : Phase power → Torque369.BracketVoxel) →
  (phase : Phase power) →
  Torque369.OrientedTorque (Torque power)
phaseOrientedTorque power geometry phase =
  Torque369.oriented-torque
    (geometry phase)
    (torque power phase)

phaseTorqueOrientation :
  (power : PhaseCoupledPower) →
  (geometry : Phase power → Torque369.BracketVoxel) →
  Phase power →
  BT.Trit
phaseTorqueOrientation power geometry phase =
  Torque369.orientedTorqueOrientation
    (phaseOrientedTorque power geometry phase)

phaseTorqueC3Phase :
  (power : PhaseCoupledPower) →
  (geometry : Phase power → Torque369.BracketVoxel) →
  Phase power →
  C3.C3Phase
phaseTorqueC3Phase power geometry phase =
  Torque369.orientedTorquePhase
    (phaseOrientedTorque power geometry phase)

phaseTorqueFace :
  (power : PhaseCoupledPower) →
  (geometry : Phase power → Torque369.BracketVoxel) →
  (phase : Phase power) →
  Cells.LocalSynthesisTwoCell
phaseTorqueFace power geometry phase =
  Torque369.orientedTorqueFace
    (phaseOrientedTorque power geometry phase)

------------------------------------------------------------------------
-- Structural sign facts for the two main power-flow directions.
------------------------------------------------------------------------

record DrivePhase : Set₁ where
  constructor drive-phase
  field
    Phase : Set
    at : Phase
    powerSign : Sign.PowerSign
    isPositive : powerSign ≡ Sign.positive

open DrivePhase public

record RegenerativePhase : Set₁ where
  constructor regenerative-phase
  field
    Phase : Set
    at : Phase
    powerSign : Sign.PowerSign
    isNegative : powerSign ≡ Sign.negative

open RegenerativePhase public
