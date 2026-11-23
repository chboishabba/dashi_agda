module DASHI.Physics.Foundations.ResonantFlightPhaseCoupledPowerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ResonantFlightPowerSignExact as Sign

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
