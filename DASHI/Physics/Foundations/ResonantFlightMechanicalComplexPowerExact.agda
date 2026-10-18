module DASHI.Physics.Foundations.ResonantFlightMechanicalComplexPowerExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Complex-power-like carrier for mechanics:
-- real-like component = net work, quadrature-like component = reactive
-- exchange. Kept structural so later numeric realizations may instantiate
-- concrete scalars/complex numbers.
------------------------------------------------------------------------

record MechanicalComplexPower : Set₁ where
  constructor mechanical-complex-power
  field
    Active Reactive : Set
    active : Active
    reactive : Reactive

open MechanicalComplexPower public

record MechanicalPhasor : Set₁ where
  constructor mechanical-phasor
  field
    Magnitude Phase : Set
    magnitude : Magnitude
    phase : Phase

open MechanicalPhasor public

record EffortFlowPhasorPair : Set₁ where
  constructor effort-flow-phasor-pair
  field
    Effort Flow : MechanicalPhasor
    ComplexPower : MechanicalComplexPower

open EffortFlowPhasorPair public

record MechanicalPowerFactor : Set₁ where
  constructor mechanical-power-factor
  field
    PhaseDifference Factor : Set
    factorFrom : PhaseDifference → Factor

open MechanicalPowerFactor public
