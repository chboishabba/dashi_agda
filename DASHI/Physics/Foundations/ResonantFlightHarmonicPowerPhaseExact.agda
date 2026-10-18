module DASHI.Physics.Foundations.ResonantFlightHarmonicPowerPhaseExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Harmonic phase relation between generalized effort and generalized flow.
------------------------------------------------------------------------

record HarmonicEffortFlow : Set₁ where
  constructor harmonic-effort-flow
  field
    Amplitude Phase : Set
    effortAmplitude flowAmplitude : Amplitude
    effortPhase flowPhase : Phase

open HarmonicEffortFlow public

record PhaseDifferenceLaw : Set₁ where
  constructor phase-difference-law
  field
    Phase Difference : Set
    difference : Phase → Phase → Difference

open PhaseDifferenceLaw public

record AverageReactivePowerLaw : Set₁ where
  constructor average-reactive-power-law
  field
    Amplitude Difference Active Reactive : Set
    activeFrom :
      Amplitude → Amplitude → Difference → Active
    reactiveFrom :
      Amplitude → Amplitude → Difference → Reactive

open AverageReactivePowerLaw public

record HarmonicPowerDecomposition : Set₁ where
  constructor harmonic-power-decomposition
  field
    Active Reactive Apparent : Set
    active : Active
    reactive : Reactive
    apparent : Apparent

open HarmonicPowerDecomposition public

------------------------------------------------------------------------
-- Structural interpretation:
-- active power is cycle-net transfer; reactive power is reversible
-- storage/exchange within the oscillator network.
------------------------------------------------------------------------

data PowerComponentRole : Set where
  netTransfer reversibleExchange : PowerComponentRole

activePowerRole : PowerComponentRole
activePowerRole = netTransfer

reactivePowerRole : PowerComponentRole
reactivePowerRole = reversibleExchange
