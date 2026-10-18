module DASHI.Physics.Foundations.ResonantFlightImpedancePowerBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ResonantFlightMechanicalImpedanceExact as Imp
import DASHI.Physics.Foundations.ResonantFlightHarmonicPowerPhaseExact as Harm
import DASHI.Physics.Foundations.ResonantFlightMechanicalComplexPowerExact as CP

------------------------------------------------------------------------
-- The bridge records the shared decomposition:
-- resistive/in-phase -> net transfer
-- reactive/quadrature -> reversible storage.
------------------------------------------------------------------------

record ImpedancePowerBridge : Set₁ where
  constructor impedance-power-bridge
  field
    Resistive Reactive Active ReactivePower : Set
    resistiveToActive : Resistive → Active
    reactiveToReactivePower : Reactive → ReactivePower

open ImpedancePowerBridge public

record MatchedMechanicalPowerState : Set₁ where
  constructor matched-mechanical-power-state
  field
    SourceImpedance LoadImpedance ActivePower ReactivePower : Set
    source : SourceImpedance
    load : LoadImpedance
    activePower : ActivePower
    reactivePower : ReactivePower

open MatchedMechanicalPowerState public

------------------------------------------------------------------------
-- Explicit domain firewall retained: this is a structural bridge between
-- impedance and power decomposition, not a claim that mechanics and RF
-- are physically identical.
------------------------------------------------------------------------

record ImpedancePowerDomainFirewall : Set where
  constructor impedance-power-domain-firewall
  field
    structuralAnalogyImpliesPhysicalIdentity : Bool
    structuralAnalogyImpliesPhysicalIdentityIsFalse :
      structuralAnalogyImpliesPhysicalIdentity ≡ false

open ImpedancePowerDomainFirewall public

canonicalImpedancePowerDomainFirewall :
  ImpedancePowerDomainFirewall
canonicalImpedancePowerDomainFirewall =
  impedance-power-domain-firewall false refl
