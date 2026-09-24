module DASHI.Physics.Foundations.ResonantFlightParametricPumpingExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Direct forcing changes generalized effort.  Parametric pumping changes
-- oscillator parameters such as stiffness or equilibrium.
------------------------------------------------------------------------

record DirectForcing : Set₁ where
  constructor direct-forcing
  field
    Phase Force : Set
    appliedForce : Phase → Force

open DirectForcing public

record ParametricPump : Set₁ where
  constructor parametric-pump
  field
    Phase Stiffness Equilibrium : Set
    stiffness : Phase → Stiffness
    equilibrium : Phase → Equilibrium

open ParametricPump public

record TunableParametricPump : Set₁ where
  constructor tunable-parametric-pump
  field
    Control Phase Stiffness Equilibrium : Set
    stiffness : Control → Phase → Stiffness
    equilibrium : Control → Phase → Equilibrium

open TunableParametricPump public

------------------------------------------------------------------------
-- Explicit firewall: changing stiffness/equilibrium is not the same
-- operation as prescribing an external force.
------------------------------------------------------------------------

record ForcingParametricFirewall : Set where
  constructor forcing-parametric-firewall
  field
    directEqualsParametric : Bool
    directEqualsParametricIsFalse : directEqualsParametric ≡ false

open ForcingParametricFirewall public

canonicalForcingParametricFirewall : ForcingParametricFirewall
canonicalForcingParametricFirewall =
  forcing-parametric-firewall false refl
