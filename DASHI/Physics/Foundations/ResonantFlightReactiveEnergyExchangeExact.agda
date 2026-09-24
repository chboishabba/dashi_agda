module DASHI.Physics.Foundations.ResonantFlightReactiveEnergyExchangeExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Reactive exchange circulates energy among inertia/compliance/bus
-- without being identified with dissipative loss.
------------------------------------------------------------------------

data ReactiveStore : Set where
  wingInertia springCompliance pneumaticCompliance inertialBus : ReactiveStore

record ReactiveExchange : Set₁ where
  constructor reactive-exchange
  field
    EnergyState : ReactiveStore → Set
    transfer :
      (from to : ReactiveStore) →
      EnergyState from →
      EnergyState to

open ReactiveExchange public

record ReactiveCycle : Set₁ where
  constructor reactive-cycle
  field
    State : Set
    forward : State → State
    backward : State → State

open ReactiveCycle public

record ReactiveLossFirewall : Set where
  constructor reactive-loss-firewall
  field
    reactiveEqualsDissipative : Bool
    reactiveEqualsDissipativeIsFalse :
      reactiveEqualsDissipative ≡ false

open ReactiveLossFirewall public

canonicalReactiveLossFirewall : ReactiveLossFirewall
canonicalReactiveLossFirewall =
  reactive-loss-firewall false refl
