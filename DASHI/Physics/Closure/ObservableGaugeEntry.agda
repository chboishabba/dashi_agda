module DASHI.Physics.Closure.ObservableGaugeEntry where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.ObservableTransportGaugeEntry
  using (ObservableTransportGaugeEntry)

------------------------------------------------------------------------
-- Minimal observable gauge entry lane.
--
-- This module stays abstract: it names an observable, a gauge fiber over that
-- observable, a state space, and a gauge action, together with the two laws
-- requested by the entry-lane interface.
--
-- See also:
--   DASHI.Physics.Closure.ObservableTransportGaugeEntry

record ObservableGaugeEntry
  {ℓO ℓF ℓS ℓG ℓA : Level}
    : Set (lsuc (ℓO ⊔ ℓF ⊔ ℓS ⊔ ℓG ⊔ ℓA)) where
  field
    Observable : Set ℓO
    GaugeFiber : Observable → Set ℓF
    State : Set ℓS
    G : Set ℓG

    obs : State → Observable
    gaugeFiber : (x : State) → GaugeFiber (obs x)
    GaugeAction : G → State → State
    admissible : State → Set ℓA

    obs-preserved :
      ∀ g x →
      obs (GaugeAction g x) ≡ obs x

    admissibility-preserved :
      ∀ g x →
      admissible x →
      admissible (GaugeAction g x)

open ObservableGaugeEntry public
