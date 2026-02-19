module UVFinitenessHolographyTests where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

------------------------------------------------------------------------
-- Abstract “region size” and counting (you will bind to poset balls / cones)
------------------------------------------------------------------------

postulate
  L : Set                  -- linear size parameter
  vol area : L → Nat        -- discrete counts

postulate
  dimH : L → Nat            -- effective Hilbert dimension / mode count
  η  : Nat                  -- holographic proportionality constant

------------------------------------------------------------------------
-- Holographic area bound: dimH(L) ≤ η * area(L)
------------------------------------------------------------------------

postulate
  _≤_ : Nat → Nat → Set
  *   : Nat → Nat → Nat

AreaBound : Set
AreaBound = ∀ ℓ → dimH ℓ ≤ (η * area ℓ)

------------------------------------------------------------------------
-- UV finiteness: bounded dim ⇒ no infinite UV tower
------------------------------------------------------------------------

record UVFinite : Set where
  field
    finiteModes : ∀ ℓ → Σ Nat (λ N → dimH ℓ ≤ N)

UVFinitenessTheorem :
  AreaBound → UVFinite
UVFinitenessTheorem bound = {!!}
