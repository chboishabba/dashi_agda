module DASHI.Algebra.Quantum.UVFinitenessHolographyTests where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.Nat using (_*_; _≤_)

------------------------------------------------------------------------
-- Abstract “region size” and counting (you will bind to poset balls / cones)
------------------------------------------------------------------------

postulate
  L : Set                  -- linear size parameter
  vol area : L -> Nat        -- discrete counts

postulate
  dimH : L -> Nat            -- effective Hilbert dimension / mode count
  eta  : Nat                  -- holographic proportionality constant

------------------------------------------------------------------------
-- Holographic area bound: dimH(L) ≤ η * area(L)
------------------------------------------------------------------------

AreaBound : Set
AreaBound = forall (l : L) -> dimH l ≤ (eta * area l)

------------------------------------------------------------------------
-- UV finiteness: bounded dim ⇒ no infinite UV tower
------------------------------------------------------------------------

record UVFinite : Set where
  field
    finiteModes : forall (l : L) -> Σ Nat (λ N -> dimH l ≤ N)

postulate
  UVFinitenessTheorem :
    AreaBound -> UVFinite
