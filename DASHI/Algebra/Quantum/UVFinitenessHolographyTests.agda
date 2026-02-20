module DASHI.Algebra.Quantum.UVFinitenessHolographyTests where

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_*_; _≤_)
open import DASHI.Algebra.Quantum.UVFiniteness public

------------------------------------------------------------------------
-- Abstract “region size” and counting (bound supplied by the user)
------------------------------------------------------------------------

postulate
  L : Set                  -- linear size parameter
  vol area : L -> Nat      -- discrete counts
  dimH : L -> Nat          -- effective Hilbert dimension / mode count
  eta  : Nat               -- holographic proportionality constant

------------------------------------------------------------------------
-- Holographic area bound: dimH(L) ≤ η * area(L)
------------------------------------------------------------------------

AreaBound : Set
AreaBound = ∀ (l : L) -> dimH l ≤ (eta * area l)

------------------------------------------------------------------------
-- UV finiteness: bounded dim ⇒ no infinite UV tower
------------------------------------------------------------------------

UVFinitenessTheorem :
  (areaBound : AreaBound) →
  UVFinite (record
    { L = L
    ; dimH = dimH
    ; bound = λ l → eta * area l
    ; dimH≤bound = areaBound
    })
UVFinitenessTheorem areaBound =
  let bounded = record
        { L = L
        ; dimH = dimH
        ; bound = λ l → eta * area l
        ; dimH≤bound = areaBound
        }
  in uvFiniteness bounded
