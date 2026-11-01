module DASHI.Algebra.Quantum.UVFinitenessHolographyTests where

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_*_; _≤_)
open import DASHI.Algebra.Quantum.UVFiniteness public

record UVFinitenessAxioms : Set₁ where
  field
    L : Set                  -- linear size parameter
    vol area : L → Nat        -- discrete counts
    dimH : L → Nat            -- effective Hilbert dimension / mode count
    eta  : Nat               -- holographic proportionality constant

open UVFinitenessAxioms public

AreaBound : UVFinitenessAxioms → Set
AreaBound A = ∀ l → dimH A l ≤ (eta A * area A l)

UVFinitenessTheorem :
  (A : UVFinitenessAxioms) →
  (areaBound : AreaBound A) →
  UVFinite (record
    { L = L A
    ; dimH = dimH A
    ; bound = λ l → eta A * area A l
    ; dimH≤bound = areaBound
    })
UVFinitenessTheorem A areaBound =
  let bounded = record
        { L = L A
        ; dimH = dimH A
        ; bound = λ l → eta A * area A l
        ; dimH≤bound = areaBound
        }
  in uvFiniteness bounded
