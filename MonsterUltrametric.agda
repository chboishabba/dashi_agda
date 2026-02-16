module MonsterUltrametric where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Data.Nat as Nat using (_<_; _≤_; zero; suc)
open import Data.Nat.Properties as NatP

open import Ultrametric
open import MonsterMask

------------------------------------------------------------------------
-- Distance = index of first differing bit (or 0 if identical)

firstDiff : Mask → Mask → Nat → Nat
firstDiff [] [] _ = 0
firstDiff (true  ∷ xs) (true  ∷ ys) n = firstDiff xs ys (suc n)
firstDiff (false ∷ xs) (false ∷ ys) n = firstDiff xs ys (suc n)
firstDiff _ _ n = n

dMask : Mask → Mask → Nat
dMask x y = firstDiff x y 0

firstDiff-self-zero : ∀ m n → firstDiff m m n ≡ 0
firstDiff-self-zero [] n = refl
firstDiff-self-zero (true ∷ xs) n = firstDiff-self-zero xs (suc n)
firstDiff-self-zero (false ∷ xs) n = firstDiff-self-zero xs (suc n)

------------------------------------------------------------------------
-- Identity distance

id-zeroMask : ∀ m → dMask m m ≡ 0
id-zeroMask m = firstDiff-self-zero m 0

------------------------------------------------------------------------
-- Symmetry

postulate
  symMask : ∀ x y → dMask x y ≡ dMask y x
  ultraMask : ∀ x y z → dMask x z ≤ max (dMask x y) (dMask y z)

------------------------------------------------------------------------

UMask : Ultrametric Mask
UMask = record
  { d            = dMask
  ; id-zero      = id-zeroMask
  ; symmetric    = symMask
  ; ultratriangle = ultraMask
  }
