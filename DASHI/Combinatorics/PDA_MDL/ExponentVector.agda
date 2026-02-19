module DASHI.Combinatorics.PDA_MDL.ExponentVector where

open import DASHI.Combinatorics.PDA_MDL.Prelude
open import Data.Vec using (Vec; []; _∷_; map; zipWith; foldr′)
open import Data.Fin using (Fin)
open import Agda.Builtin.Nat using (Nat; zero; suc)

add : Nat → Nat → Nat
add zero    n = n
add (suc m) n = suc (add m n)

-- 15-lane exponent vector
EV : Set
EV = Vec Nat 15

-- pointwise addition (useful for sufficient statistics)
_⊞_ : ∀ {n} → Vec Nat n → Vec Nat n → Vec Nat n
_⊞_ {zero} [] [] = []
_⊞_ {suc n} (x ∷ xs) (y ∷ ys) = add x y ∷ (_⊞_ {n} xs ys)

-- pointwise max (sometimes useful)
max : Nat → Nat → Nat
max zero    n       = n
max (suc m) zero    = suc m
max (suc m) (suc n) = suc (max m n)

_⊔v_ : EV → EV → EV
_⊔v_ = zipWith max

sumEV : EV → Nat
sumEV = foldr′ add zero

-- A dataset is a list of exponent vectors
DatasetEV : Set
DatasetEV = List EV

stats : DatasetEV → EV
stats []       = map (λ _ → 0) (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
stats (x ∷ xs) = x ⊞ stats xs
