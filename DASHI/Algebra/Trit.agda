{-# OPTIONS --safe #-}
module DASHI.Algebra.Trit where

open import Agda.Builtin.Equality using (_≡_; refl)

data Trit : Set where
  neg : Trit
  zer : Trit
  pos : Trit

inv : Trit → Trit
inv neg = pos
inv zer = zer
inv pos = neg

inv-invol : ∀ t → inv (inv t) ≡ t
inv-invol neg = refl
inv-invol zer = refl
inv-invol pos = refl

