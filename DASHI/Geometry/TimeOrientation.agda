{-# OPTIONS --safe #-}
module DASHI.Geometry.TimeOrientation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

record TimeOrientation {S : Set} (T : S → S) : Set₁ where
  field
    Lyap : S → Nat
    mono : ∀ s → Lyap (T s) ≤ Lyap s
    strictUnlessFixed : Set
open TimeOrientation public
