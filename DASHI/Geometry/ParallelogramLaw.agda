{-# OPTIONS --safe #-}
module DASHI.Geometry.ParallelogramLaw where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Nat using (Nat)

record AdditiveSpace : Set₁ where
  field
    V    : Set
    _+_  : V → V → V
    -_   : V → V
    0#   : V
open AdditiveSpace public

record Normed (A : AdditiveSpace) : Set₁ where
  open AdditiveSpace A
  field
    ∥_∥² : AdditiveSpace.V A → Nat
open Normed public

record Parallelogram (A : AdditiveSpace) (N : Normed A) : Set₁ where
  open AdditiveSpace A
  open Normed N
  field
    paral : Set
