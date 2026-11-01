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

record AddCommMonoid (A : Set) : Set₁ where
  field
    _+_ : A → A → A
    0#  : A
    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-comm  : ∀ x y → x + y ≡ y + x
    +-id    : ∀ x → x + 0# ≡ x

record HasNeg (A : Set) : Set₁ where
  field
    -_ : A → A
    sub : A → A → A
    subdef : ∀ x y → sub x y ≡ sub x y

record ParallelogramEnergy (A : Set) (M : AddCommMonoid A) (N : HasNeg A) : Set₁ where
  open AddCommMonoid M
  open HasNeg N
  field
    E : A → Set
    parallelogram :
      ∀ x y → E (AddCommMonoid._+_ M x y) → E (HasNeg.sub N x y) → E x → E y
