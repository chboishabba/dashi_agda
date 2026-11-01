{-# OPTIONS --safe #-}
module DASHI.Geometry.UniqueInnerProduct where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.ParallelogramLaw

record InnerProduct (A : AdditiveSpace) : Set₁ where
  open AdditiveSpace A
  field
    ⟨_,_⟩ : AdditiveSpace.V A → AdditiveSpace.V A → Nat
open InnerProduct public

record InducesNorm (A : AdditiveSpace) (IP : InnerProduct A) (N : Normed A) : Set₁ where
  open AdditiveSpace A
  open InnerProduct IP
  open Normed N
  field
    induced : Set

record UniqueUpToScale : Set₁ where
  field
    statement : Set

record JordanVonNeumann : Set₁ where
  field
    fromParallelogram :
      ∀ {A : AdditiveSpace} {N : Normed A}
      → Parallelogram A N
      → Σ (InnerProduct A) (λ IP → InducesNorm A IP N)
    unique : UniqueUpToScale
