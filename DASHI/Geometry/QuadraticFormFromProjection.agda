{-# OPTIONS --safe #-}
module DASHI.Geometry.QuadraticFormFromProjection where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.ParallelogramLaw

record ProjectionDefect (A : AdditiveSpace) : Set₁ where
  open AdditiveSpace A
  field
    P      : AdditiveSpace.V A → AdditiveSpace.V A
    D      : AdditiveSpace.V A → AdditiveSpace.V A
    split  : ∀ x → x ≡ AdditiveSpace._+_ A (P x) (D x)
    noLeak : Set
open ProjectionDefect public

record QuadraticOutput : Set₁ where
  field
    A : AdditiveSpace
    Q : AdditiveSpace.V A → Nat
    parallelogram : Parallelogram A (record { ∥_∥² = Q })
open QuadraticOutput public

record QuadraticFromProjection : Set₁ where
  field
    build :
      ∀ {A : AdditiveSpace}
      → (PD : ProjectionDefect A)
      → QuadraticOutput
