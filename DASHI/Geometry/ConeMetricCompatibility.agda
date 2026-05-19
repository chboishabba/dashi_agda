{-# OPTIONS --safe #-}
module DASHI.Geometry.ConeMetricCompatibility where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.ParallelogramLaw

record Cone (A : AdditiveSpace) : Set₁ where
  open AdditiveSpace A
  field
    InCone : AdditiveSpace.V A → Set
open Cone public

record Quadratic (A : AdditiveSpace) : Set₁ where
  open AdditiveSpace A
  field
    Scalar : Set
    Q : AdditiveSpace.V A → Scalar
open Quadratic public

record ConeMetricCompat (A : AdditiveSpace) (C : Cone A) (QF : Quadratic A) : Set₁ where
  open AdditiveSpace A
  open Quadratic QF
  field
    compat : AdditiveSpace.V A → Set
    cone⇒compat : ∀ x → Cone.InCone C x → compat x
