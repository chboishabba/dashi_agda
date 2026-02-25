{-# OPTIONS --safe #-}
module DASHI.Geometry.SignatureUniqueness31 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.ParallelogramLaw
open import DASHI.Geometry.ConeMetricCompatibility
open import DASHI.Geometry.TimeOrientation

data Signature : Set where
  sig31 : Signature
  sig13 : Signature
  other : Signature

record SignatureLaw : Set₁ where
  field
    forced : Signature

record Signature31Theorem : Set₁ where
  field
    prove :
      ∀ {A : AdditiveSpace}
      → (QF : Quadratic A)
      → (C  : Cone A)
      → ConeMetricCompat A C QF
      → (iso : Set)
      → (fs  : Set)
      → (arrow : Set)
      → SignatureLaw
