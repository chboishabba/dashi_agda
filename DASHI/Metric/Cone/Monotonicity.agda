{-# OPTIONS --safe #-}

module DASHI.Metric.Cone.Monotonicity where

open import Relation.Binary.PropositionalEquality using (_≡_)

record Ultrametric (X D : Set) : Set₁ where
  field
    d : X → X → D

record ConeMono {X D : Set}
  (U : Ultrametric X D) (T : X → X)
  : Set₁ where
  field
    _≤_ : D → D → Set
    NonZero : D → Set
    mono : ∀ {x y} → NonZero (Ultrametric.d U x y) →
      _≤_ (Ultrametric.d U (T x) (T y)) (Ultrametric.d U x y)
