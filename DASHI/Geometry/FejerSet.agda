{-# OPTIONS --safe #-}

module DASHI.Geometry.FejerSet where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Metric (A : Set) : Set₁ where
  field
    d     : A → A → Set
    refl  : ∀ x → d x x
    sym   : ∀ x y → d x y → d y x
    tri   : ∀ x y z → d x z → d x y → d y z

record FixSet {A : Set} (P : A → A) : Set₁ where
  field
    Fix : A → Set
    fixP : ∀ {x} → Fix x → P x ≡ x

record FejerToSet {A : Set} (M : Metric A) (P : A → A) (S : A → Set) : Set₁ where
  open Metric M
  field
    fejer : ∀ x y → S y → d (P x) y → d x y
