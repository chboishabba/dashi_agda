{-# OPTIONS --allow-unsolved-metas #-}
module DASHI.Combinatorics.String.Compatibility where

open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Equality

-- The compatibility predicate you want to enforce for operations, e.g. "same length"
record StringCompatibility (A : Set) : Set₁ where
  field
    compatible : String → String → Set