{-# OPTIONS --safe #-}
module DASHI.Physics.Constraints.Bracket where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Constraints.Generators

record LieLike (CS : ConstraintSystem) : Set₁ where
  open ConstraintSystem CS
  field
    _[_,]_ : ConstraintSystem.Constraint CS →
             ConstraintSystem.Constraint CS →
             ConstraintSystem.Constraint CS
    antisym : Set
    jacobi  : Set
open LieLike public
