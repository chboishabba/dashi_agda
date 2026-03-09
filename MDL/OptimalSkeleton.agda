module MDL.OptimalSkeleton where

open import MDL.Core.Core
open import MDL.PrimeSubsetModel
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (_≤_)

------------------------------------------------------------------------
-- Search space abstraction

record ModelFamily (D : Dataset) : Set₁ where
  field
    candidate : Nat → PrimeModel D

------------------------------------------------------------------------
-- Minimality condition

isMinimal :
  ∀ {D}
  (F : ModelFamily D)
  (k : Nat)
  →
  (∀ n → primeTotal (ModelFamily.candidate F k)
          ≤ primeTotal (ModelFamily.candidate F n))
  →
  Set

isMinimal F k proof = ⊤
