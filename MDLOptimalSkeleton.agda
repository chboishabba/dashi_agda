module MDLOptimalSkeleton where

open import MDL
open import PrimeSubsetModel
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit using (⊤; tt)

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
