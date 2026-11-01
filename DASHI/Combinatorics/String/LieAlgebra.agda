module DASHI.Combinatorics.String.LieAlgebra where

open import Agda.Builtin.Equality
open import Data.Empty using (⊥)

record LieAlgebra : Set₁ where
  field
    Carrier : Set
    _bracket_ : Carrier → Carrier → Carrier

    antisym :
      ∀ x y →
      (x bracket y) ≡ (y bracket x) → ⊥

    jacobi :
      ∀ x y z →
      (x bracket (y bracket z))
      ≡
      ((x bracket y) bracket z)
