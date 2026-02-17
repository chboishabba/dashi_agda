module DASHI.String.LieAlgebra where

open import Agda.Builtin.Equality

record LieAlgebra : Set₁ where
  field
    Carrier : Set
    [_ , _] : Carrier → Carrier → Carrier

    antisym :
      ∀ x y →
      [ x , y ] ≡ [ y , x ] → ⊥

    jacobi :
      ∀ x y z →
      [ x , [ y , z ] ]
      ≡
      [ [ x , y ] , z ]
