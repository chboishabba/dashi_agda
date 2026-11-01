module DASHI.Geometry.FiberContraction where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Ultrametric as UMetric
open import Data.Nat using (_<_)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record FiberDistinct {S : Set} (P : S → S) (x y : S) : Set where
  field
    x≢y : x ≢ y
    sameFiber : P x ≡ P y

record ContractiveOnFibers
       {S : Set}
       (U : UMetric.Ultrametric S)
       (P : S → S)
       : Set₁ where

  open UMetric.Ultrametric U

  field
    contractFiber :
      ∀ {x y} → FiberDistinct P x y →
      d (P x) (P y) < d x y
