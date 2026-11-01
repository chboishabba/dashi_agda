module Contraction where

open import Agda.Builtin.Equality
open import Data.Empty using (⊥)
open import Data.Nat using (_<_)
open import Ultrametric as UMetric


------------------------------------------------------------------------
-- Contraction property (strict)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record Contractive
       {S : Set}
       (U : UMetric.Ultrametric S)
       (K : S → S)
       : Set where

  open UMetric.Ultrametric U

  field
    contraction :
      ∀ x y →
      d (K x) (K y) < d x y

-- Contractive on distinct points (avoids x=x degenerate case).
record Contractive≢
       {S : Set}
       (U : UMetric.Ultrametric S)
       (K : S → S)
       : Set where

  open UMetric.Ultrametric U

  field
    contraction≢ :
      ∀ {x y} → x ≢ y →
      d (K x) (K y) < d x y

-- Strict contraction plus a specified unique fixed point.
record StrictContraction
       {S : Set}
       (U : UMetric.Ultrametric S)
       (K : S → S)
       : Set where

  field
    contractive≢ : Contractive≢ U K
    fp : S
    fixed : K fp ≡ fp
    unique : ∀ x → K x ≡ x → x ≡ fp
