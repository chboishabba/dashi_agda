module Contraction where

open import Agda.Builtin.Equality
open import Data.Nat using (_<_)
open import Ultrametric as UMetric


------------------------------------------------------------------------
-- Contraction property (strict)

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
