module DASHI.String.StringCompatibility where

open import DASHI.String.Unitary
open import DASHI.String.LieAlgebra
open import DASHI.String.Compatibility

record StringCompatible : Set₁ where
  field
    admitsUnitary :
      ∃ λ H → Unitary H

    admitsLie :
      CentralExtension

    noForcedContraction :
      ⊤
