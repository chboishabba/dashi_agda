module DASHI.Combinatorics.String.StringCompatibility where

open import DASHI.Combinatorics.String.Unitary
open import DASHI.Combinatorics.String.LieAlgebra
open import DASHI.Combinatorics.String.Compatibility
open import DASHI.Combinatorics.String.HilbertToy
open import Agda.Builtin.Sigma
open import Data.Unit using (⊤)

record StringCompatibilityAxioms : Set₁ where
  field
    CentralExtension : Set

open StringCompatibilityAxioms public

record StringCompatible (A : StringCompatibilityAxioms) : Set₁ where
  field
    admitsUnitary :
      Σ InnerProductSpace (λ H → Unitary H)

    admitsLie :
      CentralExtension A

    noForcedContraction :
      ⊤
