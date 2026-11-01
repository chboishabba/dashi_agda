module DASHI.Physics.CliffordAssumptions where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ)

------------------------------------------------------------------------
-- Minimal abstract Clifford interface
------------------------------------------------------------------------

record VectorSpace : Set₁ where
  field
    V   : Set
    _+_ : V → V → V
    _·_ : ℤ → V → V

record BilinearForm (VS : VectorSpace) : Set₁ where
  open VectorSpace VS
  field
    B : V → V → ℤ
    bilinear : Set

record CliffordData (VS : VectorSpace) (BF : BilinearForm VS) : Set₁ where
  open VectorSpace VS
  open BilinearForm BF
  field
    Cl   : Set
    ι    : V → Cl
    mul  : Cl → Cl → Cl
    one  : Cl
    s∙   : ℤ → Cl

record CliffordGate {VS : VectorSpace} {BF : BilinearForm VS}
                    (C : CliffordData VS BF) : Set₁ where
  open VectorSpace VS
  open BilinearForm BF
  open CliffordData C
  field
    clifford : ∀ v → mul (ι v) (ι v) ≡ s∙ (B v v)
