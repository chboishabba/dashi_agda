module DASHI.Physics.CliffordRepresentationCompletion where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ; +_)

open import DASHI.Physics.LorentzianCoreClosure as LCC

------------------------------------------------------------------------
-- Clifford representation existence over the concrete masked core.

record OperatorRing : Set₁ where
  field
    Op : Set
    zero one : Op
    _+_ _*_ : Op → Op → Op
    scalar : ℤ → Op

record CliffordRepresentation (R : OperatorRing) : Set₁ where
  open OperatorRing R
  field
    gamma : LCC.Core4 → Op

    -- Full anticommutator law, stronger than only gamma(v)^2 = Q(v).
    anticommutator : ∀ x y →
      (gamma x * gamma y) + (gamma y * gamma x)
        ≡ scalar (LCC.B₂₄ x y)

    squareLaw : ∀ x →
      gamma x * gamma x ≡ scalar ((+ 2) * LCC.Q₄ x)

record CliffordExistence : Set₁ where
  field
    operators : OperatorRing
    representation : CliffordRepresentation operators

open CliffordExistence public
