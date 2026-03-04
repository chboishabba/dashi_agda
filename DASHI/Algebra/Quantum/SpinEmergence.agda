module DASHI.Algebra.Quantum.SpinEmergence where

open import Data.Nat renaming (ℕ to Nat)

record SpinEmergenceAxioms : Set₂ where
  field
    QuadraticForm : Set
    Signature31 : QuadraticForm
    CliffordAlgebra : QuadraticForm → Set₁
    SpinGroup : Set₁
    SO : Nat → Nat → Set
    SpinIsDoubleCover : SpinGroup → SO 3 1

open SpinEmergenceAxioms public
