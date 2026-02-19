module DASHI.Algebra.Quantum.SpinEmergence where

open import Data.Nat renaming (ℕ to Nat)

postulate
  QuadraticForm : Set
  Signature31 : QuadraticForm

postulate
  CliffordAlgebra : QuadraticForm → Set₁

postulate
  SpinGroup : Set₁ -- Represents the type of spin group for Signature31

postulate
  SO : Nat → Nat → Set

postulate
  SpinIsDoubleCover :
    SpinGroup → SO 3 1
