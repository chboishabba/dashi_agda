module DASHI.Algebra.Quantum.SignatureDerivation where

open import DASHI.Core.Prelude
open import Data.Nat using (_>_; _*_; _∸_; _^_)

-- Using Nat as a placeholder
postulate _Nat² : Nat -> Nat
postulate a b : Nat
postulate scale : Nat -> Nat -> Nat

record CausalCounts : Set where
  field
    tau sigma : Nat

postulate
  F : CausalCounts -> Nat

postulate
  Homogeneous :
    forall (l : Nat) (x : CausalCounts) -> F x ≡ (l * l) * F x 

postulate
  ConeMonotone :
    forall (x : CausalCounts) ->
      CausalCounts.tau x > CausalCounts.sigma x -> F x > 0

postulate
  UniqueHyperbolic :
    forall (x : CausalCounts) ->
    F x ≡ (a * (CausalCounts.tau x ^ 2)) ∸ (b * (CausalCounts.sigma x ^ 2))
