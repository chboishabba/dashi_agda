module DASHI.Algebra.Quantum.SignatureDerivation where

open import DASHI.Core.Prelude
open import Data.Nat using (_>_; _*_; _∸_; _^_)

record CausalCounts : Set where
  field
    tau sigma : Nat

record SignatureDerivationAxioms : Set₁ where
  field
    _Nat² : Nat → Nat
    a b : Nat
    scale : Nat → Nat → Nat
    F : CausalCounts → Nat

    Homogeneous :
      ∀ l (x : CausalCounts) → F x ≡ (l * l) * F x

    ConeMonotone :
      ∀ (x : CausalCounts) →
        CausalCounts.tau x > CausalCounts.sigma x → F x > 0

    UniqueHyperbolic :
      ∀ (x : CausalCounts) →
        F x ≡ (a * (CausalCounts.tau x ^ 2)) ∸ (b * (CausalCounts.sigma x ^ 2))

open SignatureDerivationAxioms public
