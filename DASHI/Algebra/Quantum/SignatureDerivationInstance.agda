module DASHI.Algebra.Quantum.SignatureDerivationInstance where

open import Data.Nat using (Nat; _*_; _∸_; _^_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Algebra.Quantum.SignatureDerivation

-- Concrete hyperbolic form on scalar (tau,sigma) counts.
Nat² : Nat → Nat
Nat² n = n ^ 2

a b : Nat
a = suc zero
b = suc zero

scale : Nat → Nat → Nat
scale x y = x * y

F : CausalCounts → Nat
F x = (a * (CausalCounts.tau x ^ 2)) ∸ (b * (CausalCounts.sigma x ^ 2))

-- Build a SignatureDerivationAxioms instance by supplying the remaining proofs.
-- This keeps the formulas concrete while leaving the actual properties to be discharged.
mkSignatureDerivation :
  (hom : ∀ l (x : CausalCounts) → F x ≡ (l * l) * F x) →
  (cone : ∀ x → CausalCounts.tau x > CausalCounts.sigma x → F x > 0) →
  SignatureDerivationAxioms
mkSignatureDerivation hom cone =
  record
    { _Nat² = Nat²
    ; a = a
    ; b = b
    ; scale = scale
    ; F = F
    ; Homogeneous = hom
    ; ConeMonotone = cone
    ; UniqueHyperbolic = λ x → refl
    }
