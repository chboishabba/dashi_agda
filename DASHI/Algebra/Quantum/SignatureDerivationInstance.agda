module DASHI.Algebra.Quantum.SignatureDerivationInstance where

open import Data.Nat using (ℕ; _*_; _∸_; _^_; _>_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Algebra.Quantum.SignatureDerivation

-- Concrete hyperbolic form on scalar (tau,sigma) counts.
Nat² : ℕ → ℕ
Nat² = _^_ 2

a₀ b₀ : ℕ
a₀ = suc zero
b₀ = suc zero

scale₀ : ℕ → ℕ → ℕ
scale₀ x y = x * y

F₀ : CausalCounts → ℕ
F₀ x = (a₀ * (CausalCounts.tau x ^ 2)) ∸ (b₀ * (CausalCounts.sigma x ^ 2))

-- Build a SignatureDerivationAxioms instance by supplying the remaining proofs.
-- This keeps the formulas concrete while leaving the actual properties to be discharged.
mkSignatureDerivation :
  (hom : ∀ l (x : CausalCounts) → F₀ x ≡ (l * l) * F₀ x) →
  (cone : ∀ x → CausalCounts.tau x > CausalCounts.sigma x → F₀ x > 0) →
  SignatureDerivationAxioms
mkSignatureDerivation hom cone =
  record
    { _Nat² = Nat²
    ; a = a₀
    ; b = b₀
    ; scale = scale₀
    ; F = F₀
    ; Homogeneous = hom
    ; ConeMonotone = cone
    ; UniqueHyperbolic = λ x → refl
    }
