module DASHI.Quantum.NoGlobalAttractor where

open import DASHI.Prelude
open import DASHI.OperatorTypes

-- Iteration
iterate : ∀ {S : Set} → (S → S) → Nat → S → S
iterate f zero    x = x
iterate f (suc n) x = iterate f n (f x)

-- “Eventually constant” orbit at a.
EventuallyConst : ∀ {S : Set} → (S → S) → S → S → Set
EventuallyConst f x a = Σ Nat (λ N → ∀ n → iterate f (N + n) x ≡ a)

-- Global attractor = same a for all x.
GlobalAttractor : ∀ {S : Set} → (S → S) → Set
GlobalAttractor f = Σ _ (λ a → ∀ x → EventuallyConst f x a)

-- The useful theorem: invertible + nontrivial ⇒ no global attractor.
-- (In a finite/discrete world, invertible dynamics can’t collapse all orbits to one point unless singleton.)

postulate
  invertible-nontrivial-no-attractor :
    ∀ {S : Set} {U : S → S} →
    Invertible U →
    (Σ S (λ x → Σ S (λ y → ¬ (x ≡ y)))) →
    ¬ GlobalAttractor U
