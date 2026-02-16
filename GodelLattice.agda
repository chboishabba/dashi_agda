module GodelLattice where

open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List     using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import MonsterOntos

------------------------------------------------------------------------
-- A factor-exponent vector over the 15 primes is a canonical coordinate.

record Vec15 (A : Set) : Set where
  constructor v15
  field
    e2  : A; e3  : A; e5  : A; e7  : A; e11 : A
    e13 : A; e17 : A; e19 : A; e23 : A; e29 : A
    e31 : A; e41 : A; e47 : A; e59 : A; e71 : A

Exponent : Set
Exponent = Nat

FactorVec : Set
FactorVec = Vec15 Exponent

------------------------------------------------------------------------
-- Abstract "text" (you’ll plug a real representation later)

postulate
  Text : Set

------------------------------------------------------------------------
-- Gödel encoding contract:
-- encode gives a Nat; factorMap gives exponents over SSP primes.
-- The key property is that factorMap is a homomorphism for concatenation
-- (or some composition), if you want that. Here we keep it minimal.

postulate
  encode   : Text → Nat
  factorMap : Text → FactorVec

------------------------------------------------------------------------
-- Self-verifying coordinate means: equality of factor-vectors is a stable
-- identifier under the chosen equivalence (you decide what that is).
-- We DO NOT claim it is “reality”; we claim it is a canonical coordinate.

record CoordinateLaw : Set₁ where
  field
    stable-id :
      ∀ (t₁ t₂ : Text) →
      factorMap t₁ ≡ factorMap t₂ → encode t₁ ≡ encode t₂
