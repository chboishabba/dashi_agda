module DASHI.Arithmetic.DeltaAtConcrete where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _∸_; z≤n)

------------------------------------------------------------------------
-- Local delta / p-adic contribution surface.
--
-- This module is intentionally thin. The repo does not yet have a concrete
-- `ArithmeticIntegerEmbedding.agda`, so the carrier stays abstract and the
-- valuation-dependent facts are stated as explicit postulates rather than
-- pretending the missing arithmetic is already available.

_≢_ : Nat → Nat → Set
m ≢ n = m ≡ n → ⊥

minNat : Nat → Nat → Nat
minNat zero n = zero
minNat (suc m) zero = zero
minNat (suc m) (suc n) = suc (minNat m n)

postulate
  DeltaCarrier : Set

  valuationAt : DeltaCarrier → Nat
  gammaAt : DeltaCarrier → DeltaCarrier → Nat
  deltaAt : DeltaCarrier → DeltaCarrier → Nat

------------------------------------------------------------------------
-- Nonnegativity is the only fully constructive part of the local surface.

deltaAt-nonnegative :
  ∀ x y →
  zero ≤ deltaAt x y
deltaAt-nonnegative x y = z≤n

------------------------------------------------------------------------
-- The decomposition surface states the intended local formula:
-- the contribution is measured against the local gamma value and the
-- current valuation wall height.

postulate
  deltaAt-decomposition :
    ∀ x y →
    deltaAt x y ≡ gammaAt x y ∸ minNat (valuationAt x) (valuationAt y)

------------------------------------------------------------------------
-- Off-wall behavior: when the valuations differ, the local delta should
-- collapse to zero.

postulate
  deltaAt-off-wall-zero :
    ∀ x y →
    valuationAt x ≢ valuationAt y →
    deltaAt x y ≡ zero

deltaAt-unequal-valuations-zero :
  ∀ x y →
  valuationAt x ≢ valuationAt y →
  deltaAt x y ≡ zero
deltaAt-unequal-valuations-zero = deltaAt-off-wall-zero

------------------------------------------------------------------------
-- Equal-wall witness: when the two valuations land on the same wall, the
-- local delta stays bounded by the local gamma height.

postulate
  deltaAt-on-wall-witness :
    ∀ x y →
    valuationAt x ≡ valuationAt y →
    deltaAt x y ≤ gammaAt x y

------------------------------------------------------------------------
-- Compact surface record for downstream imports.

record DeltaAtLocalLaw : Set₁ where
  field
    carrier : Set
    valuation : carrier → Nat
    gamma : carrier → carrier → Nat
    delta : carrier → carrier → Nat
    local-nonnegative :
      ∀ x y →
      zero ≤ delta x y
    local-decomposition :
      ∀ x y →
      delta x y ≡ gamma x y ∸ minNat (valuation x) (valuation y)
    local-off-wall-zero :
      ∀ x y →
      valuation x ≢ valuation y →
      delta x y ≡ zero
    local-on-wall-witness :
      ∀ x y →
      valuation x ≡ valuation y →
      delta x y ≤ gamma x y

deltaAtLocalLaw : DeltaAtLocalLaw
deltaAtLocalLaw = record
  { carrier = DeltaCarrier
  ; valuation = valuationAt
  ; gamma = gammaAt
  ; delta = deltaAt
  ; local-nonnegative = deltaAt-nonnegative
  ; local-decomposition = deltaAt-decomposition
  ; local-off-wall-zero = deltaAt-off-wall-zero
  ; local-on-wall-witness = deltaAt-on-wall-witness
  }
