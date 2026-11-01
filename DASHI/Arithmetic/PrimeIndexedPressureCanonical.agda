module DASHI.Arithmetic.PrimeIndexedPressureCanonical where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)

open import DASHI.Arithmetic.NormalizeAddState using (normalizeAddCanonical)
open import DASHI.Arithmetic.NormalizeAdd using
  ( normalizeAdd
  ; normalizeAdd-canonical
  )
open import DASHI.Arithmetic.CancellationPressureFromCanonical using
  ( StateSupportPressure )
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( primeIndexedPressureAt
  ; sum15
  ; canonical⇒primeIndexedBounded
  ; normalizeAdd⇒primeIndexedBounded
  )

------------------------------------------------------------------------
-- Canonical integration for the current honest semantics.
--
-- The prime-indexed surface factors through the refined pressure proxy.
-- On the canonical slice that yields boundedness, not zero collapse.
------------------------------------------------------------------------

canonical⇒primeIndexedBoundedCanonical :
  ∀ s →
  normalizeAddCanonical s →
  sum15 (primeIndexedPressureAt s) ≤ StateSupportPressure s
canonical⇒primeIndexedBoundedCanonical = canonical⇒primeIndexedBounded

normalizeAdd⇒primeIndexedCanonicalBounded :
  ∀ s →
  normalizeAddCanonical (normalizeAdd s) ×
  (sum15 (primeIndexedPressureAt (normalizeAdd s)) ≤
   StateSupportPressure (normalizeAdd s))
normalizeAdd⇒primeIndexedCanonicalBounded s =
  normalizeAdd-canonical s , normalizeAdd⇒primeIndexedBounded s

record PrimeIndexedCanonicalBounded : Set₁ where
  field
    canonicalBound :
      ∀ s →
      normalizeAddCanonical s →
      sum15 (primeIndexedPressureAt s) ≤ StateSupportPressure s

    normalizeAddCanonicalBound :
      ∀ s →
      normalizeAddCanonical (normalizeAdd s) ×
      (sum15 (primeIndexedPressureAt (normalizeAdd s)) ≤
       StateSupportPressure (normalizeAdd s))

open PrimeIndexedCanonicalBounded public

primeIndexedCanonicalBounded : PrimeIndexedCanonicalBounded
primeIndexedCanonicalBounded =
  record
    { canonicalBound = canonical⇒primeIndexedBoundedCanonical
    ; normalizeAddCanonicalBound = normalizeAdd⇒primeIndexedCanonicalBounded
    }
