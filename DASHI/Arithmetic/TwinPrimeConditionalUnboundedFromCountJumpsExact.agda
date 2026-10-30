module DASHI.Arithmetic.TwinPrimeConditionalUnboundedFromCountJumpsExact where

------------------------------------------------------------------------
-- M16/G01 CONDITIONAL CLOSURE:
-- ARBITRARILY LATE GENUINE COUNT JUMPS ⇒ UNBOUNDED TWIN PRIMES.
--
-- Uses only the actual original TwinPrimeCertifiedEnumeratorExact
-- and the exact count-jump ↔ proof-bearing pair result.
-- The field laterJump is a HIGHLY NONTRIVIAL external assumption.
-- It is NOT supplied by a wheel-survivor count, symbolic congruence
-- or positive Mangoldt value at finitely many inputs.
-- In particular this is NOT an unconditional Twin Prime theorem.
--
-- Prior Brun/Hardy-Littlewood ownership retained. New finite
-- bridge source-written, kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Nat.Base using (_≤_)

import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact as Enumerator
import DASHI.Arithmetic.TwinPrimeCertifiedCountJumpBidiExact as Count

record UnboundedCertifiedCountJumps : Set where
  constructor unbounded-certified-count-jumps
  field
    laterJump :
      (N : Nat) →
      Σ Nat (λ k →
        (N ≤ suc (suc k)) ×
        (Enumerator.twinPairCountLE (suc (suc k))
          ≡ Enumerator.twinPairCountLE (suc k) → ⊥))
open UnboundedCertifiedCountJumps public

twinPrimesUnboundedIfCountJumps :
  UnboundedCertifiedCountJumps →
  (N : Nat) →
  Σ Nat (λ p → (N ≤ p) × Twin.TwinPrimeAt p)
twinPrimesUnboundedIfCountJumps growth N
  with laterJump growth N
... | k , (N≤p , actualJump) =
  suc (suc k) ,
    (N≤p , Count.twinCertifiedFromCountChange k actualJump)
