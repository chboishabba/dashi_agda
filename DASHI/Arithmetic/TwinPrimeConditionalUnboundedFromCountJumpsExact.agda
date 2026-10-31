module DASHI.Arithmetic.TwinPrimeConditionalUnboundedFromCountJumpsExact where

------------------------------------------------------------------------
-- M16/G01 CONDITIONAL CLOSURE:
-- ARBITRARILY LATE GENUINE COUNT JUMPS ⇔ UNBOUNDED TWIN PRIMES.
--
-- Uses only the actual original TwinPrimeCertifiedEnumeratorExact
-- and the exact count-jump ↔ proof-bearing pair result.
-- The field laterJump is a HIGHLY NONTRIVIAL research target.
-- It is NOT supplied by a wheel-survivor count, symbolic congruence
-- or positive Mangoldt value at finitely many inputs.
-- In particular this is NOT an unconditional Twin Prime theorem.
--
-- Reverse direction reuses twinCountChangesAtCertifiedTwin and
-- Nat order transport. Equivalence does NOT inhabit either side.
-- Prior Brun/Hardy-Littlewood ownership retained. New finite
-- bridge source-written, kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP

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

------------------------------------------------------------------------
-- NEW T10 / M16 REVERSE: ACTUAL TWIN INFINITUDE IMPLIES COFINAL
-- COUNT JUMPS. The stronger query cutoff suc(suc N) makes the
-- special 0/1 positions impossible WITHOUT assuming a prime lower
-- bound or introducing any extra source-number arithmetic.
------------------------------------------------------------------------

cutoffBelowTwoMore : (N : Nat) → N ≤ suc (suc N)
cutoffBelowTwoMore zero = z≤n
cutoffBelowTwoMore (suc N) = s≤s (cutoffBelowTwoMore N)

certifiedCountJumpsFromTwinInfinitude :
  Twin.TwinPrimesInfinitelyOften →
  (N : Nat) →
  Σ Nat (λ k →
    (N ≤ suc (suc k)) ×
    (Enumerator.twinPairCountLE (suc (suc k))
      ≡ Enumerator.twinPairCountLE (suc k) → ⊥))
certifiedCountJumpsFromTwinInfinitude twins N
  with twins (suc (suc N))
... | zero , (() , _)
... | suc zero , (() , _)
... | suc (suc k) , (late , pair) =
  k ,
    ( NP.≤-trans (cutoffBelowTwoMore N) late
    , Count.twinCountChangesAtCertifiedTwin k pair )

twinInfinitudeGivesUnboundedCertifiedCountJumps :
  Twin.TwinPrimesInfinitelyOften →
  UnboundedCertifiedCountJumps
twinInfinitudeGivesUnboundedCertifiedCountJumps twins =
  unbounded-certified-count-jumps
    (certifiedCountJumpsFromTwinInfinitude twins)

-- BIDI, not a new source of count jumps:
-- both sides are logically equivalent, and BOTH remain uninhabited
-- without a genuine infinite-prime-pair theorem or equivalent input.
record CountJumpInfinitudeBidi : Set where
  constructor count-jump-infinitude-bidi
  field
    jumpsToTwins :
      UnboundedCertifiedCountJumps → Twin.TwinPrimesInfinitelyOften
    twinsToJumps :
      Twin.TwinPrimesInfinitelyOften → UnboundedCertifiedCountJumps
open CountJumpInfinitudeBidi public

certifiedCountJumpInfinitudeBidi : CountJumpInfinitudeBidi
certifiedCountJumpInfinitudeBidi =
  count-jump-infinitude-bidi
    twinPrimesUnboundedIfCountJumps
    twinInfinitudeGivesUnboundedCertifiedCountJumps
