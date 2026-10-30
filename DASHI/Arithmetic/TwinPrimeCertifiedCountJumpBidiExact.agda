module DASHI.Arithmetic.TwinPrimeCertifiedCountJumpBidiExact where

------------------------------------------------------------------------
-- M16 FINITE CERTIFICATE RECEIPT: GENUINE TWIN PAIR ↔ COUNT JUMP.
--
-- Reuses the ORIGINAL proof-bearing Nat primality decider and
-- exact finite counting functions (not a wheel survivor count).
-- Classical twin-pair number theory: Brun (1919);
-- original Agda implementation: TwinPrimeCertifiedEnumeratorExact.
--
-- An arithmetic correlation theorem could discharge a suitable
-- count-growth obligation, but THIS module proves no analytic
-- inequality and no infinitely many twin primes. The result is
-- exact for every individual index >= 2; lower indexes excluded
-- consistently with the original finite counter.
-- Source-written, kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Nullary using (yes; no)

import DASHI.Analysis.PrimeCountingFunction as Generic
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Six
import DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact as Twin

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

predNat : Nat → Nat
predNat zero = zero
predNat (suc n) = n

sucNeverEqualsSelf : (n : Nat) → suc n ≢ n
sucNeverEqualsSelf zero ()
sucNeverEqualsSelf (suc n) same =
  sucNeverEqualsSelf n (cong predNat same)

twinCountChangesAtCertifiedTwin :
  (k : Nat) →
  Six.TwinPrimeAt (suc (suc k)) →
  Twin.twinPairCountLE (suc (suc k))
    ≢ Twin.twinPairCountLE (suc k)
twinCountChangesAtCertifiedTwin k twin same =
  sucNeverEqualsSelf
    (Twin.twinPairCountLE (suc k))
    (trans
      (sym (Generic.primeCountAtPrime Twin.twinStartPredicate k twin))
      same)

twinCertifiedFromCountChange :
  (k : Nat) →
  Twin.twinPairCountLE (suc (suc k))
    ≢ Twin.twinPairCountLE (suc k) →
  Six.TwinPrimeAt (suc (suc k))
twinCertifiedFromCountChange k changes
  with Twin.twinPrimeAt? (suc (suc k))
... | yes certified = certified
... | no notTwin =
  ⊥-elim
    (changes
      (Generic.primeCountAtNonprime Twin.twinStartPredicate k notTwin))

record CertifiedTwinCountJumpBidi (k : Nat) : Set where
  constructor certified-twin-count-jump-bidi
  field
    primePairImpliesCountChanges :
      Six.TwinPrimeAt (suc (suc k)) →
      Twin.twinPairCountLE (suc (suc k))
        ≢ Twin.twinPairCountLE (suc k)
    countChangesImpliesPrimePair :
      Twin.twinPairCountLE (suc (suc k))
        ≢ Twin.twinPairCountLE (suc k) →
      Six.TwinPrimeAt (suc (suc k))
open CertifiedTwinCountJumpBidi public

certifiedCountJumpBidi : (k : Nat) → CertifiedTwinCountJumpBidi k
certifiedCountJumpBidi k =
  certified-twin-count-jump-bidi
    (twinCountChangesAtCertifiedTwin k)
    (twinCertifiedFromCountChange k)
