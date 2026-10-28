module DASHI.Arithmetic.SignedSSPTwinFiniteCoverageExact where

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION
--
-- DASHI.Analysis.PrimeCountingFunction owns proof-bearing finite list
-- enumeration. DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact
-- instantiates it using two independent Nat primality decisions.
-- DASHI.Arithmetic.SignedSSPPrimeOutputBoundaryExact owns a generic
-- list membership and map-membership transport. DASHI.Arithmetic.
-- SignedSSPProofCarryingExponentExact owns the exact residual codec.
--
-- New theorem: EVERY certified twin start p>=2 occurs in the finite
-- genuine-twin list by cutoff p, and its exact 2^p code appears in the
-- mapped list. This establishes finite coded coverage, NOT signed
-- FRACTRAN runtime reachability nor infinitely many such p.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Nat.Primality using (Prime)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Analysis.PrimeCountingFunction as Generic
import DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact as Count
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin
import DASHI.Arithmetic.SignedSSPPrimeOutputBoundaryExact as Membership
import DASHI.Arithmetic.SignedSSPProofCarryingExponentExact as Code

-- At cutoff p itself, the proof-bearing prime-pair decider's yes case
-- prepends p. The no case contradicts the actual supplied twin proof.
twinStartAppearsAtOwnCutoff :
  (k : Nat) →
  Twin.TwinPrimeAt (suc (suc k)) →
  Membership._∈_
    (suc (suc k))
    (Count.twinStartsUpTo (suc (suc k)))
twinStartAppearsAtOwnCutoff k proof
  with Count.twinPrimeAt? (suc (suc k))
... | yes accepted = Membership.here
... | no rejected = ⊥-elim (rejected proof)

-- Important: this map is exact readout coding, NOT a lossy SSP tag.
-- A code carries its original p as a residual and proves payload=2^p.
encodedTwinStartsUpTo : Nat → List Code.CertifiedExponentCode
encodedTwinStartsUpTo limit =
  Membership.mapList Code.encodeExponent (Count.twinStartsUpTo limit)

everyCertifiedTwinCodeAppearsAtOwnCutoff :
  (k : Nat) →
  Twin.TwinPrimeAt (suc (suc k)) →
  Membership._∈_
    (Code.encodeExponent (suc (suc k)))
    (encodedTwinStartsUpTo (suc (suc k)))
everyCertifiedTwinCodeAppearsAtOwnCutoff k proof =
  Membership.memberMap Code.encodeExponent
    (twinStartAppearsAtOwnCutoff k proof)

-- The existing generic counter counts the exact same starts, so there
-- is no separate, divergent notion of encoded twin-pair cardinality.
encodedTwinListLengthExact :
  (limit : Nat) →
  Generic.listLength (encodedTwinStartsUpTo limit)
    ≡ Count.twinPairCountLE limit
encodedTwinListLengthExact limit =
  transListLength limit
  where
    lengthMap :
      ∀ {A B : Set} (f : A → B) (xs : List A) →
      Generic.listLength (Membership.mapList f xs)
        ≡ Generic.listLength xs
    lengthMap f [] = refl
    lengthMap f (x ∷ xs)
      rewrite lengthMap f xs = refl

    transListLength :
      (limit : Nat) →
      Generic.listLength (encodedTwinStartsUpTo limit)
        ≡ Count.twinPairCountLE limit
    transListLength limit =
      trans
        (lengthMap Code.encodeExponent (Count.twinStartsUpTo limit))
        (Count.twinStartListCountExact limit)

-- Step of genuine pair counting, not a survivor density estimate.
twinCountIncrementsAtCertifiedTwin :
  (k : Nat) →
  Twin.TwinPrimeAt (suc (suc k)) →
  Count.twinPairCountLE (suc (suc k))
    ≡ suc (Count.twinPairCountLE (suc k))
twinCountIncrementsAtCertifiedTwin k witness =
  Generic.primeCountAtPrime Count.twinStartPredicate k witness
