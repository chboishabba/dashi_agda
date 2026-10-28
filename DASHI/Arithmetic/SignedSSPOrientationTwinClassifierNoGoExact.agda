module DASHI.Arithmetic.SignedSSPOrientationTwinClassifierNoGoExact where

------------------------------------------------------------------------
-- SOURCE AUTHORITIES
--
-- Signed direction / orientation owner:
--   DASHI.Biology.SignedSSPFRACTRANWeaveExact
--   (negative/zero/positive multiplicity).
-- Prime predicate and Boolean evidence:
--   DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact
--   (ultimately Data.Nat.Primality.prime?).
-- Compression proof boundary:
--   DASHI.Combinatorics.SSP15FractranCompression
--   (bare SSP label may need a residual to recover full arithmetic).
--
-- NEW: a concrete no-go theorem. Two positive signed states with
-- different arithmetic magnitudes can have IDENTICAL orientation but
-- DIFFERENT arithmetic twin-primality status. Therefore no classifier
-- factoring through orientation alone decides TwinPrimeAt on all Nats.
-- This does not rule out a lossless signed SSP label + arithmetic
-- residual. It prevents purely cosmetic sign/phase transport from
-- being promoted to a twin-prime oracle.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)
open import Relation.Nullary using (Dec; yes; no)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Arithmetic.TwinPrimeCertifiedEnumeratorExact as Twin

orientationOfPositiveMagnitude : Nat → Signed.FibreOrientation
orientationOfPositiveMagnitude n =
  Signed.orientationOfMultiplicity (Signed.positiveMultiplicity n)

orientationFiveAndSevenEqual :
  orientationOfPositiveMagnitude 5 ≡ orientationOfPositiveMagnitude 7
orientationFiveAndSevenEqual = refl

twinStartBool : Nat → Bool
twinStartBool n with Twin.twinPrimeAt? n
... | yes _ = true
... | no _ = false

-- 5 and 7 are a twin pair. 7 and 9 are not, because 9 is composite.
-- The actual primality decider computes both witnesses.
twinAtFiveIsTrue : twinStartBool 5 ≡ true
twinAtFiveIsTrue = refl

twinAtSevenIsFalse : twinStartBool 7 ≡ false
twinAtSevenIsFalse = refl

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

-- No total orientation-only predicate has the same classification on
-- every Nat. The contradiction is explicitly witnessed at 5 and 7.
orientationAloneCannotDecideTwinPrimality :
  (classifier : Signed.FibreOrientation → Bool) →
  ((n : Nat) →
    classifier (orientationOfPositiveMagnitude n)
      ≡ twinStartBool n) →
  ⊥
orientationAloneCannotDecideTwinPrimality classifier correct =
  trueNotFalse
    (trans
      (sym (trans (correct 5) twinAtFiveIsTrue))
      (trans
        (cong classifier orientationFiveAndSevenEqual)
        (trans (correct 7) twinAtSevenIsFalse)))

-- A lawful richer encoder must retain the integer readout, and a
-- preserved readout leaves TwinPrimeAt invariant. No lost primality
-- is recoverable from a phase label that collides at 5 and 7.
