module DASHI.Arithmetic.SignedSSPRawCodeParityNoGoExact where

------------------------------------------------------------------------
-- SOURCE OWNERS AND CLAIM BOUNDARY
--
-- John H. Conway / Richard Guy: arithmetic prime p is represented by
-- the machine code 2^p at selected PRIMEGAME output states.
-- DASHI.Arithmetic.SignedSSPPrimeOffsetMacroExact owns the powerTwo
-- arithmetic encoding and the exact +/-2 exponent update.
-- DASHI.Arithmetic.CertifiedPrimePairModulusExact owns the actual
-- arithmetic prime-pair test mod p, including exceptional prime 2.
--
-- NEW NEGATIVE THEOREM: the raw FRACTRAN integer code 2^p is NOT
-- interchangeable with the decoded arithmetic prime p for modulo tests.
-- Already at p=3, 2^3 mod 2 = 0 while 3 mod 2 = 1.
--
-- Consequence: any correct signed SSP FRACTRAN/CRT bridge must decode
-- the represented exponent (or preserve its certified residual) BEFORE
-- applying arithmetic prime-pair divisibility. Using raw code modulo 2
-- would reject this actual odd prime; removing prime 2 would also be
-- mathematically wrong. No Monster/4B class analogy licenses either.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_%_)
open import Data.Empty using (⊥)
import DASHI.Arithmetic.SignedSSPPrimeOffsetMacroExact as Offset

powerTwoOfThreeIsEight :
  Offset.powerTwo 3 ≡ 8
powerTwoOfThreeIsEight = refl

rawCodeThreeModuloTwoIsZero :
  (Offset.powerTwo 3) % 2 ≡ 0
rawCodeThreeModuloTwoIsZero = refl

decodedPrimeThreeModuloTwoIsOne :
  3 % 2 ≡ 1
decodedPrimeThreeModuloTwoIsOne = refl

rawCodeParityMismatchesDecodedPrimeThree :
  ((Offset.powerTwo 3) % 2 ≡ 3 % 2) → ⊥
rawCodeParityMismatchesDecodedPrimeThree ()

-- Not a formula that can hold for EVERY encoded prime exponent.
rawCodeModuloTwoCannotReplaceDecodedParity :
  ((p : Nat) → (Offset.powerTwo p) % 2 ≡ p % 2) →
  ⊥
rawCodeModuloTwoCannotReplaceDecodedParity hypothetical =
  rawCodeParityMismatchesDecodedPrimeThree (hypothetical 3)
