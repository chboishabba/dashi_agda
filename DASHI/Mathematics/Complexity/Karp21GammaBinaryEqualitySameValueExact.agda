{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryEqualitySameValueExact where

------------------------------------------------------------------------
-- K05: SAME NUMERIC VALUE FOR ORIGINAL KARP GAMMA ENCODINGS.
--
-- For the ACTUAL Gamma.encodeGammaNat from the original E20/N21 codec,
-- the selected bit-native equality is true iff the represented
-- natural numbers are equal. This is NOT a fresh representation:
-- the proof uses the original readGamma on the original encoded words.
--
-- It does not prove that generic raw NatP comparisons already execute
-- this bitword comparator, or charge gamma re-encoding machine time.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (_++_)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.List.Properties as ListP

import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact as Round
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Decoder
import DASHI.Mathematics.Complexity.Karp21BinaryWordEqualityPrimitiveExact as Binary

gammaEncodedEqualImpliesSameNat :
  (a b : Nat) →
  Gamma.encodeGammaNat a ≡ Gamma.encodeGammaNat b →
  a ≡ b
gammaEncodedEqualImpliesSameNat a b equality =
  justPairInjectFirst
    (trans
      (sym (Round.gammaReadEncodeSuffix a []))
      (trans
        (cong Decoder.readGamma
          (trans
            (sym (ListP.++-identityʳ (Gamma.encodeGammaNat a)))
            (trans equality
              (ListP.++-identityʳ (Gamma.encodeGammaNat b)))))
        (Round.gammaReadEncodeSuffix b [])))
  where
    justPairInjectFirst :
      ∀ {x y : Nat} {rest : Decoder.Word.BitWord} →
      just (x , rest) ≡ just (y , rest) → x ≡ y
    justPairInjectFirst refl = refl

gammaBitNativeEqualitySound :
  (a b : Nat) →
  Binary.equalBitWords
    (Gamma.encodeGammaNat a) (Gamma.encodeGammaNat b)
      ≡ true →
  a ≡ b
gammaBitNativeEqualitySound a b eq =
  gammaEncodedEqualImpliesSameNat a b
    (Binary.bitWordEqualitySound
      (Gamma.encodeGammaNat a) (Gamma.encodeGammaNat b) eq)

gammaBitNativeEqualityComplete :
  (a b : Nat) →
  a ≡ b →
  Binary.equalBitWords
    (Gamma.encodeGammaNat a) (Gamma.encodeGammaNat b)
      ≡ true
gammaBitNativeEqualityComplete a .a refl =
  Binary.bitWordEqualityReflexive (Gamma.encodeGammaNat a)

gammaEncodedEqualityInspectionBound :
  (a b : Nat) →
  Binary.bitEqualityInspectionCount
    (Gamma.encodeGammaNat a) (Gamma.encodeGammaNat b)
      ≤ suc (Decoder.Word.encodingSize (Gamma.encodeGammaNat a))
gammaEncodedEqualityInspectionBound a b =
  Binary.bitEqualityInspectionBound
    (Gamma.encodeGammaNat a) (Gamma.encodeGammaNat b)
