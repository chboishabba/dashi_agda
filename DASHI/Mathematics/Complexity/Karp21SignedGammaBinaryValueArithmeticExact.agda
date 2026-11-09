{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21SignedGammaBinaryValueArithmeticExact where

------------------------------------------------------------------------
-- Original Karp N21: BINARY MAGNITUDE ARITHMETIC, not a parser proxy.
--
-- The original signed graph gamma decoder's BE payloadValue is
-- EXACTLY the actual binary-ledger owner valueLE after reverse.
-- The native token's magnitude (true ∷ prefix) then equals
-- pow2(length prefix) + original payloadValue prefix.
--
-- These are proof-only Nat observations: the executable score remains
-- bit-native and does not allocate unary Nat magnitudes.
-- Full signed gamma ℤ / unzigzag weld is composed separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (_++_; reverse; length)
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Nat.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Original
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value

sameBitNumber : (b : Bool) → Add.bitValue b ≡ Original.bitNat b
sameBitNumber false = refl
sameBitNumber true = refl

-- Literal LSB-first bit-value after appending the new highest bit.
-- Cost model: this is a specification, not a runtime reversal.
valueLEAppendBit :
  (bits : Word.BitWord) (last : Bool) →
  Value.valueLE (bits ++ (last ∷ [])) ≡
    Value.valueLE bits +
    Original.pow2 (length bits) * Original.bitNat last
valueLEAppendBit [] false = refl
valueLEAppendBit [] true = refl
valueLEAppendBit (b ∷ bits) last
  rewrite valueLEAppendBit bits last =
  solve
    (Add.bitValue b ∷
     Value.valueLE bits ∷
     Original.pow2 (length bits) ∷
     Original.bitNat last ∷ [])

-- The ACTUAL LE numeric observation is the old BE payload value,
-- not just an equality of parsing/acceptance flags.
reverseValueSameOriginalPayload :
  (bits : Word.BitWord) →
  Value.valueLE (reverse bits) ≡ Original.payloadValue bits
reverseValueSameOriginalPayload [] = refl
reverseValueSameOriginalPayload (b ∷ bits)
  rewrite ListP.reverse-++ (b ∷ []) bits
        | valueLEAppendBit (reverse bits) b
        | ListP.length-reverse bits
        | reverseValueSameOriginalPayload bits
        | sameBitNumber b =
  solve
    (Original.bitNat b ∷
     Original.pow2 (length bits) ∷
     Original.payloadValue bits ∷ [])

-- Explicitly preserve the leading-one bit of the original gamma
-- successor numerator when the trailing bit is reserved for sign.
nativeMagnitudeSameOriginalBinaryValue :
  (prefix : Word.BitWord) →
  Value.valueLE (reverse (true ∷ prefix)) ≡
    Original.pow2 (length prefix) + Original.payloadValue prefix
nativeMagnitudeSameOriginalBinaryValue prefix =
  reverseValueSameOriginalPayload (true ∷ prefix)
