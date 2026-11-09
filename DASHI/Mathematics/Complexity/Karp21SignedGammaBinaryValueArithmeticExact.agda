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
open import Data.Nat.Base using (_∸_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (_++_; reverse; length)
open import Data.Product using (Σ; _,_)
import Data.Nat.Properties as NatP
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
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
  trans
    (reverseValueSameOriginalPayload (true ∷ prefix))
    (cong
      (λ n → n + Original.payloadValue prefix)
      (NatP.+-identityʳ (Original.pow2 (length prefix))))


------------------------------------------------------------------------
-- Original gamma successor numeral n+1 on a nonempty signed payload.
-- This is the second genuine arithmetic identity needed by the P0
-- value proof: appending the sign bit doubles the original BE prefix.
------------------------------------------------------------------------

lengthAppendOne :
  (prefix : Word.BitWord) (last : Bool) →
  length (prefix ++ (last ∷ [])) ≡ suc (length prefix)
lengthAppendOne [] last = refl
lengthAppendOne (b ∷ prefix) last =
  cong suc (lengthAppendOne prefix last)

originalPayloadAppendBit :
  (prefix : Word.BitWord) (last : Bool) →
  Original.payloadValue (prefix ++ (last ∷ [])) ≡
    Value.two * Original.payloadValue prefix + Original.bitNat last
originalPayloadAppendBit [] false = refl
originalPayloadAppendBit [] true = refl
originalPayloadAppendBit (b ∷ prefix) last
  rewrite lengthAppendOne prefix last
        | originalPayloadAppendBit prefix last =
  solve
    (Original.bitNat b ∷
     Original.pow2 (length prefix) ∷
     Original.payloadValue prefix ∷
     Original.bitNat last ∷ [])

-- Original gamma's (n+1) numerator on prefix++[last] is exactly
-- 2*valueBE(true::prefix)+last; it is NOT merely equal in suffix.
-- The preceding reverseValueSameOriginalPayload also shows this
-- magnitude equals the literal native ledger Value.valueLE reverse.
originalSuccessorNumberDecomposes :
  (prefix : Word.BitWord) (last : Bool) →
  Original.pow2 (length (prefix ++ (last ∷ []))) +
    Original.payloadValue (prefix ++ (last ∷ [])) ≡
  Value.two *
    (Original.pow2 (length prefix) + Original.payloadValue prefix) +
    Original.bitNat last
originalSuccessorNumberDecomposes prefix last
  rewrite lengthAppendOne prefix last
        | originalPayloadAppendBit prefix last =
  solve
    (Original.pow2 (length prefix) ∷
     Original.payloadValue prefix ∷
     Original.bitNat last ∷ [])


------------------------------------------------------------------------
-- Original zigzag's twice is the same numeral 2 * n used by the
-- actual native binary-value observation. This is the explicit
-- arithmetic seam between the original Peano decoder and binary bits.
------------------------------------------------------------------------

originalTwiceIsTwoTimes : (n : Nat) →
  Original.twice n ≡ Value.two * n
originalTwiceIsTwoTimes zero = refl
originalTwiceIsTwoTimes (suc n)
  rewrite originalTwiceIsTwoTimes n =
  solve (n ∷ [])

twoTimesOnePredecessor :
  (n : Nat) →
  (Value.two * n + suc zero) ∸ suc zero
    ≡ Original.twice n
twoTimesOnePredecessor n
  rewrite NatP.+-suc (Value.two * n) zero
        | NatP.+-identityʳ (Value.two * n)
        | originalTwiceIsTwoTimes n = refl

-- Unlike a signed-zero hand-wave, the leading-one binary magnitude
-- is provably suc(k); hence the negative branch is genuinely <0.
pow2NonZero :
  (n : Nat) →
  Σ Nat (λ k → Original.pow2 n ≡ suc k)
pow2NonZero zero = zero , refl
pow2NonZero (suc n) with pow2NonZero n
... | k , equation rewrite equation =
  (suc (k + k)) , solve (k ∷ [])

sourceMagnitudePositive :
  (prefix : Word.BitWord) →
  Σ Nat (λ k →
    Original.pow2 (length prefix) + Original.payloadValue prefix
      ≡ suc k)
sourceMagnitudePositive prefix with pow2NonZero (length prefix)
... | k , equation rewrite equation =
  (k + Original.payloadValue prefix) , refl
