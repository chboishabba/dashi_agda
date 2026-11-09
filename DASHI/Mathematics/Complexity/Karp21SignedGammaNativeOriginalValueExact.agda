{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact where

------------------------------------------------------------------------
-- Karp original signed gamma: ACTUAL executable token value matches
-- original zigzag integer on EACH COMPLETE ORIGINAL GAMMA FRAME.
--
-- Zero gamma, positive last bit, negative last bit; arbitrary native
-- magnitude width and arbitrary identical suffix. There is no
-- numeric postulate, untrusted extensional oracle or Peano runtime.
--
-- The lemmas consume the source previous original/native gamma
-- readout and the actual binary-ledger valueLE(reverse bits) proof.
-- Still to do: promote complete frames to arbitrary bitwords using
-- the original parser's actual successful-frame decomposition;
-- then apply to the original readRawEdges stream and graph verifier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Nat.Base using (_∸_)
open import Data.List.Base using (reverse; length; _++_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21GammaBinarySignedPayloadValueCutExact as Frame
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Native
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedSuffixExact as Suffix
import DASHI.Mathematics.Complexity.Karp21SignedGammaAllWordFrameExtractionExact as Extract
import DASHI.Mathematics.Complexity.Karp21SignedGammaNumberTheoryExact as Number
import DASHI.Mathematics.Complexity.Karp21SignedGammaBinaryValueArithmeticExact as Binary
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value

-- The executable token stores sign+magnitude as big-endian bits;
-- numeric decoding is intentionally mathematical and separate.
negativeNativeMagnitude : Nat → ℤ
negativeNativeMagnitude zero = + zero
negativeNativeMagnitude (suc k) = -[1+ k ]

interpretNativeToken : Signed.SignedMagnitudeBits → ℤ
interpretNativeToken (Signed.positive bits) =
  + (Value.valueLE (reverse bits))
interpretNativeToken (Signed.negative bits) =
  negativeNativeMagnitude (Value.valueLE (reverse bits))

observeNativeSigned :
  Maybe (Signed.SignedMagnitudeBits × Word.BitWord) →
  Maybe (ℤ × Word.BitWord)
observeNativeSigned nothing = nothing
observeNativeSigned (just (token , suffix)) =
  just (interpretNativeToken token , suffix)

sourceMagnitude : Word.BitWord → Nat
sourceMagnitude prefix =
  Old.pow2 (length prefix) + Old.payloadValue prefix

-- Source gamma payload prefix ++ [true] has successor integer 2M+1.
-- After original gamma -1, old unzigzag returns +M, and that M is
-- exactly the magnitude of the ACTUAL native binary token.
positivePayloadValueCorrect :
  (prefix : Word.BitWord) →
  Old.unzigzag
    (Frame.originalPayloadSignedNat (prefix ++ (true ∷ [])))
    ≡ interpretNativeToken (Signed.positive (true ∷ prefix))
positivePayloadValueCorrect prefix =
  let m = sourceMagnitude prefix
  in trans
       (cong (λ n → Old.unzigzag (n ∸ suc zero))
         (Binary.originalSuccessorNumberDecomposes prefix true))
       (trans
         (cong Old.unzigzag (Binary.twoTimesOnePredecessor m))
         (trans
           (Old.unzigzagZigzag (+ m))
           (cong +_ (sym (Binary.nativeMagnitudeSameOriginalBinaryValue prefix)))))

twoTimesNegativePredecessor :
  (k : Nat) →
  (Value.two * suc k) ∸ suc zero ≡ suc (Old.twice k)
twoTimesNegativePredecessor k =
  trans
    (cong (λ n → n ∸ suc zero)
      (sym (Binary.originalTwiceIsTwoTimes (suc k))))
    (Number.negativeSuccessorPredecessor k)

-- Source gamma payload prefix ++ [false] has successor integer 2M,
-- with M=suc k by the actual leading-one magnitude proof.
-- Original zigzag then returns -(k+1)=-M, including no negative zero.
negativePayloadValueCorrect :
  (prefix : Word.BitWord) →
  Old.unzigzag
    (Frame.originalPayloadSignedNat (prefix ++ (false ∷ [])))
    ≡ interpretNativeToken (Signed.negative (true ∷ prefix))
negativePayloadValueCorrect prefix
  with Binary.sourceMagnitudePositive prefix
... | k , positive =
  let m = sourceMagnitude prefix
  in trans
       (cong (λ n → Old.unzigzag (n ∸ suc zero))
         (Binary.originalSuccessorNumberDecomposes prefix false))
       (trans
         (cong (λ n → Old.unzigzag (n ∸ suc zero))
           (NatP.+-identityʳ (Value.two * m)))
         (trans
           (cong (λ n → Old.unzigzag ((Value.two * n) ∸ suc zero))
             positive)
           (trans
             (cong Old.unzigzag (twoTimesNegativePredecessor k))
             (trans
               (Old.unzigzagZigzag (-[1+ k ]))
               (sym (trans
                 (cong negativeNativeMagnitude
                   (Binary.nativeMagnitudeSameOriginalBinaryValue prefix))
                 (cong negativeNativeMagnitude positive))))))

-- The two actual executable readers, observed by their native
-- mathematical value, agree EXACTLY on every complete nonempty
-- source gamma payload and on any untouched suffix.
karpNativeSignedTokenValueMatchesOriginalEncodedFrame :
  (prefix suffix : Word.BitWord) (last : Bool) →
  observeNativeSigned
    (Signed.readSignedBinary
      (Frame.originalGammaFrame (prefix ++ (last ∷ [])) suffix))
    ≡ Old.readSignedGamma
      (Frame.originalGammaFrame (prefix ++ (last ∷ [])) suffix)
karpNativeSignedTokenValueMatchesOriginalEncodedFrame prefix suffix true
  rewrite Frame.karpNativeSignedPayloadFrameExact prefix suffix true
        | Frame.karpOriginalSignedPayloadFrameExact
            (prefix ++ (true ∷ [])) suffix =
  cong (λ n → just (n , suffix))
    (sym (positivePayloadValueCorrect prefix))
karpNativeSignedTokenValueMatchesOriginalEncodedFrame prefix suffix false
  rewrite Frame.karpNativeSignedPayloadFrameExact prefix suffix false
        | Frame.karpOriginalSignedPayloadFrameExact
            (prefix ++ (false ∷ [])) suffix =
  cong (λ n → just (n , suffix))
    (sym (negativePayloadValueCorrect prefix))

-- n=0 is encoded as a one-bit gamma numeral [true]; its magnitude
-- is empty and its ORIGINAL sign is nonnegative zero.
karpNativeSignedZeroValueMatchesOriginal :
  observeNativeSigned
    (Signed.readSignedBinary (Frame.originalGammaFrame [] []))
    ≡ Old.readSignedGamma (Frame.originalGammaFrame [] [])
karpNativeSignedZeroValueMatchesOriginal = refl


------------------------------------------------------------------------
-- ALL-WORD lift: a successful ACTUAL gamma parse is a genuine original
-- complete frame. Exhaustively split its payload into zero or a last
-- sign bit; a failed gamma parse has no signed result on either side.
------------------------------------------------------------------------

nonemptyPayloadHasLast :
  (head : Bool) (tail : Word.BitWord) →
  Σ Word.BitWord (λ prefix →
    Σ Bool (λ last →
      head ∷ tail ≡ prefix ++ (last ∷ [])))
nonemptyPayloadHasLast head [] =
  [] , (head , refl)
nonemptyPayloadHasLast head (b ∷ tail)
  with nonemptyPayloadHasLast b tail
... | prefix , (last , equation) =
  (head ∷ prefix) , (last , cong (head ∷_) equation)

karpCompleteGammaFrameSignedValueExact :
  (payload suffix : Word.BitWord) →
  observeNativeSigned
    (Signed.readSignedBinary (Frame.originalGammaFrame payload suffix))
    ≡ Old.readSignedGamma (Frame.originalGammaFrame payload suffix)
karpCompleteGammaFrameSignedValueExact [] suffix = refl
karpCompleteGammaFrameSignedValueExact (head ∷ tail) suffix
  with nonemptyPayloadHasLast head tail
... | prefix , (last , equation)
  rewrite equation =
  karpNativeSignedTokenValueMatchesOriginalEncodedFrame
    prefix suffix last

karpNativeSignedValueOnAllSuccessfulWords :
  (word numeral suffix : Word.BitWord) →
  Native.readGammaBinary word ≡ just (numeral , suffix) →
  observeNativeSigned (Signed.readSignedBinary word)
    ≡ Old.readSignedGamma word
karpNativeSignedValueOnAllSuccessfulWords word numeral suffix success
  with Extract.nativeGammaSuccessIsOriginalCanonicalFrame
    word numeral suffix success
... | payload , exact rewrite exact =
  karpCompleteGammaFrameSignedValueExact payload suffix

nativeGammaFailureImpliesNativeSignedFailure :
  (word : Word.BitWord) →
  Native.readGammaBinary word ≡ nothing →
  Signed.readSignedBinary word ≡ nothing
nativeGammaFailureImpliesNativeSignedFailure word failure
  rewrite failure = refl

suffixNoneImpliesNothing :
  {A : Set} (result : Maybe (A × Word.BitWord)) →
  Suffix.suffixBits result ≡ nothing →
  result ≡ nothing
suffixNoneImpliesNothing nothing eq = refl
suffixNoneImpliesNothing (just (value , suffix)) ()

nativeGammaFailureImpliesOriginalSignedFailure :
  (word : Word.BitWord) →
  Native.readGammaBinary word ≡ nothing →
  Old.readSignedGamma word ≡ nothing
nativeGammaFailureImpliesOriginalSignedFailure word failure =
  suffixNoneImpliesNothing
    (Old.readSignedGamma word)
    (trans
      (sym (Suffix.karpNativeSignedGammaSuffixSameOriginal word))
      (cong Suffix.suffixBits
        (nativeGammaFailureImpliesNativeSignedFailure word failure)))

-- FULL original vs actual-native signed numeric+suffix outcome,
-- not merely agreement of acceptance flags. In the successful case
-- the original exact frame (including its suffix) is reconstructed
-- from the actual binary reader. In the failing case the existing
-- all-word suffix theorem prevents original-only acceptance.
--
-- Kernel acceptance remains subject to exact-head Agda 2.9 referee.
karpNativeSignedTokenValueMatchesOriginal :
  (word : Word.BitWord) →
  observeNativeSigned (Signed.readSignedBinary word)
    ≡ Old.readSignedGamma word
karpNativeSignedTokenValueMatchesOriginal word
  with Native.readGammaBinary word in parsed
... | nothing =
  trans
    (cong observeNativeSigned
      (nativeGammaFailureImpliesNativeSignedFailure word parsed))
    (sym (nativeGammaFailureImpliesOriginalSignedFailure word parsed))
... | just (numeral , suffix) =
  karpNativeSignedValueOnAllSuccessfulWords
    word numeral suffix parsed
