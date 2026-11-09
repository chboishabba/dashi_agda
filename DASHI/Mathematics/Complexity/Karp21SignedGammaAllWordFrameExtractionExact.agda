{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21SignedGammaAllWordFrameExtractionExact where

------------------------------------------------------------------------
-- Karp P0: extract the ACTUAL Elias-gamma frame of every successful
-- native binary read, paying prefix count, suffix, and payload length.
--
-- Canonical frame is not assumed or postulated: we descend through
-- Native.scanZeros/readPayload over the original Word.BitWord.
-- This is the source-side bridge from complete-gamma numerical proof
-- to arbitrary input bitwords. Numeric agreement still requires the
-- all-word composition below, not merely a valid frame.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (length; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Native
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Original
import DASHI.Mathematics.Complexity.Karp21GammaBinarySignedPayloadValueCutExact as Frame

------------------------------------------------------------------------
-- When the ACTUAL native parser consumes k payload bits, exactly k
-- bits are returned and the remaining suffix is unmodified.
------------------------------------------------------------------------

payloadSuccessSplitsWord :
  (k : Nat) (word payload suffix : Word.BitWord) →
  Native.readPayload k word ≡ just (payload , suffix) →
  (word ≡ payload ++ suffix) × (length payload ≡ k)
payloadSuccessSplitsWord zero word [] word refl = refl , refl
payloadSuccessSplitsWord (suc k) [] payload suffix ()
payloadSuccessSplitsWord (suc k) (b ∷ word) payload suffix agreement
  with Native.readPayload k word in tail
... | nothing with agreement
...   | ()
... | just (rest , after) with agreement
...   | refl
  with payloadSuccessSplitsWord k word rest after tail
...     | wordEq , lenEq =
  cong (b ∷_) wordEq , cong suc lenEq

------------------------------------------------------------------------
-- Actual prefix zeros and payload scan, including the pre-existing
-- zero count when this source is reused inside another gamma parser.
------------------------------------------------------------------------

record ScanFrame
    (seen : Nat)
    (word numeral suffix : Word.BitWord) : Set where
  constructor scan-frame
  field
    extraZeros : Nat
    payload : Word.BitWord
    numeralIsOnePayload :
      numeral ≡ true ∷ payload
    exactInput :
      word ≡ Original.zeroPrefix extraZeros ++
        (true ∷ (payload ++ suffix))
    exactPayloadCount :
      length payload ≡ seen + extraZeros

scanSuccessExtractsFrame :
  (seen : Nat) (word numeral suffix : Word.BitWord) →
  Native.scanZeros seen word ≡ just (numeral , suffix) →
  ScanFrame seen word numeral suffix
scanSuccessExtractsFrame seen [] numeral suffix ()
scanSuccessExtractsFrame seen (false ∷ word) numeral suffix agreement
  with scanSuccessExtractsFrame (suc seen) word numeral suffix agreement
... | scan-frame zeros payload numeralEq wordEq countEq =
  scan-frame (suc zeros) payload numeralEq
    (cong (false ∷_) wordEq)
    (trans countEq (sym (NatP.+-suc seen zeros)))
scanSuccessExtractsFrame seen (true ∷ word) numeral suffix agreement
  with Native.readPayload seen word in readEq
... | nothing with agreement
...   | ()
... | just (payload , after) with agreement
...   | refl
  with payloadSuccessSplitsWord seen word payload after readEq
...     | wordEq , lengthEq =
  scan-frame zero payload refl
    (cong (true ∷_) wordEq)
    (trans lengthEq (sym (NatP.+-identityʳ seen)))

-- Original and native zeroPrefix functions are identical by the
-- actual structural proof, not by assuming definitional equality.
nativeGammaSuccessIsOriginalCanonicalFrame :
  (word numeral suffix : Word.BitWord) →
  Native.readGammaBinary word ≡ just (numeral , suffix) →
  (Word.BitWord ×
    (word ≡ Frame.originalGammaFrame
        (ScanFrame.payload
          (scanSuccessExtractsFrame zero word numeral suffix
            (Native.readGammaBinary word ≡ just (numeral , suffix))))
        suffix))
nativeGammaSuccessIsOriginalCanonicalFrame word numeral suffix agreement
  with scanSuccessExtractsFrame zero word numeral suffix agreement
... | scan-frame zeros payload numeralEq wordEq countEq =
  payload , trans wordEq
    (cong (λ n → Original.zeroPrefix n ++
      (true ∷ (payload ++ suffix))) (sym countEq))
