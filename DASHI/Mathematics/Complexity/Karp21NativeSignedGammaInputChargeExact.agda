module DASHI.Mathematics.Complexity.Karp21NativeSignedGammaInputChargeExact where

------------------------------------------------------------------------
-- F2 SOURCE-PAID SIGNED-GAMMA TOKEN BIT CHARGE.
--
-- This proof consumes the ACTUAL recursive Gamma.readPayload,
-- Gamma.scanZeros, Signed.splitLast and Signed.readSignedBinary.
-- A successful signed token's binary magnitude+sign length, plus
-- the *actual unchanged suffix* length, cannot exceed the input
-- word length. No invented source budget/cursor/weight is assumed.
--
-- Source lemma only: no physical head/tape/allocation clock here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact as Charge

-- The ACTUAL payload reader consumes exactly k source bits on
-- successful return. Unlike a scanning cost bound this preserves
-- the returned suffix as the source accounting boundary.
actualPayloadLengthConservation :
  (k : Nat) (word payload suffix : Word.BitWord) →
  Gamma.readPayload k word ≡ just (payload , suffix) →
  length payload + length suffix ≡ length word
actualPayloadLengthConservation zero word payload suffix accepted
  with accepted
... | refl = refl
actualPayloadLengthConservation (suc k) [] payload suffix ()
actualPayloadLengthConservation (suc k) (b ∷ rest) payload suffix accepted
  with Gamma.readPayload k rest in recursive
... | nothing with accepted
... | ()
... | just (remaining , after) with accepted
... | refl =
  cong suc (actualPayloadLengthConservation k rest remaining after recursive)

-- Reading an ACTUAL gamma successor payload cannot create more
-- output bits than the input word from which it was parsed, even
-- including the preserved post-token suffix.
actualGammaScanBitCharge :
  (seen : Nat) (word successor suffix : Word.BitWord) →
  Gamma.scanZeros seen word ≡ just (successor , suffix) →
  length successor + length suffix ≤ length word
actualGammaScanBitCharge seen [] successor suffix ()
actualGammaScanBitCharge seen (false ∷ rest) successor suffix accepted =
  NatP.≤-step
    (actualGammaScanBitCharge (suc seen) rest successor suffix accepted)
actualGammaScanBitCharge seen (true ∷ rest) successor suffix accepted
  with Gamma.readPayload seen rest in parsed
... | nothing with accepted
... | ()
... | just (payload , after) with accepted
... | refl
  rewrite actualPayloadLengthConservation
    seen rest payload after parsed = NatP.≤-refl

actualGammaBinaryBitCharge :
  (word successor suffix : Word.BitWord) →
  Gamma.readGammaBinary word ≡ just (successor , suffix) →
  length successor + length suffix ≤ length word
actualGammaBinaryBitCharge word successor suffix success =
  actualGammaScanBitCharge zero word successor suffix success

-- The ACTUAL splitLast removes exactly one sign bit from the
-- read successor numeral, keeping every magnitude bit in order.
actualSignedSplitLastBitCharge :
  (successor prefix : Word.BitWord) (sign : Bool) →
  Signed.splitLast successor ≡ just (prefix , sign) →
  suc (length prefix) ≡ length successor
actualSignedSplitLastBitCharge [] prefix sign ()
actualSignedSplitLastBitCharge (b ∷ []) prefix sign accepted
  with accepted
... | refl = refl
actualSignedSplitLastBitCharge (b ∷ b2 ∷ rest) prefix sign accepted
  with Signed.splitLast (b2 ∷ rest) in parsed
... | nothing with accepted
... | ()
... | just (inside , last) with accepted
... | refl =
  cong suc
    (actualSignedSplitLastBitCharge (b2 ∷ rest) inside last parsed)

-- Source signed token width exactly matches its parsed canonical
-- gamma successor width, for either sign.
actualSignedTokenSameSuccessorCharge :
  (successor : Word.BitWord)
  (token : Signed.SignedMagnitudeBits) →
  Signed.signMagnitudeFromSuccessorBits successor ≡ just token →
  Charge.signedTokenBitCharge token ≤ length successor
actualSignedTokenSameSuccessorCharge successor token accepted
  with Signed.splitLast successor in parsed
... | nothing with accepted
... | ()
... | just (magnitude , true) with accepted
... | refl =
  NatP.≤-reflexive
    (actualSignedSplitLastBitCharge successor magnitude true parsed)
... | just (magnitude , false) with accepted
... | refl =
  NatP.≤-reflexive
    (actualSignedSplitLastBitCharge successor magnitude false parsed)

-- The real output from Signed.readSignedBinary cannot contribute
-- more signed-bit register growth than original input bits consumed
-- in precisely that word/suffix parse.
nativeSignedGammaConsumesItsBitCharge :
  (word suffix : Word.BitWord)
  (token : Signed.SignedMagnitudeBits) →
  Signed.readSignedBinary word ≡ just (token , suffix) →
  Charge.signedTokenBitCharge token + length suffix ≤ length word
nativeSignedGammaConsumesItsBitCharge word suffix token success
  with Gamma.readGammaBinary word in gamma
... | nothing with success
... | ()
... | just (successor , after)
  with Signed.signMagnitudeFromSuccessorBits successor in signed
... | nothing with success
... | ()
... | just parsed with success
... | refl =
  NatP.≤-trans
    (NatP.+-mono-≤
      (actualSignedTokenSameSuccessorCharge successor token signed)
      NatP.≤-refl)
    (actualGammaBinaryBitCharge word successor after gamma)
