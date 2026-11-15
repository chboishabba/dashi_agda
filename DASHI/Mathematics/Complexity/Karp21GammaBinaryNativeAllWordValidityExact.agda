{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeAllWordValidityExact where

------------------------------------------------------------------------
-- K05: COMPLETE ORIGINAL ALL-WORD GAMMA ACCEPT/REJECT EQUIVALENCE.
--
-- A binary-native gamma token accepts precisely when the original
-- source-owned numeric readGamma accepts, including malformed,
-- truncated and suffix-bearing inputs. This validity check does not
-- run numeric pow2 arithmetic or reconstruct a Peano Nat.
--
-- Reuses the separately proved all-word numeric-observation weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Native
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeAllWordNumericalWeldExact as Weld

accepted : ∀ {A : Set} → Maybe A → Bool
accepted nothing = false
accepted (just _) = true

-- The numeric observation and native parser share exactly the same
-- prefix and payload branches; no condition on input validity.
nativeScanAcceptanceSameNumeric :
  (seen : Nat) (word : Word.BitWord) →
  accepted (Native.scanZeros seen word)
    ≡ accepted (Weld.scanNativeNumericView seen word)
nativeScanAcceptanceSameNumeric seen [] = refl
nativeScanAcceptanceSameNumeric seen (false ∷ word) =
  nativeScanAcceptanceSameNumeric (suc seen) word
nativeScanAcceptanceSameNumeric seen (true ∷ word)
  with Native.readPayload seen word
... | nothing = refl
... | just (payload , suffix) = refl

-- Literal original source words and binary-native words have the
-- same acceptance/rejection, regardless of trailing bits.
nativeGammaAcceptsExactlyOriginal :
  (word : Word.BitWord) →
  accepted (Native.readGammaBinary word)
    ≡ accepted (Old.readGamma word)
nativeGammaAcceptsExactlyOriginal word =
  trans
    (nativeScanAcceptanceSameNumeric zero word)
    (cong accepted (Weld.originalGammaSameAllWordNumericalObservation word))
