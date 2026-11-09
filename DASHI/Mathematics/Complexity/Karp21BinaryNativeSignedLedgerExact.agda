{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact where

------------------------------------------------------------------------
-- K05: EXECUTABLE BINARY SIGNED-WEIGHT ACCUMULATOR, NO SUBTRACTION.
--
-- Store positive and negative mass independently. Addition is the
-- original bit-native ripple adder, and input is the selected gamma
-- successor binary payload split by its sign bit.
--
-- The represented integer is positiveTotal - negativeTotal, but
-- subtraction is never performed in this executable accumulator.
--
-- Bits in SignedMagnitudeBits are big-endian. The original adder uses
-- little-endian bits; reverse is a linear representation conversion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Base using (reverse; length; _++_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value

SignedLedger : Set
SignedLedger = Word.BitWord × Word.BitWord

emptyLedger : SignedLedger
emptyLedger = [] , []

insertSigned :
  Signed.SignedMagnitudeBits → SignedLedger → SignedLedger
insertSigned (Signed.positive magnitude) (positive , negative) =
  Add.addBits positive (reverse magnitude) , negative
insertSigned (Signed.negative magnitude) (positive , negative) =
  positive , Add.addBits negative (reverse magnitude)

accumulateSigned :
  List Signed.SignedMagnitudeBits → SignedLedger → SignedLedger
accumulateSigned [] ledger = ledger
accumulateSigned (signed ∷ rest) ledger =
  accumulateSigned rest (insertSigned signed ledger)

positiveValue : SignedLedger → Nat
positiveValue ledger = Value.valueLE (proj₁ ledger)

negativeValue : SignedLedger → Nat
negativeValue ledger = Value.valueLE (proj₂ ledger)

signedMagnitudeValue : Signed.SignedMagnitudeBits → Nat
signedMagnitudeValue (Signed.positive magnitude) =
  Value.valueLE (reverse magnitude)
signedMagnitudeValue (Signed.negative magnitude) =
  Value.valueLE (reverse magnitude)

-- Adding a positive signed token updates *only* the positive lane.
insertPositiveValue :
  (magnitude : Word.BitWord) (ledger : SignedLedger) →
  positiveValue (insertSigned (Signed.positive magnitude) ledger) ≡
  positiveValue ledger + Value.valueLE (reverse magnitude)
insertPositiveValue magnitude (positive , negative) =
  Value.addBitsValue positive (reverse magnitude)

insertPositiveNegativePreserved :
  (magnitude : Word.BitWord) (ledger : SignedLedger) →
  negativeValue (insertSigned (Signed.positive magnitude) ledger) ≡
  negativeValue ledger
insertPositiveNegativePreserved magnitude ledger = refl

-- Adding a negative signed token updates *only* the negative lane.
insertNegativeValue :
  (magnitude : Word.BitWord) (ledger : SignedLedger) →
  negativeValue (insertSigned (Signed.negative magnitude) ledger) ≡
  negativeValue ledger + Value.valueLE (reverse magnitude)
insertNegativeValue magnitude (positive , negative) =
  Value.addBitsValue negative (reverse magnitude)

insertNegativePositivePreserved :
  (magnitude : Word.BitWord) (ledger : SignedLedger) →
  positiveValue (insertSigned (Signed.negative magnitude) ledger) ≡
  positiveValue ledger
insertNegativePositivePreserved magnitude ledger = refl

-- A source-level use of Nat is restricted to the proof-side value
-- observation, not an operation executed by accumulateSigned.
-- The complete graph verifier must still compare the two lanes,
-- incorporate signed threshold semantics and prove an actual clock.
