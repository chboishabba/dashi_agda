{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact where

------------------------------------------------------------------------
-- N21: THE ORIGINAL GRAPH GRAMMAR HAS A STRICTLY POSITIVE THRESHOLD.
--
-- Original gamma(n) returns n as Nat, but the native gamma scanner
-- returns the bitword for n+1. We must subtract ONE in binary, rather
-- than treating that successor payload as a signed zigzag integer.
--
-- The output threshold is little-endian, directly consumable by
-- the Karp bit-native threshold comparator/adder. No unary Nat value
-- is constructed on the executable path.
--
-- Numeric all-word equality, machine tape clocks and graph parser
-- integration remain independent proof obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List.Base using (reverse)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Nat.Tactic.RingSolver using (solve)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Native
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact as Compare
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value

-- One-pass predecessor on an LSB-first positive binary successor.
-- If the head is 0, borrow continues; if the head is 1, it stops.
-- This code executes only over bits and never decodes a Nat.
predecessorLE : Word.BitWord → Word.BitWord
predecessorLE [] = []
predecessorLE (true ∷ rest) = false ∷ rest
predecessorLE (false ∷ rest) = true ∷ predecessorLE rest

anyOne : Word.BitWord → Bool
anyOne [] = false
anyOne (true ∷ rest) = true
anyOne (false ∷ rest) = anyOne rest

-- Genuine original gamma token -> binary representation of n.
-- Exactly n=0 is excluded, as in original graph acceptance.
readPositiveGammaLE :
  Word.BitWord → Maybe (Word.BitWord × Word.BitWord)
readPositiveGammaLE input with Native.readGammaBinary input
... | nothing = nothing
... | just (successorBE , suffix)
  with predecessorLE (reverse successorBE)
...   | nLE with anyOne nLE
...     | false = nothing
...     | true = just (nLE , suffix)

-- The threshold comparator no longer needs negative-threshold logic.
-- The original positive N21 condition is P >= N + W.
meetsOriginalPositiveThreshold :
  Ledger.SignedLedger → Word.BitWord → Bool
meetsOriginalPositiveThreshold (positive , negative) thresholdLE =
  Compare.atLeast positive (Add.addBits negative thresholdLE)

-- Definitional specialization of the already present signed comparison.
-- The original N21 wire parser must supply the positive threshold bits.
positiveThresholdIsGenericPositiveBranch :
  (positive negative thresholdLE : Word.BitWord) →
  meetsOriginalPositiveThreshold (positive , negative) thresholdLE
    ≡ Compare.atLeast positive (Add.addBits negative thresholdLE)
positiveThresholdIsGenericPositiveBranch positive negative thresholdLE = refl

-- Actual original gamma(0) is encoded as one true bit. It must reject.
gammaZeroThresholdRejected :
  readPositiveGammaLE (true ∷ []) ≡ nothing
gammaZeroThresholdRejected = refl

-- gamma(1)=010: successor bits=10, predecessor=01 little endian.
gammaOneThresholdAccepted :
  readPositiveGammaLE (false ∷ true ∷ false ∷ [])
    ≡ just (true ∷ false ∷ [] , [])
gammaOneThresholdAccepted = refl

-- gamma(2)=011: successor bits=11, predecessor=01 in little endian.
gammaTwoThresholdAccepted :
  readPositiveGammaLE (false ∷ true ∷ true ∷ [])
    ≡ just (false ∷ true ∷ [] , [])
gammaTwoThresholdAccepted = refl

------------------------------------------------------------------------
-- The bit-native predecessor is correct on every positive input
-- (anyOne = true). This is the mathematical observation of the
-- executable source, not a unary operation inside the decoder.
------------------------------------------------------------------------

two : Nat
two = suc (suc 0)

predecessorStepAlgebra :
  (x : Nat) →
  (suc 0 + two * x) + suc 0 ≡ two * (x + suc 0)
predecessorStepAlgebra x = solve (x ∷ [])

predecessorLEValue :
  (bits : Word.BitWord) →
  anyOne bits ≡ true →
  Value.valueLE (predecessorLE bits) + suc 0 ≡ Value.valueLE bits
predecessorLEValue [] ()
predecessorLEValue (true ∷ rest) accepted =
  NatP.+-comm (two * Value.valueLE rest) (suc 0)
predecessorLEValue (false ∷ rest) accepted =
  trans
    (predecessorStepAlgebra (Value.valueLE (predecessorLE rest)))
    (cong (λ n → two * n)
      (predecessorLEValue rest accepted))
