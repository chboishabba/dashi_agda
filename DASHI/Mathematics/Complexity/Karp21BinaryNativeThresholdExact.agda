{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact where

------------------------------------------------------------------------
-- K05 N21: EXECUTABLE SIGNED THRESHOLD WITHOUT INTEGER REBUILDING.
--
-- Original signed score = (positive total) - (negative total).
-- Test score >= threshold by moving its magnitude across the sign:
--   threshold = +t: positive >= negative + t
--   threshold = -t: positive + t >= negative
--
-- All arithmetic uses the selected Karp ripple adder; the comparison
-- below is a bitwise high-significance-first decision built from
-- structurally decreasing LITTLE-ENDIAN input lists.
--
-- Numerical comparison correctness, original source threshold weld,
-- full-word cost and graph integration remain separate proof gates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (reverse)
open import Data.Product using (_,_)
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger

data BitOrdering : Set where
  less equal greater : BitOrdering

-- A higher differing bit dominates all lower bits. If higher bits
-- compare equally, the current less significant bits decide.
orderBit : Bool → Bool → BitOrdering
orderBit false false = equal
orderBit false true = less
orderBit true false = greater
orderBit true true = equal

selectHigh : BitOrdering → BitOrdering → BitOrdering
selectHigh equal lower = lower
selectHigh less lower = less
selectHigh greater lower = greater

-- Zero extension is implicit. Leading zeros in the mathematical
-- numeral do not produce an incorrect length-order shortcut.
compareLE : Word.BitWord → Word.BitWord → BitOrdering
compareLE [] [] = equal
compareLE (a ∷ as) [] =
  selectHigh (compareLE as []) (orderBit a false)
compareLE [] (b ∷ bs) =
  selectHigh (compareLE [] bs) (orderBit false b)
compareLE (a ∷ as) (b ∷ bs) =
  selectHigh (compareLE as bs) (orderBit a b)

atLeast : Word.BitWord → Word.BitWord → Bool
atLeast xs ys with compareLE xs ys
... | less = false
... | equal = true
... | greater = true

-- Signed threshold is read from the ACTUAL native sign-magnitude
-- representation; no Nat/unzigzag arithmetic executes in the check.
ledgerMeetsSignedThreshold :
  Ledger.SignedLedger → Signed.SignedMagnitudeBits → Bool
ledgerMeetsSignedThreshold (positive , negative)
  (Signed.positive magnitude) =
  atLeast positive (Add.addBits negative (reverse magnitude))
ledgerMeetsSignedThreshold (positive , negative)
  (Signed.negative magnitude) =
  atLeast (Add.addBits positive (reverse magnitude)) negative

-- A single zero threshold example uses only definitional reduction.
zeroThresholdAcceptsEmpty :
  ledgerMeetsSignedThreshold Ledger.emptyLedger
    (Signed.positive []) ≡ true
zeroThresholdAcceptsEmpty = refl
