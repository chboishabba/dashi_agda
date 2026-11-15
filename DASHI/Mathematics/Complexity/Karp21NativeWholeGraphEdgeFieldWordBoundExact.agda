module DASHI.Mathematics.Complexity.Karp21NativeWholeGraphEdgeFieldWordBoundExact where

------------------------------------------------------------------------
-- F2.2 complete ORIGINAL N21 graph WORD pays all stored raw-edge
-- binary endpoint and signed magnitude registers:
--   sum(length u + length v + 1 + length signed magnitude) ≤ |word|.
--
-- No original Nat n/m/u/v or original integer w is executed by
-- source reader. All proofs are on ACTUAL native binary graph parse
-- and source grammar input cursor / unchanged suffix boundaries.
--
-- Excludes list-cell/pointer overhead, record tags, duplicated
-- temporary buffers, endpoint-history allocation and tape head cost.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.List.Base using (length)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeBinaryHeaderBudgetExact as Header
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact as Valid
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Whole
import DASHI.Mathematics.Complexity.Karp21NativeWholeGraphLedgerInputBoundExact as Headers
import DASHI.Mathematics.Complexity.Karp21NativeFullEdgeFieldInputBoundExact as Fields

-- Same actual binary graph parser used by the verifier. It returns
-- the exact stored raw-edge record list; no separately assumed m
-- count or original signed edge interpretation is permitted.
actualWholeBinaryGraphEdgeFieldWidthAtMostOriginalWord :
  (word n threshold : Word.BitWord)
  (edges : List Edge.BinaryRawEdge) →
  Whole.readNativeWholeBinaryGraphWord word
    ≡ just (Whole.whole-binary-graph n edges threshold) →
  Fields.allBinaryRawEdgeRegisterCharges edges ≤ length word
actualWholeBinaryGraphEdgeFieldWidthAtMostOriginalWord
  word n threshold edges accepted
  with Header.readNativeBinaryBudgetedHeader word in header
... | nothing with accepted
... | ()
... | just (Header.binary-header sourceN m afterM)
  with Whole.readBinaryRawEdgesFuel (length afterM) m afterM in stream
... | nothing with accepted
... | ()
... | just (parsed , afterEdges)
  with Positive.readPositiveGammaLE afterEdges
... | nothing with accepted
... | ()
... | just (w , _ ∷ _) with accepted
... | ()
... | just (w , [])
  with Valid.validNativeBinaryEdges sourceN Valid.noPrevious parsed
... | false with accepted
... | ()
... | true with accepted
... | refl =
  NatP.≤-trans
    (NatP.m≤m+n
      (Fields.allBinaryRawEdgeRegisterCharges parsed)
      (length afterEdges))
    (NatP.≤-trans
      (Fields.nativeRawEdgeStreamAllRegisterFieldsFitInput
        (length afterM) m afterM afterEdges parsed stream)
      (Headers.budgetedNativeHeaderSuffixFitsOriginalWord
        word sourceN m afterM header))
