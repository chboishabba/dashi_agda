module DASHI.Mathematics.Complexity.Karp21NativeWholeGraphLedgerInputBoundExact where

------------------------------------------------------------------------
-- F2.1: actual binary graph n/m gamma header + 3m-budgeted source
-- raw edge parser pays final selected two-lane signed ledger width
-- by the LENGTH OF THE COMPLETE ORIGINAL GRAPH WORD.
--
-- No independent/unbounded weight sequence: each selected token
-- must have the exact chronological token-subsequence witness from
-- the ACTUAL NativeWholeBinaryGraph binaryEdges parsed from word.
--
-- Outstanding: construct this witness from the actual first-enabled
-- binary selected event emitter, bound other allocations, and give
-- a physical bit-tape/head/cell cost model and polynomial clock.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.List.Base using (length)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeUnsignedEndpointBitReaderExact as Endpoint
import DASHI.Mathematics.Complexity.Karp21NativeBinaryHeaderBudgetExact as Header
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCountBudgetExact as Budget
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact as Valid
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Whole
import DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact as Width
import DASHI.Mathematics.Complexity.Karp21NativeSelectedLedgerInputBoundExact as Selected
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21NativeRawEdgeInputChargeExact as RawCharge

-- Both ACTUAL original gamma headers consume only a source prefix.
-- This is an input-length fact, not a numerical bound on n/m values.
binaryNativeHeadersSuffixFitsOriginalWord :
  (word n m afterM : Word.BitWord) →
  Header.readNativeBinaryGraphHeader word
    ≡ just (Header.binary-header n m afterM) →
  length afterM ≤ length word
binaryNativeHeadersSuffixFitsOriginalWord word n m afterM accepted
  with Endpoint.readGammaNatLE word in first
... | nothing with accepted
... | ()
... | just (firstBits , afterN)
  with Endpoint.readGammaNatLE afterN in second
... | nothing with accepted
... | ()
... | just (secondBits , tail) with accepted
... | refl =
  NatP.≤-trans
    (RawCharge.unsignedEndpointSuffixLengthBound
      afterN secondBits tail second)
    (RawCharge.unsignedEndpointSuffixLengthBound
      word firstBits afterN first)

-- The actual budgeted branch does not change the consumed suffix:
-- it only rejects an impossible 3m count before entering an edge loop.
budgetedNativeHeaderSuffixFitsOriginalWord :
  (word n m afterM : Word.BitWord) →
  Header.readNativeBinaryBudgetedHeader word
    ≡ just (Header.binary-header n m afterM) →
  length afterM ≤ length word
budgetedNativeHeaderSuffixFitsOriginalWord word n m afterM accepted
  with Header.readNativeBinaryGraphHeader word in header
... | nothing with accepted
... | ()
... | just (Header.binary-header n' m' suffix)
  with Budget.binaryCountBudget m' suffix
... | false with accepted
... | ()
... | true with accepted
... | refl =
  binaryNativeHeadersSuffixFitsOriginalWord
    word n' m' suffix header

-- F2.1 original FULL graph input charge: once a successful original
-- parser has produced exact binary edges, every chronological
-- selection of those actual tokens has enough input-bit budget.
actualWholeGraphSelectedLedgerWidthBound :
  (word n threshold : Word.BitWord)
  (edges : List Edge.BinaryRawEdge)
  (tokens : List Signed.SignedMagnitudeBits)
  (ledger : Ledger.SignedLedger) →
  Whole.readNativeWholeBinaryGraphWord word
    ≡ just (Whole.whole-binary-graph n edges threshold) →
  Selected.SelectedFromParsedEdges tokens edges →
  Width.actualLedgerWidth (Ledger.accumulateSigned tokens ledger)
    ≤ Width.actualLedgerWidth ledger + length word
actualWholeGraphSelectedLedgerWidthBound
  word n threshold edges tokens ledger success selected
  with Header.readNativeBinaryBudgetedHeader word in header
... | nothing with success
... | ()
... | just (Header.binary-header originalN m afterM)
  with Whole.readBinaryRawEdgesFuel (length afterM) m afterM in stream
... | nothing with success
... | ()
... | just (parsed , afterEdges)
  with Positive.readPositiveGammaLE afterEdges
... | nothing with success
... | ()
... | just (w , _ ∷ _) with success
... | ()
... | just (w , [])
  with Valid.validNativeBinaryEdges originalN Valid.noPrevious parsed
... | false with success
... | ()
... | true with success
... | refl =
  NatP.≤-trans
    (Selected.actualSelectedLedgerWidthFromOriginalInput
      selected afterM afterEdges m (length afterM)
      ledger stream)
    (NatP.+-mono-≤ NatP.≤-refl
      (budgetedNativeHeaderSuffixFitsOriginalWord
        word originalN m afterM header))
