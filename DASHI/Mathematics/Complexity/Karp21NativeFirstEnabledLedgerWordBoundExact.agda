module DASHI.Mathematics.Complexity.Karp21NativeFirstEnabledLedgerWordBoundExact where

------------------------------------------------------------------------
-- F2.1 REAL N21 FIRST-ENABLED SIGNED LEDGER INPUT-WIDTH CUT.
--
-- The executable source runs the actual binary graph parser on the
-- ORIGINAL word and the actual first-enabled signed event recorder on
-- the original certificate. If those actual source calls succeed,
-- the selected tokens are automatically a chronological subsequence
-- of the very same source-parsed original signed raw-edge stream.
--
-- Hence final two-register ripple accumulator bit-width is bounded
-- by initial width + length ORIGINAL GRAPH WORD. The source proof
-- supplies its own event-subsequence witness: the caller provides
-- only equalities describing actual source execution results.
--
-- This is register-width only; no unproved tape/head instruction
-- clock and no inference that the original typed language is in NP.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; [])
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; just)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact as Width
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Graph
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Machine
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinarySelectedEventTraceExact as Events
import DASHI.Mathematics.Complexity.Karp21NativeActualEventSubsequenceExact as Subsequence
import DASHI.Mathematics.Complexity.Karp21NativeWholeGraphLedgerInputBoundExact as FullWord

-- F2.1 SAME EXECUTION receipt, not an arbitrary signed weight list.
-- This charges the literal original source graph word, even if the
-- original gamma-numerical weights would be exponentially large
-- if decoded into unary Nat or arbitrary-precision ℤ.
actualFirstEnabledSelectedLedgerWidthBoundByOriginalWord :
  (word certificate n threshold : Word.BitWord)
  (edges : List Edge.BinaryRawEdge)
  (tokens : List Signed.SignedMagnitudeBits)
  (ledger : Ledger.SignedLedger) →
  Graph.readNativeWholeBinaryGraphWord word
    ≡ just (Graph.whole-binary-graph n edges threshold) →
  Events.actualFirstEnabledSelectedEvents (suc (length edges))
    (Machine.state Machine.active edges certificate []
      Ledger.emptyLedger threshold) ≡ just tokens →
  Width.actualLedgerWidth (Ledger.accumulateSigned tokens ledger)
    ≤ Width.actualLedgerWidth ledger + length word
actualFirstEnabledSelectedLedgerWidthBoundByOriginalWord
  word certificate n threshold edges tokens ledger graphProof eventsProof =
  FullWord.actualWholeGraphSelectedLedgerWidthBound
    word n threshold edges tokens ledger graphProof
    (Subsequence.actualFirstEnabledEventsAreParsedTokenSubsequence
      edges certificate [] Ledger.emptyLedger threshold tokens eventsProof)
