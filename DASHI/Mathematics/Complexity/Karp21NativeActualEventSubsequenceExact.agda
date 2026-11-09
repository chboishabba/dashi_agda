module DASHI.Mathematics.Complexity.Karp21NativeActualEventSubsequenceExact where

------------------------------------------------------------------------
-- F2.1 LAST SOURCE SEMANTIC LEAF: selected signed events from ACTUAL
-- original-wire FIRST-ENABLED binary N21 machine are a chronological
-- sublist of the SAME original raw-edge signed token registers.
--
-- The source event recorder is Events.actualFirstEnabledSelectedEvents
-- using the ACTUAL Compiled.directStep advance/finish/reject choice.
-- No caller-supplied fake selected tokens, symbolic score or oracle.
-- On malformed certificates the recorder returns nothing; theorem
-- concerns an actual successful selected trace.
--
-- Coupled with native source gamma input accounting, this pays
-- selected ledger register width in ORIGINAL graph WORD bits.
--
-- Agda kernel acceptance still pending; physical tape/head time
-- and all allocations are distinct F1/F3/F4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.List.Base using (length)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Machine
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinarySelectedEventTraceExact as Events
import DASHI.Mathematics.Complexity.Karp21NativeSelectedLedgerInputBoundExact as Selected

-- Proof on the genuine source first-enabled transition function:
-- selected result is neither a fabricated trace nor merely the
-- arithmetic equality of selected signed integer scores.
actualFirstEnabledEventsAreParsedTokenSubsequence :
  (edges : List Edge.BinaryRawEdge)
  (certificate : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger : Ledger.SignedLedger)
  (threshold : Word.BitWord)
  (tokens : List Signed.SignedMagnitudeBits) →
  Events.actualFirstEnabledSelectedEvents (suc (length edges))
    (Machine.state Machine.active edges certificate
      history ledger threshold)
    ≡ just tokens →
  Selected.SelectedFromParsedEdges tokens edges
actualFirstEnabledEventsAreParsedTokenSubsequence
  [] [] history ledger threshold tokens success
  with Positive.meetsOriginalPositiveThreshold ledger threshold
... | true with success
... | refl = Selected.selected-empty
... | false with success
... | refl = Selected.selected-empty
actualFirstEnabledEventsAreParsedTokenSubsequence
  [] (bit ∷ rest) history ledger threshold tokens ()
actualFirstEnabledEventsAreParsedTokenSubsequence
  (edge ∷ rest) [] history ledger threshold tokens ()
actualFirstEnabledEventsAreParsedTokenSubsequence
  (edge ∷ rest) (a ∷ []) history ledger threshold tokens ()
actualFirstEnabledEventsAreParsedTokenSubsequence
  (Edge.binary-edge u v token ∷ rest) (a ∷ b ∷ bits)
  history ledger threshold tokens success
  with History.endpointConsistentBinary u a history
     | History.endpointConsistentBinary v b history
... | false | _ with success
... | ()
... | true | false with success
... | ()
... | true | true
  with Boolean.boolEqual a b
... | true
  with Events.actualFirstEnabledSelectedEvents (suc (length rest))
    (Machine.state Machine.active rest bits
      (History.recordBinaryEndpointPair u v a b history)
      ledger threshold) in recursive
... | nothing with success
... | ()
... | just chosen with success
... | refl =
  Selected.selected-skip
    (actualFirstEnabledEventsAreParsedTokenSubsequence
      rest bits (History.recordBinaryEndpointPair u v a b history)
      ledger threshold chosen recursive)
... | false
  with Events.actualFirstEnabledSelectedEvents (suc (length rest))
    (Machine.state Machine.active rest bits
      (History.recordBinaryEndpointPair u v a b history)
      (Ledger.insertSigned token ledger) threshold) in recursive
... | nothing with success
... | ()
... | just chosen with success
... | refl =
  Selected.selected-take
    (actualFirstEnabledEventsAreParsedTokenSubsequence
      rest bits (History.recordBinaryEndpointPair u v a b history)
      (Ledger.insertSigned token ledger) threshold chosen recursive)
