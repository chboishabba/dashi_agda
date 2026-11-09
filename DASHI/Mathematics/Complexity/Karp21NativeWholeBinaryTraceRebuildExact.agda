module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryTraceRebuildExact where

------------------------------------------------------------------------
-- E1 original SAME-WORD full ordered selected-signed-weight trace.
--
-- LHS executes the ACTUAL native binary whole-graph parser and
-- follows ACTUAL first-enabled transitions, emitting precisely the
-- selected signed gamma tokens. Original signed integers are exposed
-- only through a proof-side observation after execution.
--
-- RHS executes the LITERAL original Fin-free graph reader and
-- original chronological rawSelectedTrace, on the SAME bitwords.
-- Rejects malformed graphs and certificates as nothing; a valid
-- certificate with score < W still has its full selected-edge trace.
--
-- Distinct from the later physical bit-TM trace/referee receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.List.Base using (List; length)
open import Data.Integer.Base using (ℤ)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Graph
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphOriginalExact as Weld
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Machine
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinarySelectedEventTraceExact as Events
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawTraceReplayExact as Trace

-- Proof-side original ℤ trace, after consuming the ACTUAL first-
-- enabled binary source events. No Nat endpoint decoding at runtime.
nativeWholeBinarySelectedTrace :
  Word.BitWord → Word.BitWord →
  Maybe (List ℤ)
nativeWholeBinarySelectedTrace word certificate
  with Graph.readNativeWholeBinaryGraphWord word
... | nothing = nothing
... | just (Graph.whole-binary-graph n edges threshold) =
  Events.observeMaybeSignedEvents
    (Events.actualFirstEnabledSelectedEvents
      (suc (length edges))
      (Machine.state Machine.active edges certificate []
        Ledger.emptyLedger threshold))

-- The original independent source execution is used only here.
originalWholeWordSelectedTrace :
  Word.BitWord → Word.BitWord →
  Maybe (List ℤ)
originalWholeWordSelectedTrace word certificate
  with Original.readRawGraphWord word
... | nothing = nothing
... | just (Original.parsed-raw-graph n edges threshold) =
  Trace.rawSelectedTrace edges certificate []

-- E1: full ordered source selected-edge trace and malformed failure
-- alignment, not just a final Boolean or total ℤ score.
karpFractranTraceRebuildExact :
  (word certificate : Word.BitWord) →
  nativeWholeBinarySelectedTrace word certificate ≡
    originalWholeWordSelectedTrace word certificate
karpFractranTraceRebuildExact word certificate
  with Graph.readNativeWholeBinaryGraphWord word
     | Weld.nativeWholeBinaryGraphWordSameOriginal word
... | nothing | graphEq
  rewrite sym graphEq = refl
... | just (Graph.whole-binary-graph n edges threshold) | graphEq
  rewrite sym graphEq =
  Events.nativeFirstEnabledSelectedEventsSameOriginal
    edges certificate [] Ledger.emptyLedger threshold
