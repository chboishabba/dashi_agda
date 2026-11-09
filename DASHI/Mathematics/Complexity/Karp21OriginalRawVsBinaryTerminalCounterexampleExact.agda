module DASHI.Mathematics.Complexity.Karp21OriginalRawVsBinaryTerminalCounterexampleExact where

------------------------------------------------------------------------
-- D2 NEGATIVE CONTROL: no literal terminal-state identification.
--
-- The original raw-list first-enabled machine finishes whenever
-- both edge and certificate cursors are empty, independent of W.
-- The real binary whole-word machine performs the POSITIVE signed
-- threshold check before choosing finish/reject.
--
-- Thus their literal step transitions are NOT the same original
-- operation at terminal state. Any D2 weld MUST introduce a
-- threshold-aware terminal observation/quotient or a genuinely
-- selected augmented original state. An unqualified claim that
-- their phases or direct successors coincide is mathematically
-- false, even on a valid empty-edge graph and empty certificate.
--
-- Concrete witness: empty signed ledger P=N=0 and W=1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawListMachineExact as Raw
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact as Binary

oneLE : Word.BitWord
oneLE = true ∷ []

oldCompletedCursor : Raw.State
oldCompletedCursor =
  Raw.state Raw.active [] [] [] Ledger.emptyLedger

newCompletedCursor : Binary.State
newCompletedCursor =
  Binary.state Binary.active [] [] [] Ledger.emptyLedger oneLE

-- The old original raw-list finish rule is independent of threshold.
originalRawListFinishesWithoutThreshold :
  Raw.originalRawListOneStep oldCompletedCursor ≡
    just (Raw.state Raw.finished [] [] [] Ledger.emptyLedger)
originalRawListFinishesWithoutThreshold = refl

-- The new binary actual signed threshold rejects 0 >= 0+1.
emptyBinaryLedgerMissesOne :
  Positive.meetsOriginalPositiveThreshold Ledger.emptyLedger oneLE
    ≡ false
emptyBinaryLedgerMissesOne = refl

binaryWholeWordRejectsBelowThreshold :
  Binary.originalBinaryWholeVerifierStep newCompletedCursor ≡
    just (Binary.state Binary.rejected [] [] [] Ledger.emptyLedger oneLE)
binaryWholeWordRejectsBelowThreshold = refl

-- These two concrete source reductions disprove any terminal phase
-- identity that forgets W. The original raw-list machine must finish
-- FIRST, then pass its signed ledger through the source terminal
-- W predicate; the new binary machine fuses those two actions.

------------------------------------------------------------------------
-- POSITIVE WELD: keep the old finish step, then observe its signed
-- binary ledger against the SAME supplied W. This makes the original
-- machine's two-stage terminal semantics match the new fused binary
-- finish/reject step WITHOUT asserting false phase equality.
------------------------------------------------------------------------

rawFinishedThresholdObservation :
  Maybe Raw.State → Word.BitWord → Bool
rawFinishedThresholdObservation nothing threshold = false
rawFinishedThresholdObservation
  (just (Raw.state Raw.finished edges bits history ledger))
  threshold = Positive.meetsOriginalPositiveThreshold ledger threshold
rawFinishedThresholdObservation _ threshold = false

binaryAcceptedTerminalObservation :
  Maybe Binary.State → Bool
binaryAcceptedTerminalObservation
  (just (Binary.state Binary.accepted edges bits history ledger threshold)) =
  true
binaryAcceptedTerminalObservation _ = false

-- Original source raw-list finish is unconditional. The new binary
-- whole-word machine FUSES that finish with the strict W test.
-- This theorem pays precisely the missing terminal observation seam,
-- including signed negative/positive/zero ledgers and ALL W bitwords.
originalRawFinishedThresholdObservationSameBinaryTerminal :
  (ledger : Ledger.SignedLedger)
  (threshold : Word.BitWord) →
  rawFinishedThresholdObservation
    (Raw.OriginalMachine.directStep Raw.rules
      (Raw.state Raw.active [] [] [] ledger))
    threshold
  ≡ binaryAcceptedTerminalObservation
      (Binary.Compiled.directStep Binary.rules
        (Binary.state Binary.active [] [] [] ledger threshold))
originalRawFinishedThresholdObservationSameBinaryTerminal ledger threshold
  with Positive.meetsOriginalPositiveThreshold ledger threshold
... | true = refl
... | false = refl

-- The complete original machine-step weld must now compose:
-- 1) one-to-one advance/reject edges under binary address observation;
-- 2) this terminal threshold-observation equality;
-- 3) full selected event trace plus original gamma all-word transport.
-- A literal one-step terminal phase equation is NOT a valid obligation.
