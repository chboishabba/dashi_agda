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

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)

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
