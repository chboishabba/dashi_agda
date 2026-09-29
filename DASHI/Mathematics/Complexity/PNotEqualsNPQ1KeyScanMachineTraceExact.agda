module DASHI.Mathematics.Complexity.PNotEqualsNPQ1KeyScanMachineTraceExact where

------------------------------------------------------------------------
-- RESTRICTED EXECUTION TRACE FOR THE ACTUAL FINITE-KEY SCANNER
--
-- Each active machine instruction:
--   compares the query with ONE next canonical finite truth-table key;
--   on equality, emits the current numerical position and terminates;
--   on inequality, advances the list cursor and position.
--
-- No instruction computes SAT, guesses semantic equality, or jumps directly
-- to an end-state witness. The trace is built inductively from the very same
-- decideTableEqual recursion as the executable key scanner.
--
-- Exact instruction count = findKeyComparisonCount query keys.
-- This is a genuine Iterates receipt for one restricted primitive, NOT a
-- whole Q1 graph-construction trace or a tape-machine complexity proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Sum.Base using (inj₁; inj₂)

import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableKeySearchExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1InstrumentedKeySearchExact as Instrumented
open import Data.Product using (proj₂)
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact as Executed

------------------------------------------------------------------------
-- A machine state cannot contain an unproduced proof of semantic admission.
------------------------------------------------------------------------

data KeyScanMachineState (remaining : Nat) : Set where
  scanning :
    List (Merge.SemanticKey remaining) →
    Nat →
    KeyScanMachineState remaining

  finished :
    Maybe Nat →
    Nat →
    KeyScanMachineState remaining

------------------------------------------------------------------------
-- Empty input is already terminal: no key comparison is executed.
------------------------------------------------------------------------

scanStart :
  ∀ {remaining : Nat} →
  List (Merge.SemanticKey remaining) →
  Nat →
  KeyScanMachineState remaining
scanStart [] position =
  finished nothing position
scanStart keys@(_ ∷ _) position =
  scanning keys position

------------------------------------------------------------------------
-- This step is restricted to one actual finite-vector equality attempt.
------------------------------------------------------------------------

scanMachineStep :
  ∀ {remaining : Nat} →
  Merge.SemanticKey remaining →
  KeyScanMachineState remaining →
  KeyScanMachineState remaining
scanMachineStep query (finished result count) =
  finished result count
scanMachineStep query (scanning [] position) =
  finished nothing position
scanMachineStep query (scanning (head ∷ tail) position)
    with Merge.decideTableEqual query head
... | inj₁ equal =
  finished (just position) (suc position)
... | inj₂ different =
  scanStart tail (suc position)

------------------------------------------------------------------------
-- Compute the literal final state by the same comparisons.
------------------------------------------------------------------------

scanMachineFinal :
  ∀ {remaining : Nat} →
  (query : Merge.SemanticKey remaining) →
  List (Merge.SemanticKey remaining) →
  Nat →
  KeyScanMachineState remaining
scanMachineFinal query [] position =
  finished nothing position
scanMachineFinal query (head ∷ tail) position
    with Merge.decideTableEqual query head
... | inj₁ equal =
  finished (just position) (suc position)
... | inj₂ different =
  scanMachineFinal query tail (suc position)

------------------------------------------------------------------------
-- Proof by actual steps, NOT a synthetic unit trace.
------------------------------------------------------------------------

scanMachineTrace :
  ∀ {remaining : Nat}
    (query : Merge.SemanticKey remaining)
    (keys : List (Merge.SemanticKey remaining))
    (position : Nat) →
  Executed.Iterates
    (scanMachineStep query)
    (Search.findKeyComparisonCount query keys)
    (scanStart keys position)
    (scanMachineFinal query keys position)
scanMachineTrace query [] position =
  Executed.iteratesZero
scanMachineTrace query (head ∷ tail) position
    with Merge.decideTableEqual query head
... | inj₁ equal =
  Executed.iteratesStep Executed.iteratesZero
... | inj₂ different =
  Executed.iteratesStep
    (scanMachineTrace query tail (suc position))

------------------------------------------------------------------------
-- This execution has exactly the count RETURNED by the instrumented scanner,
-- rather than a merely similar externally chosen natural number.
------------------------------------------------------------------------

scanMachineTraceMatchesInstrumentedCount :
  ∀ {remaining : Nat}
    (query : Merge.SemanticKey remaining)
    (keys : List (Merge.SemanticKey remaining))
    (position : Nat) →
  Executed.Iterates
    (scanMachineStep query)
    (proj₂ (Instrumented.scanKeyWithCharge query keys))
    (scanStart keys position)
    (scanMachineFinal query keys position)
scanMachineTraceMatchesInstrumentedCount
    query keys position
    rewrite Instrumented.scanKeyCountExact query keys =
  scanMachineTrace query keys position

------------------------------------------------------------------------
-- Count and behavior are tied to the SAME finite-vector comparison source.
-- A future full graph interpreter can compose these executions with its
-- enumeration, table evaluation, and emission steps. That composition must
-- still account for allocation and bit-level comparison cost before using
-- DirectDPChargedConstructionRun.machineStepCount.
------------------------------------------------------------------------
