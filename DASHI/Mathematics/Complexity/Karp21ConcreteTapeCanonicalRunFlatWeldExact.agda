module DASHI.Mathematics.Complexity.Karp21ConcreteTapeCanonicalRunFlatWeldExact where

------------------------------------------------------------------------
-- P1 Cook-Levin reuse, SAME CONCRETE TAPE RUN:
--
--   actual WellFormedTapeRun
--   -> existing per-transition CNF characterization
--   -> same canonical six-cell finite-width codec
--   -> actual flat Bits tableau for the identical start/tail rows.
--
-- The original row endpoint and exact run length are retained.
-- No alternative machine, fresh Boolean variable layout or
-- fictional SAT solver is constructed here.
--
-- Remaining terminal gates: coordinate placement of local clauses
-- into this SAME flat assignment, endpoints, accepting-run iff SAT,
-- polynomial map, original E20 and Karp chain; SATNotInP separate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; _∷_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat

record CanonicalSameRunCNFPacket
    (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (start : Local.TapeRow machine)
    (rows : List (Local.TapeRow machine))
    (finish : Local.TapeRow machine) : Set₁ where
  field
    originalRun : Run.WellFormedTapeRun machine start rows finish

    encodedCanonicalRunPath :
      Run.EncodedCNFRunPath
        (Canonical.canonicalWindowCodec
          machine stateCoverage symbolCoverage)
        start rows finish

    sameRowsFlatAssignment :
      Flat.FlatConcreteTableauAssignment
        machine stateCoverage symbolCoverage (start ∷ rows)

    originalStartRowPullback :
      Canonical.takeBits
        (Canonical.listLength (Local.cells start) *
          Canonical.CellWidth machine)
        (Flat.encodeRows
          stateCoverage symbolCoverage (start ∷ rows))
        ≡ Flat.encodeRow stateCoverage symbolCoverage start

    exactOriginalRunLength :
      Run.encodedRunLength encodedCanonicalRunPath
        ≡ Run.runLength originalRun

-- All the fields reuse the ORIGINAL existing Agda owners and are
-- about the SAME input run and the SAME literal flat tableau bits.
canonicalSameRunCNFPacket :
  ∀ {machine start rows finish}
  (stateCoverage :
    Canonical.EnumerationCoverage (Local.finiteState machine))
  (symbolCoverage :
    Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Run.WellFormedTapeRun machine start rows finish →
  CanonicalSameRunCNFPacket
    machine stateCoverage symbolCoverage start rows finish
canonicalSameRunCNFPacket {machine} {start} {rows} {finish}
  stateCoverage symbolCoverage run = record
  { originalRun = run
  ; encodedCanonicalRunPath =
      Run.runToEncodedCNFPath
        (Canonical.canonicalWindowCodec
          machine stateCoverage symbolCoverage) run
  ; sameRowsFlatAssignment =
      Flat.flatTableauAssignment
        stateCoverage symbolCoverage (start ∷ rows)
  ; originalStartRowPullback =
      Flat.headRowPullback
        stateCoverage symbolCoverage start rows
  ; exactOriginalRunLength =
      Run.runToCNFPreservesLength
        (Canonical.canonicalWindowCodec
          machine stateCoverage symbolCoverage) run
  }
