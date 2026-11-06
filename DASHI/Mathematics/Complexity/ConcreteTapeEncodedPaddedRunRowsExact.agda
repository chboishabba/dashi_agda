module DASHI.Mathematics.Complexity.ConcreteTapeEncodedPaddedRunRowsExact where

------------------------------------------------------------------------
-- THE ORIGINAL RUN'S ACTUAL ROWS = ITS CANONICAL ENCODED ROW BLOCKS.
--
-- The source encoder has no redundant row carrier; its row layout is
-- assembled recursively using Flat.encodeRow, appendBits, and the
-- original stepCanonicalLength transport. Induction below extracts
-- the actual row (plus its proof-relevant padded endcaps) at each
-- Global.Slot. No alternative tape semantics is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTraceDecodeExact as Trace
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapePaddedRunEndcapsExact as Padded
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

-- A row witness carries its original width equality explicitly.
-- The cast is the EXISTING Assignment.castBits, not a second codec.
EncodedPaddedRowAt :
  ∀ {machine start rows finish index}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish)
    (slot : Global.Slot index (suc (Run.runLength run))) →
  Set
EncodedPaddedRowAt {machine} {start} stateCoverage symbolCoverage run slot =
  Σ (Local.TapeRow machine) (λ row →
    Σ (Canonical.listLength (Local.cells row)
       ≡ Canonical.listLength (Local.cells start))
    (λ widthEq →
      (Slice.blockSliceBits slot
        (Assignment.encodeRunRows stateCoverage symbolCoverage run)
       ≡ Assignment.castBits
           (cong (λ n → n * Canonical.CellWidth machine) widthEq)
           (Flat.encodeRow stateCoverage symbolCoverage row))
      ×
      (Pattern.FrontPlain (Local.cells row)
       × Pattern.EndPlain (Local.cells row))))

-- Each selected row of the actual encoded run comes with both
-- original semantic endcap predicates. In the successor case the
-- existing step-length equality makes the encoder's cast definitional,
-- and the original append/drop identity exposes the encoded tail.
encodedPaddedRunRowAt :
  ∀ {machine start rows finish index}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish)
    (padded : Padded.AllWellFormedRunRowEndcaps run)
    (slot : Global.Slot index (suc (Run.runLength run))) →
  EncodedPaddedRowAt stateCoverage symbolCoverage run slot

encodedPaddedRunRowAt {start = start}
    stateCoverage symbolCoverage Run.runDone
    (Padded.endcapsDone plain) Global.here =
  start ,
    refl ,
    (Assignment.encodeRunRows_finalBlock
      stateCoverage symbolCoverage Run.runDone) ,
    plain

encodedPaddedRunRowAt {start = start}
    stateCoverage symbolCoverage (Run.runStep step rest)
    (Padded.endcapsStep plain later) Global.here =
  start ,
    refl ,
    (Assignment.encodeRunRows_head
      stateCoverage symbolCoverage step rest) ,
    plain


-- Transport the recursive encoded-row certificate across the one
-- ORIGINAL step-width equality, without abstracting a free length.
-- Both equality witnesses are eliminated simultaneously at the local
-- proof boundary; neither modifies the semantic run.
encodedTailBlockTransport :
  ∀ {machine count index currentCols nextCols rowCols}
    (stepEq : currentCols ≡ nextCols)
    (rowEq : rowCols ≡ nextCols)
    (slot : Global.Slot index count)
    (tail : CNF.Bits
      (count * (nextCols * Canonical.CellWidth machine)))
    (rowBits : CNF.Bits (rowCols * Canonical.CellWidth machine)) →
  Slice.blockSliceBits slot tail
    ≡ Assignment.castBits
        (cong (λ n → n * Canonical.CellWidth machine) rowEq)
        rowBits →
  Slice.blockSliceBits slot
    (Assignment.castBits
      (cong
        (λ n → count * (n * Canonical.CellWidth machine))
        (sym stepEq))
      tail)
    ≡ Assignment.castBits
        (cong (λ n → n * Canonical.CellWidth machine)
          (trans rowEq (sym stepEq)))
        rowBits
encodedTailBlockTransport refl refl slot tail rowBits certificate =
  certificate

encodedPaddedRunRowAt {machine} {start = start}
    stateCoverage symbolCoverage (Run.runStep step rest)
    (Padded.endcapsStep plain later) (Global.there slot)
    with encodedPaddedRunRowAt stateCoverage symbolCoverage rest later slot
... | row , rowWidthEq , (encodedEq , rowPlain) =
  row ,
    trans rowWidthEq (sym (Assignment.stepCanonicalLength step)) ,
    (trans
      (cong (Slice.blockSliceBits slot)
        (Canonical.dropAppendBits
          (Flat.encodeRow stateCoverage symbolCoverage start)
          (Assignment.castBits
            (cong
              (Trace.RowsTraceWidth machine (Run.runLength rest))
              (sym (Assignment.stepCanonicalLength step)))
            (Assignment.encodeRunRows stateCoverage symbolCoverage rest))))
      (encodedTailBlockTransport
        (Assignment.stepCanonicalLength step)
        rowWidthEq slot
        (Assignment.encodeRunRows stateCoverage symbolCoverage rest)
        (Flat.encodeRow stateCoverage symbolCoverage row)
        encodedEq)) ,
    rowPlain
