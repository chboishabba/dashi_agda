module DASHI.Mathematics.Complexity.ConcreteTapeEncodedPaddedRunDecodeWeldExact where

------------------------------------------------------------------------
-- EXACT ORIGINAL ACCEPTING-RUN ASSIGNMENT -> ORIGINAL DECODED ROWS.
--
-- No invented row codec or standalone boundary bit. This joins:
--  Assignment.encodeAcceptingRunAssignment_base
--  Slice.pullbackFinLeft_eq_takeBits
--  Slice.rowSliceBits_eq_blockSlice
--  Assignment.encodeRunBaseTrace_rows
--  EncodedPaddedRunRows.encodedPaddedRunRowAt
--  Initial.decodeRow_encodeRow
--
-- The only run premise is the original proof-relevant HeadMargin
-- certificate; the first/last boundary facts come from that run.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalBlockSliceConsistencyExact as Slice
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalFormulaSemanticsExact as FormulaSem
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeEncodedPaddedRunRowsExact as Encoded
import DASHI.Mathematics.Complexity.ConcreteTapePaddedRunEndcapsExact as Padded
import DASHI.Mathematics.Complexity.ConcreteTapeDecodedEndcapSameObjectExact as Same
import DASHI.Mathematics.Complexity.ConcreteTapeInitialDecodeSameObjectExact as Initial
import DASHI.Mathematics.Complexity.ConcreteTapeLocalWindowPatternsExact as Pattern
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

-- EXACT encoded base prefix, rather than a merely equisatisfiable
-- or extensionally similar trace.
encodedAcceptanceBaseSameObject :
  ∀ {machine start rows finish}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun machine start rows finish) →
  FormulaSem.baseTraceBits
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
  ≡ Assignment.encodeRunBaseTrace
      stateCoverage symbolCoverage (Accepting.run certificate)
encodedAcceptanceBaseSameObject
    stateCoverage symbolCoverage certificate =
  trans
    (Slice.pullbackFinLeft_eq_takeBits
      (Assignment.encodeAcceptingRunAssignment
        stateCoverage symbolCoverage certificate))
    (Assignment.encodeAcceptingRunAssignment_base
      stateCoverage symbolCoverage certificate)

-- Every literal decoded SAT row is the slot-selected original run
-- block, with the same Fin and global/extended widths.
encodedAcceptanceRowSliceSameObject :
  ∀ {machine start rows finish index}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun machine start rows finish)
    (slot :
      Global.Slot index (suc (Accepting.acceptingRunLength certificate))) →
  Global.rowSliceBits slot
    (FormulaSem.baseTraceBits
      (Assignment.encodeAcceptingRunAssignment
        stateCoverage symbolCoverage certificate))
  ≡ Slice.blockSliceBits slot
      (Assignment.encodeRunRows
        stateCoverage symbolCoverage (Accepting.run certificate))
encodedAcceptanceRowSliceSameObject
    stateCoverage symbolCoverage certificate slot =
  trans
    (cong (Global.rowSliceBits slot)
      (encodedAcceptanceBaseSameObject
        stateCoverage symbolCoverage certificate))
    (trans
      (Slice.rowSliceBits_eq_blockSlice slot
        (Assignment.encodeRunBaseTrace
          stateCoverage symbolCoverage (Accepting.run certificate)))
      (cong (Slice.blockSliceBits slot)
        (Assignment.encodeRunBaseTrace_rows
          stateCoverage symbolCoverage (Accepting.run certificate))))

-- This fixes the "decode of cast" difficulty by eliminating the
-- genuine source width equality, not by postulating codec invariance.
encodedPaddedRowDecodesSameObject :
  ∀ {machine start rows finish index}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (run : Run.WellFormedTapeRun machine start rows finish)
    (padded : Padded.AllWellFormedRunRowEndcaps run)
    (slot : Global.Slot index (suc (Run.runLength run))) →
  Σ (Local.TapeRow machine) (λ row →
    (Decode.decodeRow stateCoverage symbolCoverage
      (Canonical.listLength (Local.cells start))
      (Slice.blockSliceBits slot
        (Assignment.encodeRunRows stateCoverage symbolCoverage run))
      ≡ row)
    ×
    (Pattern.FrontPlain (Local.cells row)
     × Pattern.EndPlain (Local.cells row)))
encodedPaddedRowDecodesSameObject
    {start = start}
    stateCoverage symbolCoverage run padded slot
  with Encoded.encodedPaddedRunRowAt
    stateCoverage symbolCoverage run padded slot
... | row , refl , (blockEq , endcaps) =
  row ,
    trans
      (cong
        (Decode.decodeRow stateCoverage symbolCoverage
          (Canonical.listLength (Local.cells start)))
        blockEq)
      (Initial.decodeRow_encodeRow
        stateCoverage symbolCoverage row) ,
    endcaps

------------------------------------------------------------------------
-- The reverse exact SAT endcap producer for the ORIGINAL encoded run.
-- Width and time equalities are ordinary original-source index
-- transports (not axioms); once matched to refl this is the same
-- extended assignment and the same rowSlot used by global CNF.
------------------------------------------------------------------------

encodedAcceptingAssignmentDecodedEndcaps :
  ∀ {machine start rows finish steps colsMinusOne}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (certificate :
      Accepting.AcceptingWellFormedRun machine start rows finish)
    (padded :
      Padded.AllWellFormedRunRowEndcaps
        (Accepting.run certificate)) →
  Accepting.acceptingRunLength certificate ≡ steps →
  Canonical.listLength (Local.cells start) ≡ suc colsMinusOne →
  ∀ {rowIndex}
    (slot : Global.Slot rowIndex (suc steps)) →
  Same.DecodedRowEndcapsPlain
    stateCoverage symbolCoverage slot
    (Assignment.encodeAcceptingRunAssignment
      stateCoverage symbolCoverage certificate)
encodedAcceptingAssignmentDecodedEndcaps
    stateCoverage symbolCoverage certificate padded
    refl refl slot
  with encodedPaddedRowDecodesSameObject
    stateCoverage symbolCoverage
    (Accepting.run certificate) padded slot
... | row , (decodedEq , (frontPlain , backPlain)) =
  record
    { Same.front = subst
        (λ r → Pattern.FrontPlain (Local.cells r))
        (sym entireRowEq)
        frontPlain
    ; Same.back = subst
        (λ r → Pattern.EndPlain (Local.cells r))
        (sym entireRowEq)
        backPlain
    }
  where
    encodedRowEq =
      encodedAcceptanceRowSliceSameObject
        stateCoverage symbolCoverage certificate slot

    entireRowEq =
      trans
        (cong
          (Decode.decodeRow stateCoverage symbolCoverage
            (Canonical.listLength (Local.cells start)))
          encodedRowEq)
        decodedEq
