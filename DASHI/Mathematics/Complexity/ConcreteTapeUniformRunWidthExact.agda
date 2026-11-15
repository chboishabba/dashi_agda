module DASHI.Mathematics.Complexity.ConcreteTapeUniformRunWidthExact where

------------------------------------------------------------------------
-- ORIGINAL RUN -> SINGLE FIXED-WIDTH TABLEAU FIBRE (NO NEW SEMANTICS).
--
-- An original WellFormedTapeRun is a path in the category of tape
-- rows. Each step preserves the canonical row-length functor.
-- The chosen initial width therefore yields a section of the
-- constant-width fibre over ALL original physical time slots.
--
-- This is a proof-relevant view, not a replacement tape datatype:
-- every row returned below is definitionally the original run row.
-- It avoids a repository-wide rewrite of the original Agda owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment

-- The original run's row at the ORIGINAL indexed time coordinate.
originalRowAt :
  ∀ {machine start rows finish index}
    (run : Run.WellFormedTapeRun machine start rows finish) →
  Global.Slot index (suc (Run.runLength run)) →
  Local.TapeRow machine
originalRowAt {start = start} Run.runDone Global.here = start
originalRowAt {start = current}
    (Run.runStep step rest) Global.here = current
originalRowAt (Run.runStep step rest) (Global.there slot) =
  originalRowAt rest slot

-- Naturality of row-length along the original step transition.
-- No rewrite/with over a free row length: use trans + equality
-- elimination in the one-step canonical-width donor.
everyOriginalRowHasTableauWidth :
  ∀ {machine start rows finish index}
    (run : Run.WellFormedTapeRun machine start rows finish)
    (cols : Nat) →
  Canonical.listLength (Local.cells start) ≡ cols →
  (slot : Global.Slot index (suc (Run.runLength run))) →
  Canonical.listLength (Local.cells (originalRowAt run slot)) ≡ cols
everyOriginalRowHasTableauWidth Run.runDone cols widthEq Global.here =
  widthEq
everyOriginalRowHasTableauWidth
    (Run.runStep step rest) cols widthEq Global.here =
  widthEq
everyOriginalRowHasTableauWidth
    (Run.runStep step rest) cols widthEq (Global.there slot) =
  everyOriginalRowHasTableauWidth rest cols
    (trans (sym (Assignment.stepCanonicalLength step)) widthEq)
    slot

-- A single dependent pair packages the original row and its
-- original-tableau width; proofs are obtained for ANY selected slot.
originalFixedWidthRowAt :
  ∀ {machine start rows finish index}
    (run : Run.WellFormedTapeRun machine start rows finish)
    (cols : Nat) →
  Canonical.listLength (Local.cells start) ≡ cols →
  (slot : Global.Slot index (suc (Run.runLength run))) →
  Σ (Local.TapeRow machine) (λ row →
    Canonical.listLength (Local.cells row) ≡ cols)
originalFixedWidthRowAt run cols widthEq slot =
  originalRowAt run slot ,
  everyOriginalRowHasTableauWidth run cols widthEq slot

originalFinalRowAtFinalSlot :
  ∀ {machine start rows finish}
    (run : Run.WellFormedTapeRun machine start rows finish) →
  originalRowAt run (Assignment.finalRunRowSlot run) ≡ finish
originalFinalRowAtFinalSlot Run.runDone = refl
originalFinalRowAtFinalSlot (Run.runStep step rest) =
  originalFinalRowAtFinalSlot rest

-- The old free start/finish carrier is preserved intact. All downstream
-- SAT encoders can take this fixed-width view as the unique adaptor.
record OriginalFixedWidthRun
    {machine : Local.ConcreteTapeMachine}
    {start rows finish}
    (cols : Nat)
    (run : Run.WellFormedTapeRun machine start rows finish) : Set where
  field
    startWidth : Canonical.listLength (Local.cells start) ≡ cols

  at :
    ∀ {index} →
    (slot : Global.Slot index (suc (Run.runLength run))) →
    Σ (Local.TapeRow machine)
      (λ row → Canonical.listLength (Local.cells row) ≡ cols)
  at = originalFixedWidthRowAt run cols startWidth

  finishWidth : Canonical.listLength (Local.cells finish) ≡ cols
  finishWidth =
    trans
      (sym (Assignment.runFinishCanonicalLength run))
      startWidth

open OriginalFixedWidthRun public

originalRunToFixedWidth :
  ∀ {machine start rows finish}
    (run : Run.WellFormedTapeRun machine start rows finish) →
  OriginalFixedWidthRun
    (Canonical.listLength (Local.cells start)) run
originalRunToFixedWidth run = record { startWidth = refl }
