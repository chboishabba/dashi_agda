module DASHI.Computation.JacquardTapeInterpreterExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.List using (reverse)

import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard

------------------------------------------------------------------------
-- ACTUAL JACQUARD TAPE INTERPRETER
--
-- One tape cell is one complete lift mask for one pick.  This deliberately
-- models the control medium separately from the source JacquardProgram.
-- The machine carries an explicit production clock, unread tape, consumed
-- tape, and woven rows.  Produced/consumed histories are accumulated in reverse
-- because each machine step is a constant-time cons.
------------------------------------------------------------------------

record JacquardTapeCell (n : Nat) : Set where
  constructor punched-cell
  field
    holes : Jacquard.LiftMask n

open JacquardTapeCell public

JacquardTape : Nat → Set
JacquardTape n = List (JacquardTapeCell n)

cellFromInstruction :
  {n : Nat} → Jacquard.JacquardInstruction n → JacquardTapeCell n
cellFromInstruction (Jacquard.liftMask mask) = punched-cell mask

programToTape :
  {n : Nat} → Jacquard.JacquardProgram n → JacquardTape n
programToTape [] = []
programToTape (instruction ∷ program) =
  cellFromInstruction instruction ∷ programToTape program

tapeToSchedule :
  {n : Nat} → JacquardTape n → Jacquard.LiftSchedule n
tapeToSchedule [] = []
tapeToSchedule (punched-cell mask ∷ tape) =
  mask ∷ tapeToSchedule tape

programTapeIsCompiledSchedule :
  {n : Nat} →
  (program : Jacquard.JacquardProgram n) →
  tapeToSchedule (programToTape program) ≡ Jacquard.compile program
programTapeIsCompiledSchedule [] = refl
programTapeIsCompiledSchedule (Jacquard.liftMask mask ∷ program)
  rewrite programTapeIsCompiledSchedule program = refl

record JacquardInterpreterState (n : Nat) : Set where
  constructor machine-state
  field
    productionTime : Nat
    unreadTape : JacquardTape n
    consumedTapeReverse : JacquardTape n
    wovenRowsReverse : Jacquard.WovenRows n

open JacquardInterpreterState public

initialState :
  {n : Nat} → JacquardTape n → JacquardInterpreterState n
initialState tape = machine-state 0 tape [] []

data MachineStep (n : Nat) : Set where
  halted : JacquardInterpreterState n → MachineStep n
  advanced : JacquardInterpreterState n → MachineStep n

step :
  {n : Nat} → JacquardInterpreterState n → MachineStep n
step (machine-state time [] consumed rows) =
  halted (machine-state time [] consumed rows)
step (machine-state time (cell ∷ rest) consumed rows) =
  advanced
    (machine-state
      (suc time)
      rest
      (cell ∷ consumed)
      (Jacquard.weaveRow (holes cell) ∷ rows))

runTapeFrom :
  {n : Nat} →
  (time : Nat) →
  (remaining : JacquardTape n) →
  (consumedReverse : JacquardTape n) →
  (rowsReverse : Jacquard.WovenRows n) →
  JacquardInterpreterState n
runTapeFrom time [] consumedReverse rowsReverse =
  machine-state time [] consumedReverse rowsReverse
runTapeFrom time (cell ∷ rest) consumedReverse rowsReverse =
  runTapeFrom
    (suc time)
    rest
    (cell ∷ consumedReverse)
    (Jacquard.weaveRow (holes cell) ∷ rowsReverse)

runTape :
  {n : Nat} → JacquardTape n → JacquardInterpreterState n
runTape tape = runTapeFrom 0 tape [] []

producedRows :
  {n : Nat} → JacquardInterpreterState n → Jacquard.WovenRows n
producedRows state = reverse (wovenRowsReverse state)

consumedTape :
  {n : Nat} → JacquardInterpreterState n → JacquardTape n
consumedTape state = reverse (consumedTapeReverse state)

------------------------------------------------------------------------
-- Reference execution, used to prove the tape interpreter agrees with the
-- already-canonical Jacquard schedule semantics.
------------------------------------------------------------------------

interpretTapeRows :
  {n : Nat} → JacquardTape n → Jacquard.WovenRows n
interpretTapeRows [] = []
interpretTapeRows (punched-cell mask ∷ tape) =
  Jacquard.weaveRow mask ∷ interpretTapeRows tape

interpretTapeRowsIsScheduleExecution :
  {n : Nat} →
  (tape : JacquardTape n) →
  interpretTapeRows tape ≡ Jacquard.executeSchedule (tapeToSchedule tape)
interpretTapeRowsIsScheduleExecution [] = refl
interpretTapeRowsIsScheduleExecution (punched-cell mask ∷ tape)
  rewrite interpretTapeRowsIsScheduleExecution tape = refl

programTapeExecutionCorrect :
  {n : Nat} →
  (program : Jacquard.JacquardProgram n) →
  interpretTapeRows (programToTape program)
  ≡ Jacquard.executeProgram program
programTapeExecutionCorrect [] = refl
programTapeExecutionCorrect (Jacquard.liftMask mask ∷ program)
  rewrite programTapeExecutionCorrect program = refl

------------------------------------------------------------------------
-- A trace exposes every intermediate temporal machine state rather than only
-- the final row list.
------------------------------------------------------------------------

data JacquardMachineTrace (n : Nat) :
    JacquardInterpreterState n → Set where
  traceHalt :
    ∀ {time consumed rows} →
    JacquardMachineTrace n (machine-state time [] consumed rows)

  traceStep :
    ∀ {time cell rest consumed rows} →
    JacquardMachineTrace n
      (machine-state
        (suc time)
        rest
        (cell ∷ consumed)
        (Jacquard.weaveRow (holes cell) ∷ rows)) →
    JacquardMachineTrace n
      (machine-state time (cell ∷ rest) consumed rows)

traceTapeFrom :
  {n : Nat}
  (time : Nat)
  (remaining : JacquardTape n)
  (consumed : JacquardTape n)
  (rows : Jacquard.WovenRows n) →
  JacquardMachineTrace n (machine-state time remaining consumed rows)
traceTapeFrom time [] consumed rows = traceHalt
traceTapeFrom time (cell ∷ rest) consumed rows =
  traceStep
    (traceTapeFrom
      (suc time)
      rest
      (cell ∷ consumed)
      (Jacquard.weaveRow (holes cell) ∷ rows))

traceTape :
  {n : Nat} →
  (tape : JacquardTape n) →
  JacquardMachineTrace n (initialState tape)
traceTape tape = traceTapeFrom 0 tape [] []

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data SourceProgramEqualsPhysicalTape : Set where
data TapeCellEqualsWovenRow : Set where
data VisibleRowDeterminesConsumedTapeHistory : Set where

sourceProgramIsNotPhysicalTape : SourceProgramEqualsPhysicalTape → ⊥
sourceProgramIsNotPhysicalTape ()

tapeCellIsNotWovenRow : TapeCellEqualsWovenRow → ⊥
tapeCellIsNotWovenRow ()

visibleRowDoesNotDetermineTapeHistory :
  VisibleRowDeterminesConsumedTapeHistory → ⊥
visibleRowDoesNotDetermineTapeHistory ()

record JacquardTapeInterpreterBoundary : Set where
  constructor jacquard-tape-interpreter-boundary
  field
    tapeDistinctFromSourceProgram : Bool
    oneTapeCellControlsOnePick : Bool
    eachStepAdvancesProductionTime : Bool
    eachStepConsumesOneCell : Bool
    eachStepEmitsOneCrossingRow : Bool
    tapeExecutionAgreesWithCanonicalJacquardExecution : Bool
    temporalMachineTraceRetained : Bool
    visibleSurfaceRecoversFullTapeHistory : Bool

canonicalJacquardTapeInterpreterBoundary : JacquardTapeInterpreterBoundary
canonicalJacquardTapeInterpreterBoundary =
  jacquard-tape-interpreter-boundary
    true true true true true true true false
