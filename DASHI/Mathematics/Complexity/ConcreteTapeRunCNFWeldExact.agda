module DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact where

------------------------------------------------------------------------
-- FINITE CONCRETE TAPE RUN <-> PER-EDGE WHOLE-ROW CNF PATH
--
-- This is the time-direction induction above ConcreteTapeWholeRowCNFWeldExact.
-- It deliberately stops before flattening every row into one global assignment:
-- that specialization belongs to the unavailable canonical Cell/Bits commits.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Codec
import DASHI.Mathematics.Complexity.ConcreteTapeWholeRowCNFWeldExact as RowCNF

data WellFormedTapeRun
    (machine : Local.ConcreteTapeMachine) :
    Local.TapeRow machine →
    List (Local.TapeRow machine) →
    Local.TapeRow machine →
    Set where

  runDone :
    ∀ {row} →
    WellFormedTapeRun machine row [] row

  runStep :
    ∀ {current next finish tail} →
    WF.WellFormedMachineStep machine current next →
    WellFormedTapeRun machine next tail finish →
    WellFormedTapeRun machine current (next ∷ tail) finish

runLength :
  ∀ {machine start rows finish} →
  WellFormedTapeRun machine start rows finish →
  Nat
runLength runDone =
  zero
runLength (runStep step rest) =
  suc (runLength rest)

data EncodedCNFRunPath
    {machine : Local.ConcreteTapeMachine}
    {width : Nat}
    (codec : Codec.FixedWidthWindowCodec machine width) :
    Local.TapeRow machine →
    List (Local.TapeRow machine) →
    Local.TapeRow machine →
    Set where

  cnfRunDone :
    ∀ {row} →
    EncodedCNFRunPath codec row [] row

  cnfRunStep :
    ∀ {current next finish tail rule} →
    RowCNF.EncodedTransitionCNFCharacterization
      codec rule current next →
    EncodedCNFRunPath codec next tail finish →
    EncodedCNFRunPath codec current (next ∷ tail) finish

stepToEncodedCharacterization :
  ∀ {machine width current next}
    (codec : Codec.FixedWidthWindowCodec machine width) →
  (step : WF.WellFormedMachineStep machine current next) →
  RowCNF.EncodedTransitionCNFCharacterization
    codec
    (Local.rule (WF.step step))
    current next
stepToEncodedCharacterization codec step = record
  { RowCNF.beforeInterior =
      DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact.wellFormedStepBeforeInterior step
  ; RowCNF.afterUnique =
      WF.afterExactlyOneHead step
  ; RowCNF.ruleOccursInMachine =
      Local.ruleOccursInMachine (WF.step step)
  ; RowCNF.sameRowLength =
      DASHI.Mathematics.Complexity.ConcreteTapeWholeRowLocalityExact.rewriteOccurrencePreservesLength
        (WF.occurrence (WF.wellFormedOccurrence step))
  ; RowCNF.allLocalCNFsSatisfied =
      RowCNF.stepImpliesWholeRowCNF codec step
  }

runToEncodedCNFPath :
  ∀ {machine width start rows finish}
    (codec : Codec.FixedWidthWindowCodec machine width) →
  WellFormedTapeRun machine start rows finish →
  EncodedCNFRunPath codec start rows finish
runToEncodedCNFPath codec runDone =
  cnfRunDone
runToEncodedCNFPath codec (runStep step rest) =
  cnfRunStep
    (stepToEncodedCharacterization codec step)
    (runToEncodedCNFPath codec rest)

encodedCNFPathToRun :
  ∀ {machine width start rows finish}
    {codec : Codec.FixedWidthWindowCodec machine width} →
  EncodedCNFRunPath codec start rows finish →
  WellFormedTapeRun machine start rows finish
encodedCNFPathToRun cnfRunDone =
  runDone
encodedCNFPathToRun (cnfRunStep characterization rest) =
  runStep
    (RowCNF.wholeRowCNFImpliesStep characterization)
    (encodedCNFPathToRun rest)

encodedRunLength :
  ∀ {machine width start rows finish}
    {codec : Codec.FixedWidthWindowCodec machine width} →
  EncodedCNFRunPath codec start rows finish →
  Nat
encodedRunLength cnfRunDone =
  zero
encodedRunLength (cnfRunStep characterization rest) =
  suc (encodedRunLength rest)

runToCNFPreservesLength :
  ∀ {machine width start rows finish}
    (codec : Codec.FixedWidthWindowCodec machine width)
    (run : WellFormedTapeRun machine start rows finish) →
  encodedRunLength (runToEncodedCNFPath codec run)
  ≡ runLength run
runToCNFPreservesLength codec runDone =
  refl
runToCNFPreservesLength codec (runStep step rest)
    rewrite runToCNFPreservesLength codec rest =
  refl

record ConcreteTapeRunCNFWeldBoundary : Set where
  constructor concrete-tape-run-cnf-weld-boundary
  field
    finiteConcreteRunCarrierPaid : Bool
    runToEncodedCNFPathPaid : Bool
    encodedCNFPathToRunPaid : Bool
    runLengthPreservationPaid : Bool
    canonicalConcreteCodecSpecializationPaid : Bool
    flatAssignmentPlacementPaid : Bool
    initialEndpointCNFPaid : Bool
    acceptingEndpointCNFPaid : Bool
    acceptingRunToSATPaid : Bool
    satToAcceptingRunPaid : Bool
    genericCookLevinPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeRunCNFWeldBoundary :
  ConcreteTapeRunCNFWeldBoundary
canonicalConcreteTapeRunCNFWeldBoundary =
  concrete-tape-run-cnf-weld-boundary
    true true true true false false false false false false false false
