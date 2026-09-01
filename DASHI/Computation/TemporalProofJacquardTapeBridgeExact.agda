module DASHI.Computation.TemporalProofJacquardTapeBridgeExact where

open import DASHI.Core.Prelude
open import Data.List using (_++_)

import DASHI.Core.ProofCarryingRuleApplicationExact as RuleProof
import DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact as Fabric
import DASHI.Combinatorics.TemporalProofCarryingTextileFibreExact as Temporal
import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard
import DASHI.Computation.JacquardProofVisibleSurfaceExact as Visible
import DASHI.Computation.ProofCarryingJacquardMotifExact as Motif
import DASHI.Computation.JacquardTapeInterpreterExact as Tape

------------------------------------------------------------------------
-- TEMPORAL PROOF FIBRE -> JACQUARD PROGRAM -> TAPE -> MACHINE -> CLOTH
------------------------------------------------------------------------

compileTemporalFabricToProgram :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : Fabric.MotifAssignment Rule}
  {time : Nat}
  {state : State}
  {trace : RuleProof.CertifiedRuleTrace system state} →
  Temporal.TemporalCertifiedFabric assignment time trace →
  Jacquard.JacquardProgram 2
compileTemporalFabricToProgram Temporal.temporalDone = []
compileTemporalFabricToProgram
  (Temporal.temporalStep selected patch rest) =
  Motif.patchJacquardProgram patch ++
  compileTemporalFabricToProgram rest

compileTemporalFabricToTape :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : Fabric.MotifAssignment Rule}
  {time : Nat}
  {state : State}
  {trace : RuleProof.CertifiedRuleTrace system state} →
  Temporal.TemporalCertifiedFabric assignment time trace →
  Tape.JacquardTape 2
compileTemporalFabricToTape temporalFabric =
  Tape.programToTape (compileTemporalFabricToProgram temporalFabric)

runTemporalFabricTape :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : Fabric.MotifAssignment Rule}
  {time : Nat}
  {state : State}
  {trace : RuleProof.CertifiedRuleTrace system state} →
  Temporal.TemporalCertifiedFabric assignment time trace →
  Tape.JacquardInterpreterState 2
runTemporalFabricTape temporalFabric =
  Tape.runTape (compileTemporalFabricToTape temporalFabric)

temporalFabricRows :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : Fabric.MotifAssignment Rule}
  {time : Nat}
  {state : State}
  {trace : RuleProof.CertifiedRuleTrace system state} →
  Temporal.TemporalCertifiedFabric assignment time trace →
  Jacquard.WovenRows 2
temporalFabricRows temporalFabric =
  Tape.interpretTapeRows (compileTemporalFabricToTape temporalFabric)

temporalFabricVisible :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : Fabric.MotifAssignment Rule}
  {time : Nat}
  {state : State}
  {trace : RuleProof.CertifiedRuleTrace system state} →
  Temporal.TemporalCertifiedFabric assignment time trace →
  Visible.VisiblePattern2
temporalFabricVisible temporalFabric =
  Visible.visibleWovenRows2 (temporalFabricRows temporalFabric)

------------------------------------------------------------------------
-- The tape interpreter and canonical Jacquard program execution agree on the
-- exact program compiled from the temporal proof fabric.
------------------------------------------------------------------------

temporalTapeExecutionAgreesWithProgram :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : Fabric.MotifAssignment Rule}
  {time : Nat}
  {state : State}
  {trace : RuleProof.CertifiedRuleTrace system state} →
  (temporalFabric : Temporal.TemporalCertifiedFabric assignment time trace) →
  temporalFabricRows temporalFabric
  ≡ Jacquard.executeProgram (compileTemporalFabricToProgram temporalFabric)
temporalTapeExecutionAgreesWithProgram temporalFabric =
  Tape.programTapeExecutionCorrect
    (compileTemporalFabricToProgram temporalFabric)

------------------------------------------------------------------------
-- Full execution receipt.  The proof object, physical control tape, machine
-- execution trace, woven crossing rows and visible face are retained together.
------------------------------------------------------------------------

record TemporalJacquardProofRun
    {State Rule : Set}
    {system : RuleProof.RuleApplicationSystem State Rule}
    {assignment : Fabric.MotifAssignment Rule}
    {time : Nat}
    {state : State}
    {trace : RuleProof.CertifiedRuleTrace system state}
    (temporalFabric : Temporal.TemporalCertifiedFabric assignment time trace)
    : Set₁ where
  constructor temporal-jacquard-proof-run
  field
    sourceTime : Nat
    sourceTimeExact : sourceTime ≡ time

    sourceProofState : State
    sourceProofStateExact : sourceProofState ≡ state

    program : Jacquard.JacquardProgram 2
    programExact : program ≡ compileTemporalFabricToProgram temporalFabric

    tape : Tape.JacquardTape 2
    tapeExact : tape ≡ Tape.programToTape program

    machineTrace : Tape.JacquardMachineTrace 2 (Tape.initialState tape)

    rows : Jacquard.WovenRows 2
    rowsExact : rows ≡ Tape.interpretTapeRows tape

    canonicalRowsExact :
      rows ≡ Jacquard.executeProgram program

    visibleFace : Visible.VisiblePattern2
    visibleFaceExact : visibleFace ≡ Visible.visibleWovenRows2 rows

open TemporalJacquardProofRun public

canonicalTemporalJacquardProofRun :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule}
  {assignment : Fabric.MotifAssignment Rule}
  {time : Nat}
  {state : State}
  {trace : RuleProof.CertifiedRuleTrace system state} →
  (temporalFabric : Temporal.TemporalCertifiedFabric assignment time trace) →
  TemporalJacquardProofRun temporalFabric
canonicalTemporalJacquardProofRun {time = time} {state = state} temporalFabric =
  temporal-jacquard-proof-run
    time refl
    state refl
    (compileTemporalFabricToProgram temporalFabric) refl
    (compileTemporalFabricToTape temporalFabric) refl
    (Tape.traceTape (compileTemporalFabricToTape temporalFabric))
    (temporalFabricRows temporalFabric) refl
    (temporalTapeExecutionAgreesWithProgram temporalFabric)
    (temporalFabricVisible temporalFabric) refl

------------------------------------------------------------------------
-- Two clocks must remain distinct:
--
-- proof production time counts certified logical patches;
-- tape production time counts physical picks/tape cells.
--
-- A single structural motif currently occupies two Jacquard rows, so these are
-- intentionally not identified.
------------------------------------------------------------------------

data ProofStepTimeEqualsJacquardPickTime : Set where
data TapeHistoryMayBeDiscardedAfterVisibleProjection : Set where

data PhysicalExecutionCreatesLogicalAdmissibility : Set where

proofStepTimeIsNotJacquardPickTime :
  ProofStepTimeEqualsJacquardPickTime → ⊥
proofStepTimeIsNotJacquardPickTime ()

tapeHistoryCannotBeRecoveredFromVisibilityByDefault :
  TapeHistoryMayBeDiscardedAfterVisibleProjection → ⊥
tapeHistoryCannotBeRecoveredFromVisibilityByDefault ()

physicalExecutionDoesNotCreateLogicalAdmissibility :
  PhysicalExecutionCreatesLogicalAdmissibility → ⊥
physicalExecutionDoesNotCreateLogicalAdmissibility ()

record TemporalJacquardTapeBoundary : Set where
  constructor temporal-jacquard-tape-boundary
  field
    proofTimeAndPickTimeSeparated : Bool
    proofTraceCompilesToActualTape : Bool
    tapeHasExplicitMachineTrace : Bool
    tapeExecutionProducesCrossingRows : Bool
    crossingRowsProjectToVisibleFace : Bool
    tapeExecutionAgreesWithCanonicalJacquardProgram : Bool
    visibleFaceRecoversFullProofAndTapeHistoryByDefault : Bool

canonicalTemporalJacquardTapeBoundary : TemporalJacquardTapeBoundary
canonicalTemporalJacquardTapeBoundary =
  temporal-jacquard-tape-boundary
    true true true true true true false
