module DASHI.Biology.SignedSSPWeaveProgramMachineExact where

------------------------------------------------------------------------
-- TOTAL PROGRAM-COUNTER MACHINE FOR THE EXISTING SIGNED SSP WEAVE LANGUAGE
--
-- SignedSSPExecutionState stores summary lengths but not the remaining program,
-- so a deterministic next-state function on that record alone would require
-- hidden scheduler state.  The existing program language *does* determine a
-- canonical total machine once the remaining instruction list is retained.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

record ProgramMachineState : Set where
  constructor program-machine-state
  field
    remainingProgram : List Signed.WeaveInstruction
    accumulatedEffect : Signed.WeaveEffect

open ProgramMachineState public

initialProgramMachine : List Signed.WeaveInstruction → ProgramMachineState
initialProgramMachine program =
  program-machine-state program Signed.emptyWeaveEffect

stepProgramMachine : ProgramMachineState → ProgramMachineState
stepProgramMachine (program-machine-state [] effect) =
  program-machine-state [] effect
stepProgramMachine (program-machine-state (instruction ∷ rest) effect) =
  program-machine-state rest (Signed.applyInstruction instruction effect)

isHalted : ProgramMachineState → Bool
isHalted (program-machine-state [] effect) = true
isHalted (program-machine-state (_ ∷ rest) effect) = false

stepHaltedIsIdentity :
  (effect : Signed.WeaveEffect) →
  stepProgramMachine (program-machine-state [] effect)
  ≡ program-machine-state [] effect
stepHaltedIsIdentity effect = refl

runProgramMachine :
  List Signed.WeaveInstruction →
  Signed.WeaveEffect →
  ProgramMachineState
runProgramMachine [] effect = program-machine-state [] effect
runProgramMachine (instruction ∷ rest) effect =
  runProgramMachine rest (Signed.applyInstruction instruction effect)

runProgramMachineAgreesWithExistingExecuteProgram :
  (program : List Signed.WeaveInstruction) →
  (effect : Signed.WeaveEffect) →
  accumulatedEffect (runProgramMachine program effect)
  ≡ Signed.executeProgram program effect
runProgramMachineAgreesWithExistingExecuteProgram [] effect = refl
runProgramMachineAgreesWithExistingExecuteProgram (instruction ∷ rest) effect =
  runProgramMachineAgreesWithExistingExecuteProgram
    rest
    (Signed.applyInstruction instruction effect)

runProgramMachineAlwaysHalts :
  (program : List Signed.WeaveInstruction) →
  (effect : Signed.WeaveEffect) →
  isHalted (runProgramMachine program effect) ≡ true
runProgramMachineAlwaysHalts [] effect = refl
runProgramMachineAlwaysHalts (instruction ∷ rest) effect =
  runProgramMachineAlwaysHalts rest (Signed.applyInstruction instruction effect)

canonicalVirtualMachineFinalEffect :
  accumulatedEffect
    (runProgramMachine
      Signed.canonicalVirtualFiftyThreeProgram
      Signed.emptyWeaveEffect)
  ≡ Signed.canonicalVirtualProgramEffect
canonicalVirtualMachineFinalEffect = refl

canonicalGeometricMachineFinalEffect :
  accumulatedEffect
    (runProgramMachine
      Signed.canonicalGeometricFiftyThreeProgram
      Signed.emptyWeaveEffect)
  ≡ Signed.canonicalGeometricProgramEffect
canonicalGeometricMachineFinalEffect = refl

canonicalVirtualMachineHalts :
  isHalted
    (runProgramMachine
      Signed.canonicalVirtualFiftyThreeProgram
      Signed.emptyWeaveEffect)
  ≡ true
canonicalVirtualMachineHalts = refl

canonicalGeometricMachineHalts :
  isHalted
    (runProgramMachine
      Signed.canonicalGeometricFiftyThreeProgram
      Signed.emptyWeaveEffect)
  ≡ true
canonicalGeometricMachineHalts = refl

------------------------------------------------------------------------
-- Exact remaining seam to the richer summary state.
--
-- The program machine is executable and total, but WeaveEffect does not carry
-- enough information to reconstruct an arbitrary SignedSSPExecutionState:
-- prime identity is counted but not retained by WeaveEffect, and the summary
-- record additionally carries address, zero-residual direction and several
-- lengths.  Keep that projection an explicit witness rather than invent it.
------------------------------------------------------------------------

record ProgramMachineToSignedStateProjection : Set₁ where
  field
    project : ProgramMachineState → Signed.SignedSSPExecutionState
    haltedVirtualAgrees :
      project
        (runProgramMachine
          Signed.canonicalVirtualFiftyThreeProgram
          Signed.emptyWeaveEffect)
      ≡ Signed.canonicalVirtualFiftyThreeState
    haltedGeometryAgrees :
      project
        (runProgramMachine
          Signed.canonicalGeometricFiftyThreeProgram
          Signed.emptyWeaveEffect)
      ≡ Signed.canonicalGeometryFiftyThreeState

record SignedSSPWeaveProgramMachineBoundary : Set where
  constructor signed-ssp-weave-program-machine-boundary
  field
    totalProgramCounterMachineConstructed : Bool
    existingApplyInstructionReusedLiterally : Bool
    existingExecuteProgramIntertwined : Bool
    canonicalProgramsTerminate : Bool
    totalStepOnSummaryStateAloneConstructed : Bool
    machineToRichSignedStateProjectionPaid : Bool

canonicalSignedSSPWeaveProgramMachineBoundary :
  SignedSSPWeaveProgramMachineBoundary
canonicalSignedSSPWeaveProgramMachineBoundary =
  signed-ssp-weave-program-machine-boundary
    true true true true false false
