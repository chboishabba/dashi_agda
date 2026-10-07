module DASHI.Biology.SignedSSPWeaveRichMetadataCompilerExact where

------------------------------------------------------------------------
-- RICH SIGNED-STATE MACHINE COMPILER WITH ONLY METADATA DYNAMICS ABSTRACT
--
-- Semantic-core replay now reconstructs valuation and invariant units from the
-- existing instruction stream.  The only data not determined by an arbitrary
-- WeaveInstruction are the address/residual/description-length components.
-- Supply exactly those dynamics and the full rich execution machine compiles.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.SignedSSPWeaveSemanticCoreReplayExact as Core

record RichExecutionMetadata : Set where
  constructor rich-execution-metadata
  field
    address369 : Signed.SSP.Address 3
    zeroApproachResidual : Signed.Zero.ApproachDirection
    programLength : Nat
    executionLength : Nat
    normalFormLength : Nat
    residualWitnessLength : Nat

open RichExecutionMetadata public

record RichMetadataDynamics : Set₁ where
  field
    initialMetadata : List Signed.WeaveInstruction → RichExecutionMetadata
    stepMetadata :
      Signed.WeaveInstruction → RichExecutionMetadata → RichExecutionMetadata

open RichMetadataDynamics public

record RichProgramMachineState : Set where
  constructor rich-program-machine-state
  field
    remainingProgram : List Signed.WeaveInstruction
    semanticCore : Core.SignedSemanticCore
    metadata : RichExecutionMetadata

open RichProgramMachineState public

initialRichProgramMachine :
  RichMetadataDynamics →
  List Signed.WeaveInstruction →
  RichProgramMachineState
initialRichProgramMachine dynamics program =
  rich-program-machine-state
    program
    Core.zeroSemanticCore
    (initialMetadata dynamics program)

stepRichProgramMachine :
  RichMetadataDynamics →
  RichProgramMachineState →
  RichProgramMachineState
stepRichProgramMachine dynamics
  (rich-program-machine-state [] core metadata) =
  rich-program-machine-state [] core metadata
stepRichProgramMachine dynamics
  (rich-program-machine-state (instruction ∷ rest) core metadata) =
  rich-program-machine-state
    rest
    (Core.applyInstructionCore instruction core)
    (stepMetadata dynamics instruction metadata)

projectRichState : RichProgramMachineState → Signed.SignedSSPExecutionState
projectRichState (rich-program-machine-state program core metadata) =
  Signed.signedSSPExecutionState
    (Core.valuation core)
    (Core.invariantUnits core)
    (address369 metadata)
    (zeroApproachResidual metadata)
    (programLength metadata)
    (executionLength metadata)
    (normalFormLength metadata)
    (residualWitnessLength metadata)

richProjectedStep :
  RichMetadataDynamics →
  RichProgramMachineState →
  Signed.SignedSSPExecutionState
richProjectedStep dynamics state =
  projectRichState (stepRichProgramMachine dynamics state)

stepProjectionIsDefinitionallyCompiled :
  (dynamics : RichMetadataDynamics) →
  (state : RichProgramMachineState) →
  richProjectedStep dynamics state
  ≡ projectRichState (stepRichProgramMachine dynamics state)
stepProjectionIsDefinitionallyCompiled dynamics state = refl

record RichMetadataCompilerBoundary : Set where
  constructor rich-metadata-compiler-boundary
  field
    arbitraryProgramValuationDynamicsPaid : Bool
    arbitraryProgramInvariantUnitDynamicsPaid : Bool
    richStateProjectionConstructed : Bool
    totalRichMachineGivenMetadataDynamics : Bool
    metadataDynamicsRecoveredFromPriorRepo : Bool
    arbitraryFullRichGraphUnconditional : Bool

canonicalRichMetadataCompilerBoundary : RichMetadataCompilerBoundary
canonicalRichMetadataCompilerBoundary =
  rich-metadata-compiler-boundary
    true true true true false false
