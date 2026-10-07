module DASHI.Moonshine.OggSSPFullSignedTransitionGraphFrontierExact where

------------------------------------------------------------------------
-- FULL 15-LANE SIGNED TRANSITION GRAPH: CURRENT MAX-CUT
--
-- Paid now:
--   * fifteen-lane carrier and signed valuation path;
--   * total program-counter machine;
--   * executed trace retaining prime identity;
--   * arbitrary-program replay of valuation + invariant-unit semantics;
--   * generic program/execution/normal-form length dynamics;
--   * a total rich-state machine compiler once the residual metadata dynamics
--     are supplied;
--   * exact rich projections for both existing canonical 53 programs.
--
-- The only remaining graph constructor is now the residual metadata policy:
-- address369, zero-residual direction, and residual-witness length.  Existing
-- legacy owners provide partial examples but not a general WeaveInstruction law.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.SignedSSPWeaveProgramMachineExact as Machine
import DASHI.Biology.SignedSSPWeaveInstructionTraceExact as Trace
import DASHI.Biology.SignedSSPWeaveSemanticCoreReplayExact as Core
import DASHI.Biology.SignedSSPWeaveRichMetadataCompilerExact as Compiler
import DASHI.Biology.SignedSSPWeaveDerivedLengthDynamicsExact as Derived
import DASHI.Biology.SignedSSPWeaveCanonicalProjectionExact as Canonical
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Branch
import DASHI.Moonshine.Generated.OggSSPKernelFieldRecognitionGenerated as Generated

signedLaneCountIsFifteen : Signed.listCount Signed.canonicalSSPPrimes ≡ 15
signedLaneCountIsFifteen = Signed.canonicalSSPPrimeCountIsFifteen

pointedLaneValuation : Branch.PointedSignedSSPLane → Signed.SSPValuation
pointedLaneValuation = Branch.pointedSignedValuation

canonicalProgramMachineStep :
  Machine.ProgramMachineState → Machine.ProgramMachineState
canonicalProgramMachineStep = Machine.stepProgramMachine

canonicalVirtualPrimeIdentityRetained :
  Trace.reverseExecutedTrace
    (Trace.runTracedProgramMachine
      Signed.canonicalVirtualFiftyThreeProgram
      Signed.emptyWeaveEffect
      [])
  ≡ Trace.invariantUnitEvent
    ∷ Trace.inversePrimeEvent Signed.ssp7
    ∷ Trace.positivePrimeEvent Signed.ssp59
    ∷ []
canonicalVirtualPrimeIdentityRetained =
  Trace.canonicalVirtualReverseTraceRetainsPrimeIdentity

canonicalVirtualValuationRecovered :
  (prime : Signed.SSPPrime) →
  Core.valuation Core.canonicalVirtualSemanticCore prime
  ≡ Signed.virtualFiftyThreeValuation prime
canonicalVirtualValuationRecovered = Core.canonicalVirtualValuationPointwise

canonicalGeometryValuationRecovered :
  (prime : Signed.SSPPrime) →
  Core.valuation Core.canonicalGeometrySemanticCore prime
  ≡ Signed.zeroValuation prime
canonicalGeometryValuationRecovered = Core.canonicalGeometryValuationPointwise

canonicalVirtualExecutionLengthRecovered :
  Derived.programExecutionCost Signed.canonicalVirtualFiftyThreeProgram ≡ 3
canonicalVirtualExecutionLengthRecovered =
  Derived.canonicalVirtualExecutionCostIsThree

canonicalGeometryExecutionLengthRecovered :
  Derived.programExecutionCost Signed.canonicalGeometricFiftyThreeProgram ≡ 54
canonicalGeometryExecutionLengthRecovered =
  Derived.canonicalGeometryExecutionCostIsFiftyFour

canonicalVirtualRichProjectionPaid :
  Canonical.canonicalRichSignedState Canonical.virtualFiftyThreeRun
  ≡ Signed.canonicalVirtualFiftyThreeState
canonicalVirtualRichProjectionPaid = Canonical.canonicalVirtualProjectionExact

canonicalGeometryRichProjectionPaid :
  Canonical.canonicalRichSignedState Canonical.geometricFiftyThreeRun
  ≡ Signed.canonicalGeometryFiftyThreeState
canonicalGeometryRichProjectionPaid = Canonical.canonicalGeometryProjectionExact

-- Supplying only this reduced socket now suffices to compile the full
-- RichMetadataDynamics record; scheduler, valuation and three length fields no
-- longer remain as independent obligations.
FullRichGraphResidualMetadataSocket : Set₁
FullRichGraphResidualMetadataSocket = Derived.ResidualMetadataDynamics

compileFullRichMetadata :
  FullRichGraphResidualMetadataSocket → Compiler.RichMetadataDynamics
compileFullRichMetadata = Derived.compileRichMetadataDynamics

runtimeSearchFoundCanonicalTotalStepOnSummaryAlone :
  Generated.fullSignedCanonicalTotalStepFound ≡ false
runtimeSearchFoundCanonicalTotalStepOnSummaryAlone = refl

record FullSignedTransitionGraphBoundary : Set where
  constructor full-signed-transition-graph-boundary
  field
    fifteenLaneCarrierPaid : Bool
    totalProgramCounterMachinePaid : Bool
    executedTraceRetainsPrimeIdentity : Bool
    arbitraryProgramValuationReplayPaid : Bool
    arbitraryProgramInvariantUnitReplayPaid : Bool
    genericProgramLengthDynamicsPaid : Bool
    genericExecutionLengthDynamicsPaid : Bool
    genericNormalFormLengthDynamicsPaid : Bool
    richMachineCompilerGivenResidualMetadataPaid : Bool
    canonicalVirtualRichProjectionPaid : Bool
    canonicalGeometryRichProjectionPaid : Bool
    addressResidualWitnessDynamicsRecovered : Bool
    fullArbitraryRichSignedGraphUnconditional : Bool

canonicalFullSignedTransitionGraphBoundary : FullSignedTransitionGraphBoundary
canonicalFullSignedTransitionGraphBoundary =
  full-signed-transition-graph-boundary
    true true true true true
    true true true true true true
    false false
