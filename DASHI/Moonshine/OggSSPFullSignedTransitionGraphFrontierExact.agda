module DASHI.Moonshine.OggSSPFullSignedTransitionGraphFrontierExact where

------------------------------------------------------------------------
-- FULL 15-LANE SIGNED TRANSITION GRAPH: CURRENT MAX-CUT
--
-- Paid now:
--   * fifteen-lane carrier and signed valuation path;
--   * total program-counter machine;
--   * executed trace retaining prime identity;
--   * arbitrary-program replay of valuation + invariant-unit semantics;
--   * a total rich-state machine compiler once metadata dynamics are supplied;
--   * exact rich projections for both existing canonical 53 programs.
--
-- The only remaining graph constructor is the metadata dynamics for address,
-- zero-residual direction, and description/execution lengths.  Those fields are
-- not determined by the existing WeaveInstruction language.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.SignedSSPWeaveProgramMachineExact as Machine
import DASHI.Biology.SignedSSPWeaveInstructionTraceExact as Trace
import DASHI.Biology.SignedSSPWeaveSemanticCoreReplayExact as Core
import DASHI.Biology.SignedSSPWeaveRichMetadataCompilerExact as Compiler
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

canonicalVirtualRichProjectionPaid :
  Canonical.canonicalRichSignedState Canonical.virtualFiftyThreeRun
  ≡ Signed.canonicalVirtualFiftyThreeState
canonicalVirtualRichProjectionPaid = Canonical.canonicalVirtualProjectionExact

canonicalGeometryRichProjectionPaid :
  Canonical.canonicalRichSignedState Canonical.geometricFiftyThreeRun
  ≡ Signed.canonicalGeometryFiftyThreeState
canonicalGeometryRichProjectionPaid = Canonical.canonicalGeometryProjectionExact

-- Supplying exactly this record is sufficient to compile a total rich-state
-- machine for arbitrary programs.  No additional valuation or scheduler socket
-- remains.
FullRichGraphMetadataSocket : Set₁
FullRichGraphMetadataSocket = Compiler.RichMetadataDynamics

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
    richMachineCompilerGivenMetadataPaid : Bool
    canonicalVirtualRichProjectionPaid : Bool
    canonicalGeometryRichProjectionPaid : Bool
    metadataDynamicsRecoveredFromPriorRepo : Bool
    fullArbitraryRichSignedGraphUnconditional : Bool

canonicalFullSignedTransitionGraphBoundary : FullSignedTransitionGraphBoundary
canonicalFullSignedTransitionGraphBoundary =
  full-signed-transition-graph-boundary
    true true true true true true true true
    false false
