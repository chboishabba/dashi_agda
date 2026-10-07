module DASHI.Moonshine.OggSSPFullSignedTransitionGraphFrontierExact where

------------------------------------------------------------------------
-- FULL 15-LANE SIGNED TRANSITION GRAPH: NARROWED HONEST FRONTIER
--
-- #1105 now owns:
--   * the fifteen-lane carrier/valuation path;
--   * a canonical total program-counter machine;
--   * an information-preserving executed-instruction trace retaining prime IDs;
--   * exact rich-state projections for both existing canonical 53 programs.
--
-- The remaining graph seam is therefore only the arbitrary-program projection
-- into SignedSSPExecutionState, whose address/residual/normal-form metadata is
-- not determined by WeaveInstruction/WeaveEffect alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.SignedSSPWeaveProgramMachineExact as Machine
import DASHI.Biology.SignedSSPWeaveInstructionTraceExact as Trace
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

canonicalVirtualProgramMachineHalts :
  Machine.isHalted
    (Machine.runProgramMachine
      Signed.canonicalVirtualFiftyThreeProgram
      Signed.emptyWeaveEffect)
  ≡ true
canonicalVirtualProgramMachineHalts = Machine.canonicalVirtualMachineHalts

canonicalGeometricProgramMachineHalts :
  Machine.isHalted
    (Machine.runProgramMachine
      Signed.canonicalGeometricFiftyThreeProgram
      Signed.emptyWeaveEffect)
  ≡ true
canonicalGeometricProgramMachineHalts = Machine.canonicalGeometricMachineHalts

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

canonicalVirtualRichProjectionPaid :
  Canonical.canonicalRichSignedState Canonical.virtualFiftyThreeRun
  ≡ Signed.canonicalVirtualFiftyThreeState
canonicalVirtualRichProjectionPaid = Canonical.canonicalVirtualProjectionExact

canonicalGeometryRichProjectionPaid :
  Canonical.canonicalRichSignedState Canonical.geometricFiftyThreeRun
  ≡ Signed.canonicalGeometryFiftyThreeState
canonicalGeometryRichProjectionPaid = Canonical.canonicalGeometryProjectionExact

-- Exact arbitrary-program socket still required.  The executed trace now
-- retains prime identity, so the missing data has compressed to the richer
-- summary metadata not carried by the instruction language itself.
record ArbitraryRichSignedProjectionSocket : Set₁ where
  field
    projection : Machine.ProgramMachineToSignedStateProjection
    projectedStep :
      Signed.SignedSSPExecutionState → Signed.SignedSSPExecutionState
    projectedStepAgreesWithMachine :
      (state : Machine.ProgramMachineState) →
      projectedStep
        (Machine.ProgramMachineToSignedStateProjection.project projection state)
      ≡
      Machine.ProgramMachineToSignedStateProjection.project projection
        (Machine.stepProgramMachine state)

runtimeSearchFoundCanonicalTotalStepOnSummaryAlone :
  Generated.fullSignedCanonicalTotalStepFound ≡ false
runtimeSearchFoundCanonicalTotalStepOnSummaryAlone = refl

record FullSignedTransitionGraphBoundary : Set where
  constructor full-signed-transition-graph-boundary
  field
    fifteenLaneCarrierPaid : Bool
    signedProgramMachineryPaid : Bool
    totalProgramCounterMachinePaid : Bool
    executedTraceRetainsPrimeIdentity : Bool
    canonicalVirtualRichProjectionPaid : Bool
    canonicalGeometryRichProjectionPaid : Bool
    arbitraryProgramRichProjectionPaid : Bool
    fullArbitraryRichSignedGraphGenerated : Bool
    legacyFourCoordinateGraphPromotedToFullSignedGraph : Bool

canonicalFullSignedTransitionGraphBoundary : FullSignedTransitionGraphBoundary
canonicalFullSignedTransitionGraphBoundary =
  full-signed-transition-graph-boundary
    true true true true true true
    false false false
