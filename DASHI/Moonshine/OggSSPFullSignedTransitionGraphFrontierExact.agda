module DASHI.Moonshine.OggSSPFullSignedTransitionGraphFrontierExact where

------------------------------------------------------------------------
-- FULL 15-LANE SIGNED TRANSITION GRAPH: NARROWED HONEST FRONTIER
--
-- The existing repo pays the fifteen-lane carrier/valuation path.  #1105 now
-- additionally constructs a canonical total program-counter machine over the
-- existing WeaveInstruction/applyInstruction semantics.  What remains is no
-- longer "find a scheduler": it is the information-preserving projection from
-- that executable machine into the richer SignedSSPExecutionState summary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Biology.SignedSSPWeaveProgramMachineExact as Machine
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Branch
import DASHI.Moonshine.Generated.OggSSPKernelFieldRecognitionGenerated as Generated

signedLaneCountIsFifteen : Signed.listCount Signed.canonicalSSPPrimes ≡ 15
signedLaneCountIsFifteen = Signed.canonicalSSPPrimeCountIsFifteen

pointedLaneValuation : Branch.PointedSignedSSPLane → Signed.SSPValuation
pointedLaneValuation = Branch.pointedSignedValuation

-- The canonical total executable step now exists on the correctly enriched
-- state which retains the remaining program.
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

-- This is now the exact graph bridge still required.  WeaveEffect counts prime
-- introductions but does not retain which prime was introduced; the richer
-- summary also owns address/residual and length metadata.  Therefore a faithful
-- projection needs extra evidence, not a guessed default.
record FullSignedTransitionGraphProjectionSocket : Set₁ where
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

-- Historical generated receipt remains false because the old search asked for
-- a total step on the information-losing summary type alone.
runtimeSearchFoundCanonicalTotalStepOnSummaryAlone :
  Generated.fullSignedCanonicalTotalStepFound ≡ false
runtimeSearchFoundCanonicalTotalStepOnSummaryAlone = refl

record FullSignedTransitionGraphBoundary : Set where
  constructor full-signed-transition-graph-boundary
  field
    fifteenLaneCarrierPaid : Bool
    pointedLaneToFullValuationPaid : Bool
    signedExecutionStatePaid : Bool
    signedProgramMachineryPaid : Bool
    totalProgramCounterMachinePaid : Bool
    machineToRichSignedProjectionPaid : Bool
    fullRichSignedGraphGenerated : Bool
    legacyFourCoordinateGraphPromotedToFullSignedGraph : Bool

canonicalFullSignedTransitionGraphBoundary : FullSignedTransitionGraphBoundary
canonicalFullSignedTransitionGraphBoundary =
  full-signed-transition-graph-boundary
    true true true true true
    false false false
