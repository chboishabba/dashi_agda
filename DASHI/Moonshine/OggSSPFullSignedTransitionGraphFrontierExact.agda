module DASHI.Moonshine.OggSSPFullSignedTransitionGraphFrontierExact where

------------------------------------------------------------------------
-- FULL 15-LANE SIGNED TRANSITION GRAPH: HONEST FRONTIER
--
-- Existing repo state pays:
--   internal SSP15 lane <-> chosen Ogg prime lane;
--   Ogg prime lane <-> SignedSSP prime lane;
--   pointed signed lane -> full fifteen-lane SSP valuation;
--   SignedSSPExecutionState and program/effect machinery.
--
-- What is not currently owned by SignedSSPFRACTRANWeaveExact is a canonical
-- total scheduler/step on SignedSSPExecutionState.  Therefore a graph of that
-- exact state type cannot be generated without supplying this socket.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as Branch
import DASHI.Moonshine.Generated.OggSSPKernelFieldRecognitionGenerated as Generated

signedLaneCountIsFifteen : Signed.listCount Signed.canonicalSSPPrimes ≡ 15
signedLaneCountIsFifteen = Signed.canonicalSSPPrimeCountIsFifteen

-- Reuse the actual typed bridge rather than introducing another lane codec.
pointedLaneValuation : Branch.PointedSignedSSPLane → Signed.SSPValuation
pointedLaneValuation = Branch.pointedSignedValuation

record FullSignedTransitionGraphSocket : Set₁ where
  field
    step : Signed.SignedSSPExecutionState → Signed.SignedSSPExecutionState
    stepPreservesDeclaredAddress :
      (state : Signed.SignedSSPExecutionState) →
      Signed.address369 (step state) ≡ Signed.address369 state

-- No canonical inhabitant is supplied here.  Supplying one is the precise
-- remaining constructor required before plotting the full signed state graph.

runtimeSearchFoundCanonicalTotalStep :
  Generated.fullSignedCanonicalTotalStepFound ≡ false
runtimeSearchFoundCanonicalTotalStep = refl

record FullSignedTransitionGraphBoundary : Set where
  constructor full-signed-transition-graph-boundary
  field
    fifteenLaneCarrierPaid : Bool
    pointedLaneToFullValuationPaid : Bool
    signedExecutionStatePaid : Bool
    signedProgramMachineryPaid : Bool
    canonicalTotalStepPaid : Bool
    fullSignedGraphGenerated : Bool
    legacyFourCoordinateGraphPromotedToFullSignedGraph : Bool

canonicalFullSignedTransitionGraphBoundary : FullSignedTransitionGraphBoundary
canonicalFullSignedTransitionGraphBoundary =
  full-signed-transition-graph-boundary
    true true true true
    false false false
