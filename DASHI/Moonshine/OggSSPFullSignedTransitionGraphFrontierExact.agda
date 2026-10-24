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
--   * a total rich-state machine compiler once residual metadata dynamics exist;
--   * exact rich projections for both existing canonical 53 programs;
--   * a structural no-go for literal depth-refinement through the current
--     fixed `Address 3 -> Address 3` metadata socket, plus a typed
--     variable-depth / explicit-child repair surface.
--
-- The remaining graph constructor is therefore not an undifferentiated
-- "address369 law".  Five non-refinement instructions already have conservative
-- identity address dynamics.  For refineAt369 one must first decide whether its
-- intended semantics is same-depth mutation or genuine tree-depth refinement.
-- Genuine depth refinement requires migrating the current fixed-depth rich
-- carrier to the new variable-depth repair and sourcing a child-selection law.
-- General zero-residual direction and residual-witness length remain separately
-- source-semantic.  Existing legacy owners provide examples, not a total map.
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
import DASHI.Biology.SignedSSPWeaveMetadataAcquisitionFrontierExact as Metadata
import DASHI.Biology.SignedSSPWeaveRefineAt369FixedDepthNoGoExact as RefineNoGo
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
    nonRefinementAddressDynamicsPaid : Bool
    fixedDepthRefinementNoGoPaid : Bool
    variableDepthExplicitChildRepairConstructed : Bool
    currentFixedAddressSocketSupportsLiteralDepthRefinement : Bool
    refineAt369SourceSemanticsPaid : Bool
    zeroResidualDynamicsPaid : Bool
    residualWitnessLengthDynamicsPaid : Bool
    fullArbitraryRichSignedGraphUnconditional : Bool

canonicalFullSignedTransitionGraphBoundary : FullSignedTransitionGraphBoundary
canonicalFullSignedTransitionGraphBoundary =
  full-signed-transition-graph-boundary
    true true true true true
    true true true true true true
    Metadata.nonRefinementAddressDynamicsPaid
    RefineNoGo.canonicalBoundary.fixedDepthAddressRefinementNoGoPaid
    RefineNoGo.canonicalBoundary.variableDepthAddressRepairConstructed
    RefineNoGo.canonicalBoundary.literalDepthRefinementExpressibleByCurrentStepType
    false false false false
