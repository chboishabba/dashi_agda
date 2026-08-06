module DASHI.Physics.Foundations.Round5CompleteBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5FullBoundary as Full
import DASHI.Physics.Foundations.Round5AttachedCompletionBoundary as AttachedCompletion
import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Physics.Foundations.FiniteResidueCycleReachabilityExact as Residue
import DASHI.Physics.Foundations.FiniteMultiscaleKernelCompatibilityExact as Multiscale
import DASHI.Physics.DarkSector.DarkSectorColliderBoundary as Collider
import DASHI.Physics.DarkSector.DisplacedVertex as Vertex
import DASHI.Physics.DarkSector.TriggerCensoring as Trigger
import DASHI.Visualisation.AttachedVisualisationBoundary as Visualisation
import DASHI.Visualisation.EventPadicContinuationBoundary as EventPadic
import DASHI.Visualisation.EventFilamentFieldExact as Event
import DASHI.Visualisation.SelfConsistentEventRendererExact as Renderer
import DASHI.Biology.TernaryCyclicDialecticExact as Cyclic
import DASHI.Biology.TriadicCarryResidualExact as Carry
import DASHI.Biology.RenderablePadicReasoningFieldExact as Padic
import DASHI.Physics.Foundations.TriToBiSingularJunctionExact as Junction
import DASHI.Physics.Foundations.TriToBiPhaseDialecticExact as Phase
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Visualisation.CoarseSliceSearchExact as Search
import DASHI.Visualisation.SliceObjectiveExact as Objective
import DASHI.Visualisation.RendererParityExact as Parity
import DASHI.Visualisation.RendererReceiptExact as Receipt
import DASHI.Visualisation.MeasureFieldAdapterExact as Adapter

record Round5CompleteBoundary : Set where
  field
    fullRound5Boundary : Full.Round5FullBoundary
    attachedCompletionBoundary :
      AttachedCompletion.Round5AttachedCompletionBoundary
    colliderBoundary : Collider.DarkSectorColliderBoundary
    attachedVisualisationBoundary :
      Visualisation.AttachedVisualisationBoundary
    eventPadicContinuationBoundary :
      EventPadic.EventPadicContinuationBoundary

    reversibleHistorySubsystem :
      (configuration : History.Configuration) →
      History.reversibleStep (History.reversibleStep configuration)
      ≡
      configuration

    residueSixReturns :
      (residue : Residue.Residue6) →
      Residue.successor6Six residue ≡ residue

    residueNineReturns :
      (residue : Residue.Residue9) →
      Residue.successor9Nine residue ≡ residue

    exactKernelCoarseCompatibility :
      (state : Multiscale.FineState) →
      Multiscale.coarseProjection (Multiscale.fineKernelExact state)
      ≡
      Multiscale.coarseKernelExact (Multiscale.coarseProjection state)

    displacedColliderTriggerAccepts :
      Trigger.llpTrigger Vertex.canonicalDisplacedEvent
      ≡
      Trigger.acceptEvent

    connectedThreeToTwoNeedsThreeSaddles :
      Junction.ordinarySaddleCount
        Junction.threeSimultaneousSaddles
      ≡
      3

    phaseCancellationReachesNeutral :
      Phase.phaseResultToTrit
        (Phase.phaseResultant
          Phase.phaseZero
          Phase.phaseOne
          Phase.phaseTwo)
      ≡
      Triadic.zeroTrit

    lowPrecisionShortlistRetainsExactWinner :
      Search.InShortlist Search.floatWinner Search.coarseProposal

    combinedSliceObjectiveSelectsBroadPlane :
      Objective.combinedObjective Objective.combinedWinner
      ≡
      79

    optimisedRendererPreservesReference :
      (input : Parity.RenderInput) →
      Parity.optimisedRenderer input
      ≡
      Parity.referenceRenderer input

    rendererSourceReceiptDoesNotClaimExecution :
      Receipt.benchmarkExecuted Receipt.canonicalSourceReceipt ≡ false

    distinctSourcesCanShareCoarseImage :
      Adapter.coarseColour
        (Adapter.restrictField Adapter.leftCellSlice
          (Adapter.convolveScaled
            (Adapter.extractMeasure Adapter.sourceA)))
      ≡
      Adapter.coarseColour
        (Adapter.restrictField Adapter.leftCellSlice
          (Adapter.convolveScaled
            (Adapter.extractMeasure Adapter.sourceB)))

    eventFieldAddsPositiveContributions :
      Event.scalarFieldSample ≡ 10

    selfSharpeningFiniteFixedPoint :
      Renderer.fieldOperator Renderer.densityFixed
      ≡
      Renderer.densityFixed

    ternaryCyclicInverse :
      (a : Carry.TriResidue) →
      Cyclic.cyclicAdd3 a (Cyclic.inverseResidue a)
      ≡
      Cyclic.zeroResidue

    renderablePadicDepthNineCount :
      Padic.depthNinePrefixCount ≡ 19683

    renderablePadicRetainsAddress :
      Padic.addressMetadataRetained Padic.canonicalRenderableReasoningField
      ≡
      true

open Round5CompleteBoundary public

canonicalRound5CompleteBoundary : Round5CompleteBoundary
canonicalRound5CompleteBoundary =
  record
    { fullRound5Boundary = Full.canonicalRound5FullBoundary
    ; attachedCompletionBoundary =
        AttachedCompletion.canonicalRound5AttachedCompletionBoundary
    ; colliderBoundary = Collider.canonicalDarkSectorColliderBoundary
    ; attachedVisualisationBoundary =
        Visualisation.canonicalAttachedVisualisationBoundary
    ; eventPadicContinuationBoundary =
        EventPadic.canonicalEventPadicContinuationBoundary
    ; reversibleHistorySubsystem =
        History.reversibleStepInvolutive
    ; residueSixReturns =
        Residue.sixCycleReturns
    ; residueNineReturns =
        Residue.nineCycleReturns
    ; exactKernelCoarseCompatibility =
        Multiscale.exactKernelCompatibility
    ; displacedColliderTriggerAccepts =
        Trigger.canonicalLLPTriggerAcceptsDisplacedSignal
    ; connectedThreeToTwoNeedsThreeSaddles =
        Junction.connectedGenusZeroNeedsThreeSaddles
    ; phaseCancellationReachesNeutral =
        Phase.cancellationMapsToTernaryNeutral
    ; lowPrecisionShortlistRetainsExactWinner =
        Search.trueWinnerSurvivesShortlist
    ; combinedSliceObjectiveSelectsBroadPlane =
        Objective.combinedWinnerScore
    ; optimisedRendererPreservesReference =
        Parity.optimisedParity
    ; rendererSourceReceiptDoesNotClaimExecution =
        Receipt.sourceReceiptDoesNotClaimExecutedBenchmark
    ; distinctSourcesCanShareCoarseImage =
        Adapter.differentSourcesSameCoarseImage
    ; eventFieldAddsPositiveContributions =
        Event.scalarFieldSampleIsTen
    ; selfSharpeningFiniteFixedPoint =
        Renderer.fixedStateIsFixed
    ; ternaryCyclicInverse =
        Cyclic.cyclicInverseRight
    ; renderablePadicDepthNineCount =
        Padic.depthNineCountIs19683
    ; renderablePadicRetainsAddress =
        Padic.canonicalFieldRetainsAddress
    }
