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
import DASHI.Physics.Foundations.TriToBiSingularJunctionExact as Junction
import DASHI.Visualisation.CoarseSliceSearchExact as Search
import DASHI.Visualisation.RendererParityExact as Parity

record Round5CompleteBoundary : Set where
  field
    fullRound5Boundary : Full.Round5FullBoundary
    attachedCompletionBoundary :
      AttachedCompletion.Round5AttachedCompletionBoundary
    colliderBoundary : Collider.DarkSectorColliderBoundary
    attachedVisualisationBoundary :
      Visualisation.AttachedVisualisationBoundary

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

    lowPrecisionShortlistRetainsExactWinner :
      Search.InShortlist Search.floatWinner Search.coarseProposal

    optimisedRendererPreservesReference :
      (input : Parity.RenderInput) →
      Parity.optimisedRenderer input
      ≡
      Parity.referenceRenderer input

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
    ; lowPrecisionShortlistRetainsExactWinner =
        Search.trueWinnerSurvivesShortlist
    ; optimisedRendererPreservesReference =
        Parity.optimisedParity
    }
