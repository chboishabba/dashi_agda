module DASHI.Physics.Foundations.Round5CompleteBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5FullBoundary as Full
import DASHI.Physics.Foundations.Round5AttachedCompletionBoundary as AttachedCompletion
import DASHI.Physics.DarkSector.DarkSectorColliderBoundary as Collider

record Round5CompleteBoundary : Set where
  field
    fullRound5Boundary : Full.Round5FullBoundary
    attachedCompletionBoundary :
      AttachedCompletion.Round5AttachedCompletionBoundary
    colliderBoundary : Collider.DarkSectorColliderBoundary

    reversibleHistorySubsystem :
      (configuration : AttachedCompletion.History.Configuration) →
      AttachedCompletion.History.reversibleStep
        (AttachedCompletion.History.reversibleStep configuration)
      ≡
      configuration

    residueSixReturns :
      (residue : AttachedCompletion.Residue.Residue6) →
      AttachedCompletion.Residue.successor6Six residue ≡ residue

    residueNineReturns :
      (residue : AttachedCompletion.Residue.Residue9) →
      AttachedCompletion.Residue.successor9Nine residue ≡ residue

    exactKernelCoarseCompatibility :
      (state : AttachedCompletion.Multiscale.FineState) →
      AttachedCompletion.Multiscale.coarseProjection
        (AttachedCompletion.Multiscale.fineKernelExact state)
      ≡
      AttachedCompletion.Multiscale.coarseKernelExact
        (AttachedCompletion.Multiscale.coarseProjection state)

    displacedColliderTriggerAccepts :
      Collider.Trigger.llpTrigger Collider.Vertex.canonicalDisplacedEvent
      ≡
      Collider.Trigger.acceptEvent

open Round5CompleteBoundary public

canonicalRound5CompleteBoundary : Round5CompleteBoundary
canonicalRound5CompleteBoundary =
  record
    { fullRound5Boundary = Full.canonicalRound5FullBoundary
    ; attachedCompletionBoundary =
        AttachedCompletion.canonicalRound5AttachedCompletionBoundary
    ; colliderBoundary = Collider.canonicalDarkSectorColliderBoundary
    ; reversibleHistorySubsystem =
        AttachedCompletion.History.reversibleStepInvolutive
    ; residueSixReturns =
        AttachedCompletion.Residue.sixCycleReturns
    ; residueNineReturns =
        AttachedCompletion.Residue.nineCycleReturns
    ; exactKernelCoarseCompatibility =
        AttachedCompletion.Multiscale.exactKernelCompatibility
    ; displacedColliderTriggerAccepts =
        Collider.Trigger.canonicalLLPTriggerAcceptsDisplacedSignal
    }
