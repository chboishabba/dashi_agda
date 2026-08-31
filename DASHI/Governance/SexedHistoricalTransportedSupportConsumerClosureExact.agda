module DASHI.Governance.SexedHistoricalTransportedSupportConsumerClosureExact where

------------------------------------------------------------------------
-- TRANSPORTED-SUPPORT CONSUMER CLOSURE
--
-- Pairwise separation of support histories is weaker than closing the actual
-- downstream consumer.  This owner instantiates the canonical prediction-
-- envelope / discriminator / sequential-planner machinery on the transported
-- support collision.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Governance.SexedHistoricalTransportedAssociatorSupportExact as Transported
import DASHI.Governance.SexedHistoricalTransportedSupportDiscriminatorExact as SupportDisc

------------------------------------------------------------------------
-- 1. Evidence fibre: both support histories are live before the new probe.
------------------------------------------------------------------------

data SupportEvidence : Set where
  currentCoarseSupportEvidence : SupportEvidence

data CompatibleSupportHistory :
  SupportEvidence → Transported.SupportHistoryFine → Set where
  repairedHistoryCompatible :
    CompatibleSupportHistory
      currentCoarseSupportEvidence
      Transported.repairedThenCounterformed
  counterformedHistoryCompatible :
    CompatibleSupportHistory
      currentCoarseSupportEvidence
      Transported.counterformedThenRepaired

------------------------------------------------------------------------
-- 2. Consumer is a reopening / next-search decision, not world identity.
------------------------------------------------------------------------

data ReopeningPriority : Set where
  institutionFirstReopening
  distributedCounterformationReopening
  : ReopeningPriority

reopeningPriority : Transported.SupportHistoryFine → ReopeningPriority
reopeningPriority Transported.repairedThenCounterformed = institutionFirstReopening
reopeningPriority Transported.counterformedThenRepaired =
  distributedCounterformationReopening

coarseEvidenceDoesNotCloseReopeningConsumer :
  Envelope.PointIdentifiable
    CompatibleSupportHistory
    reopeningPriority
    currentCoarseSupportEvidence → ⊥
coarseEvidenceDoesNotCloseReopeningConsumer identifiable =
  distinct
    (identifiable
      Transported.repairedThenCounterformed
      Transported.counterformedThenRepaired
      repairedHistoryCompatible
      counterformedHistoryCompatible)
  where
  distinct :
    institutionFirstReopening ≡ distributedCounterformationReopening → ⊥
  distinct ()

------------------------------------------------------------------------
-- 3. The support-order probe prospectively closes this consumer.
------------------------------------------------------------------------

supportOrderProbeClosesReopeningConsumer :
  Discriminator.ProspectivelyClosesConsumer
    CompatibleSupportHistory
    reopeningPriority
    SupportDisc.supportOrderProbe
supportOrderProbeClosesReopeningConsumer
    currentCoarseSupportEvidence
    Transported.repairedThenCounterformed
    repairedHistoryCompatible
    left right leftCompatible rightCompatible
  with left | right | leftCompatible | rightCompatible
... | Transported.repairedThenCounterformed
    | Transported.repairedThenCounterformed | _ | _ = refl
... | Transported.repairedThenCounterformed
    | Transported.counterformedThenRepaired
    | (_ , ()) | _
... | Transported.counterformedThenRepaired
    | Transported.repairedThenCounterformed
    | (_ , ()) | _
... | Transported.counterformedThenRepaired
    | Transported.counterformedThenRepaired | _ | _ = refl
supportOrderProbeClosesReopeningConsumer
    currentCoarseSupportEvidence
    Transported.counterformedThenRepaired
    counterformedHistoryCompatible
    left right leftCompatible rightCompatible
  with left | right | leftCompatible | rightCompatible
... | Transported.repairedThenCounterformed
    | Transported.repairedThenCounterformed | _ | _ = refl
... | Transported.repairedThenCounterformed
    | Transported.counterformedThenRepaired
    | (_ , ()) | _
... | Transported.counterformedThenRepaired
    | Transported.repairedThenCounterformed
    | (_ , ()) | _
... | Transported.counterformedThenRepaired
    | Transported.counterformedThenRepaired | _ | _ = refl

------------------------------------------------------------------------
-- 4. One-shot sequential consumer plan: ask only when needed, then stop once
-- the reopening decision is identifiable.
------------------------------------------------------------------------

canonicalReopeningPlan :
  Planner.SequentialConsumerPlan
    reopeningPriority
    (CompatibleSupportHistory currentCoarseSupportEvidence)
canonicalReopeningPlan =
  Planner.oneShotConsumerClosingPlan
    CompatibleSupportHistory
    reopeningPriority
    currentCoarseSupportEvidence
    SupportDisc.supportOrderProbe
    supportOrderProbeClosesReopeningConsumer

------------------------------------------------------------------------
-- 5. Distinguish consumer closure from whole-world reconstruction.
------------------------------------------------------------------------

data ReopeningConsumerClosedMeansWholeHistoryKnown : Set where

data PairwiseSeparationAlwaysClosesConsumer : Set where

data SequentialPlanIsHistoricalPrediction : Set where

data ReopeningDecisionIsEmpiricalCausalLaw : Set where

consumerClosureDoesNotMeanWholeHistoryKnown :
  ReopeningConsumerClosedMeansWholeHistoryKnown → ⊥
consumerClosureDoesNotMeanWholeHistoryKnown ()

pairwiseSeparationDoesNotAutomaticallyCloseConsumer :
  PairwiseSeparationAlwaysClosesConsumer → ⊥
pairwiseSeparationDoesNotAutomaticallyCloseConsumer ()

sequentialPlanIsNotHistoricalPrediction :
  SequentialPlanIsHistoricalPrediction → ⊥
sequentialPlanIsNotHistoricalPrediction ()

reopeningDecisionIsNotEmpiricalCausalLaw :
  ReopeningDecisionIsEmpiricalCausalLaw → ⊥
reopeningDecisionIsNotEmpiricalCausalLaw ()

record TransportedSupportConsumerClosureBoundary : Set where
  constructor transported-support-consumer-closure-boundary
  field
    coarseEvidenceLeavesConsumerOpen : Bool
    supportOrderProbeClosesDeclaredConsumer : Bool
    sequentialPlanStopsAtConsumerClosure : Bool
    fullWorldIdentityRequired : Bool
    pairwiseSeparationAlwaysEnough : Bool
    consumerClosureCreatesPredictionAuthority : Bool

canonicalTransportedSupportConsumerClosureBoundary :
  TransportedSupportConsumerClosureBoundary
canonicalTransportedSupportConsumerClosureBoundary =
  transported-support-consumer-closure-boundary
    true true true false false false
