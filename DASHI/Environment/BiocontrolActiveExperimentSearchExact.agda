module DASHI.Environment.BiocontrolActiveExperimentSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Environment.BiocontrolExternalityExperimentExact as Experiment

------------------------------------------------------------------------
-- Reuse the same generic consumer-collision / discriminator objects used by
-- active proof search. Ecological experiment choice is not a parallel planner.
------------------------------------------------------------------------

oxygenConsumerCollision :
  Consumer.ConsumerRelevantCollision
    Experiment.suppressionObserver Experiment.oxygenConsumer
oxygenConsumerCollision = Consumer.consumer-relevant-collision
  Experiment.oxygenDebtWorld Experiment.oxygenRecoveryWorld refl (λ ())

restorationConsumerCollision :
  Consumer.ConsumerRelevantCollision
    Experiment.suppressionOxygenObserver Experiment.restorationConsumer
restorationConsumerCollision = Consumer.consumer-relevant-collision
  Experiment.restorationFailureWorld Experiment.restorationRecoveryWorld refl (λ ())

reboundConsumerCollision :
  Consumer.ConsumerRelevantCollision
    Experiment.suppressionObserver Experiment.reboundConsumer
reboundConsumerCollision = Consumer.consumer-relevant-collision
  Experiment.reboundHighWorld Experiment.reboundLowWorld refl (λ ())

agentInteractionConsumerCollision :
  Consumer.ConsumerRelevantCollision
    Experiment.suppressionAgentCountObserver Experiment.agentInteractionConsumer
agentInteractionConsumerCollision = Consumer.consumer-relevant-collision
  Experiment.agentIndependentWorld Experiment.agentInterferenceWorld refl (λ ())

------------------------------------------------------------------------
-- Declared discriminator bundles.
------------------------------------------------------------------------

oxygenExperimentBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
oxygenExperimentBundle = Synthesis.experimentBundle
  (Experiment.OxygenState × Experiment.BiomassFate)
  (λ world → Experiment.oxygen world , Experiment.biomassFate world)
  2
  "dissolved-oxygen plus biomass-fate discriminator selected by suppression collision"
  "declared dissolved-oxygen measurement plus biomass-fate observation"

communityExperimentBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
communityExperimentBundle = Synthesis.experimentBundle
  Experiment.CommunityState
  Experiment.restorationConsumer
  3
  "community-composition discriminator selected after suppression+oxygen collision"
  "declared community-composition survey"

reboundExperimentBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
reboundExperimentBundle = Synthesis.experimentBundle
  (Experiment.NutrientResidual × Experiment.SeedbankResidual)
  Experiment.reboundConsumer
  1
  "nutrient plus seedbank residual discriminator selected by rebound collision"
  "LES nutrient-conservation plus seedbank observation contracts"

agentInteractionExperimentBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
agentInteractionExperimentBundle = Synthesis.experimentBundle
  Experiment.AgentInteraction
  Experiment.agentInteractionConsumer
  4
  "agent-interaction discriminator selected by equal-count/equal-suppression collision"
  "declared agent-density, damage, abiotic-context and co-occurrence observation"

oxygenBundleSeparatesCollision :
  Synthesis.BundleSeparates oxygenExperimentBundle
    Experiment.oxygenDebtWorld Experiment.oxygenRecoveryWorld
oxygenBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

communityBundleSeparatesCollision :
  Synthesis.BundleSeparates communityExperimentBundle
    Experiment.restorationFailureWorld Experiment.restorationRecoveryWorld
communityBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

reboundBundleSeparatesCollision :
  Synthesis.BundleSeparates reboundExperimentBundle
    Experiment.reboundHighWorld Experiment.reboundLowWorld
reboundBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

agentInteractionBundleSeparatesCollision :
  Synthesis.BundleSeparates agentInteractionExperimentBundle
    Experiment.agentIndependentWorld Experiment.agentInterferenceWorld
agentInteractionBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

------------------------------------------------------------------------
-- Realised fibre refinements: observe only what the live consumer requires.
------------------------------------------------------------------------

allHypothesesLive : Experiment.InterventionWorld → Set
allHypothesesLive world = ⊤

oxygenRecoveredFibre : Experiment.InterventionWorld → Set
oxygenRecoveredFibre = Planner.RefineByBundle
  allHypothesesLive oxygenExperimentBundle
  (Experiment.oxygenRecovered , Experiment.exportedFromWater)

oxygenRecoveryWorldRemainsLive : oxygenRecoveredFibre Experiment.oxygenRecoveryWorld
oxygenRecoveryWorldRemainsLive = tt , refl

restorationRecoveredFibre : Experiment.InterventionWorld → Set
restorationRecoveredFibre = Planner.RefineByBundle
  allHypothesesLive communityExperimentBundle Experiment.nativeRecovery

restorationRecoveryWorldRemainsLive :
  restorationRecoveredFibre Experiment.restorationRecoveryWorld
restorationRecoveryWorldRemainsLive = tt , refl

reboundReducedFibre : Experiment.InterventionWorld → Set
reboundReducedFibre = Planner.RefineByBundle
  allHypothesesLive reboundExperimentBundle
  (Experiment.nutrientResidualLow , Experiment.seedbankReduced)

reboundLowWorldRemainsLive : reboundReducedFibre Experiment.reboundLowWorld
reboundLowWorldRemainsLive = tt , refl

agentIndependentFibre : Experiment.InterventionWorld → Set
agentIndependentFibre = Planner.RefineByBundle
  allHypothesesLive agentInteractionExperimentBundle Experiment.agentIndependent

agentIndependentWorldRemainsLive :
  agentIndependentFibre Experiment.agentIndependentWorld
agentIndependentWorldRemainsLive = tt , refl

------------------------------------------------------------------------
-- Ecological certificate dependency graph.
------------------------------------------------------------------------

data Artifact : Set where
  oxygenObservation : Artifact
  reboundObservation : Artifact
  communityObservation : Artifact
  agentInteractionObservation : Artifact
  oxygenOutcomeCertificate : Artifact
  reboundOutcomeCertificate : Artifact
  restorationOutcomeCertificate : Artifact
  agentInteractionCertificate : Artifact
  netOutcomeCertificate : Artifact
  hostSpecificityCertificate : Artifact


data Depends : Artifact → Artifact → Set where
  oxygenObservationAffectsOxygenOutcome :
    Depends oxygenObservation oxygenOutcomeCertificate
  reboundObservationAffectsReboundOutcome :
    Depends reboundObservation reboundOutcomeCertificate
  communityObservationAffectsRestorationOutcome :
    Depends communityObservation restorationOutcomeCertificate
  agentObservationAffectsInteractionOutcome :
    Depends agentInteractionObservation agentInteractionCertificate
  oxygenOutcomeAffectsNetOutcome :
    Depends oxygenOutcomeCertificate netOutcomeCertificate
  reboundOutcomeAffectsNetOutcome :
    Depends reboundOutcomeCertificate netOutcomeCertificate
  restorationOutcomeAffectsNetOutcome :
    Depends restorationOutcomeCertificate netOutcomeCertificate
  interactionOutcomeAffectsNetOutcome :
    Depends agentInteractionCertificate netOutcomeCertificate

------------------------------------------------------------------------
-- Reopening receipts.
------------------------------------------------------------------------

record OxygenReopeningReceipt : Set where
  constructor oxygenReopeningReceipt
  field obligation : Affected.ReopeningObligation
    Depends oxygenObservation oxygenOutcomeCertificate

canonicalOxygenReopening : OxygenReopeningReceipt
canonicalOxygenReopening = oxygenReopeningReceipt
  (Affected.oneEdgeCreatesReopeningObligation oxygenObservationAffectsOxygenOutcome)

record NetOutcomeReopeningReceipt : Set where
  constructor netOutcomeReopeningReceipt
  field obligation : Affected.ReopeningObligation
    Depends oxygenObservation netOutcomeCertificate

canonicalNetOutcomeReopening : NetOutcomeReopeningReceipt
canonicalNetOutcomeReopening = netOutcomeReopeningReceipt
  (Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation oxygenObservationAffectsOxygenOutcome)
    (Affected.oneEdgeCreatesReopeningObligation oxygenOutcomeAffectsNetOutcome))

record ReboundReopeningReceipt : Set where
  constructor reboundReopeningReceipt
  field obligation : Affected.ReopeningObligation
    Depends reboundObservation reboundOutcomeCertificate

canonicalReboundReopening : ReboundReopeningReceipt
canonicalReboundReopening = reboundReopeningReceipt
  (Affected.oneEdgeCreatesReopeningObligation reboundObservationAffectsReboundOutcome)

record RestorationReopeningReceipt : Set where
  constructor restorationReopeningReceipt
  field obligation : Affected.ReopeningObligation
    Depends communityObservation restorationOutcomeCertificate

canonicalRestorationReopening : RestorationReopeningReceipt
canonicalRestorationReopening = restorationReopeningReceipt
  (Affected.oneEdgeCreatesReopeningObligation communityObservationAffectsRestorationOutcome)

record AgentInteractionReopeningReceipt : Set where
  constructor agentInteractionReopeningReceipt
  field obligation : Affected.ReopeningObligation
    Depends agentInteractionObservation agentInteractionCertificate

canonicalAgentInteractionReopening : AgentInteractionReopeningReceipt
canonicalAgentInteractionReopening = agentInteractionReopeningReceipt
  (Affected.oneEdgeCreatesReopeningObligation agentObservationAffectsInteractionOutcome)

------------------------------------------------------------------------
-- Host-specificity is outside every declared externality-observation closure.
------------------------------------------------------------------------

netOutcomeCannotReachHostSpecificity :
  Affected.AffectedClosure Depends netOutcomeCertificate hostSpecificityCertificate → ⊥
netOutcomeCannotReachHostSpecificity ()

oxygenOutcomeCannotReachHostSpecificity :
  Affected.AffectedClosure Depends oxygenOutcomeCertificate hostSpecificityCertificate → ⊥
oxygenOutcomeCannotReachHostSpecificity
  (Affected.affectedStep oxygenOutcomeAffectsNetOutcome rest) =
    netOutcomeCannotReachHostSpecificity rest

reboundOutcomeCannotReachHostSpecificity :
  Affected.AffectedClosure Depends reboundOutcomeCertificate hostSpecificityCertificate → ⊥
reboundOutcomeCannotReachHostSpecificity
  (Affected.affectedStep reboundOutcomeAffectsNetOutcome rest) =
    netOutcomeCannotReachHostSpecificity rest

restorationOutcomeCannotReachHostSpecificity :
  Affected.AffectedClosure Depends restorationOutcomeCertificate hostSpecificityCertificate → ⊥
restorationOutcomeCannotReachHostSpecificity
  (Affected.affectedStep restorationOutcomeAffectsNetOutcome rest) =
    netOutcomeCannotReachHostSpecificity rest

interactionOutcomeCannotReachHostSpecificity :
  Affected.AffectedClosure Depends agentInteractionCertificate hostSpecificityCertificate → ⊥
interactionOutcomeCannotReachHostSpecificity
  (Affected.affectedStep interactionOutcomeAffectsNetOutcome rest) =
    netOutcomeCannotReachHostSpecificity rest

oxygenObservationCannotReachHostSpecificity :
  Affected.AffectedClosure Depends oxygenObservation hostSpecificityCertificate → ⊥
oxygenObservationCannotReachHostSpecificity
  (Affected.affectedStep oxygenObservationAffectsOxygenOutcome rest) =
    oxygenOutcomeCannotReachHostSpecificity rest

reboundObservationCannotReachHostSpecificity :
  Affected.AffectedClosure Depends reboundObservation hostSpecificityCertificate → ⊥
reboundObservationCannotReachHostSpecificity
  (Affected.affectedStep reboundObservationAffectsReboundOutcome rest) =
    reboundOutcomeCannotReachHostSpecificity rest

communityObservationCannotReachHostSpecificity :
  Affected.AffectedClosure Depends communityObservation hostSpecificityCertificate → ⊥
communityObservationCannotReachHostSpecificity
  (Affected.affectedStep communityObservationAffectsRestorationOutcome rest) =
    restorationOutcomeCannotReachHostSpecificity rest

agentObservationCannotReachHostSpecificity :
  Affected.AffectedClosure Depends agentInteractionObservation hostSpecificityCertificate → ⊥
agentObservationCannotReachHostSpecificity
  (Affected.affectedStep agentObservationAffectsInteractionOutcome rest) =
    interactionOutcomeCannotReachHostSpecificity rest

record HostSpecificityUnaffectedReceipt : Set where
  constructor hostSpecificityUnaffectedReceipt
  field noAffectedClosure :
    Affected.AffectedClosure Depends oxygenObservation hostSpecificityCertificate → ⊥

canonicalHostSpecificityUnaffected : HostSpecificityUnaffectedReceipt
canonicalHostSpecificityUnaffected =
  hostSpecificityUnaffectedReceipt oxygenObservationCannotReachHostSpecificity

------------------------------------------------------------------------
-- Per-consumer active-search packets.
------------------------------------------------------------------------

record ReboundActiveSearchReceipt : Set₁ where
  constructor reboundActiveSearchReceipt
  field
    collision : Consumer.ConsumerRelevantCollision
      Experiment.suppressionObserver Experiment.reboundConsumer
    discriminator : Synthesis.BundleSeparates reboundExperimentBundle
      Experiment.reboundHighWorld Experiment.reboundLowWorld
    realisedRefinement : reboundReducedFibre Experiment.reboundLowWorld
    reopening : ReboundReopeningReceipt
    hostSpecificityUnaffected :
      Affected.AffectedClosure Depends reboundObservation hostSpecificityCertificate → ⊥

canonicalReboundActiveSearch : ReboundActiveSearchReceipt
canonicalReboundActiveSearch = reboundActiveSearchReceipt
  reboundConsumerCollision reboundBundleSeparatesCollision reboundLowWorldRemainsLive
  canonicalReboundReopening reboundObservationCannotReachHostSpecificity

record RestorationActiveSearchReceipt : Set₁ where
  constructor restorationActiveSearchReceipt
  field
    collision : Consumer.ConsumerRelevantCollision
      Experiment.suppressionOxygenObserver Experiment.restorationConsumer
    discriminator : Synthesis.BundleSeparates communityExperimentBundle
      Experiment.restorationFailureWorld Experiment.restorationRecoveryWorld
    realisedRefinement :
      restorationRecoveredFibre Experiment.restorationRecoveryWorld
    reopening : RestorationReopeningReceipt
    hostSpecificityUnaffected :
      Affected.AffectedClosure Depends communityObservation hostSpecificityCertificate → ⊥

canonicalRestorationActiveSearch : RestorationActiveSearchReceipt
canonicalRestorationActiveSearch = restorationActiveSearchReceipt
  restorationConsumerCollision communityBundleSeparatesCollision
  restorationRecoveryWorldRemainsLive canonicalRestorationReopening
  communityObservationCannotReachHostSpecificity

record AgentInteractionActiveSearchReceipt : Set₁ where
  constructor agentInteractionActiveSearchReceipt
  field
    collision : Consumer.ConsumerRelevantCollision
      Experiment.suppressionAgentCountObserver Experiment.agentInteractionConsumer
    discriminator : Synthesis.BundleSeparates agentInteractionExperimentBundle
      Experiment.agentIndependentWorld Experiment.agentInterferenceWorld
    realisedRefinement :
      agentIndependentFibre Experiment.agentIndependentWorld
    reopening : AgentInteractionReopeningReceipt
    hostSpecificityUnaffected :
      Affected.AffectedClosure Depends agentInteractionObservation hostSpecificityCertificate → ⊥

canonicalAgentInteractionActiveSearch : AgentInteractionActiveSearchReceipt
canonicalAgentInteractionActiveSearch = agentInteractionActiveSearchReceipt
  agentInteractionConsumerCollision agentInteractionBundleSeparatesCollision
  agentIndependentWorldRemainsLive canonicalAgentInteractionReopening
  agentObservationCannotReachHostSpecificity

------------------------------------------------------------------------
-- Active ecological experiment-search weld.
------------------------------------------------------------------------

record BiocontrolActiveExperimentSearch : Set₁ where
  constructor biocontrolActiveExperimentSearch
  field
    oxygenCollision : Consumer.ConsumerRelevantCollision
      Experiment.suppressionObserver Experiment.oxygenConsumer
    oxygenDiscriminator : Synthesis.BundleSeparates oxygenExperimentBundle
      Experiment.oxygenDebtWorld Experiment.oxygenRecoveryWorld
    oxygenRealisedRefinement : oxygenRecoveredFibre Experiment.oxygenRecoveryWorld
    restorationSearch : RestorationActiveSearchReceipt
    reboundSearch : ReboundActiveSearchReceipt
    agentSearch : AgentInteractionActiveSearchReceipt
    oxygenReopening : OxygenReopeningReceipt
    netOutcomeReopening : NetOutcomeReopeningReceipt
    hostSpecificityUnaffected : HostSpecificityUnaffectedReceipt
    searchReference : String

canonicalBiocontrolActiveExperimentSearch : BiocontrolActiveExperimentSearch
canonicalBiocontrolActiveExperimentSearch = biocontrolActiveExperimentSearch
  oxygenConsumerCollision
  oxygenBundleSeparatesCollision
  oxygenRecoveryWorldRemainsLive
  canonicalRestorationActiveSearch
  canonicalReboundActiveSearch
  canonicalAgentInteractionActiveSearch
  canonicalOxygenReopening
  canonicalNetOutcomeReopening
  canonicalHostSpecificityUnaffected
  "four consumer-relevant collisions -> generic discriminator bundles -> realised fibre refinements -> selective reopening of only affected outcome certificates"

record BiocontrolActiveSearchBoundary : Set where
  constructor biocontrolActiveSearchBoundary
  field
    everyEcologicalObservationReopensEveryCertificate : Bool
    everyEcologicalObservationReopensEveryCertificateIsFalse :
      everyEcologicalObservationReopensEveryCertificate ≡ false
    completeHiddenEcosystemStateRequiredBeforeConsumerClosure : Bool
    completeHiddenEcosystemStateRequiredBeforeConsumerClosureIsFalse :
      completeHiddenEcosystemStateRequiredBeforeConsumerClosure ≡ false
    hostSpecificityAutomaticallyPaidByExternalityObservation : Bool
    hostSpecificityAutomaticallyPaidByExternalityObservationIsFalse :
      hostSpecificityAutomaticallyPaidByExternalityObservation ≡ false
    allFourExternalityClassesUseSameGenericSearchSpine : Bool
    allFourExternalityClassesUseSameGenericSearchSpineIsTrue :
      allFourExternalityClassesUseSameGenericSearchSpine ≡ true

canonicalBiocontrolActiveSearchBoundary : BiocontrolActiveSearchBoundary
canonicalBiocontrolActiveSearchBoundary =
  biocontrolActiveSearchBoundary false refl false refl false refl true refl
