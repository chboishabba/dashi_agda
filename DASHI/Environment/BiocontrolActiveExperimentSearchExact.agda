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
-- active proof search.  Ecological experiment choice is not a parallel planner.
------------------------------------------------------------------------

oxygenConsumerCollision :
  Consumer.ConsumerRelevantCollision
    Experiment.suppressionObserver Experiment.oxygenConsumer
oxygenConsumerCollision = Consumer.consumer-relevant-collision
  Experiment.oxygenDebtWorld
  Experiment.oxygenRecoveryWorld
  refl
  (λ ())

oxygenExperimentBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
oxygenExperimentBundle = Synthesis.experimentBundle
  Experiment.OxygenState
  Experiment.oxygenConsumer
  1
  "dissolved-oxygen discriminator selected by suppression collision"
  "declared dissolved-oxygen measurement / trajectory derivation"

oxygenBundleSeparatesCollision :
  Synthesis.BundleSeparates
    oxygenExperimentBundle
    Experiment.oxygenDebtWorld
    Experiment.oxygenRecoveryWorld
oxygenBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

restorationConsumerCollision :
  Consumer.ConsumerRelevantCollision
    Experiment.suppressionOxygenObserver Experiment.restorationConsumer
restorationConsumerCollision = Consumer.consumer-relevant-collision
  Experiment.restorationFailureWorld
  Experiment.restorationRecoveryWorld
  refl
  (λ ())

communityExperimentBundle : Synthesis.ExperimentBundle Experiment.InterventionWorld
communityExperimentBundle = Synthesis.experimentBundle
  Experiment.CommunityState
  Experiment.restorationConsumer
  1
  "community-composition discriminator selected after suppression+oxygen collision"
  "declared community-composition survey"

communityBundleSeparatesCollision :
  Synthesis.BundleSeparates
    communityExperimentBundle
    Experiment.restorationFailureWorld
    Experiment.restorationRecoveryWorld
communityBundleSeparatesCollision = Synthesis.bundleSeparates (λ ())

allHypothesesLive : Experiment.InterventionWorld → Set
allHypothesesLive world = ⊤

oxygenRecoveredFibre : Experiment.InterventionWorld → Set
oxygenRecoveredFibre =
  Planner.RefineByBundle
    allHypothesesLive
    oxygenExperimentBundle
    Experiment.oxygenRecovered

oxygenRecoveryWorldRemainsLive : oxygenRecoveredFibre Experiment.oxygenRecoveryWorld
oxygenRecoveryWorldRemainsLive = tt , refl

------------------------------------------------------------------------
-- Ecological certificate dependency graph.
------------------------------------------------------------------------

data Artifact : Set where
  oxygenObservation : Artifact
  oxygenOutcomeCertificate : Artifact
  netOutcomeCertificate : Artifact
  hostSpecificityCertificate : Artifact


data Depends : Artifact → Artifact → Set where
  oxygenObservationAffectsOxygenOutcome :
    Depends oxygenObservation oxygenOutcomeCertificate
  oxygenOutcomeAffectsNetOutcome :
    Depends oxygenOutcomeCertificate netOutcomeCertificate

------------------------------------------------------------------------
-- Canonical reopening obligations.
------------------------------------------------------------------------

record OxygenReopeningReceipt : Set where
  constructor oxygenReopeningReceipt
  field
    obligation :
      Affected.ReopeningObligation
        Depends oxygenObservation oxygenOutcomeCertificate

canonicalOxygenReopening : OxygenReopeningReceipt
canonicalOxygenReopening = oxygenReopeningReceipt
  (Affected.oneEdgeCreatesReopeningObligation oxygenObservationAffectsOxygenOutcome)

record NetOutcomeReopeningReceipt : Set where
  constructor netOutcomeReopeningReceipt
  field
    obligation :
      Affected.ReopeningObligation
        Depends oxygenObservation netOutcomeCertificate

canonicalNetOutcomeReopening : NetOutcomeReopeningReceipt
canonicalNetOutcomeReopening = netOutcomeReopeningReceipt
  (Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation oxygenObservationAffectsOxygenOutcome)
    (Affected.oneEdgeCreatesReopeningObligation oxygenOutcomeAffectsNetOutcome))

------------------------------------------------------------------------
-- Host-specificity is deliberately outside the oxygen reverse dependency
-- closure.  This is stronger than merely omitting a direct edge: no declared
-- transitive path can reach the host-specificity certificate either.
------------------------------------------------------------------------

netOutcomeCannotReachHostSpecificity :
  Affected.AffectedClosure Depends netOutcomeCertificate hostSpecificityCertificate → ⊥
netOutcomeCannotReachHostSpecificity ()

oxygenOutcomeCannotReachHostSpecificity :
  Affected.AffectedClosure Depends oxygenOutcomeCertificate hostSpecificityCertificate → ⊥
oxygenOutcomeCannotReachHostSpecificity
  (Affected.affectedStep oxygenOutcomeAffectsNetOutcome rest) =
    netOutcomeCannotReachHostSpecificity rest

oxygenObservationCannotReachHostSpecificity :
  Affected.AffectedClosure Depends oxygenObservation hostSpecificityCertificate → ⊥
oxygenObservationCannotReachHostSpecificity
  (Affected.affectedStep oxygenObservationAffectsOxygenOutcome rest) =
    oxygenOutcomeCannotReachHostSpecificity rest

record HostSpecificityUnaffectedReceipt : Set where
  constructor hostSpecificityUnaffectedReceipt
  field
    noAffectedClosure :
      Affected.AffectedClosure Depends oxygenObservation hostSpecificityCertificate → ⊥

canonicalHostSpecificityUnaffected : HostSpecificityUnaffectedReceipt
canonicalHostSpecificityUnaffected =
  hostSpecificityUnaffectedReceipt oxygenObservationCannotReachHostSpecificity

------------------------------------------------------------------------
-- Active ecological experiment-search weld.
------------------------------------------------------------------------

record BiocontrolActiveExperimentSearch : Set₁ where
  constructor biocontrolActiveExperimentSearch
  field
    oxygenCollision :
      Consumer.ConsumerRelevantCollision
        Experiment.suppressionObserver Experiment.oxygenConsumer
    oxygenDiscriminator :
      Synthesis.BundleSeparates
        oxygenExperimentBundle
        Experiment.oxygenDebtWorld
        Experiment.oxygenRecoveryWorld
    restorationCollision :
      Consumer.ConsumerRelevantCollision
        Experiment.suppressionOxygenObserver Experiment.restorationConsumer
    restorationDiscriminator :
      Synthesis.BundleSeparates
        communityExperimentBundle
        Experiment.restorationFailureWorld
        Experiment.restorationRecoveryWorld
    realisedRefinement : oxygenRecoveredFibre Experiment.oxygenRecoveryWorld
    oxygenReopening : OxygenReopeningReceipt
    netOutcomeReopening : NetOutcomeReopeningReceipt
    hostSpecificityUnaffected : HostSpecificityUnaffectedReceipt
    searchReference : String

canonicalBiocontrolActiveExperimentSearch : BiocontrolActiveExperimentSearch
canonicalBiocontrolActiveExperimentSearch = biocontrolActiveExperimentSearch
  oxygenConsumerCollision
  oxygenBundleSeparatesCollision
  restorationConsumerCollision
  communityBundleSeparatesCollision
  oxygenRecoveryWorldRemainsLive
  canonicalOxygenReopening
  canonicalNetOutcomeReopening
  canonicalHostSpecificityUnaffected
  "consumer-relevant collision -> generic discriminator bundle -> realised fibre refinement -> selective reopening of only affected outcome certificates"

record BiocontrolActiveSearchBoundary : Set where
  constructor biocontrolActiveSearchBoundary
  field
    everyEcologicalObservationReopensEveryCertificate : Bool
    everyEcologicalObservationReopensEveryCertificateIsFalse :
      everyEcologicalObservationReopensEveryCertificate ≡ false
    completeHiddenEcosystemStateRequiredBeforeConsumerClosure : Bool
    completeHiddenEcosystemStateRequiredBeforeConsumerClosureIsFalse :
      completeHiddenEcosystemStateRequiredBeforeConsumerClosure ≡ false
    hostSpecificityAutomaticallyPaidByOxygenObservation : Bool
    hostSpecificityAutomaticallyPaidByOxygenObservationIsFalse :
      hostSpecificityAutomaticallyPaidByOxygenObservation ≡ false

canonicalBiocontrolActiveSearchBoundary : BiocontrolActiveSearchBoundary
canonicalBiocontrolActiveSearchBoundary =
  biocontrolActiveSearchBoundary false refl false refl false refl
