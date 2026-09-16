module DASHI.Education.DigitalESDConsumerRelativeLifecycleExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact as ICT
import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact as Paper

------------------------------------------------------------------------
-- CONSUMER-RELATIVE LIFECYCLE BRIDGE
--
-- There are two distinct frontiers in this tranche:
--
--   acquisition frontier: what external evidence would reduce programme debt;
--   paper-work frontier: what the current manuscript type actually requires.
--
-- They may inform one another but neither determines the other. In particular,
-- the current integrative conceptual review requires lifecycle evidence
-- synthesis but does not require a same-object intervention LCA. If the paper
-- becomes an empirical digital-ESD intervention, that same-object obligation
-- reopens together with the refined ICT lifecycle/circularity leaves.
------------------------------------------------------------------------

record ConsumerRelativeLifecycleBoundary : Set where
  constructor consumer-relative-lifecycle-boundary
  field
    currentConsumer : Paper.PaperType
    currentConsumerIsCurrentPaperType :
      currentConsumer ≡ Paper.currentPaperType

    currentLifecycleSynthesisRequired : Bool
    currentLifecycleSynthesisRequiredIsTrue :
      currentLifecycleSynthesisRequired ≡ true
    currentLifecycleRequirementWitness :
      Paper.requiredFor currentConsumer Paper.lifecycleEvidenceSynthesis ≡ true

    currentSameObjectInterventionLCANotRequired : Bool
    currentSameObjectInterventionLCANotRequiredIsTrue :
      currentSameObjectInterventionLCANotRequired ≡ true
    currentSameObjectInterventionLCARequirementWitness :
      Paper.requiredFor currentConsumer Paper.sameObjectInterventionLCA ≡ false

    empiricalInterventionSameObjectLCARequired : Bool
    empiricalInterventionSameObjectLCARequiredIsTrue :
      empiricalInterventionSameObjectLCARequired ≡ true
    empiricalInterventionLCARequirementWitness :
      Paper.requiredFor
        Paper.empiricalDigitalESDIntervention
        Paper.sameObjectInterventionLCA
      ≡ true

    ictMethodsPaidDeploymentFactsOpen : Bool
    ictMethodsPaidDeploymentFactsOpenIsTrue :
      ictMethodsPaidDeploymentFactsOpen ≡ true
    ictLifecycleMethodPaymentWitness :
      ICT.refinedPaymentState ICT.ictLifecycleMethod
      ≡ ICT.sourceRolePaidRefined
    ictCircularityMethodPaymentWitness :
      ICT.refinedPaymentState ICT.ictCircularityMethod
      ≡ ICT.sourceRolePaidRefined
    deploymentLCIOpenWitness :
      ICT.refinedPaymentState ICT.deploymentSpecificLCI
      ≡ ICT.unpaidRefined
    deploymentReferenceSystemOpenWitness :
      ICT.refinedPaymentState ICT.deploymentReferenceSystem
      ≡ ICT.unpaidRefined
    deploymentCircularityOpenWitness :
      ICT.refinedPaymentState ICT.deploymentHardwareCircularity
      ≡ ICT.unpaidRefined
    deploymentRepairOpenWitness :
      ICT.refinedPaymentState ICT.deploymentRepairSupport
      ≡ ICT.unpaidRefined
    deploymentServiceLifeOpenWitness :
      ICT.refinedPaymentState ICT.deploymentServiceLife
      ≡ ICT.unpaidRefined
    deploymentInteroperabilityOpenWitness :
      ICT.refinedPaymentState ICT.deploymentInteroperabilityPersistence
      ≡ ICT.unpaidRefined

    parentDurabilityResidualStillOpen : Bool
    parentDurabilityResidualStillOpenIsTrue :
      parentDurabilityResidualStillOpen ≡ true
    parentDurabilityPaymentWitness :
      Acquisition.paymentState Acquisition.openInteroperabilityDurability
      ≡ Acquisition.unpaid

open ConsumerRelativeLifecycleBoundary public

canonicalConsumerRelativeLifecycleBoundary : ConsumerRelativeLifecycleBoundary
canonicalConsumerRelativeLifecycleBoundary =
  consumer-relative-lifecycle-boundary
    Paper.currentPaperType
    refl
    true refl refl
    true refl refl
    true refl refl
    true refl
    refl refl
    refl refl refl refl refl refl
    true refl refl

------------------------------------------------------------------------
-- The empirical-intervention lifecycle frontier is retained separately from
-- the current conceptual-review work frontier.
------------------------------------------------------------------------

empiricalInterventionLifecycleFrontier : List ICT.RefinedLifecycleLeaf
empiricalInterventionLifecycleFrontier =
  ICT.deploymentSpecificLCI
  ∷ ICT.deploymentReferenceSystem
  ∷ ICT.deploymentHardwareCircularity
  ∷ ICT.deploymentRepairSupport
  ∷ ICT.deploymentServiceLife
  ∷ ICT.deploymentInteroperabilityPersistence
  ∷ []

currentConceptualPaperFrontier : List Paper.ReviewCoordinate
currentConceptualPaperFrontier = Paper.currentConceptualReviewFrontier

------------------------------------------------------------------------
-- WrongType / no-promotion firewalls.
------------------------------------------------------------------------

data AcquisitionPriorityPromotesCurrentPaperPriority : Set where

data MethodPaymentClosesLifecycleEvidenceSynthesis : Set where

data ConceptualReviewClaimsSameObjectDeploymentFootprint : Set where

data ConceptualReviewDropsLifecycleEvidenceBecauseSameObjectLCAIsNotRequired : Set where

data EmpiricalConsumerInheritsConceptualNoLCAExemption : Set where

acquisitionPriorityDoesNotPromoteCurrentPaperPriority :
  AcquisitionPriorityPromotesCurrentPaperPriority → ⊥
acquisitionPriorityDoesNotPromoteCurrentPaperPriority ()

methodPaymentDoesNotCloseLifecycleEvidenceSynthesis :
  MethodPaymentClosesLifecycleEvidenceSynthesis → ⊥
methodPaymentDoesNotCloseLifecycleEvidenceSynthesis ()

conceptualReviewDoesNotClaimSameObjectDeploymentFootprint :
  ConceptualReviewClaimsSameObjectDeploymentFootprint → ⊥
conceptualReviewDoesNotClaimSameObjectDeploymentFootprint ()

conceptualReviewStillRequiresLifecycleEvidenceSynthesis :
  ConceptualReviewDropsLifecycleEvidenceBecauseSameObjectLCAIsNotRequired → ⊥
conceptualReviewStillRequiresLifecycleEvidenceSynthesis ()

empiricalConsumerDoesNotInheritConceptualNoLCAExemption :
  EmpiricalConsumerInheritsConceptualNoLCAExemption → ⊥
empiricalConsumerDoesNotInheritConceptualNoLCAExemption ()

currentPaperFirstProducerRemainsStructuredSearch :
  Paper.currentFirstPaperProducer ≡ Paper.structuredSearchProducer
currentPaperFirstProducerRemainsStructuredSearch = refl
