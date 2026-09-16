module DASHI.Education.DigitalESDConsumerRelativeLifecycleRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact as ICT
import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact as Paper
import DASHI.Education.DigitalESDConsumerRelativeLifecycleExact as Bridge

currentConsumerRegression :
  Bridge.ConsumerRelativeLifecycleBoundary.currentConsumer
    Bridge.canonicalConsumerRelativeLifecycleBoundary
  ≡ Paper.integrativeConceptualReview
currentConsumerRegression = refl

conceptualLifecycleSynthesisRequiredRegression :
  Bridge.ConsumerRelativeLifecycleBoundary.currentLifecycleSynthesisRequired
    Bridge.canonicalConsumerRelativeLifecycleBoundary
  ≡ true
conceptualLifecycleSynthesisRequiredRegression = refl

conceptualSameObjectMeasurementNotRequiredRegression :
  Bridge.ConsumerRelativeLifecycleBoundary.currentSameObjectInterventionLCANotRequired
    Bridge.canonicalConsumerRelativeLifecycleBoundary
  ≡ true
conceptualSameObjectMeasurementNotRequiredRegression = refl

empiricalSameObjectMeasurementRequiredRegression :
  Bridge.ConsumerRelativeLifecycleBoundary.empiricalInterventionSameObjectLCARequired
    Bridge.canonicalConsumerRelativeLifecycleBoundary
  ≡ true
empiricalSameObjectMeasurementRequiredRegression = refl

ictMethodsPaidButDeploymentFactsOpenRegression :
  Bridge.ConsumerRelativeLifecycleBoundary.ictMethodsPaidDeploymentFactsOpen
    Bridge.canonicalConsumerRelativeLifecycleBoundary
  ≡ true
ictMethodsPaidButDeploymentFactsOpenRegression = refl

refinedEmpiricalLifecycleFrontierRegression :
  Bridge.empiricalInterventionLifecycleFrontier
  ≡ ICT.deploymentSpecificLCI
  ∷ ICT.deploymentReferenceSystem
  ∷ ICT.deploymentHardwareCircularity
  ∷ ICT.deploymentRepairSupport
  ∷ ICT.deploymentServiceLife
  ∷ ICT.deploymentInteroperabilityPersistence
  ∷ []
refinedEmpiricalLifecycleFrontierRegression = refl

parentAcquisitionResidualRetainedRegression :
  Acquisition.paymentState Acquisition.openInteroperabilityDurability
  ≡ Acquisition.unpaid
parentAcquisitionResidualRetainedRegression = refl

acquisitionPriorityDoesNotPromotePaperPriorityRegression :
  Bridge.AcquisitionPriorityPromotesCurrentPaperPriority → ⊥
acquisitionPriorityDoesNotPromotePaperPriorityRegression =
  Bridge.acquisitionPriorityDoesNotPromoteCurrentPaperPriority

methodPaymentDoesNotClosePaperSynthesisRegression :
  Bridge.MethodPaymentClosesLifecycleEvidenceSynthesis → ⊥
methodPaymentDoesNotClosePaperSynthesisRegression =
  Bridge.methodPaymentDoesNotCloseLifecycleEvidenceSynthesis

conceptualReviewDoesNotClaimDeploymentFootprintRegression :
  Bridge.ConceptualReviewClaimsSameObjectDeploymentFootprint → ⊥
conceptualReviewDoesNotClaimDeploymentFootprintRegression =
  Bridge.conceptualReviewDoesNotClaimSameObjectDeploymentFootprint
