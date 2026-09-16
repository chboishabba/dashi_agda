module DASHI.Education.DigitalESDExternalityIncidenceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.BenefitBurdenExternalityDistributionExact as Distribution
import DASHI.Core.ResponsibilityBurdenNonfactorabilityExact as Responsibility
import DASHI.Core.ConsentTemporalExternalityExact as Temporal
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Power
import DASHI.Governance.ExternalityCarrierAttractor as Carrier
import DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact as TSMC
import DASHI.Wikimedia.IbrahimSnowballPetrochemistryLifecycleParentAuditExact as Petrochem
import DASHI.Governance.TrumpEnergyCrackSpreadCrossPollinationExact as Energy

------------------------------------------------------------------------
-- DIGITAL-ESD EXTERNALITY INCIDENCE AUDIT
--
-- Thin application owner.  The generic distributional, responsibility,
-- temporal and socio-technical non-factorability theorems remain canonical.
-- TSMC, petrochemistry, Iran/energy and Trump-policy material is imported only
-- as bounded cross-domain calibration: it illustrates failure modes that an
-- educational sustainability audit should be able to represent, but it does
-- not create a political conclusion, a digital-education finding, or a
-- deployment-specific environmental measurement.
------------------------------------------------------------------------

data ExternalityAuditQuestion : Set where
  whoContributed : ExternalityAuditQuestion
  whoBenefits : ExternalityAuditQuestion
  whoBearsBurden : ExternalityAuditQuestion
  whoHasVoice : ExternalityAuditQuestion
  whoControlsOrMediates : ExternalityAuditQuestion
  whoCanExit : ExternalityAuditQuestion
  whereInLifecycle : ExternalityAuditQuestion
  whenBurdenArrives : ExternalityAuditQuestion
  whichMaterialPosition : ExternalityAuditQuestion

externalityAuditQuestions : List ExternalityAuditQuestion
externalityAuditQuestions =
  whoContributed
  ∷ whoBenefits
  ∷ whoBearsBurden
  ∷ whoHasVoice
  ∷ whoControlsOrMediates
  ∷ whoCanExit
  ∷ whereInLifecycle
  ∷ whenBurdenArrives
  ∷ whichMaterialPosition
  ∷ []

externalityAuditQuestionCount : Nat
externalityAuditQuestionCount = 9

questionReading : ExternalityAuditQuestion → String
questionReading whoContributed =
  "who supplied labour, data, materials, knowledge, infrastructure or causal contribution?"
questionReading whoBenefits =
  "who receives learning, institutional, commercial, fiscal or strategic benefit?"
questionReading whoBearsBurden =
  "who bears workload, exclusion, surveillance, material, ecological, financial or opportunity-cost burden?"
questionReading whoHasVoice =
  "which affected parties have epistemic and decision voice over design, interpretation and downstream use?"
questionReading whoControlsOrMediates =
  "who controls infrastructure, procurement, routing, platform mediation, standards or capacity decisions?"
questionReading whoCanExit =
  "which learners, institutions or communities retain practical migration, refusal, repair or exit options?"
questionReading whereInLifecycle =
  "at which material or infrastructure lifecycle stage is the burden generated, transformed or measured?"
questionReading whenBurdenArrives =
  "is the burden immediate, deferred to later support/replacement cycles, or shifted to future parties?"
questionReading whichMaterialPosition =
  "which material position is observed: producer, intermediary, institution, worker, learner, household, community or downstream user?"

------------------------------------------------------------------------
-- Canonical theorem surfaces retained verbatim.
------------------------------------------------------------------------

distributionBoundary : Distribution.BenefitBurdenExternalityBoundary
distributionBoundary = Distribution.canonicalBenefitBurdenExternalityBoundary

responsibilityBoundary : Responsibility.ResponsibilityBurdenBoundary
responsibilityBoundary = Responsibility.canonicalResponsibilityBurdenBoundary

temporalBoundary : Temporal.ConsentTemporalExternalityBoundary
temporalBoundary = Temporal.canonicalConsentTemporalExternalityBoundary

powerBoundary : Power.SocioTechnicalPowerSelectionBoundary
powerBoundary = Power.canonicalSocioTechnicalPowerSelectionBoundary

carrierBoundary : Carrier.ExternalityCarrierBoundary
carrierBoundary = Carrier.canonicalExternalityCarrierBoundary

petrochemicalLifecycleBoundary : Petrochem.PetrochemistryParentAuditBoundary
petrochemicalLifecycleBoundary = Petrochem.canonicalPetrochemistryParentAuditBoundary

tsmcCalibration : TSMC.ManufacturingDemandPolicyCalibration
tsmcCalibration = TSMC.canonicalManufacturingDemandPolicyCalibration

energyCalibration : Energy.TrumpEnergyCrackSpreadBoundary
energyCalibration = Energy.canonicalTrumpEnergyCrackSpreadBoundary

aggregateCannotRecoverBurden = Distribution.aggregateCannotRecoverBurden
aggregateCannotRecoverVoice = Distribution.aggregateCannotRecoverVoice
responsibilityDoesNotEqualBurden = Responsibility.canonicalResponsibilityBurdenBoundary
presentBenefitCannotRecoverLaterBurden = Temporal.presentBenefitCannotRecoverLaterBurden
serviceCannotRecoverPowerTopology = Power.serviceCannotRecoverPowerTopology
participationCannotRecoverMediation = Power.participationCannotRecoverMediation
petroleumLabelCannotRecoverLifecycleStage = Petrochem.petroleumLabelCannotFactorLifecycleStage

------------------------------------------------------------------------
-- Cross-domain firewall.
------------------------------------------------------------------------

data CrossDomainCalibrationCreatesDigitalESDPoliticalConclusion : Set where
data CrossDomainCalibrationCreatesDeploymentMeasurement : Set where
data VisibleExternalityCarrierCreatesSufficientCause : Set where

crossDomainCalibrationDoesNotCreateDigitalESDPoliticalConclusion :
  CrossDomainCalibrationCreatesDigitalESDPoliticalConclusion → ⊥
crossDomainCalibrationDoesNotCreateDigitalESDPoliticalConclusion ()

crossDomainCalibrationDoesNotCreateDeploymentMeasurement :
  CrossDomainCalibrationCreatesDeploymentMeasurement → ⊥
crossDomainCalibrationDoesNotCreateDeploymentMeasurement ()

visibleExternalityCarrierDoesNotCreateSufficientCause :
  VisibleExternalityCarrierCreatesSufficientCause → ⊥
visibleExternalityCarrierDoesNotCreateSufficientCause ()

------------------------------------------------------------------------
-- Application boundary.
------------------------------------------------------------------------

record ExternalityIncidenceBoundary : Set where
  constructor externality-incidence-boundary
  field
    aggregateOutcomeDeterminesBurden : Bool
    aggregateOutcomeDeterminesBurdenIsFalse :
      aggregateOutcomeDeterminesBurden ≡ false
    contributionEqualsBurden : Bool
    contributionEqualsBurdenIsFalse : contributionEqualsBurden ≡ false
    serviceSurfaceDeterminesPowerTopology : Bool
    serviceSurfaceDeterminesPowerTopologyIsFalse :
      serviceSurfaceDeterminesPowerTopology ≡ false
    participationDeterminesMediation : Bool
    participationDeterminesMediationIsFalse :
      participationDeterminesMediation ≡ false
    presentBenefitDeterminesLaterBurden : Bool
    presentBenefitDeterminesLaterBurdenIsFalse :
      presentBenefitDeterminesLaterBurden ≡ false
    coarseMaterialLabelDeterminesLifecycleStage : Bool
    coarseMaterialLabelDeterminesLifecycleStageIsFalse :
      coarseMaterialLabelDeterminesLifecycleStage ≡ false
    capacityPlanningDeterminesPermanentChokepoint : Bool
    capacityPlanningDeterminesPermanentChokepointIsFalse :
      capacityPlanningDeterminesPermanentChokepoint ≡ false
    intermediateMarginDeterminesEndUserBenefit : Bool
    intermediateMarginDeterminesEndUserBenefitIsFalse :
      intermediateMarginDeterminesEndUserBenefit ≡ false
    visibleBurdenCarrierDeterminesSufficientCause : Bool
    visibleBurdenCarrierDeterminesSufficientCauseIsFalse :
      visibleBurdenCarrierDeterminesSufficientCause ≡ false
    crossDomainCalibrationOnly : Bool
    crossDomainCalibrationOnlyIsTrue : crossDomainCalibrationOnly ≡ true
    politicalConclusionCreated : Bool
    politicalConclusionCreatedIsFalse : politicalConclusionCreated ≡ false
    deploymentMeasurementCreated : Bool
    deploymentMeasurementCreatedIsFalse : deploymentMeasurementCreated ≡ false

open ExternalityIncidenceBoundary public

canonicalExternalityIncidenceBoundary : ExternalityIncidenceBoundary
canonicalExternalityIncidenceBoundary =
  externality-incidence-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl

externalityIncidenceReading : String
externalityIncidenceReading =
  "A digital-ESD sustainability claim must retain incidence rather than a single aggregate score. Contribution, benefit, burden, voice, control/mediation, exit, lifecycle stage, temporal displacement and material position are separately auditable. Existing TSMC/manufacturing, petrochemical lifecycle and Iran/Trump-energy owners are used only as bounded calibration examples showing how planning, lifecycle stage, intermediary margin, political identification, visible carrier and market headline can fail to recover downstream burden, benefit, control, causation or motive. They do not create a political conclusion or a deployment-specific digital-education sustainability measurement."
