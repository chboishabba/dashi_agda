module DASHI.Economics.AIAustraliaRegulatoryPolicyAcquisition20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AIRegulatoryBurdenConcentrationSensibLaw2026Exact as Burden
import DASHI.Economics.AISafetyRegulatoryMoatGameExact as Moat

------------------------------------------------------------------------
-- AUSTRALIAN AI POLICY ACQUISITION, 2026-10-12
--
-- Primary government pages establish a proposal, an explicit current outcome,
-- a voluntary/guidance lineage, and a regulatory-impact data-collection design.
-- They do not supply the same-basis realised compliance-cost vector needed to
-- measure an incumbent/startup/open-weight burden ratio.
------------------------------------------------------------------------

governmentSourceKind : Source.SourceKind
governmentSourceKind = Source.namedSourceKind "Australian Government primary policy page"

mandatoryGuardrailsProposalSource : Source.AttributedSource
mandatoryGuardrailsProposalSource = Source.mkNoDOISource
  "Department of Industry, Science and Resources"
  "Introducing mandatory guardrails for AI in high-risk settings: proposals paper"
  "Australian Government consultation"
  "2024-09-05 / current outcome page observed 2026-10-12"
  "https://consult.industry.gov.au/ai-mandatory-guardrails"
  governmentSourceKind
  "primary carrier for the proposed mandatory high-risk-AI guardrails and the current update that government will not proceed at this time with the previous mandatory-guardrail proposal"
  Source.publicAttribution

regulatoryImpactSurveySource : Source.AttributedSource
regulatoryImpactSurveySource = Source.mkNoDOISource
  "Department of Industry, Science and Resources"
  "Mandatory guardrails for AI in high-risk settings: developers and deployers survey"
  "Australian Government consultation survey"
  "2024-10-31 to 2024-12-06"
  "https://consult.industry.gov.au/ai-mandatory-guardrails-developers-deployers"
  governmentSourceKind
  "primary carrier showing government sought developer/deployer revenue, expenditure and regulatory-impact information under high-risk narrow-AI and GPAI scenarios"
  Source.publicAttribution

voluntarySafetyGuidanceSource : Source.AttributedSource
voluntarySafetyGuidanceSource = Source.mkNoDOISource
  "Department of Industry, Science and Resources / National Artificial Intelligence Centre"
  "Voluntary AI Safety Standard / subsequent Guidance for AI Adoption"
  "Australian Government guidance"
  "VAISS lineage updated by Guidance for AI Adoption on 2025-10-21"
  "https://www.industry.gov.au/publications/voluntary-ai-safety-standard"
  governmentSourceKind
  "primary carrier for voluntary testing, transparency, accountability, risk-management and human-oversight guidance; not a mandatory rule"
  Source.publicAttribution

record AustralianPolicyOutcome : Set where
  constructor australianPolicyOutcome
  field
    proposalTextAcquired : Bool
    proposedMandatoryHighRiskGuardrails : Bool
    mandatoryGuardrailsCurrentlyProceeding : Bool
    consultationFeedbackInformedNationalAIPlan : Bool
    voluntaryGuidanceExists : Bool
    realisedSameBasisComplianceCostsPublishedHere : Bool
    observedMarketConcentrationEffectEstablished : Bool

open AustralianPolicyOutcome public

mandatoryGuardrailsProposalAcquired : AustralianPolicyOutcome
mandatoryGuardrailsProposalAcquired = australianPolicyOutcome
  true true false true true false false

record RegulatoryImpactAcquisition : Set where
  constructor regulatoryImpactAcquisition
  field
    surveyInstrumentAcquired : Bool
    revenueQuestionDeclared : Bool
    expenditureQuestionDeclared : Bool
    regulatoryImpactQuestionDeclared : Bool
    gpaiScenarioDeclared : Bool
    respondentMicrodataAcquired : Bool
    harmonisedCostVectorAcquired : Bool

open RegulatoryImpactAcquisition public

regulatoryImpactSurveyAcquired : RegulatoryImpactAcquisition
regulatoryImpactSurveyAcquired = regulatoryImpactAcquisition
  true true true true true false false

sameBasisCostVectorStillOpen :
  harmonisedCostVectorAcquired regulatoryImpactSurveyAcquired ≡ false
sameBasisCostVectorStillOpen = refl

mandatoryProposalCurrentlyNotProceeding :
  mandatoryGuardrailsCurrentlyProceeding mandatoryGuardrailsProposalAcquired ≡ false
mandatoryProposalCurrentlyNotProceeding = refl

------------------------------------------------------------------------
-- Non-collapse boundaries.
------------------------------------------------------------------------

data VoluntaryGuidanceEqualsMandatoryRulePermission : Set where
data ProposalWithdrawalDisprovesStructuralMoatPermission : Set where
data SurveyDesignImpliesMeasuredCostPermission : Set where
data PolicyOutcomeImpliesNoFutureRegulationPermission : Set where

voluntaryGuidanceDoesNotEqualMandatoryRule :
  VoluntaryGuidanceEqualsMandatoryRulePermission → ⊥
voluntaryGuidanceDoesNotEqualMandatoryRule ()

proposalWithdrawalDoesNotDisproveStructuralMoatMechanism :
  ProposalWithdrawalDisprovesStructuralMoatPermission → ⊥
proposalWithdrawalDoesNotDisproveStructuralMoatMechanism ()

surveyDesignDoesNotManufactureMeasuredCost :
  SurveyDesignImpliesMeasuredCostPermission → ⊥
surveyDesignDoesNotManufactureMeasuredCost ()

currentOutcomeDoesNotProveNoFutureRegulation :
  PolicyOutcomeImpliesNoFutureRegulationPermission → ⊥
currentOutcomeDoesNotProveNoFutureRegulation ()

------------------------------------------------------------------------
-- Cross-pollination: Australia gives an observed policy-state trajectory, but
-- does not close the generic structural-moat theorem or the measured-burden
-- residual in the existing owner.
------------------------------------------------------------------------

existingStructuralMoatMechanism : Moat.RegulatoryMoatReceipt
existingStructuralMoatMechanism = Moat.canonicalStructuralMoatWithoutIntent

existingMeasuredBurdenResidual : Burden.RegulatoryBurdenProducerResidual
existingMeasuredBurdenResidual = Burden.currentRegulatoryBurdenResidual

measuredBurdenStillOpen :
  Burden.sameBasisComplianceCostsAcquired existingMeasuredBurdenResidual ≡ false
measuredBurdenStillOpen = refl

concentrationResponseStillOpen :
  Burden.concentrationEffectObserved existingMeasuredBurdenResidual ≡ false
concentrationResponseStillOpen = refl

policyBoundary : String
policyBoundary =
  "Australia supplies a concrete policy trajectory: proposed mandatory guardrails, explicit current non-progression of that proposal, and continuing voluntary/guidance machinery. The government also designed a survey to measure business regulatory impacts. None of those facts supplies a realised same-basis compliance-cost vector, proves market concentration, proves capture, or rules out future regulation."
