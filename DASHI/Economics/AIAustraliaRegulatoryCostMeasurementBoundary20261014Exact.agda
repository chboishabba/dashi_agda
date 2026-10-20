module DASHI.Economics.AIAustraliaRegulatoryCostMeasurementBoundary20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryGovernmentConsultation : Source.SourceKind
primaryGovernmentConsultation = Source.namedSourceKind "primary government consultation instrument"

surveySource : Source.AttributedSource
surveySource = Source.mkNoDOISource
  "Australian Department of Industry, Science and Resources"
  "Mandatory guardrails for AI in high-risk settings: developers and deployers survey"
  "government consultation instrument"
  "2024-10-31"
  "https://consult.industry.gov.au/ai-mandatory-guardrails-developers-deployers"
  primaryGovernmentConsultation
  "survey explicitly sought business AI activity, AI revenue/expenditure, and expected regulatory impact under high-risk narrow-AI and GPAI scenarios"
  Source.publicAttribution

responsesSource : Source.AttributedSource
responsesSource = Source.mkNoDOISource
  "Australian Department of Industry, Science and Resources"
  "Published responses: mandatory guardrails for AI in high-risk settings"
  "government consultation response index"
  "2026-10-14"
  "https://consult.industry.gov.au/ai-mandatory-guardrails/submission/list"
  primaryGovernmentConsultation
  "published response index exposes consultation submissions, but this acquisition did not locate a harmonised realised actor-class compliance-cost result vector from the survey"
  Source.publicAttribution

record RegulatoryCostMeasurementStatus : Set where
  constructor regulatory-cost-measurement-status
  field
    businessImpactSurveyInstrumentPaid : Bool
    revenueExpenditureQuestionsPaid : Bool
    expectedRegulatoryImpactQuestionsPaid : Bool
    publishedSubmissionIndexPaid : Bool
    harmonisedRealisedCostVectorPaid : Bool
    incumbentCostPaid : Bool
    startupCostPaid : Bool
    openWeightCostPaid : Bool
    observedEntryResponsePaid : Bool
    observedConcentrationResponsePaid : Bool

open RegulatoryCostMeasurementStatus public

currentRegulatoryCostMeasurementStatus : RegulatoryCostMeasurementStatus
currentRegulatoryCostMeasurementStatus = regulatory-cost-measurement-status
  true true true true false false false false false false

businessImpactSurveyInstrumentObserved :
  businessImpactSurveyInstrumentPaid currentRegulatoryCostMeasurementStatus ≡ true
businessImpactSurveyInstrumentObserved = refl

harmonisedRealisedCostVectorPaidIsFalse :
  harmonisedRealisedCostVectorPaid currentRegulatoryCostMeasurementStatus ≡ false
harmonisedRealisedCostVectorPaidIsFalse = refl

data SurveyInstrumentImpliesRealisedCostVectorPermission : Set where
data PublishedSubmissionsImpliesConcentrationEffectPermission : Set where

surveyInstrumentDoesNotCreateRealisedCostVector :
  SurveyInstrumentImpliesRealisedCostVectorPermission → ⊥
surveyInstrumentDoesNotCreateRealisedCostVector ()

publishedSubmissionsDoNotCreateConcentrationEffect :
  PublishedSubmissionsImpliesConcentrationEffectPermission → ⊥
publishedSubmissionsDoNotCreateConcentrationEffect ()

boundary : String
boundary =
  "Australia created a primary-government measurement instrument explicitly asking AI developers/deployers about revenue, expenditure and expected regulatory impacts, and publishes consultation submissions. This acquisition does not find a harmonised realised compliance-cost vector by incumbent/startup/open-weight class, nor observed entry/concentration response. Instrument existence and qualitative submissions therefore remain distinct from measured burden and causal market effects."
