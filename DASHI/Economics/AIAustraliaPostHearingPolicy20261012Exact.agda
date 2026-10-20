module DASHI.Economics.AIAustraliaPostHearingPolicy20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- AUSTRALIA POST-HEARING AI POLICY RESPONSE
--
-- October-2026 chronology now contains an observed incident -> organisational /
-- policy-response path.  That is stronger than a proposed-rule snapshot but is
-- not a realised compliance-cost or market-concentration causal estimate.
------------------------------------------------------------------------

governmentPolicyKind : Source.SourceKind
governmentPolicyKind = Source.namedSourceKind "Australian Government policy publication"

parliamentaryReportingKind : Source.SourceKind
parliamentaryReportingKind = Source.namedSourceKind "contemporaneous parliamentary-hearing reporting"

mandatoryGuardrailsOutcomeSource : Source.AttributedSource
mandatoryGuardrailsOutcomeSource = Source.mkNoDOISource
  "Australian Department of Industry, Science and Resources"
  "Introducing mandatory guardrails for AI in high-risk settings: proposals paper"
  "official consultation outcome"
  "2026-10-12"
  "https://consult.industry.gov.au/ai-mandatory-guardrails"
  governmentPolicyKind
  "official update states that the Australian Government will not proceed at this time with previous proposals to introduce mandatory guardrails for AI development and deployment; feedback informed the National AI Plan"
  Source.publicAttribution

nationalAIPlanSource : Source.AttributedSource
nationalAIPlanSource = Source.mkNoDOISource
  "Australian Department of Industry, Science and Resources"
  "National AI Plan - Keep Australians safe"
  "official government plan"
  "2025-12-02"
  "https://www.industry.gov.au/publications/national-ai-plan/keep-australians-safe"
  governmentPolicyKind
  "government approach builds on existing legal/regulatory frameworks and establishes an AI Safety Institute to monitor, test and share information on emerging capabilities, risks and harms"
  Source.publicAttribution

openAIHearingSource : Source.AttributedSource
openAIHearingSource = Source.mkNoDOISource
  "ABC News"
  "OpenAI executive flew to Australia to apologise over Medicare hack"
  "reporting of Joint Select Committee hearing"
  "2026-10-06"
  "https://www.abc.net.au/news/2026-10-06/openai-hearing-apology-key-takeaways/107235640"
  parliamentaryReportingKind
  "reports OpenAI apology, acknowledgement that government notification should have occurred sooner, new alerts for out-of-scope model internet use during training, and Anthropic support for serious AI safety incident reporting"
  Source.publicAttribution

record PostHearingPolicyState : Set where
  constructor post-hearing-policy-state
  field
    mandatoryGuardrailsNotProceeding : Bool
    nationalPlanExistingLawApproachObserved : Bool
    aiSafetyInstituteApproachObserved : Bool
    openAIApologyObserved : Bool
    openAIAdditionalMonitoringObserved : Bool
    delayedDisclosureAcknowledged : Bool
    seriousIncidentReportingProposalObservedField : Bool
    incidentResponseChronologyPaidField : Bool
    realisedSameBasisComplianceCostPaid : Bool
    observedEntryEffectPaid : Bool
    observedOpenWeightConcentrationEffectPaid : Bool
    reviewedCausalBridgePaid : Bool
    intentionalRegulatoryCapturePaid : Bool

open PostHearingPolicyState public

currentPostHearingPolicyState : PostHearingPolicyState
currentPostHearingPolicyState = post-hearing-policy-state
  true true true true true true true true
  false false false false false

mandatoryGuardrailsNotProceedingAtThisTime :
  mandatoryGuardrailsNotProceeding currentPostHearingPolicyState ≡ true
mandatoryGuardrailsNotProceedingAtThisTime = refl

openAIApologyAndMonitoringResponseObserved :
  openAIApologyObserved currentPostHearingPolicyState ≡ true
  × openAIAdditionalMonitoringObserved currentPostHearingPolicyState ≡ true
openAIApologyAndMonitoringResponseObserved = refl , refl

seriousIncidentReportingProposalObserved :
  seriousIncidentReportingProposalObservedField currentPostHearingPolicyState ≡ true
seriousIncidentReportingProposalObserved = refl

incidentResponseChronologyPaid :
  incidentResponseChronologyPaidField currentPostHearingPolicyState ≡ true
incidentResponseChronologyPaid = refl

realisedComplianceCostStillOpen :
  realisedSameBasisComplianceCostPaid currentPostHearingPolicyState ≡ false
realisedComplianceCostStillOpen = refl

concentrationCausalEffectStillOpen :
  observedOpenWeightConcentrationEffectPaid currentPostHearingPolicyState ≡ false
concentrationCausalEffectStillOpen = refl

data IncidentResponseImpliesComplianceCostPermission : Set where
data PolicyResponseImpliesConcentrationEffectPermission : Set where
data PolicyResponseImpliesRegulatoryCapturePermission : Set where

actionAfterIncidentDoesNotCreateComplianceCost :
  IncidentResponseImpliesComplianceCostPermission → ⊥
actionAfterIncidentDoesNotCreateComplianceCost ()

policyResponseDoesNotCreateConcentrationEffect :
  PolicyResponseImpliesConcentrationEffectPermission → ⊥
policyResponseDoesNotCreateConcentrationEffect ()

policyResponseDoesNotCreateRegulatoryCapture :
  PolicyResponseImpliesRegulatoryCapturePermission → ⊥
policyResponseDoesNotCreateRegulatoryCapture ()

boundary : String
boundary =
  "The October-2026 Australian evidence now pays an incident-to-response chronology: OpenAI apologised for the Medicare incident, acknowledged delayed notification and described additional monitoring; serious-incident reporting was advocated at the hearing. Separately, the Australian Government states that the earlier mandatory-guardrails proposal will not proceed at this time and the National AI Plan instead builds on existing law plus an AI Safety Institute. These observations do not supply realised same-basis compliance costs, entry/open-weight/concentration effects, a reviewed causal bridge, or intentional regulatory-capture authority."
