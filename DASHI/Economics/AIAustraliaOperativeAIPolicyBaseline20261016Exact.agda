module DASHI.Economics.AIAustraliaOperativeAIPolicyBaseline20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

governmentPolicySourceKind : Source.SourceKind
governmentPolicySourceKind = Source.institutionalSource

mandatoryGuardrailsUpdate : Source.AttributedSource
mandatoryGuardrailsUpdate = Source.mkNoDOISource
  "Australian Government Department of Industry, Science and Resources"
  "Introducing mandatory guardrails for AI in high-risk settings: proposals paper — outcomes update"
  "government consultation outcome"
  "2026-10-16"
  "https://consult.industry.gov.au/ai-mandatory-guardrails"
  governmentPolicySourceKind
  "states that government will not proceed at this time with previous proposals for mandatory guardrails and that consultation informed the National AI Plan"
  Source.publicAttribution

nationalAIPlanSafetySource : Source.AttributedSource
nationalAIPlanSafetySource = Source.mkNoDOISource
  "Australian Government Department of Industry, Science and Resources"
  "National AI Plan — Keep Australians safe"
  "government policy plan"
  "2026"
  "https://www.industry.gov.au/publications/national-ai-plan/keep-australians-safe"
  governmentPolicySourceKind
  "states that the regulatory approach continues to build on existing legal and regulatory frameworks and establishes an AI Safety Institute to monitor, test and share information"
  Source.publicAttribution

record AustralianOperativeAIPolicyBaseline : Set where
  constructor australian-operative-ai-policy-baseline
  field
    mandatoryGeneralGuardrailsProceeding : Bool
    existingLawFoundation : Bool
    aiSafetyInstituteEstablishedPolicy : Bool
    voluntaryGuidanceAvailable : Bool
    newCrossEconomyMandatoryComplianceCostObserved : Bool
    realisedActorClassCostVectorObserved : Bool
    concentrationEffectObserved : Bool
    regulatoryCaptureEstablished : Bool

open AustralianOperativeAIPolicyBaseline public

currentAustralianOperativeAIPolicy : AustralianOperativeAIPolicyBaseline
currentAustralianOperativeAIPolicy = australian-operative-ai-policy-baseline
  false true true true false false false false

mandatoryProposalCurrentlyNotProceeding : mandatoryGeneralGuardrailsProceeding currentAustralianOperativeAIPolicy ≡ false
mandatoryProposalCurrentlyNotProceeding = refl

existingLawFoundationPaid : existingLawFoundation currentAustralianOperativeAIPolicy ≡ true
existingLawFoundationPaid = refl

data ProposalCreatesOperativeBurdenPermission : Set where
data GuidanceCreatesMandatoryCostPermission : Set where
data PolicyBaselineCreatesCapturePermission : Set where

proposalDoesNotCreateOperativeBurden : ProposalCreatesOperativeBurdenPermission → ⊥
proposalDoesNotCreateOperativeBurden ()

guidanceDoesNotCreateMandatoryCost : GuidanceCreatesMandatoryCostPermission → ⊥
guidanceDoesNotCreateMandatoryCost ()

policyBaselineDoesNotCreateCapture : PolicyBaselineCreatesCapturePermission → ⊥
policyBaselineDoesNotCreateCapture ()

boundary : String
boundary =
  "Australia's current general AI-policy baseline is now claim-bounded to operative status rather than proposal history: the earlier mandatory-guardrails proposal is not proceeding at this time; the National AI Plan says existing law remains the regulatory foundation and establishes an AI Safety Institute, alongside guidance. No new cross-economy mandatory AI compliance-cost vector, realised actor-class burden, concentration effect or capture conclusion is inferred from that baseline. Future sector-specific or enacted obligations remain separate objects."
