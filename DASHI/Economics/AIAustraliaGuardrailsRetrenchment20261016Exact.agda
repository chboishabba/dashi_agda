module DASHI.Economics.AIAustraliaGuardrailsRetrenchment20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

governmentConsultationKind : Source.SourceKind
governmentConsultationKind = Source.namedSourceKind "Australian Government consultation update"

australianGuardrailsSource : Source.AttributedSource
australianGuardrailsSource = Source.mkNoDOISource
  "Australian Government Department of Industry, Science and Resources"
  "Introducing mandatory guardrails for AI in high-risk settings: proposals paper"
  "consultation page update"
  "2026"
  "https://consult.industry.gov.au/ai-mandatory-guardrails"
  governmentConsultationKind
  "states that the Australian Government will not proceed at this time with the previous mandatory-guardrails proposals and that consultation feedback informed development of the National AI Plan"
  Source.publicAttribution

record AustralianGuardrailsState : Set where
  constructor australian-guardrails-state
  field
    previousMandatoryGuardrailsProposalObserved : Bool
    mandatoryGuardrailsProceeding : Bool
    consultationFedNationalAIPlan : Bool
    enactedEquivalentObligationPaid : Bool
    realisedComplianceCostPaid : Bool
    concentrationEffectPaid : Bool
    intentionalCapturePaid : Bool

open AustralianGuardrailsState public

currentAustralianGuardrailsState : AustralianGuardrailsState
currentAustralianGuardrailsState = australian-guardrails-state
  true false true false false false false

mandatoryGuardrailsNotProceeding :
  mandatoryGuardrailsProceeding currentAustralianGuardrailsState ≡ false
mandatoryGuardrailsNotProceeding = refl

data ProposalCreatesOperativeBurdenPermission : Set where
data WithdrawalRefutesAllFutureRegulationPermission : Set where
data PolicyHistoryCreatesCapturePermission : Set where

proposalDoesNotCreateOperativeBurden : ProposalCreatesOperativeBurdenPermission → ⊥
proposalDoesNotCreateOperativeBurden ()

withdrawalDoesNotRefuteAllFutureRegulation : WithdrawalRefutesAllFutureRegulationPermission → ⊥
withdrawalDoesNotRefuteAllFutureRegulation ()

policyHistoryDoesNotCreateCapture : PolicyHistoryCreatesCapturePermission → ⊥
policyHistoryDoesNotCreateCapture ()

boundary : String
boundary =
  "Australia now supplies a useful negative/control policy observation: the Government says it will not proceed at this time with the earlier mandatory-guardrails proposals and that consultation instead informed the National AI Plan. The previous proposal therefore cannot be treated as an operative compliance burden. This does not prove the absence of future AI regulation, equivalent obligations elsewhere, realised actor-class costs, concentration effects or intentional regulatory capture. The policy lane must now track enacted/operative obligations before burden estimation."
