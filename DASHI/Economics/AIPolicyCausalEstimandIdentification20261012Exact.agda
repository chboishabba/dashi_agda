module DASHI.Economics.AIPolicyCausalEstimandIdentification20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalIdentificationFamiliesExact as Identification
import DASHI.Economics.AIPolicyCausalAdmission20261012Exact as Prior

------------------------------------------------------------------------
-- POLICY CAUSAL-ESTIMAND / IDENTIFICATION GATE
--
-- Productive cross-pollination from the repository's causal-identification
-- programme. Observed policy chronology, compliance-cost measurements and
-- market concentration observations are not enough to state a causal effect
-- until the exact intervention/comparator/outcome/population/horizon estimand
-- and an obligation-relative identification-family gate are both supplied.
------------------------------------------------------------------------

record IdentifiedPolicyCausalBridge : Set₂ where
  constructor identified-policy-causal-bridge
  field
    policyClaimReference : String
    estimand : Estimand.CausalEffectEstimand
    identificationFamily : Identification.CausalIdentificationFamily
    identificationGate : Identification.IdentificationEvidenceGate identificationFamily
    sameBasisComplianceCostPaid : Bool
    sameBasisComplianceCostPaidIsTrue : sameBasisComplianceCostPaid ≡ true
    marketResponsePaid : Bool
    marketResponsePaidIsTrue : marketResponsePaid ≡ true
    reviewedBridgeReference : String
    establishesIntentionalCapture : Bool

open IdentifiedPolicyCausalBridge public

record PolicyCausalIdentificationStatus : Set where
  constructor policy-causal-identification-status
  field
    observedPolicySubstratePaid : Bool
    realisedSameBasisCostsPaid : Bool
    marketResponsePaid : Bool
    currentPolicyEstimandPaid : Bool
    currentPolicyIdentificationPaid : Bool
    reviewedIdentifiedBridgePaid : Bool
    intentionalCapturePaid : Bool

open PolicyCausalIdentificationStatus public

currentAustralianPolicyCausalStatus : PolicyCausalIdentificationStatus
currentAustralianPolicyCausalStatus = policy-causal-identification-status
  true false false false false false false

observedPolicySubstrateStillPaid :
  observedPolicySubstratePaid currentAustralianPolicyCausalStatus ≡ true
observedPolicySubstrateStillPaid = refl

currentPolicyEstimandStillOpen :
  currentPolicyEstimandPaid currentAustralianPolicyCausalStatus ≡ false
currentPolicyEstimandStillOpen = refl

currentPolicyIdentificationStillOpen :
  currentPolicyIdentificationPaid currentAustralianPolicyCausalStatus ≡ false
currentPolicyIdentificationStillOpen = refl

currentIntentionalCaptureStillOpen :
  intentionalCapturePaid currentAustralianPolicyCausalStatus ≡ false
currentIntentionalCaptureStillOpen = refl

priorReviewedBridgeStillUninstantiated : Bool
priorReviewedBridgeStillUninstantiated = Prior.reviewedCausalBridgeStillOpen

data ObservedPolicyCreatesEstimandPermission : Set where
data CorrelationCreatesIdentificationPermission : Set where
data IdentificationCreatesIntentionalCapturePermission : Set where
data IdentificationFamilyDeterminesEstimandPermission : Set where

observedPolicyDoesNotCreateEstimand : ObservedPolicyCreatesEstimandPermission → ⊥
observedPolicyDoesNotCreateEstimand ()

correlationDoesNotCreateIdentification : CorrelationCreatesIdentificationPermission → ⊥
correlationDoesNotCreateIdentification ()

identificationDoesNotCreateIntentionalCapture : IdentificationCreatesIntentionalCapturePermission → ⊥
identificationDoesNotCreateIntentionalCapture ()

identificationFamilyDoesNotDetermineEstimand : IdentificationFamilyDeterminesEstimandPermission → ⊥
identificationFamilyDoesNotDetermineEstimand ()

boundary : String
boundary =
  "AI policy causal promotion now requires a typed CausalEffectEstimand and an obligation-relative IdentificationEvidenceGate in addition to realised same-basis compliance-cost and market-response measurements. The current Australian policy substrate pays chronology/proposal/outcome evidence only; it does not yet pay the estimand, identification gate, reviewed identified bridge or intentional-capture conclusion."
