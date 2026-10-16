module DASHI.Cognition.ClinicToStreetsPromotionChainExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.ClinicToStreetsSourceReviewReuseExact as Review
import DASHI.Cognition.ClinicToStreetsEvidenceAcquisitionMaxCutExact as Acquisition
import DASHI.Cognition.ClinicToStreetsFormulationExperimentExact as Experiment
import DASHI.Cognition.ClinicToStreetsMultiArmImplementationExact as Implementation

------------------------------------------------------------------------
-- CLINIC PROMOTION CHAIN
--
-- Thin process adapter over already-owned source, causal-identification, review,
-- experiment and implementation layers.  It does not create a new evidence
-- theory or manufacture any currently unpaid receipt.
------------------------------------------------------------------------

data PromotionStage : Set where
  exactSourceManifestation : PromotionStage
  attributedProposition : PromotionStage
  explicitCausalEstimand : PromotionStage
  admissibleIdentification : PromotionStage
  exactHumanReview : PromotionStage
  decisionEffectMeasurement : PromotionStage
  implementationFidelityMeasurement : PromotionStage
  patientMaterialOutcomeMeasurement : PromotionStage

stages : List PromotionStage
stages =
  exactSourceManifestation ∷
  attributedProposition ∷
  explicitCausalEstimand ∷
  admissibleIdentification ∷
  exactHumanReview ∷
  decisionEffectMeasurement ∷
  implementationFidelityMeasurement ∷
  patientMaterialOutcomeMeasurement ∷ []

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

stageCount : Nat
stageCount = length stages

------------------------------------------------------------------------
-- Current payment status: preserve what is actually known.
------------------------------------------------------------------------

record StageStatus : Set where
  constructor stage-status
  field
    sourceManifestationPinned : Bool
    propositionAttributed : Bool
    estimandDeclared : Bool
    identificationPaid : Bool
    reviewPaid : Bool
    decisionEffectMeasured : Bool
    implementationFidelityMeasured : Bool
    patientMaterialOutcomeMeasured : Bool

open StageStatus public

currentFamilyActivationStatus : StageStatus
currentFamilyActivationStatus =
  stage-status
    false  -- transcript exists in conversation but no durable repo manifestation/hash is pinned
    true   -- transcript-facing proposition is explicitly attributed
    true   -- Clinic-specific causal edge demand is declared on canonical estimand spine
    false  -- no admissible identification receipt currently paid
    false  -- exact human review demand remains unpaid
    false  -- no decision-effect experiment run
    false  -- no implementation study run for this exact Clinic intervention
    false  -- no patient/material outcome study run

currentTherapyCounterinsurgencyStatus : StageStatus
currentTherapyCounterinsurgencyStatus =
  stage-status
    false
    true
    false  -- the slogan-level thesis is not silently converted into a canonical causal estimand
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Upstream owners remain explicit.
------------------------------------------------------------------------

sourceReviewBoundary : Review.ClinicSourceReviewBoundary
sourceReviewBoundary = Review.canonicalClinicSourceReviewBoundary

causalAcquisitionBoundary : Acquisition.FinalMaxCutBoundary
causalAcquisitionBoundary = Acquisition.canonicalFinalMaxCutBoundary

formulationExperiment : Experiment.FormulationExperimentSpec
formulationExperiment = Experiment.canonicalFormulationExperiment

implementationEscalationGate : Implementation.EscalationGate
implementationEscalationGate = Implementation.canonicalEscalationGate

------------------------------------------------------------------------
-- Promotion boundaries.  Each stage can constrain a downstream claim but none
-- substitutes for a different stage's payment.
------------------------------------------------------------------------

record PromotionChainBoundary : Set where
  constructor promotion-chain-boundary
  field
    exactSourceRequiredBeforeTextualIdentityClaim : Bool
    explicitEstimandRequiredBeforeCausalEffectClaim : Bool
    identificationRequiredBeforeCausalEffectClaim : Bool
    exactReviewRequiredWhenReviewedUseIsClaimed : Bool
    decisionMeasurementRequiredBeforeDecisionEffectClaim : Bool
    implementationMeasurementRequiredBeforeImplementationClaim : Bool
    patientOutcomeMeasurementRequiredBeforeOutcomeClaim : Bool

    sourceAttributionCreatesTruth : Bool
    sourceAttributionCreatesCausalIdentification : Bool
    humanReviewCreatesCausalIdentification : Bool
    humanReviewCreatesClaimTruth : Bool
    identificationCreatesPatientOutcomeBenefit : Bool
    decisionEffectCreatesImplementationSuccess : Bool
    implementationFidelityCreatesPatientOutcomeBenefit : Bool
    implementationEffectCreatesInstitutionalIntent : Bool
    patientOutcomeEffectCreatesCounterinsurgencyFinding : Bool

open PromotionChainBoundary public

canonicalPromotionChainBoundary : PromotionChainBoundary
canonicalPromotionChainBoundary =
  promotion-chain-boundary
    true true true true true true true
    false false false false false false false false false

------------------------------------------------------------------------
-- Explicit non-substitution witnesses.
------------------------------------------------------------------------

data AttributionProvesTruth : Set where
data ReviewProvesIdentification : Set where
data IdentificationProvesOutcome : Set where
data ImplementationProvesIntent : Set where
data PatientOutcomeProvesCounterinsurgency : Set where

attributionDoesNotProveTruth : AttributionProvesTruth → ⊥
attributionDoesNotProveTruth ()

reviewDoesNotProveIdentification : ReviewProvesIdentification → ⊥
reviewDoesNotProveIdentification ()

identificationDoesNotProveOutcome : IdentificationProvesOutcome → ⊥
identificationDoesNotProveOutcome ()

implementationDoesNotProveIntent : ImplementationProvesIntent → ⊥
implementationDoesNotProveIntent ()

patientOutcomeDoesNotProveCounterinsurgency : PatientOutcomeProvesCounterinsurgency → ⊥
patientOutcomeDoesNotProveCounterinsurgency ()
