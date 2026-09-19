module DASHI.Wikimedia.MaboResidualDrivenWorldExpansionStepExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboResidualDrivenWorldExpansionExact as Expansion

------------------------------------------------------------------------
-- ONE REVIEWED P7d WORLD-EXPANSION STEP
--
-- Thin runtime-parity boundary over the existing residual-driven expansion
-- owner. The step does not infer residual classes from labels, perform network
-- acquisition, or grant legal/semantic authority. It binds an explicitly
-- classified open residual to candidates carrying that exact residual identity,
-- then requires disambiguation + review before ledger admission.
------------------------------------------------------------------------

slrBranch : String
slrBranch = "agent/mabo-p7d-live-step-active"

slrRuntimeHead : String
slrRuntimeHead = "68dcab7407513c6277dab9d537714f7d47af8183"

record ReviewedExpansionStepBoundary : Set where
  constructor reviewedExpansionStepBoundary
  field
    explicitPNFWorldResidualClassificationRequired : Bool
    residualMustBeOpen : Bool
    candidateMustMatchExactResidual : Bool
    residualClassInferredFromIdentifierString : Bool
    acquisitionPerformedByStep : Bool
    explicitDisambiguationRequired : Bool
    explicitReviewRequired : Bool
    oneAdmissionCompletesHundredObjectTarget : Bool
    admissionCreatesSemanticAuthority : Bool
    admissionCreatesClaimTruth : Bool
open ReviewedExpansionStepBoundary public

canonicalReviewedExpansionStepBoundary : ReviewedExpansionStepBoundary
canonicalReviewedExpansionStepBoundary =
  reviewedExpansionStepBoundary
    true
    true
    true
    false
    false
    true
    true
    false
    false
    false

explicitPNFWorldResidualClassificationRequiredTrue :
  explicitPNFWorldResidualClassificationRequired canonicalReviewedExpansionStepBoundary ≡ true
explicitPNFWorldResidualClassificationRequiredTrue = refl

residualMustBeOpenTrue : residualMustBeOpen canonicalReviewedExpansionStepBoundary ≡ true
residualMustBeOpenTrue = refl

candidateMustMatchExactResidualTrue :
  candidateMustMatchExactResidual canonicalReviewedExpansionStepBoundary ≡ true
candidateMustMatchExactResidualTrue = refl

residualClassInferredFromIdentifierStringFalse :
  residualClassInferredFromIdentifierString canonicalReviewedExpansionStepBoundary ≡ false
residualClassInferredFromIdentifierStringFalse = refl

acquisitionPerformedByStepFalse :
  acquisitionPerformedByStep canonicalReviewedExpansionStepBoundary ≡ false
acquisitionPerformedByStepFalse = refl

explicitDisambiguationRequiredTrue :
  explicitDisambiguationRequired canonicalReviewedExpansionStepBoundary ≡ true
explicitDisambiguationRequiredTrue = refl

explicitReviewRequiredTrue :
  explicitReviewRequired canonicalReviewedExpansionStepBoundary ≡ true
explicitReviewRequiredTrue = refl

oneAdmissionCompletesHundredObjectTargetFalse :
  oneAdmissionCompletesHundredObjectTarget canonicalReviewedExpansionStepBoundary ≡ false
oneAdmissionCompletesHundredObjectTargetFalse = refl

admissionCreatesSemanticAuthorityFalse :
  admissionCreatesSemanticAuthority canonicalReviewedExpansionStepBoundary ≡ false
admissionCreatesSemanticAuthorityFalse = refl

admissionCreatesClaimTruthFalse :
  admissionCreatesClaimTruth canonicalReviewedExpansionStepBoundary ≡ false
admissionCreatesClaimTruthFalse = refl

------------------------------------------------------------------------
-- Reuse the existing 100-object target and residual-indexed routing semantics.
------------------------------------------------------------------------

targetNovelObjectsIsStill100 : Expansion.targetNovelObjects ≡ 100
targetNovelObjectsIsStill100 = Expansion.targetNovelObjectsIs100

legalResidualStillPrefersGovernedLegal :
  Expansion.preferredLane Expansion.legalResidual ≡ Expansion.governedLegal
legalResidualStillPrefersGovernedLegal = Expansion.legalLanePreferredForLegalResidual

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data IdentifierStringDeterminesResidualClass : Set where
data ClosedResidualMayScheduleExpansion : Set where
data DifferentResidualCandidateMayPayCurrentStep : Set where
data ReachabilityCreatesReviewedAdmission : Set where
data OneAdmissionEqualsHundredObjectCompletion : Set where
data ReviewedAdmissionCreatesLegalAuthority : Set where
data ReviewedAdmissionCreatesClaimTruth : Set where

identifierStringDoesNotDetermineResidualClass :
  IdentifierStringDeterminesResidualClass → ⊥
identifierStringDoesNotDetermineResidualClass ()

closedResidualCannotScheduleExpansion : ClosedResidualMayScheduleExpansion → ⊥
closedResidualCannotScheduleExpansion ()

differentResidualCandidateCannotPayCurrentStep :
  DifferentResidualCandidateMayPayCurrentStep → ⊥
differentResidualCandidateCannotPayCurrentStep ()

reachabilityDoesNotCreateReviewedAdmission :
  ReachabilityCreatesReviewedAdmission → ⊥
reachabilityDoesNotCreateReviewedAdmission ()

oneAdmissionDoesNotEqualHundredObjectCompletion :
  OneAdmissionEqualsHundredObjectCompletion → ⊥
oneAdmissionDoesNotEqualHundredObjectCompletion ()

reviewedAdmissionDoesNotCreateLegalAuthority :
  ReviewedAdmissionCreatesLegalAuthority → ⊥
reviewedAdmissionDoesNotCreateLegalAuthority ()

reviewedAdmissionDoesNotCreateClaimTruth :
  ReviewedAdmissionCreatesClaimTruth → ⊥
reviewedAdmissionDoesNotCreateClaimTruth ()

------------------------------------------------------------------------
-- Runtime interpretation
--
-- explicit PNF/world residual classification
-- -> exact open residual identity
-- -> existing residual-sensitive candidate selector
-- -> explicit disambiguation
-- -> explicit review
-- -> one candidate-only world admission receipt
-- -> recompute frontier outside this step
--
-- Provider acquisition remains separately governed; this owner does not turn
-- OALC/Wikidata/Wikipedia reachability into admission or authority.
------------------------------------------------------------------------
