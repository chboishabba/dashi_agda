module DASHI.Philosophy.MentalHealthEvidenceAdapter where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.MentalHealthWorkedExample as Example
import DASHI.Promotion.SystemicDistressReframingBoundary as Distress
import DASHI.Biology.RelationalChartResidualMachine as Chart

------------------------------------------------------------------------
-- Candidate interpretation, evidence-supported interpretation, actionable
-- support, and clinical claim are distinct promotion levels.

data InterpretationLevel : Set where
  candidateInterpretation : InterpretationLevel
  evidenceSupportedInterpretation : InterpretationLevel
  actionableSupportPlan : InterpretationLevel
  clinicalClaim : InterpretationLevel

record EvidenceSupportedReading : Set₁ where
  field
    candidate : Example.MentalHealthCase
    protectedSignal : Distress.ProtectedSignalUse
    relationalChartReceipt : Chart.RelationalChartResidualMachine
    sourceReceipt : Set
    longitudinalEvidence : Set
    competingExplanationCheck : Set
    disconfirmationReview : Set
    uncertaintyRetained : Set

open EvidenceSupportedReading public

record SupportPlan : Set₁ where
  field
    reading : EvidenceSupportedReading
    proposedSupport : Example.CandidateSupport
    consent : Set
    safetyReview : Set
    accessibilityReview : Set
    rollbackOrRevision : Set
    clinicalAuthorityNotInferred : Set

open SupportPlan public

data ClinicalClaimPromotion : Set where

clinicalClaimNotDerivedFromSupportPlan :
  ClinicalClaimPromotion →
  Set
clinicalClaimNotDerivedFromSupportPlan ()

record MentalHealthPromotionBoundary : Set where
  constructor mentalHealthPromotionBoundary
  field
    candidateEqualsEvidenceSupported : Bool
    evidenceSupportedAutomaticallyActionable : Bool
    supportPlanAutomaticallyClinical : Bool
    firstPersonSignalRetained : Bool
    consentRequiredForAction : Bool
    diagnosisSeparatelyGoverned : Bool

open MentalHealthPromotionBoundary public

canonicalMentalHealthPromotionBoundary : MentalHealthPromotionBoundary
canonicalMentalHealthPromotionBoundary =
  mentalHealthPromotionBoundary
    false
    false
    false
    true
    true
    true

canonicalSupportDoesNotAutomaticallyPromoteClinicalClaim :
  supportPlanAutomaticallyClinical canonicalMentalHealthPromotionBoundary
  ≡ false
canonicalSupportDoesNotAutomaticallyPromoteClinicalClaim = refl

canonicalCandidateReading : Example.MentalHealthCase
canonicalCandidateReading = Example.canonicalMentalHealthCase

canonicalProtectedSignal : Distress.ProtectedSignalUse
canonicalProtectedSignal = Distress.sacredDataAsProtectedUse

canonicalChartReceipt : Chart.RelationalChartResidualMachine
canonicalChartReceipt = Chart.canonicalRelationalChartResidualMachine
