module DASHI.Law.SensibLawBrightonPremisesConditionEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- BRIGHTON PREMISES-CONDITION EVIDENCE
--
-- Public typed summary of a private matter corpus reviewed outside the repo.
-- Raw emails, message ids, health detail and private attachments are not copied
-- here.  This owner records only bounded source roles and the legal promotion
-- boundary needed by the Brighton s 185 consumer.
--
-- The private corpus contains mutually reinforcing contemporaneous carriers:
--   * dated surface-condition photographs;
--   * property-manager acknowledgement of a recurring condition problem;
--   * property-manager quote/work-order activity;
--   * an agent-issued Form 12 selecting non-liveability;
--   * contemporaneous property-manager explanation of that non-liveability
--     notice after discussion with a mould company;
--   * later professional inspection-occurrence correspondence.
--
-- These carriers are sufficient here only for the narrow factual coordinate:
-- a material premises-condition problem/non-liveability concern was recognized
-- by the managing agent by 24 January 2023.  They do not by themselves decide
-- the distinct statutory question whether s 185 was violated.
------------------------------------------------------------------------

data BrightonConditionSourceRole : Set where
  datedPhotoCarrier : BrightonConditionSourceRole
  propertyManagerAcknowledgementCarrier : BrightonConditionSourceRole
  maintenanceActionCarrier : BrightonConditionSourceRole
  agentNonLiveabilityNoticeCarrier : BrightonConditionSourceRole
  professionalInspectionOccurrenceCarrier : BrightonConditionSourceRole

record BrightonConditionSourceReceipt : Set where
  constructor brighton-condition-source-receipt
  field
    role : BrightonConditionSourceRole
    sourceDateReference : String
    privateCarrierVerified : Bool
    privateCarrierVerifiedIsTrue : privateCarrierVerified ≡ true
    boundedObservation : String
    sourceReceiptReference : String
open BrightonConditionSourceReceipt public

record BrightonPremisesConditionEvidenceBundle : Set where
  constructor brighton-premises-condition-evidence-bundle
  field
    sourceReceipts : List BrightonConditionSourceReceipt
    photographsReviewed : Bool
    photographsReviewedIsTrue : photographsReviewed ≡ true
    agentAcknowledgementReviewed : Bool
    agentAcknowledgementReviewedIsTrue : agentAcknowledgementReviewed ≡ true
    nonLiveabilityNoticeReviewed : Bool
    nonLiveabilityNoticeReviewedIsTrue : nonLiveabilityNoticeReviewed ≡ true
    noticeIssued24Jan2023 : Bool
    noticeIssued24Jan2023IsTrue : noticeIssued24Jan2023 ≡ true
    narrowConditionCoordinatePaid : Bool
    narrowConditionCoordinatePaidIsTrue : narrowConditionCoordinatePaid ≡ true
    statutoryMaintenanceFailurePaid : Bool
    statutoryMaintenanceFailurePaidIsFalse : statutoryMaintenanceFailurePaid ≡ false
    section185ViolationPaid : Bool
    section185ViolationPaidIsFalse : section185ViolationPaid ≡ false
    evidenceBundleReference : String
open BrightonPremisesConditionEvidenceBundle public

canonicalBrightonPremisesConditionEvidenceBundle : BrightonPremisesConditionEvidenceBundle
canonicalBrightonPremisesConditionEvidenceBundle =
  brighton-premises-condition-evidence-bundle
    (brighton-condition-source-receipt
       datedPhotoCarrier
       "2022-12-02"
       true refl
       "dated photographs visually record widespread dark spotting/staining on painted surfaces; image review does not independently diagnose species or cause"
       "private Brighton dated-photo carrier reviewed" ∷
     brighton-condition-source-receipt
       propertyManagerAcknowledgementCarrier
       "2022-11-25 to 2023-01-24"
       true refl
       "property-manager correspondence acknowledges a recurring condition problem and, by 24-Jan-2023, describes the returned condition as a larger issue requiring extensive attention"
       "private Brighton property-manager acknowledgement carrier reviewed" ∷
     brighton-condition-source-receipt
       maintenanceActionCarrier
       "2022-12 to 2023-01"
       true refl
       "property-manager correspondence records quote/work-order activity directed to the condition problem"
       "private Brighton maintenance-action carrier reviewed" ∷
     brighton-condition-source-receipt
       agentNonLiveabilityNoticeCarrier
       "2023-01-24"
       true refl
       "agent-issued Form 12 selects non-liveability and the contemporaneous agent explanation ties that notice to the recurring condition problem after discussion with a mould company"
       "private Brighton non-liveability notice carrier reviewed" ∷
     brighton-condition-source-receipt
       professionalInspectionOccurrenceCarrier
       "2023-02"
       true refl
       "professional correspondence confirms an inspection occurred on behalf of the managing agent; report contents remain unavailable"
       "private Brighton inspection-occurrence carrier reviewed" ∷ [])
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Brighton premises-condition evidence bundle v1"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data VisualSpottingAutomaticallyDiagnosesMouldSpecies : Set where
data AgentNonLiveabilityNoticeAutomaticallyProvesS185Violation : Set where
data RepairWorkOrderAutomaticallyProvesFailureToRepair : Set where
data InspectionOccurrenceAutomaticallyImportsReportFindings : Set where
data ConditionCoordinateAutomaticallyProvesMedicalCausation : Set where

visualSpottingDoesNotDiagnoseSpecies :
  VisualSpottingAutomaticallyDiagnosesMouldSpecies → ⊥
visualSpottingDoesNotDiagnoseSpecies ()

nonLiveabilityNoticeDoesNotAutoProveS185Violation :
  AgentNonLiveabilityNoticeAutomaticallyProvesS185Violation → ⊥
nonLiveabilityNoticeDoesNotAutoProveS185Violation ()

workOrderDoesNotAutoProveFailureToRepair :
  RepairWorkOrderAutomaticallyProvesFailureToRepair → ⊥
workOrderDoesNotAutoProveFailureToRepair ()

inspectionOccurrenceDoesNotImportReportFindings :
  InspectionOccurrenceAutomaticallyImportsReportFindings → ⊥
inspectionOccurrenceDoesNotImportReportFindings ()

conditionCoordinateDoesNotProveMedicalCausation :
  ConditionCoordinateAutomaticallyProvesMedicalCausation → ⊥
conditionCoordinateDoesNotProveMedicalCausation ()

record BrightonPremisesConditionEvidenceBoundary : Set where
  constructor brighton-premises-condition-evidence-boundary
  field
    privateRawCorpusExcluded : Bool
    datedPhotosUsedAsVisualConditionEvidence : Bool
    agentAcknowledgementRequired : Bool
    nonLiveabilityNoticeRequired : Bool
    narrowConditionCoordinatePaid : Bool
    statutoryMaintenanceFailurePaid : Bool
    section185ViolationPaid : Bool
    imageReviewDiagnosesMouldSpecies : Bool
    inspectionOccurrenceImportsReportFindings : Bool
    conditionCoordinateCreatesMedicalCausation : Bool

canonicalBrightonPremisesConditionEvidenceBoundary :
  BrightonPremisesConditionEvidenceBoundary
canonicalBrightonPremisesConditionEvidenceBoundary =
  brighton-premises-condition-evidence-boundary
    true true true true true false false false false false
