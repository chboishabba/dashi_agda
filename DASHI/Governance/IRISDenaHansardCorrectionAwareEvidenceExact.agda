module DASHI.Governance.IRISDenaHansardCorrectionAwareEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.IRISDenaSenateEstimatesDutyNarrowingExact as Estimates

------------------------------------------------------------------------
-- IRIS DENA / HANSARD CORRECTION-AWARE PRIMARY RECORD
--
-- The parliamentary transcript schedule identifies the 3 June 2026 FADT
-- Estimates transcript as ref. 29619 and "Published in full".
-- The committee's Defence evidence page separately lists later Chief of Navy
-- correction letters for evidence given on 2-3 June 2026.
--
-- Therefore the primary object needed to promote a hearing proposition is not
-- merely a page citation.  It is the transcript plus any applicable correction.
------------------------------------------------------------------------

transcriptSchedule : Source.AttributedSource
transcriptSchedule = Source.mkNoDOISource
  "Parliament of Australia, Hansard"
  "Estimates Transcript Schedule: 3 June 2026 Foreign Affairs, Defence and Trade, ref. 29619"
  "Parliament of Australia"
  "2026"
  "https://www.aph.gov.au/Parliamentary_Business/Hansard/Estimates_Transcript_Schedule"
  Source.governmentSource
  "primary publication index: FADT 3 June 2026 transcript ref. 29619 is published in full; index does not by itself establish the content of pp. 49-52"
  Source.publicAttribution

defenceEvidencePage : Source.AttributedSource
defenceEvidencePage = Source.mkNoDOISource
  "Senate Foreign Affairs, Defence and Trade Legislation Committee"
  "2026-27 Budget Estimates: Defence, including Veterans' Affairs"
  "Parliament of Australia"
  "2026"
  "https://www.aph.gov.au/Parliamentary_Business/Senate_estimates/fadt/2026-27_Budget_estimates/Defence"
  Source.governmentSource
  "primary committee evidence index: later Chief of Navy letters correct evidence given at public hearings on 2-3 June 2026; the index does not reveal which propositions each letter changes"
  Source.publicAttribution

record HansardIdentityReceipt : Set where
  constructor hansard-identity-receipt
  field
    committeeRef : String
    hearingDate : String
    transcriptRefNo : String
    relevantPages : String
    transcriptPublishedInFull : Bool
    transcriptPublishedInFullIsTrue :
      transcriptPublishedInFull ≡ true
    relevantTopicLocated : Bool
    relevantTopicLocatedIsTrue :
      relevantTopicLocated ≡ true
    relevantPageContentReviewed : Bool
    relevantPageContentReviewedIsFalse :
      relevantPageContentReviewed ≡ false

open HansardIdentityReceipt public

canonicalHansardIdentity : HansardIdentityReceipt
canonicalHansardIdentity =
  hansard-identity-receipt
    "Foreign Affairs, Defence and Trade Legislation Committee"
    "2026-06-03"
    "29619"
    "proof Committee Hansard pp. 49-52"
    true refl
    true refl
    false refl

record CorrectionIndexReceipt : Set where
  constructor correction-index-receipt
  field
    witnessRef : String
    hearingDatesCovered : String
    firstCorrectionDate : String
    laterCorrectionDate : String
    correctionDocumentListed : Bool
    correctionDocumentListedIsTrue :
      correctionDocumentListed ≡ true
    correctionContentReviewed : Bool
    correctionContentReviewedIsFalse :
      correctionContentReviewed ≡ false
    correctionAffectsIRISDutyEvidence : Bool
    correctionAffectsIRISDutyEvidenceIsFalse :
      correctionAffectsIRISDutyEvidence ≡ false

open CorrectionIndexReceipt public

chiefOfNavyCorrectionIndex : CorrectionIndexReceipt
chiefOfNavyCorrectionIndex =
  correction-index-receipt
    "Vice Admiral Mark Hammond AO RAN, Chief of Navy"
    "public hearings on 2-3 June 2026"
    "2026-06-22"
    "2026-07-23"
    true refl
    false refl
    false refl

record CorrectionAwarePrimaryBundle : Set where
  constructor correction-aware-primary-bundle
  field
    hansard : HansardIdentityReceipt
    correctionIndex : CorrectionIndexReceipt
    secondaryDutyReceipt : Estimates.DutyNarrowingReceipt
    primaryTranscriptIdentityPaid : Bool
    primaryTranscriptIdentityPaidIsTrue :
      primaryTranscriptIdentityPaid ≡ true
    laterCorrectionExistencePaid : Bool
    laterCorrectionExistencePaidIsTrue :
      laterCorrectionExistencePaid ≡ true
    primaryDutyContentPaid : Bool
    primaryDutyContentPaidIsFalse :
      primaryDutyContentPaid ≡ false
    correctionApplicabilityPaid : Bool
    correctionApplicabilityPaidIsFalse :
      correctionApplicabilityPaid ≡ false
    secondarySummaryMayPromoteDutyClass : Bool
    secondarySummaryMayPromoteDutyClassIsFalse :
      secondarySummaryMayPromoteDutyClass ≡ false

open CorrectionAwarePrimaryBundle public

canonicalPrimaryBundle : CorrectionAwarePrimaryBundle
canonicalPrimaryBundle =
  correction-aware-primary-bundle
    canonicalHansardIdentity
    chiefOfNavyCorrectionIndex
    Estimates.senateDutyNarrowing
    true refl
    true refl
    false refl
    false refl
    false refl

record CorrectionAwareResidual : Set where
  constructor correction-aware-residual
  field
    residualRef : String
    requiredObject : String
    verificationRule : String
    mayIgnoreLaterCorrection : Bool
    mayIgnoreLaterCorrectionIsFalse :
      mayIgnoreLaterCorrection ≡ false

open CorrectionAwareResidual public

canonicalResidual : CorrectionAwareResidual
canonicalResidual =
  correction-aware-residual
    "residual:iris-dena:hansard-29619-plus-corrections"
    "FADT 3 June 2026 transcript ref. 29619 pp. 49-52 plus any Chief of Navy correction that applies to those propositions"
    "promote a duty-class proposition only from the correction-aware primary record, never from the publication index or partisan secondary summary alone"
    false refl

data TranscriptPublishedMeansDutyContentVerified : Set where
data CorrectionListedMeansCorrectionAppliesToIRIS : Set where
data LaterCorrectionMayBeIgnored : Set where
data SecondarySummaryMayOverridePrimaryRecord : Set where

publishedDoesNotVerifyDutyContent :
  TranscriptPublishedMeansDutyContentVerified → ⊥
publishedDoesNotVerifyDutyContent ()

listedCorrectionDoesNotProveIRISApplicability :
  CorrectionListedMeansCorrectionAppliesToIRIS → ⊥
listedCorrectionDoesNotProveIRISApplicability ()

laterCorrectionMayNotBeIgnored :
  LaterCorrectionMayBeIgnored → ⊥
laterCorrectionMayNotBeIgnored ()

secondarySummaryDoesNotOverridePrimary :
  SecondarySummaryMayOverridePrimaryRecord → ⊥
secondarySummaryDoesNotOverridePrimary ()

transcriptSnowball : Snowball.SourceRoleSnowballReceipt transcriptSchedule
transcriptSnowball = Snowball.canonicalSourceRoleSnowballReceipt transcriptSchedule

correctionIndexSnowball : Snowball.SourceRoleSnowballReceipt defenceEvidencePage
correctionIndexSnowball = Snowball.canonicalSourceRoleSnowballReceipt defenceEvidencePage
