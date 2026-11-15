module DASHI.Cognition.CCDCOEP3ClimateObservedActivityAndCorpusExact where

------------------------------------------------------------------------
-- CCDCOE P3: ACTUALLY DOCUMENTED COMMUNICATIONS, SEPARATE CAMPAIGNS,
-- PUBLISHED 187-DOCUMENT CONTENT ANALYSIS AND NONPROMOTION GATES.
--
-- Do NOT identify the independent campaigns below with an execution
-- of the specific April 1998 API draft. Media releases/ads and meeting
-- invitations have different epistemic content and time coordinates.
--
-- Scholarly aggregate metrics are published observations about coded
-- DOCUMENTS, not treatment effects on populations or campaign success.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Cognition.CCDCOEP3API1998PrimaryPlanExact as Draft

data SourceFamily : Set where
  ice1991 : SourceFamily
  gcc1995 : SourceFamily
  gccPrimer1996 : SourceFamily
  apiDraft1998 : SourceFamily
  coolerHeadsInvitation1998 : SourceFamily
  exxonCorpus2017 : SourceFamily

data EvidenceStage : Set where
  authoredDraft : EvidenceStage
  publishedCommunications : EvidenceStage
  archivedEditorialReview : EvidenceStage
  invitationIssued : EvidenceStage
  measuredDocumentContent : EvidenceStage

-- Evidence stages are an exact sample of historical source TYPES,
-- not a complete chronology or certificate of causal implementation.
sourceStage : SourceFamily → EvidenceStage
sourceStage ice1991 = publishedCommunications
sourceStage gcc1995 = publishedCommunications
sourceStage gccPrimer1996 = archivedEditorialReview
sourceStage apiDraft1998 = authoredDraft
sourceStage coolerHeadsInvitation1998 = invitationIssued
sourceStage exxonCorpus2017 = measuredDocumentContent

data GenericClimateLabel : Set where
  climateCommunication : GenericClimateLabel

unqualifiedLabel : SourceFamily → GenericClimateLabel
unqualifiedLabel _ = climateCommunication

draftAndAdvertisementNotSameEvidence :
  sourceStage apiDraft1998 ≡ sourceStage ice1991 → ⊥
draftAndAdvertisementNotSameEvidence ()

stageDoesNotFactorThroughGenericLabel :
  NF.FactorsThrough unqualifiedLabel sourceStage → ⊥
stageDoesNotFactorThroughGenericLabel =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      apiDraft1998 ice1991 refl draftAndAdvertisementNotSameEvidence)

evidenceStageBundle :
  Discriminator.ExperimentBundle SourceFamily
evidenceStageBundle =
  Discriminator.experimentBundle
    EvidenceStage
    sourceStage
    1
    "Inspect source dates, original medium and whether an action was public"
    "Bounded source-indexed archival evidence; not campaign-impact data"

stageSeparatesDraftFromPublicCommunication :
  Discriminator.BundleSeparates evidenceStageBundle
    apiDraft1998 ice1991
stageSeparatesDraftFromPublicCommunication =
  Discriminator.bundleSeparates draftAndAdvertisementNotSameEvidence

evidenceStageLanguageExtension :
  Discriminator.DiscriminatingLanguageExtension unqualifiedLabel
evidenceStageLanguageExtension =
  Discriminator.discriminatingLanguageExtension
    (Discriminator.currentObserverCollision
      apiDraft1998 ice1991 refl)
    evidenceStageBundle
    stageSeparatesDraftFromPublicCommunication

-- A dated invitation is proof of the event's ANNOUNCEMENT, not of
-- actual attendance or persuasion. This retains that sharp distinction.
data EventProofKind : Set where
  planProposed : EventProofKind
  publicationDocumented : EventProofKind
  invitationDocumented : EventProofKind
  actualAttendanceDocumented : EventProofKind
  measuredBeliefChange : EventProofKind

invitationKind : EventProofKind
invitationKind = invitationDocumented

data InvitationProvesAttendance : Set where
invitationDoesNotProveAttendance :
  InvitationProvesAttendance → ⊥
invitationDoesNotProveAttendance ()

-- Source: Supran and Oreskes (2017), Environmental Research Letters
-- 12 084019, DOI 10.1088/1748-9326/aa815f.
-- 187 coded communications. These numerals replicate the PUBLISHED
-- aggregate report only; the original coded microdata is not admitted.
record PublishedCorpusMeasurement : Set where
  constructor publishedCorpusMeasurement
  field
    sourceDOI : String
    corpusScope : String
    totalDocuments : Nat
    totalAdvertorials : Nat
    advertorialsTakingPosition : Nat
    advertorialAcknowledgementCount : Nat
    advertorialDoubtCount : Nat
    peerReviewedAcknowledgementPercent : Nat
    internalAcknowledgementPercent : Nat
    publicAdvertorialAcknowledgementPercent : Nat
    publicAdvertorialDoubtPercent : Nat
    isHumanTreatmentEffect : Bool

originalPublishedCorpusMeasurement : PublishedCorpusMeasurement
originalPublishedCorpusMeasurement =
  publishedCorpusMeasurement
    "10.1088/1748-9326/aa815f"
    "ExxonMobil internal/scientific/public communications, 1977–2014"
    187 36 26 3 21 83 80 12 81 false

publishedCorpusSize :
  PublishedCorpusMeasurement.totalDocuments
    originalPublishedCorpusMeasurement ≡ 187
publishedCorpusSize = refl

-- In the original AGW-real-and-human-caused category, 21 of 26
-- position-taking advertorials code as doubt, 3 of 26 as acknowledge.
-- The percentages 81 and 12 use that eligible subset; never pass
-- them off as 21/36 and 3/36 or as population percentages.
observedAdvertorialPositionSubset :
  PublishedCorpusMeasurement.advertorialsTakingPosition
    originalPublishedCorpusMeasurement ≡ 26
observedAdvertorialPositionSubset = refl

observedAdvertorialDoubtCount :
  PublishedCorpusMeasurement.advertorialDoubtCount
    originalPublishedCorpusMeasurement ≡ 21
observedAdvertorialDoubtCount = refl

publishedPeerAndPublicAcknowledgementsDistinct :
  PublishedCorpusMeasurement.peerReviewedAcknowledgementPercent
    originalPublishedCorpusMeasurement
  ≡ PublishedCorpusMeasurement.publicAdvertorialAcknowledgementPercent
    originalPublishedCorpusMeasurement → ⊥
publishedPeerAndPublicAcknowledgementsDistinct ()

documentContentIsNotPublicBeliefEffect :
  PublishedCorpusMeasurement.isHumanTreatmentEffect
    originalPublishedCorpusMeasurement ≡ false
documentContentIsNotPublicBeliefEffect = refl

-- An observed communication can be source-bounded even where its
-- specific effect is not identified. Keep this outcome type distinct.
data Question : Set where
  publishedOrExecutedMaterial : Question
  originating1998APIDraftExecuted : Question
  changedAudienceBeliefs : Question
  changedPolicyDecisions : Question

data EvidenceAnswer : Set where
  separatePublicMaterial : EvidenceAnswer
  originalDraftPresent : EvidenceAnswer
  unobserved : EvidenceAnswer

availableAnswer : Question → EvidenceAnswer
availableAnswer publishedOrExecutedMaterial = separatePublicMaterial
availableAnswer originating1998APIDraftExecuted = unobserved
availableAnswer changedAudienceBeliefs = unobserved
availableAnswer changedPolicyDecisions = unobserved

-- Never define observational equivalence across wholly different
-- campaigns as proof of one direct plan's authorisation or efficacy.

------------------------------------------------------------------------
-- VERSIONED 2020 ADDENDUM: not the original 2017 denominator.
-- Supran/Oreskes ERL 15 (2020) 119401, DOI 10.1088/1748-9326/ab89d5.
-- 1,448 gathered candidate adverts -> 267 not-irrelevant adverts;
-- 61 of the expanded advertorial sample express positions on AGW as
-- real and human-caused. These do NOT replace the 2017 original
-- 187-communication / 36-advertorial cohort or its 26 denominator.
------------------------------------------------------------------------

record ExpandedAddendumCohort : Set where
  constructor expandedAddendumCohort
  field
    sourceDOI : String
    retrievedCandidateDocuments : Nat
    notIrrelevantAdvertorials : Nat
    advertorialsTakingPosition : Nat
    isOriginal2017SamplingFrame : Bool

addendum2020Source : ExpandedAddendumCohort
addendum2020Source =
  expandedAddendumCohort
    "10.1088/1748-9326/ab89d5"
    1448
    267
    61
    false

expandedAdvertorialCandidateCount :
  ExpandedAddendumCohort.retrievedCandidateDocuments
    addendum2020Source ≡ 1448
expandedAdvertorialCandidateCount = refl

expandedAdvertorialRelevantCount :
  ExpandedAddendumCohort.notIrrelevantAdvertorials
    addendum2020Source ≡ 267
expandedAdvertorialRelevantCount = refl

expandedAdvertorialPositions :
  ExpandedAddendumCohort.advertorialsTakingPosition
    addendum2020Source ≡ 61
expandedAdvertorialPositions = refl

addendumCannotAutoReplaceOriginalFrame :
  ExpandedAddendumCohort.isOriginal2017SamplingFrame
    addendum2020Source ≡ false
addendumCannotAutoReplaceOriginalFrame = refl

-- Cross-year cohort inclusion, revised document identities and common
-- coding rules would need a source-level crosswalk not constructed
-- by copying the two published aggregate summaries.
