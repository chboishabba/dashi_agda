module DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawSubmittedEvidencePackageWrongTypeExact as Package

------------------------------------------------------------------------
-- LONGITUDINAL HOUSING / DISPLACEMENT EVIDENCE LINEAGE
--
-- Separate tenancy disputes may be ordered into one longitudinal history when
-- their source carriers and occupant continuity are known.  Episode continuity
-- is observational/provenance structure only: it does not merge defendants,
-- legal duties, breaches, harms, causation questions, or remedies.
------------------------------------------------------------------------

data HousingProcessState : Set where
  tenancyDisputeProcess : HousingProcessState
  noticeToLeaveProcess : HousingProcessState
  qcatProceedingProcess : HousingProcessState
  tenancyExitProcess : HousingProcessState
  possessionOrEvictionOrderProcess : HousingProcessState
  housingProcessUnresolved : HousingProcessState


data EpisodeSourceRole : Set where
  primaryTenancyCarrier : EpisodeSourceRole
  primaryNoticeCarrier : EpisodeSourceRole
  primaryTribunalCarrier : EpisodeSourceRole
  primaryHealthCarrier : EpisodeSourceRole
  contemporaneousCommunicationCarrier : EpisodeSourceRole
  retrospectiveTimelineCarrier : EpisodeSourceRole

record EpisodeSource : Set₁ where
  constructor episodeSource
  field
    sourceRole : EpisodeSourceRole
    carrierReference : String
    sourceReference : String
    sourceReceipt : Set

open EpisodeSource public

record HousingEpisode : Set₁ where
  constructor housingEpisode
  field
    episodeReference : String
    premisesReference : String
    periodReference : String
    occupantReferences : List String
    processStates : List HousingProcessState
    sources : List EpisodeSource
    healthContextReferences : List String
    episodeReceipt : Set

open HousingEpisode public

record LongitudinalHousingSequence : Set₁ where
  constructor longitudinalHousingSequence
  field
    sequenceReference : String
    episodes : List HousingEpisode
    occupantContinuityReference : String
    chronologicalOrderReference : String
    occupantContinuityReceipt : Set
    chronologicalOrderReceipt : Set

open LongitudinalHousingSequence public

------------------------------------------------------------------------
-- Authority boundaries across episodes.
------------------------------------------------------------------------

record HousingEpisodeLineageBoundary : Set where
  constructor housingEpisodeLineageBoundary
  field
    sameOccupantsMeansSameLegalCause : Bool
    sameOccupantsMeansSameLegalCauseIsFalse :
      sameOccupantsMeansSameLegalCause ≡ false

    repeatedNoticeProcessesProveSystemicWrongdoing : Bool
    repeatedNoticeProcessesProveSystemicWrongdoingIsFalse :
      repeatedNoticeProcessesProveSystemicWrongdoing ≡ false

    repeatedHealthContextsProveCumulativeMedicalCausation : Bool
    repeatedHealthContextsProveCumulativeMedicalCausationIsFalse :
      repeatedHealthContextsProveCumulativeMedicalCausation ≡ false

    laterEpisodeRewritesEarlierSubmittedCarrier : Bool
    laterEpisodeRewritesEarlierSubmittedCarrierIsFalse :
      laterEpisodeRewritesEarlierSubmittedCarrier ≡ false

    retrospectiveTimelineMayReplacePrimaryCarrier : Bool
    retrospectiveTimelineMayReplacePrimaryCarrierIsFalse :
      retrospectiveTimelineMayReplacePrimaryCarrier ≡ false

    noticeToLeaveAutomaticallyEqualsEvictionOrder : Bool
    noticeToLeaveAutomaticallyEqualsEvictionOrderIsFalse :
      noticeToLeaveAutomaticallyEqualsEvictionOrder ≡ false

canonicalHousingEpisodeLineageBoundary : HousingEpisodeLineageBoundary
canonicalHousingEpisodeLineageBoundary =
  housingEpisodeLineageBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameOccupantsAutomaticallySameLegalCause : Set where
data RepeatedNoticesAutomaticallySystemicWrongdoing : Set where
data RepeatedHealthContextAutomaticallyCumulativeCausation : Set where
data LaterEpisodeAutomaticallyRewritesEarlierCarrier : Set where
data RetrospectiveTimelineAutomaticallyPrimaryEvidence : Set where
data NoticeToLeaveAutomaticallyEvictionOrder : Set where

sameOccupantsDoNotIdentifyLegalCause :
  SameOccupantsAutomaticallySameLegalCause → ⊥
sameOccupantsDoNotIdentifyLegalCause ()

repeatedNoticesDoNotAutoProveSystemicWrongdoing :
  RepeatedNoticesAutomaticallySystemicWrongdoing → ⊥
repeatedNoticesDoNotAutoProveSystemicWrongdoing ()

repeatedHealthContextDoesNotAutoProveCumulativeCausation :
  RepeatedHealthContextAutomaticallyCumulativeCausation → ⊥
repeatedHealthContextDoesNotAutoProveCumulativeCausation ()

laterEpisodeDoesNotRewriteEarlierCarrier :
  LaterEpisodeAutomaticallyRewritesEarlierCarrier → ⊥
laterEpisodeDoesNotRewriteEarlierCarrier ()

retrospectiveTimelineDoesNotReplacePrimaryEvidence :
  RetrospectiveTimelineAutomaticallyPrimaryEvidence → ⊥
retrospectiveTimelineDoesNotReplacePrimaryEvidence ()

noticeToLeaveDoesNotAutomaticallyEqualEvictionOrder :
  NoticeToLeaveAutomaticallyEvictionOrder → ⊥
noticeToLeaveDoesNotAutomaticallyEqualEvictionOrder ()

------------------------------------------------------------------------
-- Bounded source-backed fixtures.
--
-- Herries/Russell is the already-closed May 2022 submitted package.
-- Brighton is source-backed here at notice/remedy + health-context + exit
-- carrier level; a final QCAT possession/eviction order is not asserted.
-- Chapel Hill is source-backed at Form-12 + later QCAT/housing proceeding
-- chronology level; a particular termination/warrant receipt remains separate.
------------------------------------------------------------------------

herriesEpisode : (episodeReceipt : Set) → HousingEpisode
herriesEpisode episodeReceipt =
  housingEpisode
    "Herries Street / Russell-Caton QCAT 0096/22"
    "Herries Street tenancy"
    "2022"
    ("John Brown" ∷ "Johl Brown" ∷ [])
    (tenancyDisputeProcess ∷ qcatProceedingProcess ∷ tenancyExitProcess ∷ [])
    (episodeSource
       primaryTribunalCarrier
       Package.qcat0096PackageReference
       "final 83-page May 2022 QCAT submitted package"
       episodeReceipt ∷ [])
    ("submitted stress/injury narrative" ∷
     "submitted hypertension assertion" ∷
     "submitted physiological charts/tables" ∷ [])
    episodeReceipt

brightonEpisode :
  (form11Receipt : Set) →
  (exitReportReceipt : Set) →
  HousingEpisode
brightonEpisode form11Receipt exitReportReceipt =
  housingEpisode
    "17 Gordon Street Brighton tenancy displacement episode"
    "17 Gordon Street, Brighton QLD 4017"
    "2022-2023"
    ("John Brown" ∷ "Johl Brown" ∷ [])
    (tenancyDisputeProcess ∷ noticeToLeaveProcess ∷ tenancyExitProcess ∷ [])
    (episodeSource
       primaryNoticeCarrier
       "RTA Form 11.pdf"
       "24 January 2023 Brighton remedy/notice context"
       form11Receipt ∷
     episodeSource
       primaryTenancyCarrier
       "Entry and Exit Inspection report (15).pdf"
       "6 June 2023 Brighton exit carrier"
       exitReportReceipt ∷ [])
    ("Form 11 asserts multiple hospitalisations" ∷
     "Form 11 asserts continued breathing impairment" ∷
     "Form 11 links unresolved mould/roof repair context" ∷ [])
    form11Receipt

chapelHillEpisode :
  (form12Receipt : Set) →
  (qcatHousingReceipt : Set) →
  HousingEpisode
chapelHillEpisode form12Receipt qcatHousingReceipt =
  housingEpisode
    "50 Tucker Street Chapel Hill housing/QCAT episode"
    "50 Tucker Street, Chapel Hill QLD 4069"
    "2023-2025"
    ("John Brown" ∷ "Johl Brown" ∷ [])
    (tenancyDisputeProcess ∷ noticeToLeaveProcess ∷ qcatProceedingProcess ∷ [])
    (episodeSource
       primaryNoticeCarrier
       "50 Tucker St - Notice to Leave[86].pdf"
       "Form 12 issued 3 June 2024 with stated 5 August 2024 vacate date"
       form12Receipt ∷
     episodeSource
       primaryTribunalCarrier
       "QCAT Housing"
       "later Chapel Hill notice/remedy/QCAT proceeding chronology"
       qcatHousingReceipt ∷ [])
    ("housing record contains health/care context" ∷
     "health context remains episode-specific" ∷ [])
    form12Receipt

herriesBrightonChapelHillSequence :
  (herriesReceipt : Set) →
  (brightonForm11Receipt : Set) →
  (brightonExitReceipt : Set) →
  (chapelHillForm12Receipt : Set) →
  (chapelHillQCATReceipt : Set) →
  (continuityReceipt : Set) →
  (orderReceipt : Set) →
  LongitudinalHousingSequence
herriesBrightonChapelHillSequence
  herriesReceipt
  brightonForm11Receipt
  brightonExitReceipt
  chapelHillForm12Receipt
  chapelHillQCATReceipt
  continuityReceipt
  orderReceipt =
  longitudinalHousingSequence
    "Herries -> Brighton -> Chapel Hill housing sequence"
    (herriesEpisode herriesReceipt ∷
     brightonEpisode brightonForm11Receipt brightonExitReceipt ∷
     chapelHillEpisode chapelHillForm12Receipt chapelHillQCATReceipt ∷ [])
    "John/Johl occupant continuity across three separately sourced tenancy episodes"
    "Herries 2022 precedes Brighton 2022-2023 precedes Chapel Hill 2023-2025"
    continuityReceipt
    orderReceipt
