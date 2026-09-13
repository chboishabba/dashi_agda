module DASHI.Culture.LinguisticAnthropologyTlureyPragmaticsBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Philosophy.RelationalProtocol as Tlurey
import DASHI.Culture.LanguageUseGovernedStandingBidiExact as GovernedLanguage
import DASHI.Culture.AnthropologyEthnographicFieldworkReceiptExact as Ethnography

------------------------------------------------------------------------
-- LINGUISTIC ANTHROPOLOGY x TLUREY PRAGMATICS BRIDGE
--
-- Source anchors:
-- * Dell Hymes, "Introduction: Toward Ethnographies of Communication",
--   American Anthropologist 66 (1964).
--   DOI: 10.1525/aa.1964.66.suppl_3.02a00010
-- * Alessandro Duranti, Linguistic Anthropology (1997/2012).
--   DOI: 10.1017/CBO9780511810190
-- * Alessandro Duranti, "Linguistic anthropology: the study of language as
--   a non-neutral medium", Cambridge Handbook of Sociolinguistics (2011).
--   DOI: 10.1017/CBO9780511997068.006
-- * Alessandro Duranti, "Speaking as social action".
--   DOI: 10.1017/CBO9780511810190.008
--
-- Reuse boundary:
-- Tlurey already supplies a trust/care/history/repair-indexed relation carrier.
-- GovernedLanguage already proves that the same words/use surface cannot recover
-- standing, permission or interpretive obligation.  Linguistic anthropology
-- supplies the empirical/source discipline explaining why speaking must be
-- studied as situated social/cultural practice.  None of these collapses into
-- the others.
------------------------------------------------------------------------

record LinguisticAnthropologySource : Set where
  constructor linguistic-anthropology-source
  field
    author : String
    title : String
    sourceId : String
    sourceRole : String
open LinguisticAnthropologySource public

hymesEthnographyOfCommunication : LinguisticAnthropologySource
hymesEthnographyOfCommunication =
  linguistic-anthropology-source
    "Dell Hymes"
    "Introduction: Toward Ethnographies of Communication"
    "doi:10.1525/aa.1964.66.suppl_3.02a00010"
    "method/source anchor for ethnographic study of communicative events"

durantiLinguisticAnthropology : LinguisticAnthropologySource
durantiLinguisticAnthropology =
  linguistic-anthropology-source
    "Alessandro Duranti"
    "Linguistic Anthropology"
    "doi:10.1017/CBO9780511810190"
    "discipline/source anchor: language as cultural resource and speaking as cultural practice"

durantiNonNeutralMedium : LinguisticAnthropologySource
durantiNonNeutralMedium =
  linguistic-anthropology-source
    "Alessandro Duranti"
    "Linguistic anthropology: the study of language as a non-neutral medium"
    "doi:10.1017/CBO9780511997068.006"
    "source anchor for language as representation, social organization and differentiation"

durantiSpeakingAsSocialAction : LinguisticAnthropologySource
durantiSpeakingAsSocialAction =
  linguistic-anthropology-source
    "Alessandro Duranti"
    "Speaking as social action"
    "doi:10.1017/CBO9780511810190.008"
    "source anchor for context/indexicality and speaking as socially constitutive action"

------------------------------------------------------------------------
-- A speech event is not reducible to its token string.
------------------------------------------------------------------------

record SituatedSpeechEvent : Set where
  constructor situated-speech-event
  field
    words : String
    speaker : String
    participants : String
    communityOrField : String
    place : String
    time : String
    activity : String
    localTerms : String
    relationHistory : String
    speakerStanding : String
    disclosurePermission : String
    interpretiveObligation : String
    interactionalEffect : String
    sourceProvenance : String
open SituatedSpeechEvent public

record LinguisticAnthropologyAdmission : Set where
  constructor linguistic-anthropology-admission
  field
    event : SituatedSpeechEvent
    ethnographicContextBound : Bool
    speechCommunityOrFieldBound : Bool
    participantRolesBound : Bool
    localLanguageUseBound : Bool
    standingPermissionObligationBound : Bool
    sourceProvenanceBound : Bool
    empiricalPromotionAllowed : Bool
open LinguisticAnthropologyAdmission public

------------------------------------------------------------------------
-- Tlurey is useful here as formal substrate only.
------------------------------------------------------------------------

record TlureyLinguisticAnthropologyWeld : Set₁ where
  constructor tlurey-linguistic-anthropology-weld
  field
    tlureyRelationCarrierReusable : Bool
    governedLanguageCarrierReusable : Bool
    ethnographicReceiptCarrierReusable : Bool
    hymesSourceBound : Bool
    durantiSourceBound : Bool
    sameWordsDoNotDetermineSocialRelation : Bool
    trustHistoryCareAreContextCoordinates : Bool
    tlureyDeterminesCommunityMeaning : Bool
    tlureyDeterminesEmpiricalLanguageUse : Bool
    linguisticAnthropologyBridgePaid : Bool
    concreteSpeechCommunityProducerPaid : Bool
open TlureyLinguisticAnthropologyWeld public

canonicalTlureyLinguisticAnthropologyWeld : TlureyLinguisticAnthropologyWeld
canonicalTlureyLinguisticAnthropologyWeld =
  tlurey-linguistic-anthropology-weld
    true true true true true true true false false true false

------------------------------------------------------------------------
-- Remaining producer frontier.
------------------------------------------------------------------------

record LinguisticAnthropologyProducerFrontier : Set where
  constructor linguistic-anthropology-producer-frontier
  field
    disciplineSourceLanePaid : Bool
    formalContextBridgePaid : Bool
    speechEventReceiptShapePaid : Bool
    concreteCommunityCorpusPaid : Bool
    concreteFieldworkReceiptPaid : Bool
    languageSpecificAnalysisPaid : Bool
    architectureStillMissing : Bool
open LinguisticAnthropologyProducerFrontier public

currentLinguisticAnthropologyFrontier : LinguisticAnthropologyProducerFrontier
currentLinguisticAnthropologyFrontier =
  linguistic-anthropology-producer-frontier
    true true true false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TlureyCreatesCommunitySemantics : Set where
data SharedHistoryCreatesSharedMeaning : Set where
data SameWordsCreateSameSocialAct : Set where
data LinguisticTheoryCreatesEthnographicObservation : Set where
data SourceBookCreatesCommunityEvidence : Set where

tlureyDoesNotCreateCommunitySemantics : TlureyCreatesCommunitySemantics → ⊥
tlureyDoesNotCreateCommunitySemantics ()

sharedHistoryDoesNotCreateSharedMeaning : SharedHistoryCreatesSharedMeaning → ⊥
sharedHistoryDoesNotCreateSharedMeaning ()

sameWordsDoNotCreateSameSocialAct : SameWordsCreateSameSocialAct → ⊥
sameWordsDoNotCreateSameSocialAct ()

linguisticTheoryIsNotEthnographicObservation : LinguisticTheoryCreatesEthnographicObservation → ⊥
linguisticTheoryIsNotEthnographicObservation ()

sourceBookIsNotCommunityEvidence : SourceBookCreatesCommunityEvidence → ⊥
sourceBookIsNotCommunityEvidence ()

record LinguisticAnthropologyTlureyBoundary : Set where
  constructor linguistic-anthropology-tlurey-boundary
  field
    sourceTraditionsRetained : Bool
    tlureyReusedNotPromoted : Bool
    governedStandingRetained : Bool
    contextAndWordsSeparated : Bool
    empiricalCommunityReceiptStillRequired : Bool
    formalRelationCreatesEmpiricalMeaning : Bool
open LinguisticAnthropologyTlureyBoundary public

canonicalLinguisticAnthropologyTlureyBoundary : LinguisticAnthropologyTlureyBoundary
canonicalLinguisticAnthropologyTlureyBoundary =
  linguistic-anthropology-tlurey-boundary true true true true true false
