module DASHI.Law.TasmanianColonialPrimaryArchiveAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawTasmanianColonialGenocideSourceBoundaryExact as Genocide

------------------------------------------------------------------------
-- TASMANIAN COLONIAL PRIMARY-ARCHIVE ACQUISITION FRONTIER
--
-- This owner upgrades generic "primary archives needed" debt into exact
-- repository/series/file locators exposed by Libraries Tasmania.  Locator and
-- catalogue custody are not page-level replay, interpretation, genocide proof,
-- actor-intent proof, or exhaustive archive coverage.
------------------------------------------------------------------------

librariesTasmaniaAboriginalRecordsGuide : Source.AttributedSource
librariesTasmaniaAboriginalRecordsGuide = Source.mkNoDOISource
  "Libraries Tasmania — State Library and Archives of Tasmania"
  "Tasmanian Aboriginal people — What else is available?"
  "Libraries Tasmania guides to records"
  "current guide surface searched 2026-09-14"
  "https://libraries.tas.gov.au/slat/guides-to-records/tasmanian-aboriginal-people/what-else-is-available/"
  Source.institutionalSource
  "Authoritative archive-guide locator for Governor Arthur-era Aboriginal records, including Colonial Secretary file 7578, CSO1 indexes and a copy of Arthur's 1830 campaign itinerary. The guide identifies holdings but does not itself pay the contents of every underlying page."
  Source.publicAttribution

librariesTasmaniaAboriginalIntroduction : Source.AttributedSource
librariesTasmaniaAboriginalIntroduction = Source.mkNoDOISource
  "Libraries Tasmania — State Library and Archives of Tasmania"
  "Tasmanian Aboriginal people — Introduction"
  "Libraries Tasmania guides to records"
  "current guide surface searched 2026-09-14"
  "https://libraries.tas.gov.au/slat/guides-to-records/tasmanian-aboriginal-people/introduction/"
  Source.institutionalSource
  "Authoritative archive-guide locator for online Aboriginal-related records, including 1830-1833 Committee for the Care and Treatment of Captured Aborigines minutes (CBE1). Catalogue exposure does not by itself establish what each minute proves."
  Source.publicAttribution

librariesTasmaniaColonialAdministrationGuide : Source.AttributedSource
librariesTasmaniaColonialAdministrationGuide = Source.mkNoDOISource
  "Libraries Tasmania — State Library and Archives of Tasmania"
  "Early colonial administration records — What is online?"
  "Libraries Tasmania guides to records"
  "current guide surface searched 2026-09-14"
  "https://libraries.tas.gov.au/slat/guides-to-records/early-colonial-administration-records/what-is-online/"
  Source.institutionalSource
  "Authoritative archive-guide locator for Governor's Office and Colonial Secretary records, including GO1, GO2 and GO33 despatch series. Series identity is an acquisition coordinate, not a claim that every relevant item has been inspected."
  Source.publicAttribution

tasmanianPrimaryArchiveAcquisitionSources : List Source.AttributedSource
tasmanianPrimaryArchiveAcquisitionSources =
  librariesTasmaniaAboriginalRecordsGuide ∷
  librariesTasmaniaAboriginalIntroduction ∷
  librariesTasmaniaColonialAdministrationGuide ∷
  []

tasmanianPrimaryArchiveAcquisitionAtlas : Source.AttributedSourceAtlas
tasmanianPrimaryArchiveAcquisitionAtlas = Source.mkSourceAtlas
  "Tasmanian colonial primary-archive acquisition atlas"
  "DASHI.Law.TasmanianColonialPrimaryArchiveAcquisitionExact"
  tasmanianPrimaryArchiveAcquisitionSources
  "Exact archive-guide and series/file locators for the colonial Tasmania lane. Locator custody, digitisation, page replay, interpretation and downstream historical conclusions remain distinct payment coordinates."

parentGenocideSourceBoundary : Genocide.TasmanianColonialGenocideBoundary
parentGenocideSourceBoundary = Genocide.canonicalTasmanianColonialGenocideBoundary

record TasmanianPrimaryArchiveAcquisitionBoundary : Set where
  constructor tasmanianPrimaryArchiveAcquisitionBoundary
  field
    parentGenocideSourceBoundaryReused : Bool
    governorArthurAboriginalFile7578Located : Bool
    arthur1830CampaignItineraryLocated : Bool
    capturedAboriginesCommitteeMinutesLocated : Bool
    colonialDespatchSeriesLocated : Bool
    primaryArchivePageLevelReplayPaid : Bool
    archiveLocatorAutomaticallyPaysHistoricalClaim : Bool
    archiveGuideAutomaticallyMeansCompleteDigitisation : Bool
    seriesIdentityAutomaticallySameObjectAsQuotedPassage : Bool
    cataloguePresenceAutomaticallyProvesInterpretation : Bool
    locatedPrimaryArchiveAutomaticallySupersedesNamedScholarship : Bool
    sourceAcquisitionMayProceedBeforeConclusionPayment : Bool

open TasmanianPrimaryArchiveAcquisitionBoundary public

canonicalTasmanianPrimaryArchiveAcquisitionBoundary :
  TasmanianPrimaryArchiveAcquisitionBoundary
canonicalTasmanianPrimaryArchiveAcquisitionBoundary =
  tasmanianPrimaryArchiveAcquisitionBoundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    true

------------------------------------------------------------------------
-- Current exact acquisition coordinates.
------------------------------------------------------------------------

data TasmanianArchiveCoordinate : Set where
  colonialSecretaryFile7578 : TasmanianArchiveCoordinate
  cso1ArthurIndexes1824to1836 : TasmanianArchiveCoordinate
  cso66ArthurCampaignItinerary1830 : TasmanianArchiveCoordinate
  cbe1CapturedAboriginesMinutes1830to1833 : TasmanianArchiveCoordinate
  go1InwardDespatches : TasmanianArchiveCoordinate
  go2ColoniesUnderSecretaryDespatches : TasmanianArchiveCoordinate
  go33OutwardDespatches : TasmanianArchiveCoordinate

data AcquisitionState : Set where
  exactArchiveLocatorPaid : AcquisitionState
  underlyingItemReplayOpen : AcquisitionState

archiveAcquisitionState : TasmanianArchiveCoordinate → AcquisitionState
archiveAcquisitionState coordinate = exactArchiveLocatorPaid

-- This separate constant prevents locator payment being silently re-described as
-- content replay.  Each literal item/page remains a later same-object leaf.
underlyingItemReplayState : AcquisitionState
underlyingItemReplayState = underlyingItemReplayOpen
