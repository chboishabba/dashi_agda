module DASHI.Governance.BoloBoloOWSArchivesWorkingGroupLocatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- OWS ARCHIVES WORKING GROUP LOCATOR ROUTE
--
-- Attribution / source-role firewall:
--
-- * Kylie Message, Collecting Activism, Archiving Occupy Wall Street (2020)
--   is a SECONDARY archival history / bibliographic locator source.
-- * the bibliography identifies contemporaneous OWS Archives Working Group
--   Google Groups discussion-post locators and Tamiment collection coordinates.
-- * those discussion posts / attachments / archival notes become PRIMARY OR
--   CONTEMPORANEOUS RECORDS only if their actual contents are recovered.
-- * DASHI coding of any recovered record is a later DERIVED layer.
--
-- The PDF preview containing the bibliography could not be materialised for
-- page-image inspection in this acquisition environment. The indexed search
-- extract exposes the bibliographic strings below, while Routledge separately
-- verifies the book identity/author/year. Therefore this owner pays locator
-- identity only and explicitly leaves page-image verification and record
-- content unpaid.
------------------------------------------------------------------------

data ArchiveLocatorRole : Set where
  secondaryBibliographicLocator : ArchiveLocatorRole
  primaryThreadTarget : ArchiveLocatorRole
  archivalCollectionTarget : ArchiveLocatorRole

record ArchiveAcquisitionLocator : Set where
  constructor archive-acquisition-locator
  field
    label : String
    reference : String
    role : ArchiveLocatorRole
    locatorKnown : Bool
    contentRecovered : Bool
    sourceSupports : String
    sourceDoesNotByItselfSupport : String

open ArchiveAcquisitionLocator public

message2020Bibliography : ArchiveAcquisitionLocator
message2020Bibliography =
  archive-acquisition-locator
    "Kylie Message, Collecting Activism, Archiving Occupy Wall Street, bibliography"
    "Routledge, 2020; bibliography pp. 115-127; indexed bibliography extract exposes Roberts 2011d/2011e thread references"
    secondaryBibliographicLocator
    true
    false
    "secondary bibliographic locator identity for two OWS Archives Working Group discussion posts and related Tamiment holdings"
    "the contents of the Google Groups posts, any attachment bytes, primary Spokes minutes, or event truth"

nov8ForwardedSpokesDocuments : ArchiveAcquisitionLocator
nov8ForwardedSpokesDocuments =
  archive-acquisition-locator
    "Amy Roberts (2011e), Fwd: Spokes Council Address and Documents"
    "https://groups.google.com/forum/#!topic/ows-archives/_F02nGKeU1s"
    primaryThreadTarget
    true
    false
    "Message's bibliography identifies a Nov 8, 2011 OWS Archives Working Group discussion post with this title and explicitly labels it a discussion post with attachment"
    "the thread body, attachment content, attachment provenance, primary Spokes minutes, or implementation outcome"

nov11SpokescouncilDiscussion : ArchiveAcquisitionLocator
nov11SpokescouncilDiscussion =
  archive-acquisition-locator
    "Amy Roberts (2011d), Spokescouncil"
    "https://groups.google.com/forum/#!topic/ows-archives/sDSy_C6dso4"
    primaryThreadTarget
    true
    false
    "Message's bibliography identifies a Nov 11, 2011 OWS Archives Working Group discussion post with this title and exact thread identifier"
    "the thread body, the exact Nov 11 NYCGA Spokes minute page, primary meeting semantics, or causal interpretation"

archivesWorkingGroupTamimentCollection : ArchiveAcquisitionLocator
archivesWorkingGroupTamimentCollection =
  archive-acquisition-locator
    "Occupy Wall Street Archives Working Group Records, TAM 630"
    "NYU Tamiment Library / Robert F. Wagner Labor Archives; bibliography cites e.g. Box 3 Folder 2.15 and Box 2 Folders 2.10, 2.9, 2.7, 2.4, 2.3, 2.2"
    archivalCollectionTarget
    true
    false
    "secondary bibliographic coordinates for physical/archive holdings of OWS Archives Working Group notes and organizational documents"
    "Spokes-specific content in any cited folder, primary Spokes minutes, or any claim about realised governance"

canonicalArchivesWorkingGroupLocators : List ArchiveAcquisitionLocator
canonicalArchivesWorkingGroupLocators =
  message2020Bibliography
  ∷ nov8ForwardedSpokesDocuments
  ∷ nov11SpokescouncilDiscussion
  ∷ archivesWorkingGroupTamimentCollection
  ∷ []

------------------------------------------------------------------------
-- Current payment boundary.
------------------------------------------------------------------------

record OWSArchivesWorkingGroupLocatorBoundary : Set where
  constructor ows-archives-working-group-locator-boundary
  field
    routledgeBookIdentityVerified : Bool
    indexedBibliographyExtractAvailable : Bool
    bibliographyPdfPageVisuallyVerified : Bool

    nov8ForwardedSpokesDocumentsLocatorPaid : Bool
    nov8BibliographyReportsAttachment : Bool
    nov8ThreadContentRecovered : Bool
    nov8ForwardedAttachmentRecovered : Bool

    nov11SpokescouncilThreadLocatorPaid : Bool
    nov11ThreadContentRecovered : Bool

    tamimentCollectionCoordinatesPaid : Bool
    tamimentCoordinatesProveSpokesMinuteContent : Bool

    googleGroupsThreadEqualsPrimarySpokesMinutes : Bool
    secondaryLocatorEqualsPrimaryContent : Bool
    futureRecoveredRecordsRequireOwnSourceRole : Bool
    futureRecoveredRecordsMayCorroborateOrContradictOtherSources : Bool

open OWSArchivesWorkingGroupLocatorBoundary public

canonicalOWSArchivesWorkingGroupLocatorBoundary :
  OWSArchivesWorkingGroupLocatorBoundary
canonicalOWSArchivesWorkingGroupLocatorBoundary =
  ows-archives-working-group-locator-boundary
    true
    true
    false
    true
    true
    false
    false
    true
    false
    true
    false
    false
    false
    true
    true

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data SecondaryLocatorPaysPrimaryContent : Set where
data ThreadLocatorPaysAttachmentContent : Set where
data TamimentCoordinatePaysSpokesMinutes : Set where

secondaryLocatorDoesNotPayPrimaryContent :
  SecondaryLocatorPaysPrimaryContent → ⊥
secondaryLocatorDoesNotPayPrimaryContent ()

threadLocatorDoesNotPayAttachmentContent :
  ThreadLocatorPaysAttachmentContent → ⊥
threadLocatorDoesNotPayAttachmentContent ()

tamimentCoordinateDoesNotPaySpokesMinutes :
  TamimentCoordinatePaysSpokesMinutes → ⊥
tamimentCoordinateDoesNotPaySpokesMinutes ()

canonicalOWSArchivesWorkingGroupLocatorReceipt : GenericReceipt.GenericReceipt
canonicalOWSArchivesWorkingGroupLocatorReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS Archives Working Group archival locator route"
    "DASHI.Governance.BoloBoloOWSArchivesWorkingGroupLocatorExact"
    "nov8ForwardedSpokesDocuments / nov11SpokescouncilDiscussion / archivesWorkingGroupTamimentCollection / canonicalOWSArchivesWorkingGroupLocatorBoundary"
    "records a secondary bibliography-derived acquisition route to exact OWS Archives Working Group Google Groups thread identifiers and Tamiment TAM 630 holdings coordinates, including the bibliography's report that the Nov 8 'Spokes Council Address and Documents' post had an attachment"
    "the bibliography search extract is locator evidence only; its PDF page was not visually materialised here; thread and attachment contents remain unrecovered; Google Groups discussion posts and Tamiment coordinates are not silently promoted to primary Spokes minutes or meeting truth"
    "agda -i . DASHI/Governance/BoloBoloOWSArchivesWorkingGroupLocatorRegression.agda"
