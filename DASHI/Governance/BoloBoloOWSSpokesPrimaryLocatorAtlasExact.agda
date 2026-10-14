module DASHI.Governance.BoloBoloOWSSpokesPrimaryLocatorAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- OWS SPOKES PRIMARY-RECORD LOCATOR ATLAS
--
-- Attribution discipline:
--
-- * Holmes (2023), Organizing Occupy Wall Street: This Is Just Practice,
--   bibliography = SECONDARY bibliographic locator evidence.
-- * the referenced NYCGA pages = PRIMARY archival records if/when their
--   contents are actually recovered.
-- * DASHI's transcription/coding of those records = a later DERIVED layer.
--
-- Knowing a Wayback locator is not equivalent to possessing or validating the
-- primary minute content.  This owner therefore pays locator identity only.
------------------------------------------------------------------------

data LocatorProvenance : Set where
  holmes2023Bibliography : LocatorProvenance

record SpokesPrimaryLocator : Set where
  constructor spokes-primary-locator
  field
    meetingDate : String
    archiveLocator : String
    locatorProvenance : LocatorProvenance
    locatorKnown : Bool
    exactPagePathKnown : Bool
    primaryContentRecovered : Bool

open SpokesPrimaryLocator public

nov7SpokesLocator : SpokesPrimaryLocator
nov7SpokesLocator =
  spokes-primary-locator
    "2011-11-07"
    "https://web.archive.org/web/20120617080006/http://www.nycga.net/2011/11/07/operational-spokes-council-1172011-2/#more-2845"
    holmes2023Bibliography
    true true false

nov9SpokesLocator : SpokesPrimaryLocator
nov9SpokesLocator =
  spokes-primary-locator
    "2011-11-09"
    "https://web.archive.org/web/20120617080341/http://www.nycga.net/2011/11/09/operational-spokes-council-1192011/#more-3037"
    holmes2023Bibliography
    true true false

-- Holmes' bibliography identifies the 2011-11-11 Spokes Council and the
-- archived NYCGA snapshot, but the cited surface available in this acquisition
-- pass does not expose a distinct exact page path. Keep that partiality typed.
nov11SpokesLocator : SpokesPrimaryLocator
nov11SpokesLocator =
  spokes-primary-locator
    "2011-11-11"
    "https://web.archive.org/web/20120617072354/http://www.nycga.net"
    holmes2023Bibliography
    true false false

nov14SpokesLocator : SpokesPrimaryLocator
nov14SpokesLocator =
  spokes-primary-locator
    "2011-11-14"
    "https://web.archive.org/web/20120617072354/http://www.nycga.net/2011/11/14/nyc-operational-spokes-council-minutes-11142011/"
    holmes2023Bibliography
    true true false

------------------------------------------------------------------------
-- Acquisition boundary.
------------------------------------------------------------------------

record SpokesPrimaryLocatorBoundary : Set where
  constructor spokes-primary-locator-boundary
  field
    secondaryBibliographicLocatorPaid : Bool
    exactNov7Nov9Nov14LocatorPaid : Bool
    nov11MeetingIdentityPaid : Bool
    nov11ExactPagePathPaid : Bool
    primaryContentMaterialised : Bool
    primaryMinuteSemanticsCoded : Bool
    bibliographicLocatorEqualsPrimaryMinuteContent : Bool
    retrospectiveQuotationEqualsPrimaryMinuteContent : Bool
    futureRecoveredMinutesMayBeCodedAsDerivedObservation : Bool

open SpokesPrimaryLocatorBoundary public

canonicalSpokesPrimaryLocatorBoundary : SpokesPrimaryLocatorBoundary
canonicalSpokesPrimaryLocatorBoundary =
  spokes-primary-locator-boundary
    true true true false
    false false false false
    true

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data LocatorPaysPrimaryContent : Set where
data RetrospectiveQuotationPaysPrimaryContent : Set where

data LocatorPaysMeetingOutcome : Set where

locatorDoesNotPayPrimaryContent : LocatorPaysPrimaryContent → ⊥
locatorDoesNotPayPrimaryContent ()

retrospectiveQuotationDoesNotPayPrimaryContent :
  RetrospectiveQuotationPaysPrimaryContent → ⊥
retrospectiveQuotationDoesNotPayPrimaryContent ()

locatorDoesNotPayMeetingOutcome : LocatorPaysMeetingOutcome → ⊥
locatorDoesNotPayMeetingOutcome ()
