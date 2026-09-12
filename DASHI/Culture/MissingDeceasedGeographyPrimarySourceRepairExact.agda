module DASHI.Culture.MissingDeceasedGeographyPrimarySourceRepairExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.MissingDeceasedSouthwestGeographyDiscriminatorExact as Geo

------------------------------------------------------------------------
-- PRIMARY EVENT-LOCATION SOURCE REPAIR
--
-- Geographic clustering must be computed from event coordinates, not from a
-- person's employer or a narrative facility anchor.  These sources pay only
-- the event-location/date fields exposed by the issuing public authority.
------------------------------------------------------------------------

chavezLosAlamosCounty : Source.AttributedSource
chavezLosAlamosCounty = Source.mkNoDOISource
  "Incorporated County of Los Alamos / Los Alamos Police Department"
  "Search Continues for Missing Person, Anthony Chavez"
  "Los Alamos County public safety release"
  "2025"
  "https://www.losalamosnm.gov/Community/News-media/Search-Continues-Anthony-Chavez"
  Source.governmentSource
  "Primary public-safety manifestation for the Anthony Chavez search in Los Alamos. It does not weld the missing person to a scientific publication identity or quantum-physics project."
  Source.publicAttribution

casiasNMDPS : Source.AttributedSource
casiasNMDPS = Source.mkNoDOISource
  "New Mexico Department of Public Safety"
  "Melissa Shirley Casias missing-person poster"
  "New Mexico Missing Persons"
  "2025"
  "https://missingpersons.dps.nm.gov/mpweb/mpposter_serv?id=M100749"
  Source.governmentSource
  "Primary state missing-person manifestation paying date missing 2025-06-26 and Missing From: Taos, NM. LANL employment is a separate work-location fibre."
  Source.publicAttribution

garciaNMDPS : Source.AttributedSource
garciaNMDPS = Source.mkNoDOISource
  "New Mexico Department of Public Safety"
  "Steven Abel Garcia missing-person record"
  "New Mexico Missing Persons"
  "2025"
  "https://missingpersons.dps.nm.gov/mpweb/mpdetailreport_serv?id=M101688"
  Source.governmentSource
  "Primary state missing-person manifestation paying date missing 2025-08-28 and Missing from: Albuquerque, NM; it does not pay employer duty or inventory anomaly."
  Source.publicAttribution

mccaslandNMDPS : Source.AttributedSource
mccaslandNMDPS = Source.mkNoDOISource
  "New Mexico Department of Public Safety"
  "William McCasland missing-person record"
  "New Mexico Missing Persons"
  "2026"
  "https://missingpersons.dps.nm.gov/mpweb/mpdetailreport_serv?id=M104337"
  Source.governmentSource
  "Primary state missing-person manifestation paying date missing 2026-02-27 and Missing from: Albuquerque, NM; it does not pay a Space Force meeting or programme cause."
  Source.publicAttribution

rezaCaliforniaDOJ : Source.AttributedSource
rezaCaliforniaDOJ = Source.mkNoDOISource
  "California Department of Justice, Office of the Attorney General"
  "Monica Jacinto Reza missing-person record"
  "California Missing Persons"
  "2025"
  "https://oag.ca.gov/missing/search?page=119"
  Source.governmentSource
  "Primary state missing-person database manifestation identifying Monica Jacinto Reza / AKA Monica Andrea Jacinto, Los Angeles County Sheriff's Office and case 025-00905-1257-400. It is a California event carrier, not a New Mexico-cluster carrier."
  Source.publicAttribution

chavezPrimaryCoordinatePresent : Geo.anthonyChavezLocation ≡ Geo.anthonyChavezLocation
chavezPrimaryCoordinatePresent = refl

casiasPrimaryCoordinatePresent : Geo.melissaCasiasLocation ≡ Geo.melissaCasiasLocation
casiasPrimaryCoordinatePresent = refl

garciaPrimaryCoordinatePresent : Geo.stevenGarciaLocation ≡ Geo.stevenGarciaLocation
garciaPrimaryCoordinatePresent = refl

mccaslandPrimaryCoordinatePresent : Geo.mccaslandLocation ≡ Geo.mccaslandLocation
mccaslandPrimaryCoordinatePresent = refl

rezaCaliforniaControlPresent : Geo.monicaRezaControlLocation ≡ Geo.monicaRezaControlLocation
rezaCaliforniaControlPresent = refl

stateLevelNewMexicoClusterIsNotFacilityTriangle : Bool
stateLevelNewMexicoClusterIsNotFacilityTriangle = true

employmentLocationDoesNotOverwriteEventLocation : Bool
employmentLocationDoesNotOverwriteEventLocation = true

recoveryLocationDoesNotOverwriteDisappearanceLocation : Bool
recoveryLocationDoesNotOverwriteDisappearanceLocation = true

whiteSandsStillNeedsCaseSpecificAnchor : Bool
whiteSandsStillNeedsCaseSpecificAnchor = true

record GeographyPrimarySourceBoundary : Set where
  constructor geography-primary-source-boundary
  field
    employerMaySubstituteForEventCoordinate : Bool
    recoveryCoordinateMaySubstituteForLastSeenCoordinate : Bool
    narrativeFacilityMayBeInsertedWithoutReceipt : Bool
    stateLevelClusteringMayNominateMatchedControlStudy : Bool
    sourceBackedCoordinateCreatesCommonCause : Bool

canonicalGeographyPrimarySourceBoundary : GeographyPrimarySourceBoundary
canonicalGeographyPrimarySourceBoundary =
  geography-primary-source-boundary false false false true false
