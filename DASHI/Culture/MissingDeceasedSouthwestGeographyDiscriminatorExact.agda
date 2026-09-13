module DASHI.Culture.MissingDeceasedSouthwestGeographyDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedInvestigativeAttributedSourceAtlasExact as Sources

------------------------------------------------------------------------
-- SOUTHWEST GEOGRAPHY DISCRIMINATOR
--
-- Event location, employment/facility relationship and speculative facility
-- topology are separate fibres.  Geography may nominate controls/acquisitions;
-- it cannot create a common programme, operation or cause.
------------------------------------------------------------------------

record SouthwestCaseLocation : Set where
  constructor southwest-case-location
  field
    person : String
    eventLocation : String
    workOrFacilityRelationship : String
    locationSource : String
    eventLocationPaid : Bool
    workRelationshipPaidAtStatedStrength : Bool
    samePhysicalFacilityAsEvent : Bool

open SouthwestCaseLocation public

anthonyChavezLocation : SouthwestCaseLocation
anthonyChavezLocation = southwest-case-location
  "Anthony Chavez"
  "Los Alamos, New Mexico"
  "reported former Los Alamos National Laboratory worker; exact technical identity remains independently constrained by the Chavez identity firewall"
  "New Mexico DPS missing-person record + bounded KOB aggregation"
  true true false

stevenGarciaLocation : SouthwestCaseLocation
stevenGarciaLocation = southwest-case-location
  "Steven Abel Garcia"
  "Albuquerque, New Mexico"
  "reported property-custodian relationship to the Albuquerque branch of Kansas City National Security Campus; primary employer/duty scope still required"
  "New Mexico DPS missing-person record + bounded KOB aggregation"
  true false false

mccaslandLocation : SouthwestCaseLocation
mccaslandLocation = southwest-case-location
  "William Neil McCasland"
  "Albuquerque, New Mexico"
  "historical AFRL/aerospace leadership is independently source-backed; event-time Kirtland or Space Force tasking is not paid here"
  "New Mexico DPS missing-person record"
  true true false

melissaCasiasLocation : SouthwestCaseLocation
melissaCasiasLocation = southwest-case-location
  "Melissa Casias"
  "Taos / northern New Mexico disappearance context; remains later recovered in Carson National Forest"
  "Los Alamos National Laboratory administrative employment reported by KOB and Los Angeles Times"
  "KOB + Los Angeles Times bounded secondary reporting"
  true true false

monicaRezaControlLocation : SouthwestCaseLocation
monicaRezaControlLocation = southwest-case-location
  "Monica Jacinto Reza"
  "Mount Waterman / Angeles National Forest, California"
  "JPL/materials role is a separate work fibre; California event is outside the New Mexico geographic cluster"
  "Los Angeles Magazine bounded secondary reporting"
  true true false

newMexicoClusterIsSourceBacked : Bool
newMexicoClusterIsSourceBacked = true

whiteSandsEventAnchorIsUnpaid : Bool
whiteSandsEventAnchorIsUnpaid = true

lanlKirtlandWhiteSandsTriangleIsPaid : Bool
lanlKirtlandWhiteSandsTriangleIsPaid = false

geographyDoesNotCreateCommonCause : Bool
geographyDoesNotCreateCommonCause = true

record GeographicHypothesisDiscriminator : Set where
  constructor geographic-hypothesis-discriminator
  field
    hypothesis : String
    paidKernel : String
    missingBridge : String
    matchedControl : String
    nextAcquisition : String
    commonCausePaid : Bool

southwestOperationalCorridorHypothesis : GeographicHypothesisDiscriminator
southwestOperationalCorridorHypothesis = geographic-hypothesis-discriminator
  "the New Mexico cases were selected through one shared Southwest operational/security infrastructure"
  "four cases are publicly aggregated in New Mexico; person-specific work/facility relationships vary in source strength"
  "a shared programme, access system, logistics route, security database, tasking object or event-time facility intersection"
  "matched New Mexico laboratory/defense personnel with comparable role, age, clearance/access and geography who were not selected into the narrative roster"
  "recover event-time duty sites, facility-access objects, travel/tasking records where public, and a denominator for comparable LANL/Kirtland/Sandia/KCNSC-linked personnel"
  false

record SouthwestGeographyBoundary : Set where
  constructor southwest-geography-boundary
  field
    newMexicoClusterMayNominateSearch : Bool
    facilityEmploymentEqualsEventLocation : Bool
    whiteSandsMayBeInsertedWithoutCaseReceipt : Bool
    proximityCreatesSharedProgramme : Bool
    geographyNeedsReferencePopulation : Bool
    californiaCaseMayBeForcedIntoNewMexicoTriangle : Bool

canonicalSouthwestGeographyBoundary : SouthwestGeographyBoundary
canonicalSouthwestGeographyBoundary = southwest-geography-boundary
  true false false false true false

sourceAtlasPresent :
  Sources.investigativeSourceAtlas ≡ Sources.investigativeSourceAtlas
sourceAtlasPresent = refl
