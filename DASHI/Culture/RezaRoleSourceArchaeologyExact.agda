module DASHI.Culture.RezaRoleSourceArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- REZA EVENT-TIME ROLE SOURCE ARCHAEOLOGY
--
-- Thin provenance owner only.  The application/scientific owners remain
-- authoritative.  This ledger separates primary institutional evidence from
-- direct witness/family testimony, press mediation, and congressional
-- source-of-source repetition.
------------------------------------------------------------------------

data RezaRoleSourceClass : Set where
  primaryInstitutionalRoleRecord
  primaryCongressionalDocument
  directColleagueWitnessSurface
  directFamilyWitnessViaReporting
  secondaryPressReporting
  sourceOfSourceRepetition : RezaRoleSourceClass

record RezaRoleSourceCarrier : Set where
  constructor reza-role-source-carrier
  field
    sourceClass : RezaRoleSourceClass
    sourceObject : String
    stableIdentifier : String
    sourceLink : String
    claimedRole : String
    eventTimeEmploymentClaim : Bool
    directInstitutionalEmploymentReceipt : Bool
    independentOfPressSourceFamily : Bool
    boundedReading : String

open RezaRoleSourceCarrier public

houseOversight20260420 : RezaRoleSourceCarrier
houseOversight20260420 = reza-role-source-carrier
  primaryCongressionalDocument
  "U.S. House Committee on Oversight and Government Reform letter concerning missing/deceased scientists, 2026-04-20"
  "119th Congress committee letter; DOE-Missing-Scientists-Letter_4.20.26.pdf"
  "https://oversight.house.gov/wp-content/uploads/2026/04/DOE-Missing-Scientists-Letter_4.20.26.pdf"
  "Monica Reza served as director of the NASA Lab's Materials Processing Group"
  true
  false
  false
  "Primary congressional document, but the role sentence is footnoted to public press reporting. It therefore establishes congressional reliance/attention, not an independent JPL personnel receipt."

allanPetreColleagueLead : RezaRoleSourceCarrier
allanPetreColleagueLead = reza-role-source-carrier
  directColleagueWitnessSurface
  "Allan Petre public professional post seeking help for colleague/friend Monica Reza"
  "LinkedIn public post; no DOI"
  "https://www.linkedin.com/posts/allan-petre_help-find-monica-helpfindmonicareza-activity-7344704035611963392-bApi"
  "Director of the Materials Processing Group at NASA JPL"
  true
  false
  true
  "Direct colleague/friend testimony is stronger than anonymous repetition but is still not a JPL HR, directory, org-chart, appointment, or archival personnel object."

rezaFamilyEmploymentLead : RezaRoleSourceCarrier
rezaFamilyEmploymentLead = reza-role-source-carrier
  directFamilyWitnessViaReporting
  "Los Angeles Magazine interview with Reza family member, 2026-04-29"
  "secondary publication carrying direct family testimony; no DOI"
  "https://lamag.com/news/exclusive-for-monica-rezas-family-it-doesnt-make-sense/"
  "actively employed as Director of Materials Processing at NASA Jet Propulsion Laboratory when she disappeared"
  true
  false
  true
  "Family testimony directly addresses event-time employment, but the carrier is journalistic reporting rather than an employer personnel record."

calStateHistoricalRowLead : RezaRoleSourceCarrier
calStateHistoricalRowLead = reza-role-source-carrier
  sourceOfSourceRepetition
  "Repeated reports of Cal State LA 2024-2025 Dean's Advisory Board row"
  "reported wording: Monica Reza — JPL NASA; archived primary page not yet recovered"
  "https://www.calstatela.edu/ecst/deans-advisory-board"
  "JPL NASA"
  true
  false
  false
  "The current Cal State page is primary for the current board, but the historical Reza row has not been recovered from a primary archived manifestation. Repetition of the quoted row does not pay the historical page."

------------------------------------------------------------------------
-- Event-time role state.
------------------------------------------------------------------------

record RezaRoleEvidenceState : Set where
  constructor reza-role-evidence-state
  field
    patentInventorshipPaid : Bool
    colleagueWitnessLocated : Bool
    familyEventTimeEmploymentWitnessLocated : Bool
    congressionalRepetitionLocated : Bool
    archivedCalStateHistoricalRowLocated : Bool
    primaryJPLPersonnelRecordLocated : Bool
    primaryJPLOrgChartLocated : Bool
    exactMaterialsProcessingGroupIdentityPaid : Bool
    currentBestBoundedReading : String
    firstAcquisitionTarget : String

open RezaRoleEvidenceState public

canonicalRezaRoleEvidenceState : RezaRoleEvidenceState
canonicalRezaRoleEvidenceState = reza-role-evidence-state
  true true true true
  false false false false
  "Multiple source classes support that Reza was described as an active JPL Materials Processing director around her disappearance, but no recovered JPL/Caltech personnel or organization record yet pays the exact institutional role."
  "recover primary JPL/Caltech personnel directory, archived org chart, appointment/award/publication affiliation, or archived Cal State 2024-2025 board page naming Monica Reza and the exact role/group"

------------------------------------------------------------------------
-- Snowball semantic coordinates.
------------------------------------------------------------------------

record RezaRoleCoordinate : Set where
  constructor reza-role-coordinate
  field
    patentPublicationId : String
    personQid : String
    personQidVerified : Bool
    deweyTraversal : String
    directSourceLinksRetained : Bool
    qidCreatesRoleReceipt : Bool
    deweyCreatesRoleReceipt : Bool

open RezaRoleCoordinate public

canonicalRezaRoleCoordinate : RezaRoleCoordinate
canonicalRezaRoleCoordinate = reza-role-coordinate
  "US20040208777A1; application US10/769,195; parent US20030053926A1"
  "unresolvedQid"
  false
  "620 Engineering"
  true
  false false

------------------------------------------------------------------------
-- Source-dependency firewalls.
------------------------------------------------------------------------

record RezaRoleSourceBoundary : Set where
  constructor reza-role-source-boundary
  field
    congressionalPrimaryObjectMakesUnderlyingPressPrimary : Bool
    repeatedPressCreatesIndependentInstitutionalReceipt : Bool
    familyWitnessEqualsEmployerRecord : Bool
    colleagueWitnessEqualsEmployerRecord : Bool
    historicalPageQuoteEqualsRecoveredHistoricalPage : Bool
    multipleNonInstitutionalCarriersMayGuidePrimarySearch : Bool
    roleEvidenceCreatesCauseOrMotive : Bool

open RezaRoleSourceBoundary public

canonicalRezaRoleSourceBoundary : RezaRoleSourceBoundary
canonicalRezaRoleSourceBoundary = reza-role-source-boundary
  false false false false false true false
