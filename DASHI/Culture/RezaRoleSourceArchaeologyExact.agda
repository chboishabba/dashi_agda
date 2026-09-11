module DASHI.Culture.RezaRoleSourceArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- REZA EVENT-TIME ROLE SOURCE ARCHAEOLOGY
--
-- Thin provenance owner only. The application/scientific owners remain
-- authoritative. This ledger separates primary institutional evidence from
-- direct witness/family testimony, press mediation, congressional
-- source-of-source repetition, and the earlier Monica Jacinto identity lineage.
------------------------------------------------------------------------

data RezaRoleSourceClass : Set where
  primaryInstitutionalRoleRecord
  primaryHistoricalIdentityRecord
  primaryLawEnforcementIdentityRecord
  primaryPatentManifestation
  primaryCongressionalDocument
  directColleagueWitnessSurface
  directFamilyWitnessViaReporting
  secondaryPressReporting
  sourceOfSourceRepetition
  semanticCoordinateOnly : RezaRoleSourceClass

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

boeing2004Jacinto : RezaRoleSourceCarrier
boeing2004Jacinto = reza-role-source-carrier
  primaryHistoricalIdentityRecord
  "Boeing news release: Two Boeing Employees Receive National Recognition, 2004-10-11"
  "Boeing corporate release dated 2004-10-11"
  "https://boeing.mediaroom.com/2004-10-11-Two-Boeing-Employees-Receive-National-Recognition"
  "Monica Jacinto; Boeing Integrated Defense Systems engineer; Boeing Associate Technical Fellow; metallic-alloy-development expertise"
  false true true
  "Primary employer/corporate carrier for the Monica Jacinto professional identity in 2004. It does not itself contain the later surname Reza or establish the 2025 JPL role."

calState2021Jacinto : RezaRoleSourceCarrier
calState2021Jacinto = reza-role-source-carrier
  primaryHistoricalIdentityRecord
  "Cal State LA LAunchPad Program 2021 materials-science profile"
  "Cal State LA institutional profile; 2021 programme object"
  "https://www.calstatela.edu/ecst/success/launchpad-program-2021"
  "Monica Jacinto; Technical Fellow for Materials and Processes Engineering at Aerojet Rocketdyne; Mondaloy co-inventor"
  false true true
  "Primary institutional carrier for the Monica Jacinto identity and pre-JPL Aerojet Rocketdyne role. It provides a high-confidence historical identity lineage but does not itself weld Jacinto to the later Monica Reza event-time identity."

californiaDOJ2026Alias : RezaRoleSourceCarrier
californiaDOJ2026Alias = reza-role-source-carrier
  primaryLawEnforcementIdentityRecord
  "California Department of Justice Missing Person record: Monica Jacinto Reza"
  "LASD case 025-00905-1257-400; DOB 1964-12-30; last seen 2025-06-22"
  "https://oag.ca.gov/missing/person/monica-jacinto-reza"
  "legal/current missing-person name Monica Jacinto Reza; AKA Monica Andrea Jacinto"
  false false true
  "Primary state law-enforcement identity carrier directly spanning the Reza surname and Monica Andrea Jacinto alias. It pays that legal/alias bridge, but does not by itself prove that every historical Monica A. Jacinto publication/patent is this person or establish a JPL employment role."

patentParent2003NameCarrier : RezaRoleSourceCarrier
patentParent2003NameCarrier = reza-role-source-carrier
  primaryPatentManifestation
  "US20030053926A1 — Burn-resistant and high tensile strength metal alloys"
  "US09/954,835; publication US20030053926A1; priority 2001-09-18"
  "https://patents.google.com/patent/US20030053926A1/en"
  "Inventors listed as Monica Jacinto and Dallis Hardwick; same patent family contains later continuation-in-part and continuation manifestations using Monica A. Jacinto"
  false false true
  "The parent patent manifestation pays that the same patent family can omit the middle initial for Monica Jacinto. This shrinks the name-normalisation debt but does not itself expand A. to Andrea or prove identity with the California DOJ missing-person record."

houseOversight20260420 : RezaRoleSourceCarrier
houseOversight20260420 = reza-role-source-carrier
  primaryCongressionalDocument
  "U.S. House Committee on Oversight and Government Reform letter concerning missing/deceased scientists, 2026-04-20"
  "119th Congress committee letter; DOE-Missing-Scientists-Letter_4.20.26.pdf"
  "https://oversight.house.gov/wp-content/uploads/2026/04/DOE-Missing-Scientists-Letter_4.20.26.pdf"
  "Monica Reza served as director of the NASA Lab's Materials Processing Group"
  true false false
  "Primary congressional document, but the role sentence is footnoted to public press reporting. It therefore establishes congressional reliance/attention, not an independent JPL personnel receipt."

allanPetreColleagueLead : RezaRoleSourceCarrier
allanPetreColleagueLead = reza-role-source-carrier
  directColleagueWitnessSurface
  "Allan Petre public professional post seeking help for colleague/friend Monica Reza"
  "LinkedIn public post; no DOI"
  "https://www.linkedin.com/posts/allan-petre_help-find-monica-helpfindmonicareza-activity-7344704035611963392-bApi"
  "Director of the Materials Processing Group at NASA JPL"
  true false true
  "Direct colleague/friend testimony is stronger than anonymous repetition but is still not a JPL HR, directory, org-chart, appointment, or archival personnel object."

rezaFamilyEmploymentLead : RezaRoleSourceCarrier
rezaFamilyEmploymentLead = reza-role-source-carrier
  directFamilyWitnessViaReporting
  "Los Angeles Magazine interview with Reza family member, 2026-04-29"
  "secondary publication carrying direct family testimony; no DOI"
  "https://lamag.com/news/exclusive-for-monica-rezas-family-it-doesnt-make-sense/"
  "actively employed as Director of Materials Processing at NASA Jet Propulsion Laboratory when she disappeared"
  true false true
  "Family testimony directly addresses event-time employment, but the carrier is journalistic reporting rather than an employer personnel record."

calStateHistoricalRowLead : RezaRoleSourceCarrier
calStateHistoricalRowLead = reza-role-source-carrier
  sourceOfSourceRepetition
  "Repeated reports of Cal State LA 2024-2025 Dean's Advisory Board row"
  "reported wording: Monica Reza — JPL NASA; archived primary page not yet recovered"
  "https://www.calstatela.edu/ecst/deans-advisory-board"
  "JPL NASA"
  true false false
  "The current Cal State page is primary for the current board, but the historical Reza row has not been recovered from a primary archived manifestation. Repetition of the quoted row does not pay the historical page."

wikidataMonicaJacinto : RezaRoleSourceCarrier
wikidataMonicaJacinto = reza-role-source-carrier
  semanticCoordinateOnly
  "Wikidata Monica Jacinto"
  "Q139385030"
  "https://www.wikidata.org/wiki/Q139385030"
  "semantic item labels Monica Jacinto and aliases Monica Jacinto Reza"
  false false true
  "Verified external semantic coordinate only. The item currently carries no cited references for the alias/biographical statements; the primary California DOJ alias carrier, not this QID, pays the Reza/Andrea-Jacinto alias bridge."

------------------------------------------------------------------------
-- Patent-family name manifestation boundary.
------------------------------------------------------------------------

record PatentNameManifestationState : Set where
  constructor patent-name-manifestation-state
  field
    parentPublication : String
    parentInventorForm : String
    continuationFamily : String
    laterInventorForm : String
    sharedPriorityDate : String
    samePatentFamilyPaid : Bool
    middleInitialPresenceVariesWithinFamily : Bool
    middleInitialExpansionToAndreaPaid : Bool
    patentInventorEqualsDOJMissingPersonPaid : Bool

open PatentNameManifestationState public

canonicalPatentNameManifestationState : PatentNameManifestationState
canonicalPatentNameManifestationState = patent-name-manifestation-state
  "US20030053926A1"
  "Monica Jacinto"
  "US20040208777A1 / US20100266442A1 continuation family"
  "Monica A. Jacinto in later manifestations"
  "2001-09-18"
  true true false false

------------------------------------------------------------------------
-- Event-time role and alias state.
------------------------------------------------------------------------

record RezaRoleEvidenceState : Set where
  constructor reza-role-evidence-state
  field
    patentInventorshipPaid : Bool
    historicalJacintoEmployerLineagePaid : Bool
    patentFamilyNameVariationPaid : Bool
    verifiedSemanticQidLocated : Bool
    semanticQidPaysAliasIdentity : Bool
    primaryLegalAliasBridgePaid : Bool
    patentInitialIdentityToMissingPersonPaid : Bool
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
  true true true true false true false true true true
  false false false false
  "California DOJ directly pays Monica Jacinto Reza = AKA Monica Andrea Jacinto. The patent family itself shows Monica Jacinto / Monica A. Jacinto manifestation variation under one priority lineage, while Boeing and Cal State pay a long Monica Jacinto materials-engineering/Mondaloy lineage. The remaining identity debt is exact patent-inventor-to-DOJ-person identity; independently, the JPL event-time role remains unpaid by an employer record."
  "recover a primary carrier tying the patent/Mondaloy inventor identity to Monica Andrea Jacinto or Monica Jacinto Reza; independently recover JPL/Caltech personnel/directory/org-chart evidence for the exact Materials Processing role"

------------------------------------------------------------------------
-- Snowball semantic coordinates.
------------------------------------------------------------------------

record RezaRoleCoordinate : Set where
  constructor reza-role-coordinate
  field
    patentPublicationId : String
    personQid : String
    personQidVerified : Bool
    personQidReferencePaid : Bool
    primaryAliasCarrier : String
    deweyTraversal : String
    directSourceLinksRetained : Bool
    qidCreatesRoleReceipt : Bool
    qidCreatesAliasWeld : Bool
    deweyCreatesRoleReceipt : Bool

open RezaRoleCoordinate public

canonicalRezaRoleCoordinate : RezaRoleCoordinate
canonicalRezaRoleCoordinate = reza-role-coordinate
  "US20030053926A1; US20040208777A1; US20100266442A1; priority 2001-09-18"
  "Q139385030"
  true false
  "California DOJ missing-person record; LASD case 025-00905-1257-400"
  "620 Engineering"
  true false false false

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
    primaryHistoricalJacintoRoleAutomaticallyEqualsLaterRezaIdentity : Bool
    uncitedWikidataAliasPaysSamePersonIdentity : Bool
    patentFamilyInitialVariationPaysAndreaExpansion : Bool
    dojAndreaAliasAutomaticallyPaysPatentInventorIdentity : Bool
    primaryAliasBridgeAutomaticallyPaysJPLRole : Bool
    multipleNonInstitutionalCarriersMayGuidePrimarySearch : Bool
    roleEvidenceCreatesCauseOrMotive : Bool

open RezaRoleSourceBoundary public

canonicalRezaRoleSourceBoundary : RezaRoleSourceBoundary
canonicalRezaRoleSourceBoundary = reza-role-source-boundary
  false false false false false false false false false false true false
