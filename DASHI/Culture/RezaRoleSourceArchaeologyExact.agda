module DASHI.Culture.RezaRoleSourceArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- REZA EVENT-TIME ROLE SOURCE ARCHAEOLOGY
--
-- Thin provenance owner only. The application/scientific owners remain
-- authoritative. This ledger separates primary institutional evidence from
-- patent facsimiles/assignment manifestations, direct witness/family testimony,
-- press mediation, congressional source-of-source repetition, and semantic
-- coordinates.
------------------------------------------------------------------------

data RezaRoleSourceClass : Set where
  primaryInstitutionalRoleRecord
  primaryHistoricalIdentityRecord
  primaryLawEnforcementIdentityRecord
  primaryPatentManifestation
  patentAssignmentIndexManifestation
  renderedIndexManifestation
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

aiaaSciTech2023Jacinto : RezaRoleSourceCarrier
aiaaSciTech2023Jacinto = reza-role-source-carrier
  primaryHistoricalIdentityRecord
  "AIAA SciTech 2023 History of Materials joint special-session Call for Papers"
  "AIAA SciTech 2023; conference 2023-01-23 through 2023-01-27"
  "https://www.aiaa.org/docs/default-source/uploadedfiles/aiaa-scitech-forum/callforpapers/mat-adf-v2.pdf"
  "Dr. Monica Jacinto; Aerojet Rocketdyne; organizer/contact for the History of Materials special session"
  false true true
  "Primary AIAA professional-society carrier placing the Monica Jacinto identity at Aerojet Rocketdyne in the 2023 SciTech cycle. It narrows the pre-JPL transition window but does not pay the later surname Reza, JPL employment, or a transition date."

californiaDOJ2026Alias : RezaRoleSourceCarrier
californiaDOJ2026Alias = reza-role-source-carrier
  primaryLawEnforcementIdentityRecord
  "California Department of Justice Missing Person record: Monica Jacinto Reza"
  "LASD case 025-00905-1257-400; DOB 1964-12-30; last seen 2025-06-22"
  "https://oag.ca.gov/missing/person/monica-jacinto-reza"
  "legal/current missing-person name Monica Jacinto Reza; AKA Monica Andrea Jacinto"
  false false true
  "Primary state law-enforcement identity carrier directly spanning the Reza surname and Monica Andrea Jacinto alias. It pays that legal/alias bridge, but does not by itself prove that every historical Monica A. Jacinto publication/patent is this person or establish a JPL employment role."

patentParent2003FacsimileCarrier : RezaRoleSourceCarrier
patentParent2003FacsimileCarrier = reza-role-source-carrier
  primaryPatentManifestation
  "US20030053926A1 publication facsimile — Burn-resistant and high tensile strength metal alloys"
  "US09/954,835; publication US20030053926A1; priority 2001-09-18"
  "https://patentimages.storage.googleapis.com/58/4f/d7/4d0e60f1762cd4/US20030053926A1.pdf"
  "front page identifies inventors Monica A. Jacinto, Glendale, CA, and Dallis Ann Hardwick, Dayton, OH"
  false false true
  "Publication facsimile preserves the middle initial A. in the source text. It does not expand A. to Andrea or by itself prove identity with the California DOJ missing-person record."

patentParent2003RenderedCarrier : RezaRoleSourceCarrier
patentParent2003RenderedCarrier = reza-role-source-carrier
  renderedIndexManifestation
  "Google Patents rendered metadata for US20030053926A1"
  "US20030053926A1 rendered/index manifestation"
  "https://patents.google.com/patent/US20030053926A1/en"
  "rendered inventor field displays Monica Jacinto and Dallis Hardwick"
  false false true
  "The rendered/index manifestation omits the middle initial that is present in the publication facsimile. This is retained as a manifestation-normalisation conflict, not evidence that the source patent itself used two different inventor identities."

patent2004BoeingAssignmentCarrier : RezaRoleSourceCarrier
patent2004BoeingAssignmentCarrier = reza-role-source-carrier
  patentAssignmentIndexManifestation
  "US20040208777A1 patent assignment timeline"
  "US10/769,195; assignment dated 2004-01-30 to THE BOEING COMPANY"
  "https://patents.google.com/patent/US20040208777A1/en"
  "assignment metadata names assignors HARDWICK, DALLIS ANN and JACINTO, MONICA A.; assignee THE BOEING COMPANY"
  false false true
  "Exact patent-assignment metadata ties the Monica A. Jacinto inventor form to a Boeing assignment on 2004-01-30 and records later IP transfers through United Technologies / Pratt & Whitney Rocketdyne / Ruby Acquisition Enterprises. This pays an IP-transfer lineage, not the A.-to-Andrea expansion, later surname Reza, or JPL employment."

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
-- Current Cal State board manifestation versus unrecovered historical row.
------------------------------------------------------------------------

record CalStateBoardManifestationState : Set where
  constructor cal-state-board-manifestation-state
  field
    currentPage : String
    currentBoardLabel : String
    currentRezaRowPresent : Bool
    currentJplRepresentative : String
    currentJplRole : String
    allegedHistoricalRowRecoveredFromPrimaryArchive : Bool
    currentAbsenceProvesHistoricalAbsence : Bool
    currentDifferentJplMemberProvesRoleReplacement : Bool
    boundedReading : String

open CalStateBoardManifestationState public

canonicalCalStateBoardManifestationState : CalStateBoardManifestationState
canonicalCalStateBoardManifestationState = cal-state-board-manifestation-state
  "https://www.calstatela.edu/ecst/deans-advisory-board"
  "2025-2026 Board Members"
  false
  "Sergio Valdez — JPL NASA"
  "Engineering Manager"
  false false false
  "The current primary Cal State LA board manifestation contains no Monica Reza row and instead lists Sergio Valdez of JPL NASA as Engineering Manager. This pays only the current 2025-2026 manifestation state. It neither disproves a reported 2024-2025 Monica Reza row nor identifies Valdez as Reza's employer-role successor. The historical primary board manifestation remains a separate acquisition target."

------------------------------------------------------------------------
-- Patent-publication / assignment manifestation boundary.
------------------------------------------------------------------------

record PatentNameManifestationState : Set where
  constructor patent-name-manifestation-state
  field
    publication : String
    facsimileInventorForm : String
    renderedInventorForm : String
    samePublicationIdentityPaid : Bool
    renderedNameDiffersFromFacsimile : Bool
    sourceTextMiddleInitialPaid : Bool
    boeingAssignmentOfMonicaAInterestPaid : Bool
    familyLevelInitialVariationPaid : Bool
    middleInitialExpansionToAndreaPaid : Bool
    patentInventorEqualsDOJMissingPersonPaid : Bool

open PatentNameManifestationState public

canonicalPatentNameManifestationState : PatentNameManifestationState
canonicalPatentNameManifestationState = patent-name-manifestation-state
  "US20030053926A1 / US20040208777A1 family; priority 2001-09-18"
  "Monica A. Jacinto"
  "Monica Jacinto"
  true true true true false false false

record PatentAssignmentLineageState : Set where
  constructor patent-assignment-lineage-state
  field
    publication : String
    initialAssignment : String
    laterTransferChain : String
    exactInitialAssignorNamePaid : Bool
    exactInitialAssigneePaid : Bool
    assignmentChainPaysEmploymentContinuity : Bool
    assignmentChainPaysPersonIdentityAcrossSurnameChange : Bool
    assignmentChainPaysJPLRole : Bool

open PatentAssignmentLineageState public

canonicalPatentAssignmentLineageState : PatentAssignmentLineageState
canonicalPatentAssignmentLineageState = patent-assignment-lineage-state
  "US20040208777A1 / application US10/769,195"
  "2004-01-30: HARDWICK, DALLIS ANN; JACINTO, MONICA A. -> THE BOEING COMPANY"
  "2006 United Technologies; 2007 Pratt & Whitney Rocketdyne; 2013 corrective Ruby Acquisition Enterprises / Pratt & Whitney Rocketdyne chain"
  true true false false false

------------------------------------------------------------------------
-- Event-time role and alias state.
------------------------------------------------------------------------

record RezaRoleEvidenceState : Set where
  constructor reza-role-evidence-state
  field
    patentInventorshipPaid : Bool
    historicalJacintoEmployerLineagePaid : Bool
    patentManifestationNameConflictPaid : Bool
    patentBoeingAssignmentPaid : Bool
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
  true true true true true false true false true true true
  false false false false
  "California DOJ directly pays Monica Jacinto Reza = AKA Monica Andrea Jacinto. Patent facsimile/assignment metadata pay Monica A. Jacinto inventorship and the 2004 assignment to Boeing; Boeing, Cal State and AIAA independently pay a long Monica Jacinto materials-engineering lineage through the 2023 SciTech cycle. Rendered patent metadata normalises the middle initial away. The current 2025-2026 Cal State board does not list Reza and lists Sergio Valdez of JPL NASA instead, but that current manifestation neither disproves the reported historical row nor pays a successor relationship. The remaining identity debt is exact Monica A. Jacinto -> Monica Andrea Jacinto/Reza; independently, the JPL event-time role remains unpaid by an employer record."
  "recover a primary carrier tying the patent/Mondaloy inventor identity Monica A. Jacinto to Monica Andrea Jacinto or Monica Jacinto Reza; independently recover JPL/Caltech personnel/directory/org-chart evidence for the exact Materials Processing role or the archived primary 2024-2025 Cal State board manifestation"

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
  "US20030053926A1; US20040208777A1; US20100266442A1; priority 2001-09-18; 2004-01-30 Boeing assignment"
  "Q139385030"
  true false
  "California DOJ missing-person record; LASD case 025-00905-1257-400"
  "620 Engineering / 346.048 intellectual-property traversal"
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
    renderedPatentNameOverridesPublicationFacsimile : Bool
    patentFacsimileInitialPaysAndreaExpansion : Bool
    patentAssignmentPaysLaterSurnameIdentity : Bool
    patentAssignmentPaysJPLRole : Bool
    dojAndreaAliasAutomaticallyPaysPatentInventorIdentity : Bool
    primaryAliasBridgeAutomaticallyPaysJPLRole : Bool
    multipleNonInstitutionalCarriersMayGuidePrimarySearch : Bool
    roleEvidenceCreatesCauseOrMotive : Bool

open RezaRoleSourceBoundary public

canonicalRezaRoleSourceBoundary : RezaRoleSourceBoundary
canonicalRezaRoleSourceBoundary = reza-role-source-boundary
  false false false false false false false false false false false false false true false
