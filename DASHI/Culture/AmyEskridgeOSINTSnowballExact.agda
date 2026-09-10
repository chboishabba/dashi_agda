module DASHI.Culture.AmyEskridgeOSINTSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.AmyEskridgeDemiseCircumstancesSnowballExact as Demise

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: OSINT SNOWBALL
--
-- This is a concrete Amy specialization of the domain-neutral snowball OSINT
-- invariant being added in the snowball tranche. OSINT changes acquisition
-- route, not truth standard. Public artifacts may accumulate out of order, but
-- source identity, proposition support, corroboration independence, authority,
-- and downstream inference remain separate coordinates.
------------------------------------------------------------------------

data AmyOSINTProposition : Set where
  deathDate : AmyOSINTProposition
  amyReportedApartmentIntrusions : AmyOSINTProposition
  reportedOfficialSuicideCharacterization : AmyOSINTProposition
  amyIncludedIn2026ReviewReporting : AmyOSINTProposition
  broaderFederalInquiryExists : AmyOSINTProposition
  noPublicCaseLinkEstablished : AmyOSINTProposition
  publicPrimaryForensicRecordNotLocated : AmyOSINTProposition

data CarrierRelation : Set where
  exactPublicCarrier : CarrierRelation
  authenticatedArchiveOfSpeakerCarrier : CarrierRelation
  secondaryReportOfUninspectedPrimary : CarrierRelation
  institutionalContextNotAmySpecific : CarrierRelation
  publicRecordAudit : CarrierRelation
  discoveryLeadOnly : CarrierRelation

data OriginIndependence : Set where
  sameOriginRepublication : OriginIndependence
  independentOrigin : OriginIndependence
  independenceUnresolved : OriginIndependence

record AmyOSINTAtom : Set where
  constructor amy-osint-atom
  field
    source : Attribution.AttributedSource
    proposition : AmyOSINTProposition
    carrierRelation : CarrierRelation
    originGroupReference : String
    independence : OriginIndependence
    propositionScope : String
    sourceOfSourceOnly : Bool
    supportsNarrowProposition : Bool
    createsForensicCauseFinding : Bool
    createsCulpritInference : Bool
    createsResearchLinkInference : Bool

open AmyOSINTAtom public

------------------------------------------------------------------------
-- Attributed public-source carriers.
------------------------------------------------------------------------

familyObituarySource : Attribution.AttributedSource
familyObituarySource = Attribution.mkNoDOISource
  "Family of Amy Catherine Eskridge"
  "Amy Eskridge obituary"
  "AL.com / Legacy.com"
  "2022"
  "https://www.legacy.com/us/obituaries/huntsville/name/amy-eskridge-obituary?id=35311909"
  (Attribution.namedSourceKind "family memorial / obituary")
  "supports the publicly memorialized date of death and biographical context only; no cause or manner is supplied"
  Attribution.publicAttribution

archivedAmyInterviewSource : Attribution.AttributedSource
archivedAmyInterviewSource = Attribution.mkNoDOISource
  "Amy Eskridge"
  "Amy Eskridge Zoom [archived recording/transcript]"
  "Blocked Epistemology archive"
  "public archive"
  "https://blockedepistemology.substack.com/p/archive-amy-eskridge-zoom"
  Attribution.archivalSource
  "speaker-attributed carrier for what Amy publicly reported about apartment intrusions; not independent event verification"
  Attribution.publicAttribution

foxReviewSource : Attribution.AttributedSource
foxReviewSource = Attribution.mkNoDOISource
  "Michael Dorgan"
  "White House reviewing cases of missing, dead scientists for possible links as 11th person identified"
  "Fox News Digital"
  "2026"
  "https://www.foxnews.com/politics/white-house-reviewing-cases-missing-dead-scientists-possible-links-11th-person-identified"
  Attribution.newsSource
  "secondary report that Amy was included in the reviewed set; also records that no public evidence links her death to the other cases"
  Attribution.publicAttribution

foxDeathCharacterizationSource : Attribution.AttributedSource
foxDeathCharacterizationSource = Attribution.mkNoDOISource
  "Morgan Phillips"
  "11th scientist death emerges in string of missing, dead officials with access to US secrets"
  "Fox News Digital"
  "2026"
  "https://www.foxnews.com/politics/11th-scientist-death-emerges-string-missing-dead-officials-access-us-secrets/"
  Attribution.newsSource
  "secondary report that Amy's death has been characterized as a self-inflicted gunshot wound while official detail remains limited"
  Attribution.publicAttribution

houseOversightSource : Attribution.AttributedSource
houseOversightSource = Attribution.mkNoDOISource
  "James Comer; Eric Burlison"
  "Letter to DOE Secretary Wright on Missing Scientists"
  "U.S. House Committee on Oversight and Government Reform"
  "2026"
  "https://oversight.house.gov/wp-content/uploads/2026/04/DOE-Missing-Scientists-Letter_4.20.26.pdf"
  Attribution.governmentSource
  "primary institutional carrier proving the broader congressional inquiry/request for briefing; letter describes underlying public reporting as unconfirmed and is not an Amy-specific forensic finding"
  Attribution.publicAttribution

publicRecordAuditSource : Attribution.AttributedSource
publicRecordAuditSource = Attribution.mkNoDOISource
  "Troth Record"
  "What the public record establishes about Amy Eskridge — TR-0013"
  "Troth Press"
  "2026"
  "https://troth.press/records/tr-0013/"
  (Attribution.namedSourceKind "secondary public-record audit")
  "secondary audit useful for locating source gaps and checking provenance; its non-location findings do not prove records are absent"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Concrete OSINT atoms.
------------------------------------------------------------------------

obituaryDeathDateAtom : AmyOSINTAtom
obituaryDeathDateAtom = amy-osint-atom
  familyObituarySource
  deathDate
  exactPublicCarrier
  "family-obituary-origin"
  independentOrigin
  "Amy Catherine Eskridge died on 11 June 2022; obituary does not state cause or manner"
  false true false false false

amyIntrusionOSINTAtom : AmyOSINTAtom
amyIntrusionOSINTAtom = amy-osint-atom
  archivedAmyInterviewSource
  amyReportedApartmentIntrusions
  authenticatedArchiveOfSpeakerCarrier
  "amy-first-person-interview-origin"
  independentOrigin
  "Amy publicly reported repeated apartment entries while she and her then-partner were absent and described a cut micro-USB charger"
  false true false false false

reportedSuicideCharacterizationAtom : AmyOSINTAtom
reportedSuicideCharacterizationAtom = amy-osint-atom
  foxDeathCharacterizationSource
  reportedOfficialSuicideCharacterization
  secondaryReportOfUninspectedPrimary
  "fox-2026-death-reporting-origin"
  independenceUnresolved
  "records only that secondary reporting says the death was characterized as a self-inflicted gunshot wound; underlying primary forensic carrier remains uninspected"
  true true false false false

reviewInclusionReportingAtom : AmyOSINTAtom
reviewInclusionReportingAtom = amy-osint-atom
  foxReviewSource
  amyIncludedIn2026ReviewReporting
  secondaryReportOfUninspectedPrimary
  "fox-2026-review-reporting-origin"
  independenceUnresolved
  "secondary reporting says Amy is being included in the broader review set"
  true true false false false

foxNoPublicLinkAtom : AmyOSINTAtom
foxNoPublicLinkAtom = amy-osint-atom
  foxReviewSource
  noPublicCaseLinkEstablished
  exactPublicCarrier
  "fox-2026-review-reporting-origin"
  sameOriginRepublication
  "Fox explicitly reports no publicly available evidence linking Amy's death to the other cases and no authority-indicated tie between her work and death circumstances"
  false true false false false

houseInquiryAtom : AmyOSINTAtom
houseInquiryAtom = amy-osint-atom
  houseOversightSource
  broaderFederalInquiryExists
  institutionalContextNotAmySpecific
  "house-oversight-2026-missing-scientists-origin"
  independentOrigin
  "official House letter establishes that the Committee requested agency briefings regarding unconfirmed reports of deaths/disappearances involving sensitive scientific personnel; not an Amy-specific factual finding"
  true true false false false

publicRecordGapAuditAtom : AmyOSINTAtom
publicRecordGapAuditAtom = amy-osint-atom
  publicRecordAuditSource
  publicPrimaryForensicRecordNotLocated
  publicRecordAudit
  "troth-2026-public-record-audit-origin"
  independentOrigin
  "secondary audit reports no public police, autopsy or toxicology carrier located through its review; this is search-state evidence, not known absence"
  false true false false false

------------------------------------------------------------------------
-- Relationship to the pre-existing demise snowball.
------------------------------------------------------------------------

obituaryAtomAgreesWithDemiseRole :
  Demise.proposition Demise.familyObituaryDateAtom ≡ Demise.dateOfDeath
obituaryAtomAgreesWithDemiseRole = refl

intrusionAtomAgreesWithDemiseRole :
  Demise.proposition Demise.amyIntrusionStatementAtom ≡ Demise.preDeathIntrusionReport
intrusionAtomAgreesWithDemiseRole = refl

------------------------------------------------------------------------
-- OSINT-specific firewalls.
------------------------------------------------------------------------

record AmyOSINTBoundary : Set where
  constructor amy-osint-boundary
  field
    osintChangesAcquisitionRouteNotTruthStandard : Bool
    publicSourceMayBeRetainedOutOfOrder : Bool
    newsReportEqualsUnderlyingPrimaryRecord : Bool
    repeatedReportingEqualsIndependentCorroboration : Bool
    archiveEqualsNativeCarrierWithoutIdentityCheck : Bool
    sourceOfSourceEqualsExactSource : Bool
    searchNonLocationEqualsKnownAbsence : Bool
    federalInquiryEqualsAmyCaseConnection : Bool
    reportedSuicideEqualsInspectedForensicFinding : Bool
    intrusionSelfReportEqualsIndependentIntrusionProof : Bool
    scientificNoveltyMayPayDeathCausation : Bool
    osintAtomMayCreateCulpritByAccumulation : Bool

open AmyOSINTBoundary public

canonicalAmyOSINTBoundary : AmyOSINTBoundary
canonicalAmyOSINTBoundary = amy-osint-boundary
  true true false false false false false false false false false false
