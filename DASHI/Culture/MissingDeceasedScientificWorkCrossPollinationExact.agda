module DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact where

------------------------------------------------------------------------
-- BROADER ROSTER / SCIENTIFIC-WORK ATTRIBUTION CROSS-POLLINATION
--
-- Extends MissingDeceasedScientistWorkAttributionExact with two further
-- principles exposed by the wider public roster:
--
--   1. not every person grouped into a 'missing scientists' narrative is a
--      scientist or named scientific contributor;
--   2. similar names are not same-object identity receipts.
--
-- Accordingly, administrative/support/security-site roles remain institution
-- relations, not silently promoted scientific authorship.  A publication under
-- a longer/similar name is not attached to a missing person without an identity
-- weld.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Culture.MissingDeceasedScientistWorkAttributionExact as Atlas

------------------------------------------------------------------------
-- Anthony Chavez: primary LANL institutional evidence.
--
-- Los Alamos National Laboratory's Summer 2025 National Security Science
-- engineering issue describes Anthony Chavez as entering the machinist
-- apprenticeship programme in 1989, later earning mechanical engineering, and
-- working for more than 25 years at DARHT.  It specifically states that he
-- completed design work for the Scorpius accelerator.
------------------------------------------------------------------------

anthonyChavezDARHT : Attribution.ScientificWorkAttribution
anthonyChavezDARHT =
  Attribution.scientific-work-attribution
    "Anthony Chavez"
    "engineering and design work at the Dual-Axis Radiographic Hydrodynamic Test facility (DARHT)"
    "Los Alamos National Laboratory"
    Attribution.institutionalResearchRole
    Attribution.primaryInstitutionalRecord
    "Los Alamos National Laboratory, National Security Science, Summer 2025, Engineering / Anthony Chavez profile"
    "LANL itself describes Chavez as a mechanical engineer with more than 25 years at DARHT; this is stronger than generic 'former LANL employee' reporting."
    Attribution.externalSourceOwner

anthonyChavezScorpius : Attribution.ScientificWorkAttribution
anthonyChavezScorpius =
  Attribution.scientific-work-attribution
    "Anthony Chavez"
    "design work for the Scorpius accelerator"
    "Los Alamos / Nevada National Security Sites Scorpius development"
    Attribution.institutionalResearchRole
    Attribution.primaryInstitutionalRecord
    "Los Alamos National Laboratory, National Security Science, Summer 2025, Anthony Chavez profile"
    "LANL explicitly attributes completed Scorpius accelerator design work to Anthony Chavez."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Identity firewall: LANL's repository also contains a 2018 paper listing a
-- 'Mark Anthony Chavez' as coauthor on DARHT spectrometer calibration.  The
-- topical overlap is striking but our same-object rule forbids equating the
-- publication identity with the missing Anthony Chavez solely from name and
-- institution similarity.  It remains a candidate identity weld, not an
-- attribution receipt.
------------------------------------------------------------------------

record AnthonyChavezPublicationIdentityBoundary : Set where
  constructor anthony-chavez-publication-identity-boundary
  field
    lanlPaperCandidateLocated : Bool
    lanlPaperCandidateLocatedIsTrue : lanlPaperCandidateLocated ≡ true
    nameSimilarityProvesSamePerson : Bool
    nameSimilarityProvesSamePersonIsFalse : nameSimilarityProvesSamePerson ≡ false
    sameInstitutionAndTopicProvesSamePerson : Bool
    sameInstitutionAndTopicProvesSamePersonIsFalse :
      sameInstitutionAndTopicProvesSamePerson ≡ false
    publicationAuthorshipAttachedBeforeIdentityWeld : Bool
    publicationAuthorshipAttachedBeforeIdentityWeldIsFalse :
      publicationAuthorshipAttachedBeforeIdentityWeld ≡ false

canonicalAnthonyChavezPublicationIdentityBoundary :
  AnthonyChavezPublicationIdentityBoundary
canonicalAnthonyChavezPublicationIdentityBoundary =
  anthony-chavez-publication-identity-boundary
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Jason R. Thomas: publication-level chemical-biology attribution.
------------------------------------------------------------------------

jasonThomasSTINGScreen : Attribution.ScientificWorkAttribution
jasonThomasSTINGScreen =
  Attribution.scientific-work-attribution
    "Jason R. Thomas"
    "A High Content Screen in Macrophages Identifies Small Molecule Modulators of STING-IRF3 and NFkB Signaling"
    "Novartis Institutes for BioMedical Research, Chemical Biology and Therapeutics"
    Attribution.namedAuthor
    Attribution.primaryPublicationRecord
    "ACS Chemical Biology 13(4), 1066-1081 (2018), DOI 10.1021/acschembio.7b01060"
    "The ACS publication names Jason R. Thomas as an author and identifies his Novartis Chemical Biology and Therapeutics affiliation."
    Attribution.externalSourceOwner

jasonThomasVPS34 : Attribution.ScientificWorkAttribution
jasonThomasVPS34 =
  Attribution.scientific-work-attribution
    "Jason Thomas"
    "Selective VPS34 inhibitor blocks autophagy and uncovers a role for NCOA4 in ferritin degradation and iron homeostasis in vivo"
    "Novartis Institutes for BioMedical Research"
    Attribution.namedAuthor
    Attribution.primaryPublicationRecord
    "Nature Cell Biology 16 (2014), author/affiliation record"
    "The publication's author list includes Jason Thomas among the Novartis authors; this is publication authorship, not sole ownership of the project."
    Attribution.externalSourceOwner

------------------------------------------------------------------------
-- Wider-roster role classification.
--
-- This carrier is intentionally NOT ScientificWorkAttribution.  It records why
-- a person may occur in the public cluster even when no named scientific work
-- has yet been attached under our evidence threshold.
------------------------------------------------------------------------

data RosterRoleClass : Set where
  documentedScientistOrEngineer
  documentedTechnicalLeadership
  administrativeInstitutionStaff
  propertyOrAssetCustodian
  intelligenceOrMilitaryRole
  unresolvedRosterRole
  : RosterRoleClass

record RosterPersonRole : Set where
  constructor roster-person-role
  field
    rosterPersonName : String
    rosterRole : RosterRoleClass
    rosterInstitution : String
    rosterSourceStrength : Attribution.SourceStrength
    rosterSourceLocator : String
    scientificAuthorshipClaimedByThisRole : Bool

open RosterPersonRole public

melissaCasiasRole : RosterPersonRole
melissaCasiasRole =
  roster-person-role
    "Melissa Casias"
    administrativeInstitutionStaff
    "Los Alamos National Laboratory"
    Attribution.secondaryReportingOnly
    "CBS News, 2026 identification report; family described her as a LANL administrative assistant"
    false

stevenGarciaRole : RosterPersonRole
stevenGarciaRole =
  roster-person-role
    "Steven Garcia"
    propertyOrAssetCustodian
    "Kansas City National Security Campus"
    Attribution.secondaryReportingOnly
    "KOAT / broader 2026 reporting describes Garcia as a KCNSC property custodian; primary employment record not attached here"
    false

matthewSullivanRole : RosterPersonRole
matthewSullivanRole =
  roster-person-role
    "Matthew Sullivan"
    intelligenceOrMilitaryRole
    "United States Air Force"
    Attribution.secondaryReportingOnly
    "public reporting describes Sullivan as a former Air Force intelligence officer; no scientific-work object is inferred from that role"
    false

------------------------------------------------------------------------
-- Exact anti-reification witnesses for the broader roster.
------------------------------------------------------------------------

melissaRoleDoesNotClaimScientificAuthorship :
  scientificAuthorshipClaimedByThisRole melissaCasiasRole ≡ false
melissaRoleDoesNotClaimScientificAuthorship = refl

stevenRoleDoesNotClaimScientificAuthorship :
  scientificAuthorshipClaimedByThisRole stevenGarciaRole ≡ false
stevenRoleDoesNotClaimScientificAuthorship = refl

matthewRoleDoesNotClaimScientificAuthorship :
  scientificAuthorshipClaimedByThisRole matthewSullivanRole ≡ false
matthewRoleDoesNotClaimScientificAuthorship = refl

record BroaderRosterAttributionBoundary : Set where
  constructor broader-roster-attribution-boundary
  field
    beingInRosterImpliesScientist : Bool
    beingInRosterImpliesScientistIsFalse : beingInRosterImpliesScientist ≡ false

    employmentAtScientificInstitutionImpliesScientificAuthorship : Bool
    employmentAtScientificInstitutionImpliesScientificAuthorshipIsFalse :
      employmentAtScientificInstitutionImpliesScientificAuthorship ≡ false

    securityClearanceImpliesScientificContribution : Bool
    securityClearanceImpliesScientificContributionIsFalse :
      securityClearanceImpliesScientificContribution ≡ false

    roleEvidenceMayStillMatterToSecurityInvestigation : Bool
    roleEvidenceMayStillMatterToSecurityInvestigationIsTrue :
      roleEvidenceMayStillMatterToSecurityInvestigation ≡ true

    scientificWorkGraphAndCaseConnectionGraphAreSeparate : Bool
    scientificWorkGraphAndCaseConnectionGraphAreSeparateIsTrue :
      scientificWorkGraphAndCaseConnectionGraphAreSeparate ≡ true

canonicalBroaderRosterAttributionBoundary : BroaderRosterAttributionBoundary
canonicalBroaderRosterAttributionBoundary =
  broader-roster-attribution-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
