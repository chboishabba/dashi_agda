module DASHI.Culture.McCaslandDBEAttributionArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MCCASLAND / DBE CONSULTING ATTRIBUTION ARCHAEOLOGY
--
-- Thin provenance owner.  This does not promote a corporate ownership timeline
-- from inconsistent public labels.  It preserves distinct dated manifestations
-- and routes the next acquisition to an actual corporate-status/transfer record.
------------------------------------------------------------------------

data DBESourceClass : Set where
  primaryGovernmentRecord primaryLetterheadRecord primaryOrganisationPage secondaryLead : DBESourceClass

record DBEAttributionManifestation : Set where
  constructor dbe-attribution-manifestation
  field
    sourceDate : String
    sourceClass : DBESourceClass
    sourceObject : String
    sourceLink : String
    attributedPerson : String
    attributedRole : String
    stableIdentifier : String
    personQid : String
    deweyTraversal : String
    boundedReading : String

open DBEAttributionManifestation public

stateDepartment2011Tegnelia : DBEAttributionManifestation
stateDepartment2011Tegnelia = dbe-attribution-manifestation
  "2011-07"
  primaryGovernmentRecord
  "U.S. Department of State notice: Meeting of the International Security Advisory Board"
  "https://2009-2017.state.gov/r/pa/prs/ps/2011/07/168130.htm"
  "James A. Tegnelia"
  "President and Owner of DBE Consulting LLC"
  "State Department PRN 2011/1166"
  "unresolvedQid"
  "650 Management / consulting traversal only"
  "Primary government carrier paying Tegnelia's 2011 DBE President/Owner attribution. It does not determine later ownership or exclude a later transfer/reorganisation involving McCasland."

fec2014TegneliaAddress : DBEAttributionManifestation
fec2014TegneliaAddress = dbe-attribution-manifestation
  "2014-05-27"
  primaryGovernmentRecord
  "Federal Election Commission Schedule A itemized receipt naming James Tegnelia"
  "https://docquery.fec.gov/pdf/904/14020503904/14020503904.pdf"
  "James Tegnelia"
  "FEC contributor mailing address 11039 Bridgepointe NE, Albuquerque, NM 87111"
  "FEC filing 14020503904; Transaction ID C10047764"
  "unresolvedQid"
  "324 Political process record / 650 management traversal only"
  "Primary federal filing pays James Tegnelia's personal/contributor mailing address at 11039 Bridgepointe NE in 2014. Because the later DBE letterhead uses the same address, that letterhead address cannot by itself be promoted to an independently established corporate office."

tegneliaLetterhead2017 : DBEAttributionManifestation
tegneliaLetterhead2017 = dbe-attribution-manifestation
  "2017-09-01"
  primaryLetterheadRecord
  "DBE CONSULTING LLC letter supporting UNM MS Global and National Security"
  "https://www.nmt.edu/gradstudies/nmcgd/docs/UNM%20MS%20Global%20and%20National%20Security.pdf"
  "Jim Tegnelia"
  "DBE Consulting LLC signatory; Chair Army Science Board; UNM external advisory role"
  "DBE CONSULTING LLC, 11039 Bridgepointe NE, Albuquerque, NM 87111"
  "unresolvedQid"
  "650 Management / consulting traversal only"
  "Dated DBE-letterhead carrier showing Tegnelia acting through the company in 2017. The same 11039 Bridgepointe NE address is independently paid as Tegnelia's 2014 FEC contributor mailing address, so this source pays a DBE correspondence address but not a distinct corporate-office identity."

kirtlandCurrentTegnelia : DBEAttributionManifestation
kirtlandCurrentTegnelia = dbe-attribution-manifestation
  "current page observed 2026-09"
  primaryOrganisationPage
  "Kirtland Partnership Committee board profile: Jim Tegnelia"
  "https://kpcnm.org/jim-tegnelia/"
  "James A. Tegnelia"
  "heading: Founder, Owner, and President, DBE Consulting LLC"
  "Kirtland Partnership Committee board profile"
  "unresolvedQid"
  "650 Management / consulting traversal only"
  "Current organisational page independently assigns the same Founder/Owner/President DBE heading to Tegnelia. This creates a live role-label collision with the McCasland profile and therefore weakens the heading as an ownership-history carrier."

kirtlandCurrentMcCasland : DBEAttributionManifestation
kirtlandCurrentMcCasland = dbe-attribution-manifestation
  "current page observed 2026-09"
  primaryOrganisationPage
  "Kirtland Partnership Committee board profile: Neil McCasland, PhD"
  "https://kpcnm.org/board/neil-mccasland/"
  "William Neil McCasland"
  "heading: Founder, Owner, and President, DBE Consulting LLC; body still calls him ATA Director of Technology"
  "Kirtland Partnership Committee board profile"
  "unresolvedQid"
  "650 Management / consulting traversal only"
  "Primary organisational page pays the current displayed DBE title string, but its stale ATA body and duplicate DBE Founder/Owner/President heading on Tegnelia's Kirtland profile make the page temporally and attributionally mixed. It cannot by itself establish DBE founding date, transfer date, exclusive ownership, 2026 client portfolio, or event-time corporate status."

federalDOTAtlantaDBE : DBEAttributionManifestation
federalDOTAtlantaDBE = dbe-attribution-manifestation
  "current U.S. DOT DOCR DBE database surface observed 2026-09"
  primaryGovernmentRecord
  "U.S. Department of Transportation DOCR DBE Database for Decision Appeals: DBE Consulting, LLC"
  "https://www.transportation.gov/disadvantaged-business-enterprise/dbe-consulting-llc"
  "Kimberly Griffin"
  "Company Owner; applicant type Disadvantaged Business Enterprise; Atlanta, Georgia"
  "U.S. DOT DOCR DBE database record; 325 Centennial Park Drive, Suite 1366, Atlanta, GA 30313"
  "unresolvedQid"
  "338.7 Enterprises / 650 Management traversal only"
  "Primary federal government carrier paying existence, owner name and Atlanta address for a DBE Consulting, LLC distinct in place/person from the Albuquerque DBE attributed to Tegnelia. It is a negative-control entity carrier only and does not identify the New Mexico legal entity or its ownership history."

------------------------------------------------------------------------
-- Address-manifestation boundary.
------------------------------------------------------------------------

record DBEAddressReuseState : Set where
  constructor dbe-address-reuse-state
  field
    address : String
    fecPersonAddressPaid : Bool
    laterDBELetterheadAddressPaid : Bool
    sameAddressAcrossManifestationsPaid : Bool
    addressProvesSeparateCorporateOffice : Bool
    addressProvesLegalEntityIdentity : Bool
    addressMayGuideRegistrySearch : Bool

open DBEAddressReuseState public

canonicalDBEAddressReuseState : DBEAddressReuseState
canonicalDBEAddressReuseState = dbe-address-reuse-state
  "11039 Bridgepointe NE, Albuquerque, NM 87111"
  true true true false false true

------------------------------------------------------------------------
-- Same-label company collision control.
------------------------------------------------------------------------

record SameLabelCompanyCollision : Set where
  constructor same-label-company-collision
  field
    candidateLabel : String
    candidateSource : String
    candidateLink : String
    candidateJurisdictionOrPlace : String
    candidateBusinessDomain : String
    targetLabel : String
    targetPaidCarrier : String
    sameLegalEntityPaid : Bool
    mayMergeByCompanyName : Bool
    usefulAsNegativeControl : Bool

open SameLabelCompanyCollision public

atlantaDBEConsultingCollision : SameLabelCompanyCollision
atlantaDBEConsultingCollision = same-label-company-collision
  "DBE Consulting, LLC"
  "U.S. Department of Transportation DOCR DBE Database for Decision Appeals"
  "https://www.transportation.gov/disadvantaged-business-enterprise/dbe-consulting-llc"
  "Atlanta, Georgia; 325 Centennial Park Drive, Suite 1366"
  "Disadvantaged Business Enterprise applicant; owner Kimberly Griffin"
  "DBE Consulting LLC, Albuquerque, New Mexico"
  "State Department PRN 2011/1166 naming James A. Tegnelia as President/Owner; 2017 Albuquerque DBE letterhead at 11039 Bridgepointe NE"
  false false true

------------------------------------------------------------------------
-- Conflict / payment state.
------------------------------------------------------------------------

record DBEOwnershipArchaeologyState : Set where
  constructor dbe-ownership-archaeology-state
  field
    tegneliaOwner2011Paid : Bool
    tegneliaAddress2014Paid : Bool
    tegneliaCompanyCarrier2017Paid : Bool
    tegneliaCurrentFounderHeadingPaid : Bool
    mccaslandCurrentDBEHeadingPaid : Bool
    currentKirtlandRoleLabelCollisionPaid : Bool
    unrelatedSameLabelCompanyLocated : Bool
    unrelatedSameLabelCompanyPrimaryGovernmentPaid : Bool
    sameDBEEntityAcrossAllManifestationsPaid : Bool
    mccaslandFounderFromCompanyInceptionPaid : Bool
    ownershipTransferDatePaid : Bool
    eventTime2026CorporateStatusPaid : Bool
    eventTime2026ClientPortfolioPaid : Bool
    nextPrimaryAcquisition : String

open DBEOwnershipArchaeologyState public

canonicalDBEOwnershipArchaeologyState : DBEOwnershipArchaeologyState
canonicalDBEOwnershipArchaeologyState = dbe-ownership-archaeology-state
  true true true true true true true true false false false false false
  "recover New Mexico corporate filing/history or equivalent primary government/vendor record identifying the exact Albuquerque DBE entity, jurisdictional/entity identifier, formation date, members/managers/ownership changes and dated McCasland role; treat 11039 Bridgepointe NE as a paid Tegnelia/DBE correspondence coordinate rather than an independently established corporate office; only then acquire primary 2025-2026 client/contract carriers"

record DBEAttributionBoundary : Set where
  constructor dbe-attribution-boundary
  field
    currentHeadingRewrites2011Ownership : Bool
    tegnelia2011OwnershipExcludesLaterMcCaslandOwnership : Bool
    sameCompanyLabelProvesSameLegalEntity : Bool
    organisationBiographyEqualsCorporateFiling : Bool
    duplicateFounderHeadingsCanBothBeReadAsLiteralCorporateHistory : Bool
    unrelatedSameLabelCompanyMayBeMergedByName : Bool
    federalDBERecordIdentifiesAlbuquerqueEntity : Bool
    sharedPersonalAndLetterheadAddressProvesSeparateOffice : Bool
    secondaryClientClaimsPromoteWithoutPrimaryContract : Bool
    datedManifestationsMayGuideCorporateRecordSearch : Bool

open DBEAttributionBoundary public

canonicalDBEAttributionBoundary : DBEAttributionBoundary
canonicalDBEAttributionBoundary = dbe-attribution-boundary
  false false false false false false false false false true
