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
  "Dated DBE-letterhead carrier showing Tegnelia acting through the company in 2017. It is not a corporate filing and does not itself identify every owner/member."

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
  "Primary organisational page pays the current displayed DBE title string, but its stale ATA body makes the page temporally mixed. It cannot by itself establish DBE founding date, transfer date, exclusive ownership, 2026 client portfolio, or event-time corporate status."

------------------------------------------------------------------------
-- Conflict / payment state.
------------------------------------------------------------------------

record DBEOwnershipArchaeologyState : Set where
  constructor dbe-ownership-archaeology-state
  field
    tegneliaOwner2011Paid : Bool
    tegneliaCompanyCarrier2017Paid : Bool
    mccaslandCurrentDBEHeadingPaid : Bool
    sameDBEEntityAcrossAllManifestationsPaid : Bool
    mccaslandFounderFromCompanyInceptionPaid : Bool
    ownershipTransferDatePaid : Bool
    eventTime2026CorporateStatusPaid : Bool
    eventTime2026ClientPortfolioPaid : Bool
    nextPrimaryAcquisition : String

open DBEOwnershipArchaeologyState public

canonicalDBEOwnershipArchaeologyState : DBEOwnershipArchaeologyState
canonicalDBEOwnershipArchaeologyState = dbe-ownership-archaeology-state
  true true true false false false false false
  "recover New Mexico corporate filing/history or equivalent primary company record identifying exact DBE entity, formation date, members/managers/ownership changes, and dated McCasland role; only then acquire primary 2025-2026 client/contract carriers"

record DBEAttributionBoundary : Set where
  constructor dbe-attribution-boundary
  field
    currentHeadingRewrites2011Ownership : Bool
    tegnelia2011OwnershipExcludesLaterMcCaslandOwnership : Bool
    sameCompanyLabelProvesSameLegalEntity : Bool
    organisationBiographyEqualsCorporateFiling : Bool
    secondaryClientClaimsPromoteWithoutPrimaryContract : Bool
    datedManifestationsMayGuideCorporateRecordSearch : Bool

open DBEAttributionBoundary public

canonicalDBEAttributionBoundary : DBEAttributionBoundary
canonicalDBEAttributionBoundary = dbe-attribution-boundary
  false false false false false true
