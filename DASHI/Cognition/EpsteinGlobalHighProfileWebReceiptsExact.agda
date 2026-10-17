module DASHI.Cognition.EpsteinGlobalHighProfileWebReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- GLOBAL HIGH-PROFILE / INSTITUTIONAL WEB-VERIFIED RECEIPTS
--
-- These records encode externally documented relationship/institutional facts
-- discovered in the 2026 web pass. Source descriptions remain explicit and
-- edge-local. A receipt below establishes only its typed relation; it does not
-- establish wrongdoing, scientific control, coordination with other hubs, or
-- knowledge of Epstein's crimes unless separately sourced.
------------------------------------------------------------------------

data GlobalReceiptKind : Set where
  repeatedMeeting : GlobalReceiptKind
  philanthropicBrokerage : GlobalReceiptKind
  institutionalDonation : GlobalReceiptKind
  institutionalVisit : GlobalReceiptKind
  hiddenOrRestrictedDonationHandling : GlobalReceiptKind
  scienceFundingContext : GlobalReceiptKind
  institutionalEmploymentConsequence : GlobalReceiptKind
  nonprofitDonation : GlobalReceiptKind
  historicalCorporateGenealogy : GlobalReceiptKind
  familyRelationship : GlobalReceiptKind

record GlobalWebReceipt : Set where
  constructor global-web-receipt
  field
    fromLabel toLabel : String
    kind : GlobalReceiptKind
    sourceDescription : String
    primaryOrInstitutionalSource : Bool
    relationEstablished : Bool
    wrongdoingEstablished : Bool
    coordinationWithOtherHubsEstablished : Bool
open GlobalWebReceipt public

------------------------------------------------------------------------
-- Gates Foundation / Bill Gates lane.
------------------------------------------------------------------------

gatesFoundationEngagementReceipt : GlobalWebReceipt
gatesFoundationEngagementReceipt = global-web-receipt
  "Gates Foundation / Bill Gates" "Jeffrey Epstein"
  philanthropicBrokerage
  "Gates Foundation 21 July 2026 external-review release: foundation engagement with Epstein from 2011-2014 centred on a proposed donor-advised public-health fund and on IPI, which Epstein introduced to the Chair; IPI later received foundation funding after internal diligence."
  true true false false

gatesApproxThirtyMeetingsReceipt : GlobalWebReceipt
gatesApproxThirtyMeetingsReceipt = global-web-receipt
  "Bill Gates / Gates Foundation staff" "Jeffrey Epstein"
  repeatedMeeting
  "AP 2026 report on WilmerHale review: about 30 meetings involving Gates/foundation staff and Epstein between 2011 and 2014, including Epstein's townhouse and Gates Foundation campus."
  false true false false

record GatesFoundationBoundary : Set where
  constructor gates-foundation-boundary
  field
    repeatedEngagementEstablished : Bool
    philanthropicBrokerageEstablished : Bool
    foundationPaidEpsteinEstablished : Bool
    criminalParticipationEstablished : Bool
open GatesFoundationBoundary public

canonicalGatesFoundationBoundary : GatesFoundationBoundary
canonicalGatesFoundationBoundary =
  gates-foundation-boundary true true false false

------------------------------------------------------------------------
-- MIT / Media Lab lane.
------------------------------------------------------------------------

mitDonationReceipt : GlobalWebReceipt
mitDonationReceipt = global-web-receipt
  "Jeffrey Epstein" "MIT"
  institutionalDonation
  "MIT 10 January 2020 fact-finding: 10 Epstein donations totaling USD 850,000 between 2002 and 2017; nine gifts followed the 2008 conviction."
  true true false false

mitVisitReceipt : GlobalWebReceipt
mitVisitReceipt = global-web-receipt
  "Jeffrey Epstein" "MIT campus"
  institutionalVisit
  "MIT fact-finding: Epstein visited MIT nine times between 2013 and 2017."
  true true false false

mitRestrictedHandlingReceipt : GlobalWebReceipt
mitRestrictedHandlingReceipt = global-web-receipt
  "MIT administrators / Media Lab" "Epstein donations"
  hiddenOrRestrictedDonationHandling
  "MIT fact-finding and Executive Committee statement: post-conviction donations were approved under an informal framework; some handling sought small/unpublicized or anonymous treatment, limiting visibility in donor records."
  true true false false

record MITInstitutionalBoundary : Set where
  constructor mit-institutional-boundary
  field
    tenDonations850kEstablished : Bool
    nineCampusVisitsEstablished : Bool
    postConvictionDonationHandlingEstablished : Bool
    institutionalRelationshipEstablished : Bool
    criminalParticipationEstablished : Bool
open MITInstitutionalBoundary public

canonicalMITInstitutionalBoundary : MITInstitutionalBoundary
canonicalMITInstitutionalBoundary =
  mit-institutional-boundary true true true true false

------------------------------------------------------------------------
-- Harvard / scientific-patronage lane.
------------------------------------------------------------------------

natureScienceFundingContextReceipt : GlobalWebReceipt
natureScienceFundingContextReceipt = global-web-receipt
  "Jeffrey Epstein" "scientific research"
  scienceFundingContext
  "Nature editorial, 4 March 2026: Epstein was a significant donor to research; mathematical biology and artificial intelligence were among fields he funded; correspondence showed some scientists maintained links after conviction."
  false true false false

nowakInstitutionalConsequenceReceipt : GlobalWebReceipt
nowakInstitutionalConsequenceReceipt = global-web-receipt
  "Harvard University" "Martin Nowak"
  institutionalEmploymentConsequence
  "Nature, 25 February 2026: Harvard confirmed Martin Nowak was placed on leave during an investigation into his association with Epstein."
  false true false false

summersInstitutionalConsequenceReceipt : GlobalWebReceipt
summersInstitutionalConsequenceReceipt = global-web-receipt
  "Harvard University" "Lawrence Summers"
  institutionalEmploymentConsequence
  "Nature, 25 February 2026: Harvard confirmed Summers would leave his academic position and resign as co-director of the Mossavar-Rahmani Center in connection with its Epstein-document review."
  false true false false

------------------------------------------------------------------------
-- Ghislaine Maxwell / TerraMar lane.
------------------------------------------------------------------------

terramarEpsteinFoundationDonationReceipt : GlobalWebReceipt
terramarEpsteinFoundationDonationReceipt = global-web-receipt
  "Epstein Interests Foundation" "TerraMar Project Inc"
  nonprofitDonation
  "US v Maxwell court exhibit 97-15, filed 14 December 2020: records a USD 57,000 Epstein Interests Foundation donation to TerraMar Project Inc for the financial year ending 21 January 2013."
  true true false false

record TerraMarBoundary : Set where
  constructor terramar-boundary
  field
    ghislaineFoundedTerraMar : Bool
    epsteinFoundationDonation57kEstablished : Bool
    donationImpliesPublishingControl : Bool
    donationImpliesScientificControl : Bool
open TerraMarBoundary public

canonicalTerraMarBoundary : TerraMarBoundary
canonicalTerraMarBoundary = terramar-boundary true true false false

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data MeetingImpliesWrongdoing : Set where
data DonationImpliesScientificControl : Set where
data InstitutionalFailureImpliesUniversalCoordination : Set where
data TerraMarDonationImpliesElsevierControl : Set where

meetingDoesNotImplyWrongdoing : MeetingImpliesWrongdoing → ⊥
meetingDoesNotImplyWrongdoing ()

donationDoesNotImplyScientificControl : DonationImpliesScientificControl → ⊥
donationDoesNotImplyScientificControl ()

institutionalFailureDoesNotImplyUniversalCoordination :
  InstitutionalFailureImpliesUniversalCoordination → ⊥
institutionalFailureDoesNotImplyUniversalCoordination ()

terramarDonationDoesNotImplyElsevierControl : TerraMarDonationImpliesElsevierControl → ⊥
terramarDonationDoesNotImplyElsevierControl ()
