module DASHI.Cognition.EpsteinCBPBorderAccessInvestigationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- EPSTEIN / CBP BORDER-ACCESS INVESTIGATION
--
-- Released DOJ files and subsequent reporting document a federal investigation
-- into Epstein's relationships with CBP personnel in St Thomas.  This owner
-- distinguishes access/favour allegations, investigation/subpoena status,
-- officer contact, knowledge of trafficking, and criminal liability.
------------------------------------------------------------------------

data BorderEdgeKind : Set where
  stThomasCBPContact : BorderEdgeKind
  expeditedInspectionAllegation : BorderEdgeKind
  friendlyOfficerSchedulingAllegation : BorderEdgeKind
  giftsRidesFavours : BorderEdgeKind
  islandVisitByOfficer : BorderEdgeKind
  fbiDhsOIGInvestigation : BorderEdgeKind
  subpoenasForAdditionalOfficers : BorderEdgeKind
  noOfficerCharges : BorderEdgeKind
  traffickingKnowledgeUnpaid : BorderEdgeKind

record BorderReceipt : Set where
  constructor border-receipt
  field
    edgeKind : BorderEdgeKind
    sourceIdentity : String
    sourceRole : String
    boundedFinding : String
    relationPaid : Bool
    criminalCorruptionEstablished : Bool
    traffickingKnowledgePaid : Bool
open BorderReceipt public

contactReceipt : BorderReceipt
contactReceipt = border-receipt
  stThomasCBPContact
  "DOJ-released CBP/FBI materials as reviewed by Guardian, 2026-02-19"
  "released investigative records / high-quality reporting"
  "Records reviewed in 2026 show Epstein interacted with multiple CBP officers associated with St Thomas airport and related travel."
  true false false

accessReceipt : BorderReceipt
accessReceipt = border-receipt
  expeditedInspectionAllegation
  "DOJ-released investigative materials, 2026"
  "federal investigative allegation"
  "Investigative records contain allegations that Epstein received unusually expedited or preferential inspection treatment from at least one CBP officer."
  true false false

scheduleReceipt : BorderReceipt
scheduleReceipt = border-receipt
  friendlyOfficerSchedulingAllegation
  "DOJ-released investigative materials, 2026"
  "federal investigative allegation"
  "Records contain allegations that Epstein or staff were informed about which officers would be on duty or otherwise assisted with travel-screening logistics."
  true false false

giftsReceipt : BorderReceipt
giftsReceipt = border-receipt
  giftsRidesFavours
  "DOJ-released investigative materials, 2026"
  "federal investigative record"
  "Released records describe meals, rides, financial advice or other favours exchanged in the course of Epstein's relationships with certain border officers."
  true false false

islandVisitReceipt : BorderReceipt
islandVisitReceipt = border-receipt
  islandVisitByOfficer
  "DOJ-released investigative materials / Guardian 2026"
  "federal investigative record"
  "At least one investigated officer acknowledged visiting Epstein's island while denying knowledge of trafficking or abuse."
  true false false

investigationReceipt : BorderReceipt
investigationReceipt = border-receipt
  fbiDhsOIGInvestigation
  "DOJ-released FBI/CBP materials, 2026"
  "federal investigation"
  "FBI and DHS oversight/investigative authorities examined Epstein's relationship with at least one St Thomas CBP officer over an extended period."
  true false false

subpoenaReceipt : BorderReceipt
subpoenaReceipt = border-receipt
  subpoenasForAdditionalOfficers
  "DOJ-released investigative materials / Guardian 2026"
  "grand-jury/investigative process"
  "Investigators issued subpoenas related to three additional CBP officers at St Thomas airport."
  true false false

noChargesReceipt : BorderReceipt
noChargesReceipt = border-receipt
  noOfficerCharges
  "Guardian review of released federal records, 2026"
  "case-outcome boundary"
  "The investigation did not result in criminal charges against the CBP officers identified in the released record."
  true false false

knowledgeBoundaryReceipt : BorderReceipt
knowledgeBoundaryReceipt = border-receipt
  traffickingKnowledgeUnpaid
  "current released-record boundary"
  "absence-of-promotion boundary"
  "Current reviewed records do not establish that the identified CBP officers knew of or participated in Epstein's trafficking crimes."
  true false false

record BorderAccessBoundary : Set where
  constructor border-access-boundary
  field
    officerContactPaid : Bool
    preferentialAccessAllegationsPaid : Bool
    federalInvestigationPaid : Bool
    additionalOfficerSubpoenasPaid : Bool
    criminalChargesPaid : Bool
    traffickingKnowledgePaid : Bool
    institutionalCBPComplicityPaid : Bool
open BorderAccessBoundary public

canonicalBorderAccessBoundary : BorderAccessBoundary
canonicalBorderAccessBoundary =
  border-access-boundary true true true true false false false

data PreferentialAccessImpliesTraffickingKnowledge : Set where
data OfficerRelationshipImpliesAgencyComplicity : Set where
data InvestigationImpliesCorruptionConviction : Set where
data NoChargesImpliesNoMisconduct : Set where

accessDoesNotCreateTraffickingKnowledge : PreferentialAccessImpliesTraffickingKnowledge → ⊥
accessDoesNotCreateTraffickingKnowledge ()

officerRelationshipDoesNotCreateAgencyComplicity : OfficerRelationshipImpliesAgencyComplicity → ⊥
officerRelationshipDoesNotCreateAgencyComplicity ()

investigationDoesNotCreateConviction : InvestigationImpliesCorruptionConviction → ⊥
investigationDoesNotCreateConviction ()

noChargesDoesNotCreateNoMisconduct : NoChargesImpliesNoMisconduct → ⊥
noChargesDoesNotCreateNoMisconduct ()
