module DASHI.Physics.Foundations.RFSensingProofSearchSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Physics.Foundations.PhasedArrayRFSensingSourceAtlasExact as Sources

------------------------------------------------------------------------
-- Consumer/SDR examples are acquisition leads, not promoted technical facts.
-- Reuse the exact source-atlas objects so source identity is not duplicated.
------------------------------------------------------------------------

record AcquisitionLead : Set where
  constructor acquisition-lead
  field
    source : Attribution.AttributedSource
    observedCapabilityClass : String
    primarySourceAcquisitionStillRequired : Bool
    primarySourceAcquisitionStillRequiredIsTrue :
      primarySourceAcquisitionStillRequired ≡ true
    demonstrationAloneClosesTechnicalLeaf : Bool
    demonstrationAloneClosesTechnicalLeafIsFalse :
      demonstrationAloneClosesTechnicalLeaf ≡ false
open AcquisitionLead public

hackadayConsumerWifiSource : Attribution.AttributedSource
hackadayConsumerWifiSource = Sources.hackadayConsumerWifiLead

hackadaySDRPassiveRadarSource : Attribution.AttributedSource
hackadaySDRPassiveRadarSource = Sources.hackadaySDRPassiveRadarLead

hackadayPhasedArrayThroughWallSource : Attribution.AttributedSource
hackadayPhasedArrayThroughWallSource = Sources.hackadayPhasedArrayThroughWallLead

hackadayConsumerWifiLead : AcquisitionLead
hackadayConsumerWifiLead =
  acquisition-lead hackadayConsumerWifiSource
    "commodity Wi-Fi CSI person/motion sensing"
    true refl false refl

hackadaySDRPassiveRadarLead : AcquisitionLead
hackadaySDRPassiveRadarLead =
  acquisition-lead hackadaySDRPassiveRadarSource
    "low-cost SDR passive radar"
    true refl false refl

hackadayPhasedArrayThroughWallLead : AcquisitionLead
hackadayPhasedArrayThroughWallLead =
  acquisition-lead hackadayPhasedArrayThroughWallSource
    "low-cost phased-array through-wall radar demonstration"
    true refl false refl

------------------------------------------------------------------------
-- Use the existing proof-search admission surface.  Discovery can propose a
-- route, but cannot self-certify truth or authority.
------------------------------------------------------------------------

data RFSearchAxis : Set where
  commodityCSIHardwareAxis : RFSearchAxis
  passiveSDRReceiverAxis : RFSearchAxis
  phasedArrayThroughWallAxis : RFSearchAxis
  primaryPaperLineageAxis : RFSearchAxis

consumerWifiAxisProposal : Discovery.AxisProposal RFSearchAxis
consumerWifiAxisProposal = Discovery.axis-proposal
  commodityCSIHardwareAxis
  Discovery.externalKnowledgeComparison
  "consumer-grade RF sensing implementation family"
  "which observation families are demonstrated with commodity hardware?"
  "Hackaday ESP32 CSI lead plus existing CSI primary/survey sources"
  "community lead does not pay the general technical theorem"
  "observation capability does not create surveillance authority"

sdrAxisProposal : Discovery.AxisProposal RFSearchAxis
sdrAxisProposal = Discovery.axis-proposal
  passiveSDRReceiverAxis
  Discovery.externalKnowledgeComparison
  "passive-radar receiver implementation family"
  "does inexpensive SDR hardware instantiate the passive-observation role?"
  "Hackaday RTL-SDR passive-radar lead"
  "demonstration is an acquisition lead; exact primary lineage remains payable"
  "receiver capability does not identify a target or authorise action"

record RFSearchRoute : Set where
  constructor rf-search-route
  field
    routeAdmission : ProofSearch.RouteAdmission
    consumerWifiProposal : Discovery.AxisProposal RFSearchAxis
    passiveSDRProposal : Discovery.AxisProposal RFSearchAxis
    proofSearchSelfCertifiesSourceTruth : Bool
    proofSearchSelfCertifiesSourceTruthIsFalse :
      proofSearchSelfCertifiesSourceTruth ≡ false
    communityLeadMayClosePrimaryLeaf : Bool
    communityLeadMayClosePrimaryLeafIsFalse :
      communityLeadMayClosePrimaryLeaf ≡ false
open RFSearchRoute public

canonicalRFSearchRoute : RFSearchRoute
canonicalRFSearchRoute = rf-search-route
  ProofSearch.canonicalRouteAdmission
  consumerWifiAxisProposal
  sdrAxisProposal
  false refl
  false refl

------------------------------------------------------------------------
-- Reuse the repository attribution-snowball invariant directly.
------------------------------------------------------------------------

consumerWifiSourceSnowballReceipt :
  SnowballAttribution.SourceRoleSnowballReceipt hackadayConsumerWifiSource
consumerWifiSourceSnowballReceipt =
  SnowballAttribution.canonicalSourceRoleSnowballReceipt hackadayConsumerWifiSource

sdrSourceSnowballReceipt :
  SnowballAttribution.SourceRoleSnowballReceipt hackadaySDRPassiveRadarSource
sdrSourceSnowballReceipt =
  SnowballAttribution.canonicalSourceRoleSnowballReceipt hackadaySDRPassiveRadarSource

record RFAttributionBoundary : Set where
  constructor rf-attribution-boundary
  field
    sourceKindRetainedAcrossSnowball : Bool
    sourceKindRetainedAcrossSnowballIsTrue :
      sourceKindRetainedAcrossSnowball ≡ true
    formalisationRelationshipRetainedAcrossSnowball : Bool
    formalisationRelationshipRetainedAcrossSnowballIsTrue :
      formalisationRelationshipRetainedAcrossSnowball ≡ true
    communityDemonstrationEqualsPrimaryAuthority : Bool
    communityDemonstrationEqualsPrimaryAuthorityIsFalse :
      communityDemonstrationEqualsPrimaryAuthority ≡ false
    consumerHardwareEqualsPurposeBuiltRFImager : Bool
    consumerHardwareEqualsPurposeBuiltRFImagerIsFalse :
      consumerHardwareEqualsPurposeBuiltRFImager ≡ false
    passiveSDREqualsPhasedArrayDirectionFinder : Bool
    passiveSDREqualsPhasedArrayDirectionFinderIsFalse :
      passiveSDREqualsPhasedArrayDirectionFinder ≡ false
open RFAttributionBoundary public

canonicalRFAttributionBoundary : RFAttributionBoundary
canonicalRFAttributionBoundary =
  rf-attribution-boundary true refl true refl false refl false refl false refl
