module DASHI.Cognition.OracleEllisonTranscriptClaimAtlasExact where

------------------------------------------------------------------------
-- ORACLE / ELLISON / CHINA / ISRAEL TRANSCRIPT CLAIM ATLAS
--
-- Case-specific extraction only. A transcript claim is not source payment.
-- The carrier keeps literal claim identity separate from evidence status,
-- interpretation, causal explanation, motive and controller identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Claim identity.
------------------------------------------------------------------------

data TranscriptClaim : Set where
  netanyahuSayeretService : TranscriptClaim
  netanyahuSayeretControlWorldview : TranscriptClaim
  netanyahuPermanentThreatMaintenanceMotive : TranscriptClaim
  ellisonFIDFDonation : TranscriptClaim
  ellisonNetanyahuReportedRelationshipActivity : TranscriptClaim
  ellisonImmortalityMotive : TranscriptClaim
  oracleChinaPoliceGoldenShield : TranscriptClaim
  oracleRafaelDefenseIntegration : TranscriptClaim
  oracleDeclaredDefenseNationalSecurityOrientation : TranscriptClaim
  oracleNimbusPrimeCloudProvider : TranscriptClaim
  oracleWritesIsraeliSecurityBlueprint : TranscriptClaim
  commonControllerFromSharedVendor : TranscriptClaim

claimLabel : TranscriptClaim → String
claimLabel netanyahuSayeretService =
  "Benjamin Netanyahu served in Sayeret Matkal"
claimLabel netanyahuSayeretControlWorldview =
  "Sayeret Matkal trained Netanyahu to treat politics and human behaviour as systems to control"
claimLabel netanyahuPermanentThreatMaintenanceMotive =
  "Netanyahu intentionally maintains permanent security threats in order to remain in power"
claimLabel ellisonFIDFDonation =
  "Larry Ellison made a major donation to Friends of the IDF"
claimLabel ellisonNetanyahuReportedRelationshipActivity =
  "Public reporting documents repeated Ellison-Netanyahu relationship activity, including trial-witness, Lanai and reported legal-intervention surfaces"
claimLabel ellisonImmortalityMotive =
  "Larry Ellison is motivated by technological immortality / ghost-in-the-machine aspirations"
claimLabel oracleChinaPoliceGoldenShield =
  "Oracle products were supplied into PRC police Golden Shield upgrade infrastructure"
claimLabel oracleRafaelDefenseIntegration =
  "RAFAEL IMILITE and FIRE WEAVER are integrated with Oracle Cloud Infrastructure"
claimLabel oracleDeclaredDefenseNationalSecurityOrientation =
  "Oracle explicitly positions its cloud/AI business as supporting defense and allied national-security missions"
claimLabel oracleNimbusPrimeCloudProvider =
  "Oracle is a winning prime cloud provider for Project Nimbus"
claimLabel oracleWritesIsraeliSecurityBlueprint =
  "Oracle writes the blueprint for Israel's surveillance/security system"
claimLabel commonControllerFromSharedVendor =
  "Use of the same vendor in two state systems establishes a common controller"

------------------------------------------------------------------------
-- Source roles. These are provenance coordinates only.
------------------------------------------------------------------------

data SourceRole : Set where
  officialBiography : SourceRole
  donorEventReporting : SourceRole
  relationshipReporting : SourceRole
  corporatePrimaryAnnouncement : SourceRole
  governmentProcurementRecord : SourceRole
  courtTenderReporting : SourceRole
  investigativeReporting : SourceRole
  legislativeCommissionSummary : SourceRole
  transcriptInterpretation : SourceRole

data SourceIdentity : Set where
  israelGovernmentNetanyahuBiography : SourceIdentity
  friendsIDFEllison2017Record : SourceIdentity
  timesOfIsraelEllisonNetanyahuRelationshipReporting : SourceIdentity
  oracleRafael2024Announcement : SourceIdentity
  oracleDefenseEcosystem2025Announcement : SourceIdentity
  israelNimbusProcurementRecord : SourceIdentity
  oracleNimbusTenderChallengeReporting : SourceIdentity
  associatedPressChinaSurveillance2025 : SourceIdentity
  ceccChinaMonitor : SourceIdentity
  transcript20261002 : SourceIdentity

sourceRole : SourceIdentity → SourceRole
sourceRole israelGovernmentNetanyahuBiography = officialBiography
sourceRole friendsIDFEllison2017Record = donorEventReporting
sourceRole timesOfIsraelEllisonNetanyahuRelationshipReporting = relationshipReporting
sourceRole oracleRafael2024Announcement = corporatePrimaryAnnouncement
sourceRole oracleDefenseEcosystem2025Announcement = corporatePrimaryAnnouncement
sourceRole israelNimbusProcurementRecord = governmentProcurementRecord
sourceRole oracleNimbusTenderChallengeReporting = courtTenderReporting
sourceRole associatedPressChinaSurveillance2025 = investigativeReporting
sourceRole ceccChinaMonitor = legislativeCommissionSummary
sourceRole transcript20261002 = transcriptInterpretation

sourceLocator : SourceIdentity → String
sourceLocator israelGovernmentNetanyahuBiography =
  "Government of Israel / Benjamin Netanyahu biography; Sayeret Matkal service coordinate"
sourceLocator friendsIDFEllison2017Record =
  "2017 Friends of the IDF gala reporting: Larry Ellison donation USD 16.6 million"
sourceLocator timesOfIsraelEllisonNetanyahuRelationshipReporting =
  "Times of Israel 2020-2021 reporting: Ellison as Netanyahu-trial witness; reported Milchan/Ben Tzur intervention; Netanyahu Lanai stay and reported dinner with Ellison"
sourceLocator oracleRafael2024Announcement =
  "Oracle News, 2024-09-10: Oracle and RAFAEL to Provide Cloud-Based AI Solutions for Defense Missions"
sourceLocator oracleDefenseEcosystem2025Announcement =
  "Oracle News, 2025-06-17: Oracle Launches First-of-its-Kind Defense Ecosystem to Redefine National Security Innovation"
sourceLocator israelNimbusProcurementRecord =
  "Government Procurement Administration, Project Nimbus: AWS and Google chosen cloud providers"
sourceLocator oracleNimbusTenderChallengeReporting =
  "2021 Jerusalem District Court / tender reporting: Oracle challenged its rejection from Project Nimbus; AWS and Google remained the selected providers"
sourceLocator associatedPressChinaSurveillance2025 =
  "Associated Press investigation: U.S. technology and Chinese mass surveillance / Golden Shield"
sourceLocator ceccChinaMonitor =
  "Congressional-Executive Commission on China, China Monitor #1; AP Golden Shield summary"
sourceLocator transcript20261002 =
  "transcript-2026-10-02.srt"

------------------------------------------------------------------------
-- Claim-relative evidence edges.
------------------------------------------------------------------------

data EvidenceRelation : Set where
  directSupport : EvidenceRelation
  corroboratingSupport : EvidenceRelation
  materialCounterevidence : EvidenceRelation
  interpretationOnly : EvidenceRelation

record EvidenceEdge : Set where
  constructor evidence-edge
  field
    source : SourceIdentity
    claim : TranscriptClaim
    relation : EvidenceRelation
    note : String

netanyahuServiceEvidence : EvidenceEdge
netanyahuServiceEvidence = evidence-edge
  israelGovernmentNetanyahuBiography
  netanyahuSayeretService
  directSupport
  "Official biography pays the service antecedent only; it does not pay a political-control psychology."

ellisonDonationEvidence : EvidenceEdge
ellisonDonationEvidence = evidence-edge
  friendsIDFEllison2017Record
  ellisonFIDFDonation
  directSupport
  "Donation relationship is source-paid; downstream policy authorship and motive are not imported."

ellisonNetanyahuRelationshipEvidence : EvidenceEdge
ellisonNetanyahuRelationshipEvidence = evidence-edge
  timesOfIsraelEllisonNetanyahuRelationshipReporting
  ellisonNetanyahuReportedRelationshipActivity
  directSupport
  "The paid proposition is the existence of repeated public reporting about concrete relationship activity. It does not promote those reports into policy control, common ideology, or a psychological motive theorem."

oracleChinaAPEvidence : EvidenceEdge
oracleChinaAPEvidence = evidence-edge
  associatedPressChinaSurveillance2025
  oracleChinaPoliceGoldenShield
  directSupport
  "AP reports Oracle among U.S. firms whose products entered PRC policing / Golden Shield upgrade infrastructure."

oracleChinaCECCEvidence : EvidenceEdge
oracleChinaCECCEvidence = evidence-edge
  ceccChinaMonitor
  oracleChinaPoliceGoldenShield
  corroboratingSupport
  "CECC summarizes the AP investigation and names Oracle in Golden Shield police-system upgrades; CECC summary does not replace AP's underlying investigation."

oracleRafaelEvidence : EvidenceEdge
oracleRafaelEvidence = evidence-edge
  oracleRafael2024Announcement
  oracleRafaelDefenseIntegration
  directSupport
  "Oracle and RAFAEL state that IMILITE and FIRE WEAVER are available on OCI for defense missions."

oracleDefenseOrientationEvidence : EvidenceEdge
oracleDefenseOrientationEvidence = evidence-edge
  oracleDefenseEcosystem2025Announcement
  oracleDeclaredDefenseNationalSecurityOrientation
  directSupport
  "Oracle's own announcement explicitly describes a global Defense Ecosystem intended to strengthen U.S. and allied national security and route defense innovators through Oracle cloud/AI delivery channels. This pays declared corporate posture, not control of any particular sovereign security system."

oracleNimbusSelectionCounterevidence : EvidenceEdge
oracleNimbusSelectionCounterevidence = evidence-edge
  israelNimbusProcurementRecord
  oracleNimbusPrimeCloudProvider
  materialCounterevidence
  "Israeli procurement records identify AWS and Google as the selected public-cloud providers."

oracleNimbusChallengeCounterevidence : EvidenceEdge
oracleNimbusChallengeCounterevidence = evidence-edge
  oracleNimbusTenderChallengeReporting
  oracleNimbusPrimeCloudProvider
  materialCounterevidence
  "Oracle's court challenge documents its position as an unsuccessful bidder rather than a selected Nimbus prime provider."

oracleBlueprintInterpretation : EvidenceEdge
oracleBlueprintInterpretation = evidence-edge
  transcript20261002
  oracleWritesIsraeliSecurityBlueprint
  interpretationOnly
  "The acquired Oracle-Israel evidence pays specific defense integration and an unsuccessful Nimbus bid; it does not establish generic authorship of Israel's security-system blueprint. Nimbus counterevidence is local to the Nimbus-prime-provider claim and does not refute every Oracle-Israel relationship."

netanyahuControlWorldviewInterpretation : EvidenceEdge
netanyahuControlWorldviewInterpretation = evidence-edge
  transcript20261002
  netanyahuSayeretControlWorldview
  interpretationOnly
  "Transcript inference; the service record alone does not establish the claimed training doctrine or resulting worldview."

netanyahuThreatMotiveInterpretation : EvidenceEdge
netanyahuThreatMotiveInterpretation = evidence-edge
  transcript20261002
  netanyahuPermanentThreatMaintenanceMotive
  interpretationOnly
  "Political-motive hypothesis requires evidence beyond policy chronology and political survival incentives."

ellisonImmortalityInterpretation : EvidenceEdge
ellisonImmortalityInterpretation = evidence-edge
  transcript20261002
  ellisonImmortalityMotive
  interpretationOnly
  "Psychological/motive interpretation is not paid by donation, relationship reporting, employment or technology-deployment facts."

------------------------------------------------------------------------
-- Anti-collapse boundary.
------------------------------------------------------------------------

record ClaimAtlasBoundary : Set where
  constructor claim-atlas-boundary
  field
    sourceIdentityImpliesClaimTruth : Bool
    serviceImpliesPoliticalPsychology : Bool
    donationImpliesPolicyAuthorship : Bool
    reportedRelationshipImpliesPolicyControl : Bool
    declaredCorporateDefensePostureImpliesSovereignControl : Bool
    vendorImpliesStateController : Bool
    deploymentImpliesMotive : Bool
    localCounterevidenceRefutesAllRelationships : Bool
    transcriptInterpretationIsSourcePayment : Bool

canonicalClaimAtlasBoundary : ClaimAtlasBoundary
canonicalClaimAtlasBoundary =
  claim-atlas-boundary false false false false false false false false false
