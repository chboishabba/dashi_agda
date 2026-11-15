module DASHI.Law.SensibLawWoogarooPostApprovalPoliticalGasBenefit20261027Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Gas
import DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact as Cumulative

------------------------------------------------------------------------
-- POST-APPROVAL WOOGAROO 2019/8575 CROSS-PR EXACT-SOURCE CONSUMER
--
-- A finite, evidence-gated join across already-merged Springfield gas
-- and Woogaroo cumulative-impact owners. Historical infrastructure
-- proximity is not a present gas connection; political credit is not
-- personal enrichment; a Queensland state lobbying diary is not a
-- federal ministerial lobbying instruction or an EPBC decision record.
-- Separate climate/gas policy source genealogy lives in PR #1251:
-- no imports from an unmerged child branch.
------------------------------------------------------------------------

data SourceGrade : Set where
  governmentOriginal : SourceGrade
  originalPublisherClaim : SourceGrade
  independentNewsLocator : SourceGrade
  thirdPartyIndexOnly : SourceGrade
  originalObjectMissing : SourceGrade

data OrderOfBenefit : Set where
  firstOrderDevelopment : OrderOfBenefit
  secondOrderPoliticalHousing : OrderOfBenefit
  secondOrderPotentialUtilities : OrderOfBenefit
  thirdOrderLandAndNetworkOption : OrderOfBenefit
  thirdOrderInstitutionalPolicy : OrderOfBenefit
  personalFinancialGain : OrderOfBenefit
  improperInfluence : OrderOfBenefit

data EvidenceState : Set where
  datedOriginalPaid : EvidenceState
  attributedStatementPaid : EvidenceState
  historicalOnly : EvidenceState
  boundedAnalyticalHypothesis : EvidenceState
  primarySameObjectOpen : EvidenceState

data ActionState : Set where
  decisionOnApprovalPublished : ActionState
  actualSignedNoticeNotAcquired : ActionState
  statutoryDecisionMakerUnconfirmed : ActionState
  futureGasConnectionUnconfirmed : ActionState
  legalReviewNotEstablished : ActionState

approvalNotice : Source.AttributedSource
approvalNotice = Source.mkNoDOISource
  "National Environmental Protection Agency"
  "EPBC Act Public Portal — all notices, EPBC 2019/8575"
  "EPBC Act Public Portal"
  "15 October 2026"
  "https://epbcpublicportal.environment.gov.au/all-notices/"
  Source.governmentSource
  "Original notice-list record: Decision on approval of action — Approved with conditions, dated 15 October 2026. It does NOT furnish the signed notice, name of signatory, precise conditions, or review filings."
  Source.publicAttribution

finalPDNotice : Source.AttributedSource
finalPDNotice = Source.mkNoDOISource
  "National Environmental Protection Agency"
  "EPBC 2019/8575 final preliminary-documentation public-information notice"
  "EPBC Act Public Portal — section 95B(2) publication"
  "23 July 2026"
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/ed51b5fa-9efb-ee11-9f89-00224892a860/2ab10dab-d681-4911-b881-cc99413f07b6?file=2019-8575-Final-PD.pdf"
  Source.governmentSource
  "One-page original portal publication notice records 1786 public comments, dates 13 February–12 March 2026, and final-PD display 23 July–20 August. The notice is NOT the actual final PD, comment responses, or decision reasons."
  Source.publicAttribution

housingRelease : Source.AttributedSource
housingRelease = Source.mkNoDOISource
  "Murray Watt and Clare O'Neil"
  "Joint media release: Significant milestone achieved in supply of new homes"
  "Australian Government — environment and housing ministers"
  "21 August 2026"
  "https://minister.dcceew.gov.au/watt/media-releases/joint-media-release-significant-milestone-achieved-supply-new-homes"
  Source.governmentSource
  "Original ministerial policy communication reports more than 80000 proposed dwellings previously cleared under national environmental law and the housing-approvals strike team. It predates this 15 October project decision and does not identify 2019/8575 as part of that total."
  Source.publicAttribution

stocklandSpringview : Source.AttributedSource
stocklandSpringview = Source.mkNoDOISource
  "Stockland"
  "Springview future planning / FAQs"
  "Stockland project website"
  "October 2026 access"
  "https://www.stockland.com.au/residential/qld/springview"
  Source.practitionerSource
  "First-party statements: approval acknowledged, private third-party freehold ownership, construction start unknown, ongoing plans/conditions. Proponent developer role must not be turned into land title or a completed housing outcome."
  Source.publicAttribution

historicGasAlliance : Source.AttributedSource
historicGasAlliance = Source.mkNoDOISource
  "Australian Broadcasting Corporation"
  "Development aims to set alternative energy use trend"
  "ABC News"
  "30 April 2004"
  "https://www.abc.net.au/news/2004-04-30/development-aims-to-set-alternative-energy-use/178340"
  Source.newsSource
  "Contemporaneous report and attributed Energex CEO statement regarding Springfield Land Corporation gas/electricity trench alliance and 8000 gas connections. Original 2004 agreement, location-specific connection schedules and current gas asset beneficiaries remain open."
  Source.publicAttribution

santoroQueenslandDiary : Source.AttributedSource
santoroQueenslandDiary = Source.mkNoDOISource
  "Queensland Government — Steven Minnikin"
  "February 2025 ministerial diary"
  "Queensland Cabinet"
  "4 February 2025"
  "https://cabinet.qld.gov.au/ministers-portfolios/assets/diary/current/steven-minnikin/2025/february/Minister-Minnikin-February-2025.pdf"
  Source.governmentSource
  "Original state-government diary records Santo Santoro and Springfield principals at a Lobbyist Introductory Meeting. It establishes attendance, not the meeting content, a Commonwealth EPBC contact, lobbying success, or impropriety."
  Source.publicAttribution

wattInterestsIndex : Source.AttributedSource
wattInterestsIndex = Source.mkNoDOISource
  "OPAX (third-party transcriber of Senate declarations)"
  "Murray Watt — declared interests, 6 October 2026"
  "OPAX index of parliamentary sources"
  "6 October 2026"
  "https://opax.com.au/subject/person/murray-watt"
  Source.newsSource
  "Third-party index indicates a 6 October snapshot, not a full independently checked primary declaration or a post-approval change search. Absence of a named holding in visible rows does not pay a conflict-of-interest clearance."
  Source.publicAttribution

gasReservationRelease : Source.AttributedSource
gasReservationRelease = Source.mkNoDOISource
  "Chris Bowen, Madeleine King and Tim Ayres"
  "Joint media release: Landmark legislation to secure Australian gas"
  "Australian Government"
  "14 October 2026"
  "https://minister.dcceew.gov.au/bowen/media-releases/joint-media-release-landmark-legislation-secure-australian-gas-industry-and-households"
  Source.governmentSource
  "Original contemporaneous policy release announces introduction of domestic gas reservation legislation; an introduced Bill is not an Act, a local gas connection or realised income. Distinct from proposals for an LNG export-value levy."
  Source.publicAttribution

agnIpswichRegistry : Source.AttributedSource
agnIpswichRegistry = Source.mkNoDOISource
  "Australian Energy Market Commission"
  "Queensland: AGN Queensland gas distribution network"
  "AEMC Gas Pipeline Register"
  "October 2026 access"
  "https://www.aemc.gov.au/energy-system/gas/gas-pipeline-register/qld-agn-queensland-gas-distribution-network"
  Source.governmentSource
  "Original regulator register describes Australian Gas Networks ownership and Ipswich service-region coverage; not a specific Springview street-main, meter or contract."
  Source.publicAttribution

allgasNetworkRegistry : Source.AttributedSource
allgasNetworkRegistry = Source.mkNoDOISource
  "Australian Energy Market Commission"
  "Queensland: Allgas gas distribution network"
  "AEMC Gas Pipeline Register"
  "October 2026 access"
  "https://www.aemc.gov.au/energy-system/gas/gas-pipeline-register/qld-allgas-gas-distribution-network"
  Source.governmentSource
  "Original AEMC registry says Allgas Energy now owned by Stonepeak, AGIG operator; March 2026 sale from GDI; southern Brisbane and other service areas. A regional footprint is NOT evidence that EPBC 2019/8575 is connected to Allgas rather than AGN."
  Source.publicAttribution

priorSep2DecisionExtension : Source.AttributedSource
priorSep2DecisionExtension = Source.mkNoDOISource
  "National Environmental Protection Agency — Declan O'Connor-Cox"
  "EPBC 2019/8575 notification of decision-period extension"
  "Original signed section 130(1A) statutory specification"
  "2 September 2026"
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/e04e17b3-a2a6-f111-b8dd-7c1e5263208b/2ab10dab-d681-4911-b881-cc99413f07b6?file=2019-8575-Extension-of-Timeframe.pdf"
  Source.governmentSource
  "Original signed extension by Branch Head Declan O'Connor-Cox, extends decision period to 1 October 2026. Superseded by 25 September specification. This does not identify who ultimately signed approval."
  Source.publicAttribution

latestSep25DecisionExtension : Source.AttributedSource
latestSep25DecisionExtension = Source.mkNoDOISource
  "National Environmental Protection Agency — Mark Hall"
  "EPBC 2019/8575 subsequent notification of decision-period extension"
  "Original signed section 130(1A) statutory specification"
  "25 September 2026"
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/d7e6d9ac-0ebb-f111-aaad-7c1e522b52b7/2ab10dab-d681-4911-b881-cc99413f07b6?file=2019-8575-Extension-of-Timeframe.pdf"
  Source.governmentSource
  "Original signed extension by Acting Branch Head Mark Hall: 11 business days, new decision deadline 16 October 2026; approval public notice dated 15 October. Extension signer is not proven final approval signer."
  Source.publicAttribution

record TimeScopedExtension : Set where
  constructor time-scoped-extension
  field
    originalExtension : Source.AttributedSource
    signedDate : String
    decisionDeadline : String
    signedExtensionNotFinalApproval : Bool
    independenceBoundary : signedExtensionNotFinalApproval ≡ true

open TimeScopedExtension public

september2Extension : TimeScopedExtension
september2Extension = time-scoped-extension
  priorSep2DecisionExtension "2 September 2026" "1 October 2026" true refl

september25Extension : TimeScopedExtension
september25Extension = time-scoped-extension
  latestSep25DecisionExtension "25 September 2026" "16 October 2026" true refl

record ScopedReceipt : Set where
  constructor scoped-receipt
  field
    namedOrder : OrderOfBenefit
    source : Source.AttributedSource
    grade : SourceGrade
    evidentialState : EvidenceState
    supportedScope : String
    missingSameObject : String
    sourceAlonePaysPersonalOrDecisionCausation : Bool
    causationFirewall : sourceAlonePaysPersonalOrDecisionCausation ≡ false

open ScopedReceipt public

developmentRegulatoryGate : ScopedReceipt
developmentRegulatoryGate = scoped-receipt
  firstOrderDevelopment approvalNotice governmentOriginal datedOriginalPaid
  "Commonwealth granted EPBC 2019/8575 with conditions on 15 October 2026; this reduces one regulatory uncertainty, not all construction conditions."
  "Signed instrument, conditions, exact approving officer, enforceable preclearance, land title and contract value."
  false refl

housingNarrativeAlignment : ScopedReceipt
housingNarrativeAlignment = scoped-receipt
  secondOrderPoliticalHousing housingRelease governmentOriginal boundedAnalyticalHypothesis
  "Watt/O'Neil explicitly promoted accelerated EPBC housing approvals before Springview approval; policy alignment is evidenced."
  "Direct dated communication counting Springview in the housing initiative, exact dwellings, employment and affordability commitments."
  false refl

utilityDemandCandidate : ScopedReceipt
utilityDemandCandidate = scoped-receipt
  secondOrderPotentialUtilities historicGasAlliance independentNewsLocator historicalOnly
  "Springfield had a 2004 gas/electricity network-planning alliance; possibility of utility demand follows only as a hypothesis."
  "EPBC 2019/8575 estate lot servicing plan, meters, current connections, distributor, contracted offtake and economic beneficiary."
  false refl

regionalDistributorIdentityFork : ScopedReceipt
regionalDistributorIdentityFork = scoped-receipt
  secondOrderPotentialUtilities agnIpswichRegistry governmentOriginal boundedAnalyticalHypothesis
  "AEMC identifies Ipswich as an AGN Queensland gas network area; a separate Allgas/Stonepeak system covers other southern Brisbane and regional places. Same operator or wider-region marketing does not pay same current site distributor."
  "2019/8575 site-specific asset/mains map, distributor NMI/GPR-like connection identifier or dated distribution quotation, current licence, tariffs and supplier records."
  false refl

landNetworkOptionCandidate : ScopedReceipt
landNetworkOptionCandidate = scoped-receipt
  thirdOrderLandAndNetworkOption stocklandSpringview originalPublisherClaim boundedAnalyticalHypothesis
  "Stockland describes privately owned land and future planned development; any approval-option uplift remains unquantified."
  "Title/beneficial owner and contemporaneous purchase, options, valuations, construction and utility agreements."
  false refl

lobbyingHistory : ScopedReceipt
lobbyingHistory = scoped-receipt
  thirdOrderInstitutionalPolicy santoroQueenslandDiary governmentOriginal datedOriginalPaid
  "One 2025 Queensland ministerial diary meeting between state officials, a registered lobbyist and Springfield principals."
  "Commonwealth Watt or departmental EPBC contact, topic, requests, response and exact decision-sequence receipt."
  false refl

ministerHoldingsAuditOpen : ScopedReceipt
ministerHoldingsAuditOpen = scoped-receipt
  personalFinancialGain wattInterestsIndex thirdPartyIndexOnly primarySameObjectOpen
  "A dated third-party transcription is a locator for Watt's Senate interest form, not evidence of project-linked personal benefit."
  "Official complete Senate form and alterations, counterparty mapping, relevant dates and any legally disclosable conflict record."
  false refl

gasNationalPolicySeparate : ScopedReceipt
gasNationalPolicySeparate = scoped-receipt
  thirdOrderInstitutionalPolicy gasReservationRelease governmentOriginal datedOriginalPaid
  "Domestic gas reservation bill introduced 14 October; distinguish national gas supply policy from local subdivision planning."
  "Proof the Springfield project has a particular connection/offtake or benefited financially from the bill; enacted text and delivery records."
  false refl

postApprovalReceipts : List ScopedReceipt
postApprovalReceipts =
  developmentRegulatoryGate ∷
  housingNarrativeAlignment ∷
  utilityDemandCandidate ∷
  regionalDistributorIdentityFork ∷
  landNetworkOptionCandidate ∷
  lobbyingHistory ∷
  ministerHoldingsAuditOpen ∷
  gasNationalPolicySeparate ∷ []

data StateLobbyingMeetingPaysCommonwealthApprovalCause : Set where
data Historic8000GasConnectionsPayCurrentEstateConnection : Set where
data HousingPolicyAlignmentPaysImproperInfluence : Set where
data PublisherLandDescriptionPaysCurrentTitle : Set where
data ReservationBillPaysAnEnactedLocalGasSubsidy : Set where
data RegionalGasNetworkCoveragePaysSpringviewConnection : Set where
data ApprovalNoticePaysSignedReasonsAndJudicialValidity : Set where
data InterestsIndexPaysPersonalEnrichmentOrExoneration : Set where
data ExtensionSignerPaysFinalApprovalSigner : Set where

stateMeetingNotCommonwealthCausation :
  StateLobbyingMeetingPaysCommonwealthApprovalCause → ⊥
stateMeetingNotCommonwealthCausation ()

historicConnectionNotCurrentEstate :
  Historic8000GasConnectionsPayCurrentEstateConnection → ⊥
historicConnectionNotCurrentEstate ()

housingNarrativeNotImproperInfluence :
  HousingPolicyAlignmentPaysImproperInfluence → ⊥
housingNarrativeNotImproperInfluence ()

websiteNotLandTitle : PublisherLandDescriptionPaysCurrentTitle → ⊥
websiteNotLandTitle ()

proposedBillNotLocalSubsidy :
  ReservationBillPaysAnEnactedLocalGasSubsidy → ⊥
proposedBillNotLocalSubsidy ()

portalNoticeNotJudicialValidity :
  ApprovalNoticePaysSignedReasonsAndJudicialValidity → ⊥
portalNoticeNotJudicialValidity ()

regionalCoverageNotSameConnection :
  RegionalGasNetworkCoveragePaysSpringviewConnection → ⊥
regionalCoverageNotSameConnection ()

thirdPartyIndexNotDispositive :
  InterestsIndexPaysPersonalEnrichmentOrExoneration → ⊥
thirdPartyIndexNotDispositive ()

extensionSignerNotFinalApprovalSigner :
  ExtensionSignerPaysFinalApprovalSigner → ⊥
extensionSignerNotFinalApprovalSigner ()
