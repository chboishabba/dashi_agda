module DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SPRINGFIELD GAS / LOBBYING / OWNERSHIP INVESTIGATIVE SNOWBALL
--
-- Method boundary follows the same discipline used by the Eskridge lane:
-- documented behaviour may generate hypotheses and producer searches, but a
-- relationship is not promoted beyond the literal source object which pays it.
-- Corporate control, employment lineage, project partnership, political
-- donation, registered lobbying contact, infrastructure alliance and asset
-- ownership are deliberately distinct edge kinds.
------------------------------------------------------------------------

data EntityCoordinate : Set where
  springfieldCityGroup055714531 : EntityCoordinate
  azureDevelopmentGroup600740163 : EntityCoordinate
  unrelatedAzureGroup093795334 : EntityCoordinate
  chrisSchroor : EntityCoordinate
  mahaSinnathamby : EntityCoordinate
  bobSharpless : EntityCoordinate
  santoSantoro : EntityCoordinate
  energex : EntityCoordinate
  allgas : EntityCoordinate

data EdgeKind : Set where
  corporateControl : EdgeKind
  employmentLineage : EdgeKind
  projectPartnership : EdgeKind
  politicalDonation : EdgeKind
  registeredLobbyingContact : EdgeKind
  infrastructureAlliance : EdgeKind
  energyAssetOwnership : EdgeKind
  governmentProgramPartnership : EdgeKind

data EvidenceStatus : Set where
  governmentPrimaryPaid : EvidenceStatus
  courtRecordPaid : EvidenceStatus
  firstPartyPaid : EvidenceStatus
  secondaryLocatorOnly : EvidenceStatus
  acquisitionOpen : EvidenceStatus

------------------------------------------------------------------------
-- Attributed sources.  Citation imports neither proof nor authority.
------------------------------------------------------------------------

azureABR : Source.AttributedSource
azureABR = Source.mkNoDOISource
  "Australian Business Register"
  "Current details for ABN 67 600 740 163 — AZURE DEVELOPMENT GROUP PTY LTD"
  "ABN Lookup"
  "2026"
  "https://abr.business.gov.au/ABN/View?id=67600740163"
  Source.governmentSource
  "Primary registry identity coordinate for Azure Development Group Pty Ltd; ABN/ACN identity does not establish shareholders, political influence, project ownership or gas interests."
  Source.publicAttribution

azureNameSearchABR : Source.AttributedSource
azureNameSearchABR = Source.mkNoDOISource
  "Australian Business Register"
  "Active ABN search — Azure names"
  "ABN Lookup"
  "2026"
  "https://abr.business.gov.au/Search/ResultsActive?SearchText=azure+development+group"
  Source.governmentSource
  "Primary registry disambiguation showing Azure Development Group Pty Ltd ABN 67 600 740 163 is distinct from Azure Group Pty Ltd ABN 79 093 795 334 and other similarly named entities."
  Source.publicAttribution

azureFounderBiography : Source.AttributedSource
azureFounderBiography = Source.mkNoDOISource
  "Azure"
  "Our Story — Chris Schroor"
  "Azure Development Group"
  "2026"
  "https://www.azd.com.au/our-story"
  Source.practitionerSource
  "First-party biography stating Chris Schroor is a founding director of Azure and previously served as Executive Director — Commercial Development for Springfield Land Corporation; biography is an employment-lineage source, not proof of continuing Springfield control."
  Source.publicAttribution

azureBrookwaterPartnershipPost : Source.AttributedSource
azureBrookwaterPartnershipPost = Source.mkNoDOISource
  "Chris Schroor"
  "Seasons / Ember / Oakmont partnership post"
  "LinkedIn"
  "2025"
  "https://www.linkedin.com/posts/chris-schroor-57428b3_after-the-successful-completion-of-seasons-activity-7293212553076162560-Maty"
  Source.practitionerSource
  "First-person public statement that Azure partnered with Maha Sinnathamby and Bob Sharpless on Seasons at Brookwater and Ember and described Oakmont as their third project together; does not establish common corporate ownership."
  Source.publicAttribution

azureDonationDisclosure : Source.AttributedSource
azureDonationDisclosure = Source.mkNoDOISource
  "Electoral Commission of Queensland"
  "Electronic Disclosure System — gifts to Liberal National Party of Queensland"
  "ECQ Electronic Disclosure System"
  "2019"
  "https://disclosures.ecq.qld.gov.au/Report/AdvertisersData/697/Gifts"
  Source.governmentSource
  "Primary electoral disclosure source containing Azure Development Group entries; a disclosed gift does not by itself establish access, influence, quid pro quo, decision causation or policy benefit."
  Source.publicAttribution

springfieldLobbyingDiary : Source.AttributedSource
springfieldLobbyingDiary = Source.mkNoDOISource
  "Queensland Government"
  "Ministerial Diary — Minister for Customer Services and Open Data, Small and Family Business — February 2025"
  "Queensland Cabinet"
  "2025"
  "https://cabinet.qld.gov.au/ministers-portfolios/assets/diary/current/steven-minnikin/2025/february/steven-minnikin.pdf"
  Source.governmentSource
  "Primary ministerial diary recording a 4 February 2025 Lobbyist Introductory Meeting involving Santo Santoro of Santoro Consulting and Springfield principals; meeting attendance does not establish a decision outcome or improper influence."
  Source.publicAttribution

springfieldLobbyingDiaryFinance : Source.AttributedSource
springfieldLobbyingDiaryFinance = Source.mkNoDOISource
  "Queensland Government"
  "Ministerial Diary — Minister for Finance, Trade, Employment and Training — February 2025"
  "Queensland Cabinet"
  "2025"
  "https://cabinet.qld.gov.au/ministers-portfolios/assets/diary/current/rosslyn-bates/2025/february/rosslyn-bates.pdf"
  Source.governmentSource
  "Primary ministerial diary recording a 12 February 2025 Springfield Land Corporation meeting attended by Springfield executives and Santo Santoro identified as a registered lobbyist; no policy or development outcome is imported."
  Source.publicAttribution

springfieldGasAllianceReport : Source.AttributedSource
springfieldGasAllianceReport = Source.mkNoDOISource
  "Australian Broadcasting Corporation"
  "Development aims to set alternative energy use trend"
  "ABC News"
  "2004"
  "https://www.abc.net.au/news/2004-04-30/development-aims-to-set-alternative-energy-use/178340"
  Source.newsSource
  "Secondary contemporaneous report locating an Energex–Springfield Land Corporation alliance to develop gas and electricity networks at Springfield, including an Energex statement referring to 8,000 gas connections. The underlying alliance agreement and same-object gas asset records remain unpaid."
  Source.publicAttribution

springfieldControlJudgment : Source.AttributedSource
springfieldControlJudgment = Source.mkNoDOISource
  "Supreme Court of Queensland"
  "Springfield City Group Pty Ltd v Pipe Networks Pty Ltd [2022] QSC 255"
  "Queensland Supreme Court judgment (public mirror)"
  "2022"
  "https://www.casechat.au/cases/au/springfield-city-group-pty-ltd-v-pipe-networks-pty-ltd"
  (Source.namedSourceKind "court judgment")
  "Court finding relevant to historical 2005 control: the judgment records evidence that Maha Sinnathamby controlled 75 percent of SLC shares and Bob Sharpless 25 percent, while expressly noting some conflict with company-search material. This is historical and does not pay current ownership."
  Source.publicAttribution

springfieldInfluenceSources : List Source.AttributedSource
springfieldInfluenceSources =
  azureABR ∷
  azureNameSearchABR ∷
  azureFounderBiography ∷
  azureBrookwaterPartnershipPost ∷
  azureDonationDisclosure ∷
  springfieldLobbyingDiary ∷
  springfieldLobbyingDiaryFinance ∷
  springfieldGasAllianceReport ∷
  springfieldControlJudgment ∷
  []

springfieldInfluenceAtlas : Source.AttributedSourceAtlas
springfieldInfluenceAtlas = Source.mkSourceAtlas
  "Springfield gas / lobbying / ownership investigative source atlas"
  "DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact"
  springfieldInfluenceSources
  "Identity-separated primary/first-party/secondary sources for tracing corporate control, personnel lineage, project partnerships, donations, registered lobbying contacts and gas/infrastructure relationships without promoting proximity into causation."

------------------------------------------------------------------------
-- Exact currently paid or bounded edges.
------------------------------------------------------------------------

record AttributedInfluenceEdge : Set where
  constructor attributed-influence-edge
  field
    from : EntityCoordinate
    to : EntityCoordinate
    kind : EdgeKind
    source : Source.AttributedSource
    exactLocator : String
    boundedStatement : String
    status : EvidenceStatus
    importsInfluenceConclusion : Bool
    importsInfluenceConclusionIsFalse : importsInfluenceConclusion ≡ false

open AttributedInfluenceEdge public

azureDevelopmentGroupIdentity : AttributedInfluenceEdge
azureDevelopmentGroupIdentity = attributed-influence-edge
  azureDevelopmentGroup600740163
  azureDevelopmentGroup600740163
  corporateControl
  azureABR
  "ABN 67 600 740 163 / ACN 600 740 163"
  "The relevant Queensland entity is AZURE DEVELOPMENT GROUP PTY LTD, an active Australian private company with ABN 67 600 740 163 and ACN 600 740 163. This is an identity receipt only."
  governmentPrimaryPaid
  false refl

springfieldAzureEmploymentLineage : AttributedInfluenceEdge
springfieldAzureEmploymentLineage = attributed-influence-edge
  chrisSchroor
  azureDevelopmentGroup600740163
  employmentLineage
  azureFounderBiography
  "Meet the Founders — Chris Schroor"
  "Azure's first-party biography states that founding director Chris Schroor previously served as Executive Director — Commercial Development for Springfield Land Corporation."
  firstPartyPaid
  false refl

springfieldAzureProjectPartnership : AttributedInfluenceEdge
springfieldAzureProjectPartnership = attributed-influence-edge
  azureDevelopmentGroup600740163
  mahaSinnathamby
  projectPartnership
  azureBrookwaterPartnershipPost
  "Chris Schroor public post — Seasons / Ember / Oakmont"
  "Chris Schroor publicly described Seasons at Brookwater as completed with the partnership, Ember as another partnership with Maha Sinnathamby and Bob Sharpless, and Oakmont as their third project together."
  firstPartyPaid
  false refl

azureLnpDonation2019A : AttributedInfluenceEdge
azureLnpDonation2019A = attributed-influence-edge
  azureDevelopmentGroup600740163
  azureDevelopmentGroup600740163
  politicalDonation
  azureDonationDisclosure
  "ECQ gifts table — 11 February 2019"
  "The ECQ disclosure table records Azure Development Group as giving $15,000 to the Liberal National Party of Queensland on 11 February 2019."
  governmentPrimaryPaid
  false refl

azureLnpDonation2019B : AttributedInfluenceEdge
azureLnpDonation2019B = attributed-influence-edge
  azureDevelopmentGroup600740163
  azureDevelopmentGroup600740163
  politicalDonation
  azureDonationDisclosure
  "ECQ gifts table — 15 March 2019"
  "The ECQ disclosure table records Azure Development Group as giving $10,000 to the Liberal National Party of Queensland on 15 March 2019."
  governmentPrimaryPaid
  false refl

springfieldRegisteredLobbyistMeeting2025 : AttributedInfluenceEdge
springfieldRegisteredLobbyistMeeting2025 = attributed-influence-edge
  santoSantoro
  mahaSinnathamby
  registeredLobbyingContact
  springfieldLobbyingDiary
  "4 February 2025 — Lobbyist Introductory Meeting"
  "A Queensland ministerial diary records Santo Santoro of Santoro Consulting identified as lobbyist at a Lobbyist Introductory Meeting with Maha Sinnathamby, Raynuha Sinnathamby, Russell Luhrs and Jim Varghese of Springfield City Group."
  governmentPrimaryPaid
  false refl

springfieldEnergexGasAllianceLocator : AttributedInfluenceEdge
springfieldEnergexGasAllianceLocator = attributed-influence-edge
  springfieldCityGroup055714531
  energex
  infrastructureAlliance
  springfieldGasAllianceReport
  "ABC News, 30 April 2004"
  "ABC contemporaneously reported an alliance between Energex and Springfield Land Corporation to develop a gas and electricity network for Springfield and quoted Energex referring to 8,000 gas connections. The original alliance instrument is not yet acquired."
  secondaryLocatorOnly
  false refl

------------------------------------------------------------------------
-- Current ownership and gas-asset lineage remain explicit residuals.
------------------------------------------------------------------------

record AcquisitionResidual : Set where
  constructor acquisition-residual
  field
    label : String
    exactMissingObject : String
    whyNeeded : String
    secondaryCanClose : Bool
    absenceFromSearchMeansNonExistence : Bool

open AcquisitionResidual public

gasAssetLineageResidual : AcquisitionResidual
gasAssetLineageResidual = acquisition-residual
  "Springfield gas asset lineage"
  "Original Energex–Springfield alliance/agreement plus same-object network maps, easements or asset-register records sufficient to identify who owned/operated the Springfield gas assets and any subsequent transfer into Allgas/APA/other ownership."
  "Without the literal asset/instrument chain, the historical gas alliance cannot be promoted into current gas ownership or beneficiary claims."
  false
  false

currentOwnershipResidual : AcquisitionResidual
currentOwnershipResidual = acquisition-residual
  "Current Springfield and Azure beneficial/control ownership"
  "Current and historical ASIC extracts/share registers for Springfield City Group Pty Ltd ACN 055 714 531, relevant Springfield trusts/entities, and Azure Development Group Pty Ltd ACN 600 740 163."
  "ABR identity and historical court evidence do not establish current shareholders, beneficial ownership or ultimate control."
  false
  false

------------------------------------------------------------------------
-- Identity / WrongType firewalls.
------------------------------------------------------------------------

data AzureNameCollisionPaysIdentity : Set where
data FormerEmploymentCreatesControl : Set where
data ProjectPartnershipCreatesCommonOwnership : Set where
data PoliticalDonationCreatesInfluence : Set where
data LobbyingMeetingCreatesDecisionOutcome : Set where
data InfrastructureAllianceCreatesAssetOwnership : Set where
data SecondaryGasReportPaysPrimaryAgreement : Set where

aazureNameCollisionPlaceholder : Bool
aazureNameCollisionPlaceholder = false

azureNameCollisionDoesNotPayIdentity : AzureNameCollisionPaysIdentity → ⊥
azureNameCollisionDoesNotPayIdentity ()

formerEmploymentDoesNotCreateControl : FormerEmploymentCreatesControl → ⊥
formerEmploymentDoesNotCreateControl ()

projectPartnershipDoesNotCreateCommonOwnership : ProjectPartnershipCreatesCommonOwnership → ⊥
projectPartnershipDoesNotCreateCommonOwnership ()

politicalDonationDoesNotCreateInfluence : PoliticalDonationCreatesInfluence → ⊥
politicalDonationDoesNotCreateInfluence ()

lobbyingMeetingDoesNotCreateDecisionOutcome : LobbyingMeetingCreatesDecisionOutcome → ⊥
lobbyingMeetingDoesNotCreateDecisionOutcome ()

infrastructureAllianceDoesNotCreateAssetOwnership : InfrastructureAllianceCreatesAssetOwnership → ⊥
infrastructureAllianceDoesNotCreateAssetOwnership ()

secondaryGasReportDoesNotPayPrimaryAgreement : SecondaryGasReportPaysPrimaryAgreement → ⊥
secondaryGasReportDoesNotPayPrimaryAgreement ()

------------------------------------------------------------------------
-- Eskridge-style BIDI / Pareto policy.
------------------------------------------------------------------------

record InfluenceSnowballBoundary : Set where
  constructor influence-snowball-boundary
  field
    acquisitionMayRunOutOfDependencyOrder : Bool
    sameObjectRequiredBeforeRelationshipPromotion : Bool
    secondaryMayLocatePrimary : Bool
    secondaryMayPayPrimary : Bool
    proximityMayCreateBeneficiaryEdge : Bool
    donationMayCreateDecisionCausation : Bool
    registeredLobbyingMayCreateOutcome : Bool
    historicalControlMayPayCurrentOwnership : Bool
    negativeSearchResultCreatesKnownAbsence : Bool

canonicalInfluenceSnowballBoundary : InfluenceSnowballBoundary
canonicalInfluenceSnowballBoundary = influence-snowball-boundary
  true true true false false false false false false

data InfluenceParetoLeaf : Set where
  springfieldAndAzureASICExtracts : InfluenceParetoLeaf
  originalEnergexSpringfieldAgreement : InfluenceParetoLeaf
  springfieldGasAssetMapAndEasements : InfluenceParetoLeaf
  ecqAndAecEntityNormalisedDonationLedger : InfluenceParetoLeaf
  registeredLobbyistClientAndMeetingLedger : InfluenceParetoLeaf
  brookwaterAzureProjectTitleAndApplicantChain : InfluenceParetoLeaf
  gasNetworkTransferChain : InfluenceParetoLeaf

record InfluenceParetoPolicy : Set where
  constructor influence-pareto-policy
  field
    identityBeforeNetworkInference : Bool
    ownershipBeforeBeneficiaryClaim : Bool
    agreementBeforeGasAssetClaim : Bool
    donationLedgerBeforeInfluenceHypothesis : Bool
    meetingPurposeBeforeOutcomeHypothesis : Bool
    projectTitleBeforeCommonOwnershipClaim : Bool
    preserveNegativeFindingsAsResiduals : Bool

canonicalInfluenceParetoPolicy : InfluenceParetoPolicy
canonicalInfluenceParetoPolicy = influence-pareto-policy
  true true true true true true true
