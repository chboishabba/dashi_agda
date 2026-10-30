{-# OPTIONS --safe #-}
module DASHI.Law.SensibLawWoogarooDeveloperGasTemporalIdentityCut20261030Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.IdentifierExact as Identifier
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Ibrahim
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Lobby
import DASHI.Law.SensibLawAzureSpringfieldInducedGasDemandExact as Demand
import DASHI.Law.SensibLawWoogarooGasSecondThirdOrderNonPromotion20261030Exact as Prior
import DASHI.Law.SensibLawWoogaroo9281EPBCInstrumentDisambiguationExact as Instrument
import DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact as Cumulative

------------------------------------------------------------------------
-- WOOGAROO / SPRINGFIELD - TIME AND PERSON/ASSET IDENTITY CUT
--
-- Historical gas rollout speech (2005) + office diary (2025) + current
-- network-level register (2026) do not establish an actual asset or
-- consideration flowing from the 2019/8575 approval.
-- Historical PR #1276 owns prior incidence source and proof adaptation;
-- only existing merged owners imported. QID is a navigation coordinate,
-- never a substitute for legal-person or site/parcel identity.
------------------------------------------------------------------------

hansard2005 : Source.AttributedSource
hansard2005 = Source.mkNoDOISource
  "John English MP / Queensland Legislative Assembly"
  "Energy Legislation Amendment Bill debate, 27 October 2005, pp 1-2"
  "Queensland Parliament official Hansard speech"
  "27 October 2005"
  "https://documents.parliament.qld.gov.au/speeches/spk2005/John%20English%20spk%20Redlands%202005_10_27_121.PDF"
  Source.governmentSource
  "Dated parliamentary speech: developer-distributor commercial arrangements and a planned Energex/Allgas gas-network rollout to Springfield. This is NOT a Springfield contract, accomplished asset transfer, ministerial decision or evidence of a 2026 benefit."
  Source.publicAttribution

april2025Diary : Source.AttributedSource
april2025Diary = Source.mkNoDOISource
  "Queensland Government"
  "Chief-of-staff diary, Treasurer / Energy / Home Ownership, April 2025, PDF p 3"
  "Queensland Office of the Premier published diary"
  "9 April 2025"
  "https://origin-www.premiers.qld.gov.au/right-to-info/published-info/assets/chief-of-staff-diaries-2025-04.pdf?v3="
  Source.governmentSource
  "Records Raynuha Sinnathamby, Ian Murray, Springfield City Group and Santo Santoro at an introduction/project-update meeting. Portfolio remit does not pay gas subject matter, policy tasking or decision causation."
  Source.publicAttribution

cherishPublicCommentNotice : Source.AttributedSource
cherishPublicCommentNotice = Source.mkNoDOISource
  "Cherish Enterprises Pty Ltd"
  "Springfield Residential Development EPBC 2019/8575 preliminary-documentation invitation"
  "EPBC Act Public Portal original proponent notice"
  "13 February 2026"
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/4f8edc14-9ffb-ee11-9f89-00224892a860/2ab10dab-d681-4911-b881-cc99413f07b6?file=2019-8575-Draft-PD.pdf"
  Source.practitionerSource
  "Named proponent and public-comment notice. Proponent identity is not registered title, a developer mandate, or a gas servicing contract."
  Source.publicAttribution

stocklandSpringview : Source.AttributedSource
stocklandSpringview = Source.mkNoDOISource
  "Stockland"
  "Springview masterplanned community FAQs and October 2026 disclaimer"
  "Stockland first-party project page"
  "October 2026"
  "https://www.stockland.com.au/residential/qld/springview"
  Source.practitionerSource
  "First-party page: Stockland describes itself as proposed developer, not registered site owner; says private third-party freehold and no confirmed construction start. Neither proves exact title holder, option terms or gas supply."
  Source.publicAttribution


priorVillageOneTransfer2017 : Source.AttributedSource
priorVillageOneTransfer2017 = Source.mkNoDOISource
  "Commonwealth Department of the Environment and Energy / Rod Whyte"
  "Signed EPBC 2014/7306 section 145B Notice of Transfer of Approval, 16 June 2017"
  "Original instrument reproduced in Stockland-hosted 2019 Kalina compliance report, PDF page 38"
  "16 June 2017"
  "https://www.stockland.com.au/globalassets/residential/qld/kalina/news-and-events/annual-compliance-report-to-8-july-2019.pdf"
  Source.governmentSource
  "Original signed transfer face names Cherish Enterprises Pty Ltd ACN 052 055 811 as transferor and Stockland Development Pty Limited ACN 000 664 835 as transferee for VILLAGE ONE, EPBC 2014/7306, Lot 43 on SP2442290. This does not transfer EPBC 2019/8575."
  Source.publicAttribution

council2023DocumentIndex : Source.AttributedSource
council2023DocumentIndex = Source.mkNoDOISource
  "Ipswich City Council"
  "6243/2023/LAP application document index, entries 316 and 318"
  "Official council document index, original signed document faces not yet authenticated"
  "29 June 2023"
  "https://edoc.ipswich.qld.gov.au/objective/?env=iccecm&id=1596235&plat=pwy"
  Source.governmentSource
  "Same planning application index separately lists Stockland Development Pty Limited submission consent and Cherish Enterprises Pty Ltd landowner-consent documents; file labels are not signatures, verified parcel title or corporate transaction terms."
  Source.publicAttribution

springfieldCityGroupCouncilCommentIndex2024 : Source.AttributedSource
springfieldCityGroupCouncilCommentIndex2024 = Source.mkNoDOISource
  "Ipswich City Council"
  "6243/2023/LAP, entry 6: 14 March 2024 s275Z Planning Act - SCG Comment"
  "Official Council application document index; underlying comment face not retrieved"
  "14 March 2024"
  "https://edoc.ipswich.qld.gov.au/objective/?env=iccecm&id=1596235&plat=pwy"
  Source.governmentSource
  "Official index names a Springfield City Group comment under the same Council planning application that also lists Cherish and Stockland consents. Index only: neither comment content, stance, authority nor gas/EPBC linkage is established."
  Source.publicAttribution

networkLevelRegister : Source.AttributedSource
networkLevelRegister = Demand.allgasCurrentOwnership

existingFebruaryMeeting : Lobby.AttributedInfluenceEdge
existingFebruaryMeeting = Lobby.springfieldRegisteredLobbyistMeeting2025

environmentalLawNavigationOnly : Identifier.ItemId
environmentalLawNavigationOnly = Ibrahim.environmentalLawQid

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "Woogaroo 2019/8575 developer / 2005 gas / 2025 portfolio / 2026 asset temporal cut"
  "DASHI.Law.SensibLawWoogarooDeveloperGasTemporalIdentityCut20261030Exact"
  (hansard2005 ∷ april2025Diary ∷ cherishPublicCommentNotice ∷
   stocklandSpringview ∷ priorVillageOneTransfer2017 ∷
   council2023DocumentIndex ∷ springfieldCityGroupCouncilCommentIndex2024 ∷
   networkLevelRegister ∷ [])
  "Retains source author, time and claim scope; AEMC network ownership is reused from the existing Agda owner. A repeated report is not an independent evidence producer."

data LegalRole : Set where
  epbcProponent : LegalRole
  proposedDeveloper : LegalRole
  registeredLandowner : LegalRole
  lobbyingClient : LegalRole
  networkOwner : LegalRole
  networkOperator : LegalRole
  retailer : LegalRole
  serviceConnectionHolder : LegalRole
  revenueRecipient : LegalRole
  indexedPlanningCommentator : LegalRole

-- Reuse canonical EPBC identifier owners; do not create a competing case enum.
villageOneInstrument : Instrument.FederalInstrumentCoordinate
villageOneInstrument = Instrument.epbc2014_7306

springviewCurrentInstrument : Instrument.FederalInstrumentCoordinate
springviewCurrentInstrument = Instrument.epbc2019_8575

scenicSeparateProject : Cumulative.ProjectCoordinate
scenicSeparateProject = Cumulative.scenic2020_8651

villageOneIsNotCurrentAction :
  villageOneInstrument ≡ springviewCurrentInstrument → ⊥
villageOneIsNotCurrentAction ()

record ScopedRole : Set where
  constructor scoped-role
  field
    legalRole : LegalRole
    objectKey : String
    source : Source.AttributedSource
    roleFromSourcePaid : Bool
    directContractBetweenRolesPaid : Bool
open ScopedRole public

cherishProponent : ScopedRole
cherishProponent = scoped-role epbcProponent
  "EPBC 2019/8575 — Cherish Enterprises Pty Ltd"
  cherishPublicCommentNotice true false

stocklandProposedDeveloper : ScopedRole
stocklandProposedDeveloper = scoped-role proposedDeveloper
  "Springview project page — proposed developer"
  stocklandSpringview true false

landTitleStillOpen : ScopedRole
landTitleStillOpen = scoped-role registeredLandowner
  "EPBC 2019/8575 — exact registered parcel title"
  stocklandSpringview false false

springfieldCouncilIndexOnly : ScopedRole
springfieldCouncilIndexOnly = scoped-role indexedPlanningCommentator
  "Council 6243/2023/LAP — Springfield City Group comment (index only)"
  springfieldCityGroupCouncilCommentIndex2024 true false

-- A programme-level gas expansion statement and an aggregate network owner
-- are compatible with different exact project-pipe identities. The fact that
-- these are different source carriers does not supply the missing asset join.
data NetworkWorld : Set where
  generalNetworkNotSiteBound : NetworkWorld
  originalSiteServicingContractFound : NetworkWorld

data AggregateObservation : Set where
  historicalPlanAndCurrentNetworkOwner : AggregateObservation

data ParcelAssetStatus : Set where
  noExactParcelAssetReceipt : ParcelAssetStatus
  exactParcelAssetReceipt : ParcelAssetStatus

aggregate : NetworkWorld → AggregateObservation
aggregate generalNetworkNotSiteBound = historicalPlanAndCurrentNetworkOwner
aggregate originalSiteServicingContractFound = historicalPlanAndCurrentNetworkOwner

parcelAsset : NetworkWorld → ParcelAssetStatus
parcelAsset generalNetworkNotSiteBound = noExactParcelAssetReceipt
parcelAsset originalSiteServicingContractFound = exactParcelAssetReceipt

parcelAssetDiffers :
  parcelAsset generalNetworkNotSiteBound ≡
  parcelAsset originalSiteServicingContractFound → ⊥
parcelAssetDiffers ()

networkHistoryDoesNotIdentifyParcelAssets :
  INF.FactorsThrough aggregate parcelAsset → ⊥
networkHistoryDoesNotIdentifyParcelAssets =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness generalNetworkNotSiteBound
      originalSiteServicingContractFound refl parcelAssetDiffers)

-- A named EPBC proponent and a separately self-described proposed developer
-- can have different contractual arrangements and landowner identities.
data DeveloperWorld : Set where
  namedRolesNoContractFound : DeveloperWorld
  namedRolesWithSignedContractFound : DeveloperWorld

data NamedActors : Set where
  cherishAndStocklandNamed : NamedActors

data LegalTransaction : Set where
  transactionUnacquired : LegalTransaction
  signedMandateAcquired : LegalTransaction

namedActors : DeveloperWorld → NamedActors
namedActors namedRolesNoContractFound = cherishAndStocklandNamed
namedActors namedRolesWithSignedContractFound = cherishAndStocklandNamed

transaction : DeveloperWorld → LegalTransaction
transaction namedRolesNoContractFound = transactionUnacquired
transaction namedRolesWithSignedContractFound = signedMandateAcquired

transactionDiffers :
  transaction namedRolesNoContractFound ≡
  transaction namedRolesWithSignedContractFound → ⊥
transactionDiffers ()

namedProjectRolesDoNotEstablishTransfer :
  INF.FactorsThrough namedActors transaction → ⊥
namedProjectRolesDoNotEstablishTransfer =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness namedRolesNoContractFound
      namedRolesWithSignedContractFound refl transactionDiffers)

data ReceiptTarget : Set where
  aprilClientContactAndAuthorityRecord : ReceiptTarget
  aprilMeetingBriefAndDecisionFile : ReceiptTarget
  exactCherishStocklandLandownerChain : ReceiptTarget
  originalSpringfieldGasServicingAgreement : ReceiptTarget
  parcelMapAndMIRNDistributor : ReceiptTarget
  assetTransferSchedulesAndRevenueAllocation : ReceiptTarget
  epbcSignedApprovalConditionsAnd95B95C : ReceiptTarget

record PriorityCut : Set where
  constructor priority-cut
  field
    target : ReceiptTarget
    identityJoinPaid : Bool
    outcomeProved : Bool
open PriorityCut public

portfolioAgendaCut : PriorityCut
portfolioAgendaCut = priority-cut aprilMeetingBriefAndDecisionFile false false

assetChainCut : PriorityCut
assetChainCut = priority-cut assetTransferSchedulesAndRevenueAllocation false false

federalApprovalCut : PriorityCut
federalApprovalCut = priority-cut epbcSignedApprovalConditionsAnd95B95C false false


-- A genuine 2017 Cherish -> Stockland Commonwealth approval transfer exists
-- for a different action. It is stronger than proximity but not a current
-- assignment of the 2019/8575 approval, contract or land title.
record PriorApprovalTransfer : Set where
  constructor prior-approval-transfer
  field
    project : Instrument.FederalInstrumentCoordinate
    transferorACN : String
    transfereeACN : String
    instrument : Source.AttributedSource
    datedTransferFacePaid : Bool
    current20198575TransferPaid : Bool
open PriorApprovalTransfer public

historicalCherishStocklandTransfer : PriorApprovalTransfer
historicalCherishStocklandTransfer = prior-approval-transfer
  villageOneInstrument
  "052055811"
  "000664835"
  priorVillageOneTransfer2017
  true
  false

-- This proof is about the epistemic limit of transferring information
-- between two distinct action identifiers, not about denying any later deal.
data TransferWorld : Set where
  priorTransferWithoutNewContract : TransferWorld
  priorTransferWithSeparatelyFoundNewContract : TransferWorld

data HistoricalTransferObserved : Set where
  cherishtoStocklandVillageOne2017 : HistoricalTransferObserved

data CurrentActionContract : Set where
  currentContractUnacquired : CurrentActionContract
  currentContractDocumented : CurrentActionContract

historical : TransferWorld → HistoricalTransferObserved
historical priorTransferWithoutNewContract = cherishtoStocklandVillageOne2017
historical priorTransferWithSeparatelyFoundNewContract = cherishtoStocklandVillageOne2017

current : TransferWorld → CurrentActionContract
current priorTransferWithoutNewContract = currentContractUnacquired
current priorTransferWithSeparatelyFoundNewContract = currentContractDocumented

currentContractDiffers :
  current priorTransferWithoutNewContract ≡
  current priorTransferWithSeparatelyFoundNewContract → ⊥
currentContractDiffers ()

pastApprovalTransferDoesNotProveCurrentProjectContract :
  INF.FactorsThrough historical current → ⊥
pastApprovalTransferDoesNotProveCurrentProjectContract =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness priorTransferWithoutNewContract
      priorTransferWithSeparatelyFoundNewContract refl currentContractDiffers)


-- A listed comment within the Council case adds a real project-process edge,
-- but without its face it does not determine the speaker's substantive stance.
data CommentWorld : Set where
  scgCommentCritical : CommentWorld
  scgCommentSupportive : CommentWorld

data IndexedComment : Set where
  scgCommentListed : IndexedComment

data CommentDisposition : Set where
  criticalComment : CommentDisposition
  supportiveComment : CommentDisposition

commentIndex : CommentWorld → IndexedComment
commentIndex scgCommentCritical = scgCommentListed
commentIndex scgCommentSupportive = scgCommentListed

commentContent : CommentWorld → CommentDisposition
commentContent scgCommentCritical = criticalComment
commentContent scgCommentSupportive = supportiveComment

commentContentDiffers :
  commentContent scgCommentCritical ≡
  commentContent scgCommentSupportive → ⊥
commentContentDiffers ()

scgIndexDoesNotEstablishPosition :
  INF.FactorsThrough commentIndex commentContent → ⊥
scgIndexDoesNotEstablishPosition =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness scgCommentCritical
      scgCommentSupportive refl commentContentDiffers)
