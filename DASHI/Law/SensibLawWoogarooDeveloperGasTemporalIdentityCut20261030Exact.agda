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
   stocklandSpringview ∷ networkLevelRegister ∷ [])
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

data ProjectCoordinate : Set where
  epbc20198575 : ProjectCoordinate
  scenic20208651 : ProjectCoordinate

distinctEPBCProjects : epbc20198575 ≡ scenic20208651 → ⊥
distinctEPBCProjects ()

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
