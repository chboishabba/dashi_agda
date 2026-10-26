module DASHI.Cognition.SpringfieldValueCaptureReceiptRound20261013Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SpringfieldLayeredValueCaptureParetoExact as Layered
import DASHI.Cognition.BlackRockMirvacSpringfieldCapitalOverlapExact as Capital
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as GasLobby

------------------------------------------------------------------------
-- SPRINGFIELD VALUE-CAPTURE RECEIPT ROUND — 2026-10-13
-- Pays only source-local edges resolved in the current max-cut.
------------------------------------------------------------------------

data ReceiptKind : Set where
  landSale : ReceiptKind
  tenantCommitment : ReceiptKind
  assetOwnership : ReceiptKind
  assetValuation : ReceiptKind
  substantialHolding : ReceiptKind
  lobbyingAccess : ReceiptKind
  lobbyingSubject : ReceiptKind
  politicalDonation : ReceiptKind
  gasInfrastructureAlliance : ReceiptKind
  longTermEnergyAlliance : ReceiptKind

record Receipt : Set where
  constructor receipt
  field
    kind : ReceiptKind
    actorA : String
    actorB : String
    source : String
    boundedFinding : String
    paid : Bool
open Receipt public

cityWestSale : Receipt
cityWestSale = receipt landSale
  "Springfield City Group"
  "Gordon Corp / Bruce Mathieson family partnership"
  "Gordon Corp; Colliers/Stonebridge; 2026 transaction reporting"
  "A 12.7 ha Town Centre-zoned City West site was sold for AUD 50 million by Springfield City Group to the Gordon Corp/Mathieson partnership. The campaign attracted more than 200 enquiries and multiple formal offers. This pays land transfer and downstream development rights, not the acquisition vehicle's debt/equity stack."
  true

springfieldVillageTenantStack : Receipt
springfieldVillageTenantStack = receipt tenantCommitment
  "Gordon Corp / Mathieson partnership"
  "Springfield Village tenant pipeline"
  "2026 transaction/project reporting"
  "The first planned precinct is a 10,581 sqm retail/lifestyle hub within a roughly 30,000 sqm retail precinct, anchored by Coles/Liquorland with reported early commitments including McDonald's, The Good Guys, Banjo's, Pillow Talk, Auto Masters, Hungry Jack's and 7-Eleven. Commitment does not equal completed lease, rent receipt or operating revenue."
  true

orionOwnershipAndValue : Receipt
orionOwnershipAndValue = receipt assetOwnership
  "Mirvac"
  "Orion Springfield Central"
  "Mirvac FY26 portfolio / property compendium"
  "Mirvac reports 100% ownership of Orion Springfield Central, acquisition/agreement date August 2002, development by Mirvac, a 30 June 2026 valuation of AUD 518 million, and adjoining vacant land for future expansion."
  true

blackRockMirvacGrowth : Receipt
blackRockMirvacGrowth = receipt substantialHolding
  "BlackRock Group"
  "Mirvac Group"
  "Mirvac FY25 and FY26 annual-report substantial-holder tables"
  "BlackRock Group's disclosed substantial holding in Mirvac increased from 6.66% at 28 February 2025 to 7.70% at 2 April 2026, corresponding to 303,997,515 stapled securities in the FY26 table. This pays equity exposure and change over time, not operational control."
  true

springfieldSantoroHealthMeeting : Receipt
springfieldSantoroHealthMeeting = receipt lobbyingAccess
  "Springfield City Group / Santo Santoro"
  "Queensland Health Minister"
  "Queensland ministerial diary, 16 January 2025"
  "Maha Sinnathamby, Raynuha Sinnathamby, Bob Sharpless and registered lobbyist Santo Santoro met the Health Minister to introduce Springfield City Group and provide an update on Springfield. Exact asks and downstream decisions remain unresolved."
  true

springfieldSantoroCustomerServicesMeeting : Receipt
springfieldSantoroCustomerServicesMeeting = receipt lobbyingAccess
  "Springfield City Group / Santo Santoro"
  "Queensland Customer Services/Open Data/Small Business Minister"
  "Queensland ministerial diary, 4 February 2025"
  "Santo Santoro, Maha Sinnathamby, Raynuha Sinnathamby, Russell Luhrs and Jim Varghese attended a recorded 'Lobbyist Introductory Meeting'. Exact subject matter beyond the diary label remains unresolved."
  true

springfieldSantoroFinanceMeeting : Receipt
springfieldSantoroFinanceMeeting = receipt lobbyingAccess
  "Springfield Land Corporation / Santo Santoro"
  "Queensland Finance/Trade/Employment/Training Minister's office"
  "Queensland ministerial diary, 12 February 2025"
  "Maha Sinnathamby, Bob Sharpless, Richard Eden and registered lobbyist Santo Santoro attended a recorded Springfield Land Corporation meeting with the Finance/Trade/Employment/Training Minister's office. Exact asks remain unresolved."
  true

springfieldSantoroTAFESubject : Receipt
springfieldSantoroTAFESubject = receipt lobbyingSubject
  "Springfield City Group / Santo Santoro"
  "Queensland Finance/Trade/Employment/Training office"
  "Queensland Chief of Staff diary, 10 April 2025"
  "A diary entry records Santo Santoro and Springfield City Group CEO Richard Eden in a meeting whose stated purpose was 'Discussion on TAFE premises, Springfield'. This pays one exact lobbying subject, not the desired outcome, decision, consideration or causal effect."
  true

springfieldSantoroPremierOfficeMeeting : Receipt
springfieldSantoroPremierOfficeMeeting = receipt lobbyingAccess
  "Springfield Land Corporation / Santo Santoro"
  "Queensland Premier's office"
  "Queensland Chief of Staff diary, 16 April 2025"
  "The Premier's office diary records Santo Santoro, identified with Springfield Land Corporation and as lobbyist, and Springfield Health City chair Rob Stable in a meeting with Springfield City Group. Exact requests/outcomes remain unresolved."
  true

springfieldLnpDonation2019 : Receipt
springfieldLnpDonation2019 = receipt politicalDonation
  "Springfield Land Corporation"
  "Liberal National Party of Queensland"
  "Electoral Commission of Queensland Electronic Disclosure System"
  "The ECQ ledger records a AUD 7,000 Springfield Land Corporation gift to the Liberal National Party of Queensland on 15 March 2019. Donation does not establish influence, quid pro quo or decision causation."
  true

springfieldEnergexAlliance : Receipt
springfieldEnergexAlliance = receipt gasInfrastructureAlliance
  "Springfield Land Corporation"
  "Energex"
  "ABC News, 30 April 2004"
  "A contemporaneous report states that Energex and Springfield Land Corporation formed an alliance to develop gas and electricity networks for Springfield; Energex's CEO referred to 8,000 gas connections and common gas/electric trenching. The underlying alliance instrument remains unpaid."
  true

springfieldEngieAlliance : Receipt
springfieldEngieAlliance = receipt longTermEnergyAlliance
  "Greater Springfield / Springfield City Group"
  "ENGIE"
  "ENGIE public announcement, 2018"
  "ENGIE announced a long-term alliance with Greater Springfield focused on integrated energy, storage and zero-net-energy ambitions. This is a later energy-system partnership distinct from the historical Energex gas/electric alliance."
  true

canonicalReceiptRound : List Receipt
canonicalReceiptRound =
  cityWestSale ∷ springfieldVillageTenantStack ∷ orionOwnershipAndValue ∷
  blackRockMirvacGrowth ∷ springfieldSantoroHealthMeeting ∷
  springfieldSantoroCustomerServicesMeeting ∷ springfieldSantoroFinanceMeeting ∷
  springfieldSantoroTAFESubject ∷ springfieldSantoroPremierOfficeMeeting ∷
  springfieldLnpDonation2019 ∷ springfieldEnergexAlliance ∷ springfieldEngieAlliance ∷ []

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

data TenantCommitmentImpliesExecutedLease : Set where
data MultipleLobbyingMeetingsImpliesDecisionCausation : Set where
data LobbyingSubjectImpliesDesiredOutcome : Set where
data PoliticalDonationImpliesInfluence : Set where
data SubstantialHoldingImpliesOperationalControl : Set where
data GasAllianceImpliesCurrentAssetOwnership : Set where
data EnergyAllianceImpliesCommonOwnership : Set where

tenantCommitmentDoesNotCreateExecutedLease : TenantCommitmentImpliesExecutedLease → ⊥
tenantCommitmentDoesNotCreateExecutedLease ()

lobbyingAccessDoesNotCreateDecisionCausation : MultipleLobbyingMeetingsImpliesDecisionCausation → ⊥
lobbyingAccessDoesNotCreateDecisionCausation ()

lobbyingSubjectDoesNotCreateDesiredOutcome : LobbyingSubjectImpliesDesiredOutcome → ⊥
lobbyingSubjectDoesNotCreateDesiredOutcome ()

politicalDonationDoesNotCreateInfluence : PoliticalDonationImpliesInfluence → ⊥
politicalDonationDoesNotCreateInfluence ()

substantialHoldingDoesNotCreateOperationalControl : SubstantialHoldingImpliesOperationalControl → ⊥
substantialHoldingDoesNotCreateOperationalControl ()

gasAllianceDoesNotCreateCurrentAssetOwnership : GasAllianceImpliesCurrentAssetOwnership → ⊥
gasAllianceDoesNotCreateCurrentAssetOwnership ()

energyAllianceDoesNotCreateCommonOwnership : EnergyAllianceImpliesCommonOwnership → ⊥
energyAllianceDoesNotCreateCommonOwnership ()

------------------------------------------------------------------------
-- Residual max-cut after this payment round.
------------------------------------------------------------------------

data ResidualCut : Set where
  cityWestSPVAndFinancing : ResidualCut
  santoroRemainingAsksAndOutcomes : ResidualCut
  originalEnergexAgreement : ResidualCut
  springfieldGasAssetTransferChain : ResidualCut
  orionOriginalCounterpartyAndRevenueRights : ResidualCut
  springfieldRetainedLandCadastre : ResidualCut
  blackRockFundVotingDecomposition : ResidualCut
  publicInfrastructureIncidence : ResidualCut
  parcelEcologicalIncidence : ResidualCut

record ResidualPriority : Set where
  constructor residual-priority
  field
    cut : ResidualCut
    priority : Nat
    instruction : String
open ResidualPriority public

canonicalResidualPriority : List ResidualPriority
canonicalResidualPriority =
  residual-priority cityWestSPVAndFinancing 100
    "Resolve purchaser SPV/title, beneficial interests, lender/security documents, equity split and project guarantees for the AUD 50m City West acquisition."
  ∷ residual-priority originalEnergexAgreement 100
    "Acquire the original Energex-Springfield alliance instrument or board/project records fixing rights, obligations, capital contributions and network ownership."
  ∷ residual-priority springfieldGasAssetTransferChain 100
    "Trace same-object gas assets/easements through Energex/Allgas/APA/AGIG/Stonepeak and quantify connection/fixed/throughput revenue incidence."
  ∷ residual-priority santoroRemainingAsksAndOutcomes 99
    "TAFE-premises subject matter is now paid for one April meeting; acquire briefing papers, correspondence, lobbyist contact-log entries and decision chronology for that meeting and the remaining Health/Finance/Premier/customer-services meetings."
  ∷ residual-priority orionOriginalCounterpartyAndRevenueRights 98
    "Resolve Mirvac's August-2002 Orion acquisition/agreement counterparties, land consideration, adjoining-land rights and any Springfield City Group continuing revenue/option interests."
  ∷ residual-priority springfieldRetainedLandCadastre 98
    "Build parcel-level retained/sold/JV/optioned land map for Springfield City Group and downstream developers."
  ∷ residual-priority blackRockFundVotingDecomposition 97
    "Decompose the 7.70% Mirvac substantial holding by BlackRock legal entity/fund/mandate and voting/disposal authority."
  ∷ residual-priority publicInfrastructureIncidence 96
    "Quantify public capital, developer contributions, rates/taxes and service obligations supporting each private asset layer."
  ∷ residual-priority parcelEcologicalIncidence 95
    "Join parcel-level habitat/heat/water/traffic burdens to the private value-capture ledger."
  ∷ []
