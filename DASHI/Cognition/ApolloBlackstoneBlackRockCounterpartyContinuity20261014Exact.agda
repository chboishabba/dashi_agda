module DASHI.Cognition.ApolloBlackstoneBlackRockCounterpartyContinuity20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- APOLLO / BLACKSTONE / BLACKROCK COUNTERPARTY CONTINUITY — 2026-10-14
--
-- Purpose: replace vague "same private-capital ecosystem" language with
-- instrument-typed, dated relationships. None of these edges retroactively
-- creates an Epstein->Blackstone/BlackRock relationship.
------------------------------------------------------------------------

data CounterpartySurface : Set where
  historicalCoOwnership : CounterpartySurface
  controlTransferWithRetainedMinority : CounterpartySurface
  listedEquityExposure : CounterpartySurface
  listedCREExposure : CounterpartySurface
  aiComputeFinancing : CounterpartySurface
  powerInfrastructureFinancing : CounterpartySurface
  personnelMobility : CounterpartySurface

record CounterpartyReceipt : Set where
  constructor counterparty-receipt
  field
    label : String
    date : String
    source : String
    surface : CounterpartySurface
    boundedFinding : String
    paid : Bool
    controlPaid : Bool
    epsteinEdgePaid : Bool
open CounterpartyReceipt public

nalcoCoOwnership : CounterpartyReceipt
nalcoCoOwnership = counterparty-receipt
  "Apollo/Blackstone co-ownership at Nalco"
  "2005-2006"
  "Nalco SEC ownership filing"
  historicalCoOwnership
  "SEC filings identify Blackstone funds and Apollo Investment Fund V / related co-investment partnerships as holders of Nalco common stock; Leon Black is identified as Apollo's founding principal while disclaiming beneficial ownership of Apollo-fund shares. This pays same-company co-ownership by sponsor funds, not common command."
  true false false

aquaTransfer2021 : CounterpartyReceipt
aquaTransfer2021 = counterparty-receipt
  "Aqua Finance Blackstone -> Athene/Apollo transition"
  "2021-11-29"
  "Apollo/Athene transaction announcement"
  controlTransferWithRetainedMinority
  "Athene agreed to acquire a controlling interest in Aqua Finance from Blackstone-managed funds at an approximately USD1bn valuation, with Apollo to manage the investment and Blackstone retaining a minority interest. This pays a direct transaction bridge and continuing co-ownership period."
  true true false

blackRockApolloGlobal2024 : CounterpartyReceipt
blackRockApolloGlobal2024 = counterparty-receipt
  "BlackRock beneficial ownership of Apollo Global"
  "2024-12-31"
  "SEC Schedule 13G filed 2025-01-31"
  listedEquityExposure
  "BlackRock reported beneficial ownership of more than 35.5m Apollo Global Management common shares at year-end 2024. Ordinary institutional beneficial ownership pays capital exposure and voting/dispositive rights reported under 13G, not operational control or a coordinated group."
  true false false

blackRockARI2025 : CounterpartyReceipt
blackRockARI2025 = counterparty-receipt
  "BlackRock exposure to Apollo Commercial Real Estate Finance"
  "2025-06-30"
  "SEC Schedule 13G/A filed 2025-07-17"
  listedCREExposure
  "BlackRock reported approximately 20.79m shares, 15.0% of Apollo Commercial Real Estate Finance common stock. The filing certifies ordinary-course investment and no control purpose."
  true false false

broadcomAIXPV2026 : CounterpartyReceipt
broadcomAIXPV2026 = counterparty-receipt
  "Apollo/Blackstone Broadcom AI XPV platform"
  "2026-06-09"
  "Apollo / Blackstone / Broadcom announcements"
  aiComputeFinancing
  "Apollo and Blackstone became anchor capital partners in an AI compute-financing platform launching with a USD35bn transaction for >1GW and targeting >20GW through 2028."
  true false false

williamsPower2026 : CounterpartyReceipt
williamsPower2026 = counterparty-receipt
  "Blackstone/Apollo/KKR Williams Power Innovation JV"
  "2026-07-13"
  "Williams / Blackstone transaction announcement"
  powerInfrastructureFinancing
  "Blackstone-led funds, with Apollo and KKR-managed vehicles, committed USD5.34bn for a 49% noncontrolling interest in five behind-the-meter power projects serving large-load/data-centre demand. Williams retains operating/commercial control."
  true false false

nvidiaFinancing2026 : CounterpartyReceipt
nvidiaFinancing2026 = counterparty-receipt
  "NVIDIA independent compute-financing platforms"
  "2026-08-10"
  "NVIDIA / Apollo announcements"
  aiComputeFinancing
  "NVIDIA announced independent strategic financing platforms with Apollo, BlackRock, Blackstone, Brookfield, Goldman Sachs and KKR intended collectively to mobilize over USD500bn of third-party AI-infrastructure capital. The firms are parallel/overlapping capital providers, not a single pooled command structure."
  true false false

blackRockToApolloPersonnel : CounterpartyReceipt
blackRockToApolloPersonnel = counterparty-receipt
  "BlackRock private-credit executive joins Apollo"
  "current biography"
  "Apollo Celia Yan biography"
  personnelMobility
  "Apollo identifies partner Celia Yan as previously BlackRock's APAC private-credit head and portfolio manager. Personnel mobility is an organizational bridge but does not back-project current Apollo strategy into BlackRock or vice versa."
  true false false

record CounterpartyBoundary : Set where
  constructor counterparty-boundary
  field
    repeatedApolloBlackstoneTransactionsPaid : Bool
    blackRockApolloListedExposurePaid : Bool
    currentAIOverlapPaid : Bool
    currentPowerOverlapPaid : Bool
    sameSectorImpliesCommonCommand : Bool
    blackRockEquityImpliesApolloControl : Bool
    modernCounterpartyOverlapImpliesEpsteinTie : Bool
    personnelMobilityImpliesTechniqueTransfer : Bool
open CounterpartyBoundary public

canonicalCounterpartyBoundary : CounterpartyBoundary
canonicalCounterpartyBoundary = counterparty-boundary
  true true true true false false false false

data SectorOverlapImpliesCommonCommand : Set where
data ListedExposureImpliesControl : Set where
data ModernOverlapImpliesHistoricalEpsteinEdge : Set where
data PersonnelMobilityImpliesTechniqueTransfer : Set where

sectorOverlapDoesNotCreateCommand : SectorOverlapImpliesCommonCommand → ⊥
sectorOverlapDoesNotCreateCommand ()

listedExposureDoesNotCreateControl : ListedExposureImpliesControl → ⊥
listedExposureDoesNotCreateControl ()

modernOverlapDoesNotCreateEpsteinTie : ModernOverlapImpliesHistoricalEpsteinEdge → ⊥
modernOverlapDoesNotCreateEpsteinTie ()

personnelMobilityDoesNotCreateTechniqueTransfer : PersonnelMobilityImpliesTechniqueTransfer → ⊥
personnelMobilityDoesNotCreateTechniqueTransfer ()

------------------------------------------------------------------------
-- Next acquisition: look for direct same-vehicle historical intersections,
-- not generic lists of large asset managers.
------------------------------------------------------------------------

data CounterpartyDebt : Set where
  historicalApolloBlackstoneDealAtlas : CounterpartyDebt
  blackRockApolloFundMandateOverlap : CounterpartyDebt
  blackRockApolloCreditCounterparties : CounterpartyDebt
  blackApolloBlackstoneSharedLPs : CounterpartyDebt
  epsteinEntityDirectBlackstoneBlackRockReceipt : CounterpartyDebt

record CounterpartyAcquisition : Set where
  constructor counterparty-acquisition
  field
    debt : CounterpartyDebt
    priority : Nat
    question : String
open CounterpartyAcquisition public

canonicalCounterpartyAcquisition : List CounterpartyAcquisition
canonicalCounterpartyAcquisition =
  counterparty-acquisition historicalApolloBlackstoneDealAtlas 100
    "Build the dated same-company/same-vehicle Apollo-Blackstone transaction history around the Leon Black era, including entry/exit economics and board/control rights rather than treating co-ownership as uniform partnership."
  ∷ counterparty-acquisition blackApolloBlackstoneSharedLPs 100
    "Resolve named institutional LPs/co-investors common to Black-era Apollo funds and Blackstone vehicles only from fund/SEC/pension disclosures; shared LP does not create shared strategy."
  ∷ counterparty-acquisition blackRockApolloCreditCounterparties 99
    "Map current credit/real-estate/AI vehicles in which BlackRock and Apollo are issuer-investor, lender-borrower, co-financier or secondary counterparties, keeping index ownership separate."
  ∷ counterparty-acquisition blackRockApolloFundMandateOverlap 98
    "Decompose BlackRock's Apollo/ARI positions by funds/mandates and voting authority where public 13G exhibits permit."
  ∷ counterparty-acquisition epsteinEntityDirectBlackstoneBlackRockReceipt 96
    "Continue direct Epstein-entity -> Blackstone/BlackRock search for investment, mandate, payment, meeting or transaction receipts; do not infer it from Apollo counterparty continuity."
  ∷ []
