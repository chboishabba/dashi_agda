module DASHI.Cognition.EpsteinValarPortfolioLookthrough20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinValarCapitalLedgerClosure20261014Exact as Ledger
import DASHI.Cognition.EpsteinValarLPMechanics20261014Exact as Mechanics

------------------------------------------------------------------------
-- VALAR PORTFOLIO LOOK-THROUGH / LP INCIDENCE
--
-- Fund-level holdings produce indirect economic exposure for an LP. They do
-- not make Southern Trust a direct shareholder/controller of each portfolio
-- company and do not show that Epstein selected each investment.
------------------------------------------------------------------------

data PortfolioCompany : Set where
  vend : PortfolioCompany
  stashFinancial : PortfolioCompany
  eden : PortfolioCompany
  irisVR : PortfolioCompany
  camera : PortfolioCompany
  jopwell : PortfolioCompany
  unidentifiedScheduleRows : PortfolioCompany

record FundHolding : Set where
  constructor fund-holding
  field
    company : PortfolioCompany
    security : String
    costUSD : Nat
    fairValueUSD : Nat
    source : String
    fundLevelPaid : Bool
    southernTrustDirectOwnershipPaid : Bool
open FundHolding public

vendHolding : FundHolding
vendHolding = fund-holding vend "Series D Preferred Shares" 1336200 1382304
  "EFTA00811793 — Valar Global Fund II Schedule of Investments, 30 Jun 2018" true false

stashHolding : FundHolding
stashHolding = fund-holding stashFinancial "Series Seed-2 Preferred Shares" 169998 1360925
  "EFTA00811793 — Valar Global Fund II Schedule of Investments, 30 Jun 2018" true false

edenPreferred : FundHolding
edenPreferred = fund-holding eden "Series D Preference Shares" 509980 704361
  "EFTA00811794 — Valar Global Fund II Schedule of Investments, 30 Jun 2018" true false

irisSeed : FundHolding
irisSeed = fund-holding irisVR "Series AA Preferred Shares" 170000 258612
  "EFTA00811794 — Valar Global Fund II Schedule of Investments, 30 Jun 2018" true false

cameraSeed : FundHolding
cameraSeed = fund-holding camera "Series Seed Preferred Shares" 170000 265618
  "EFTA00811794 — Valar Global Fund II Schedule of Investments, 30 Jun 2018" true false

jopwellSeriesA : FundHolding
jopwellSeriesA = fund-holding jopwell "Series A-1 Preferred Stock" 226382 226382
  "EFTA00811794 — Valar Global Fund II Schedule of Investments, 30 Jun 2018" true false

record FundIISnapshot : Set where
  constructor fundII-snapshot
  field
    date : String
    totalInvestmentCostUSD : Nat
    totalInvestmentFairValueUSD : Nat
    totalUnrealizedGainUSD : Nat
    fundPartnerCapitalUSD : Nat
    southernTrustCommitmentUSD : Nat
    southernTrustPaidInUSD : Nat
    southernTrustEndingCapitalUSD : Nat
    southernTrustInceptionRealizedLossUSD : Nat
    southernTrustInceptionUnrealizedGainUSD : Nat
    southernTrustDistributionsUSD : Nat
open FundIISnapshot public

fundIIJune2018 : FundIISnapshot
fundIIJune2018 = fundII-snapshot
  "2018-06-30"
  52964083 107942704 54978621 108441624
  15000000 14550000 21000471 1895721 9741421 0

record LookthroughBoundary : Set where
  constructor lookthrough-boundary
  field
    fundPortfolioPaid : Bool
    southernTrustLPPositionPaid : Bool
    southernTrustIndirectEconomicExposurePaid : Bool
    exactSouthernTrustDollarExposurePerCompanyPaid : Bool
    southernTrustDirectPortfolioOwnershipPaid : Bool
    southernTrustPortfolioControlPaid : Bool
    epsteinSelectedEachPortfolioCompanyPaid : Bool
    fundValueEqualsSouthernTrustRealisedCash : Bool
open LookthroughBoundary public

canonicalLookthroughBoundary : LookthroughBoundary
canonicalLookthroughBoundary = lookthrough-boundary
  true true true false false false false false

data LPExposureImpliesDirectOwnership : Set where
data LPExposureImpliesPortfolioControl : Set where
data FundHoldingImpliesEpsteinSelection : Set where
data FundValueImpliesRealisedCash : Set where

lpExposureDoesNotCreateDirectOwnership : LPExposureImpliesDirectOwnership → ⊥
lpExposureDoesNotCreateDirectOwnership ()

lpExposureDoesNotCreatePortfolioControl : LPExposureImpliesPortfolioControl → ⊥
lpExposureDoesNotCreatePortfolioControl ()

fundHoldingDoesNotCreateEpsteinSelection : FundHoldingImpliesEpsteinSelection → ⊥
fundHoldingDoesNotCreateEpsteinSelection ()

fundValueDoesNotCreateRealisedCash : FundValueImpliesRealisedCash → ⊥
fundValueDoesNotCreateRealisedCash ()

------------------------------------------------------------------------
-- Estate-level deployment snapshot: exact total allocation and fresh call.
-- Exact January carrying values of Valar II/III are deliberately left open.
------------------------------------------------------------------------

record SouthernTrust201901Snapshot : Set where
  constructor southern-trust-201901-snapshot
  field
    date : String
    cashUSD : Nat
    fixedIncomeUSD : Nat
    equitiesUSD : Nat
    hedgeFundsUSD : Nat
    investmentsUSD : Nat
    totalAssetsUSD : Nat
    valarIIIFreshCallUSD : Nat
    exactJanuaryValarLineValuesPaid : Bool
    source : String
open SouthernTrust201901Snapshot public

january2019Snapshot : SouthernTrust201901Snapshot
january2019Snapshot = southern-trust-201901-snapshot
  "2019-01-31"
  64386774 48504739 115692726 105853201 56643626 416190539
  2500000 false
  "EFTA00811948 — Southern Trust valuation report; pays total asset allocation and January Valar III capital call, while exact January Valar line carrying values require schedule-level extraction"

------------------------------------------------------------------------
-- Next Pareto.
------------------------------------------------------------------------

data PortfolioDebt : Set where
  completeFundIISchedule : PortfolioDebt
  completeFundIIISchedule : PortfolioDebt
  southernTrustProRataAllocation : PortfolioDebt
  distributionsAndExitLedger : PortfolioDebt
  sideLettersCoInvestmentRights : PortfolioDebt
  portfolioCompanyBoardInformationRights : PortfolioDebt
  january2019ValarLineValues : PortfolioDebt

record PortfolioAcquisition : Set where
  constructor portfolio-acquisition
  field
    debt : PortfolioDebt
    priority : Nat
    question : String
open PortfolioAcquisition public

canonicalPortfolioAcquisition : List PortfolioAcquisition
canonicalPortfolioAcquisition =
  portfolio-acquisition completeFundIIISchedule 100
    "Acquire complete Fund III schedules of investments by date and join Southern Trust's LP capital account to indirect portfolio exposure without turning fund holdings into direct ownership." ∷
  portfolio-acquisition distributionsAndExitLedger 100
    "Reconstruct Southern Trust distributions and realised exits from Funds II/III; June 2018 Fund II statement pays zero distributions and separates realised loss from unrealised gain." ∷
  portfolio-acquisition sideLettersCoInvestmentRights 99
    "Resolve any Southern Trust side letter, co-investment, advisory-committee or enhanced-information rights beyond ordinary LP status." ∷
  portfolio-acquisition completeFundIISchedule 98
    "Recover the full Fund II June 2018 schedule including rows preceding the visible Vend/Stash segment so the portfolio atlas is exhaustive." ∷
  portfolio-acquisition southernTrustProRataAllocation 98
    "Resolve allocation methodology/ownership percentage over time before assigning exact Southern Trust dollar exposure to individual portfolio companies." ∷
  portfolio-acquisition january2019ValarLineValues 98
    "Extract exact Valar II/III carrying values from the January 2019 schedule instead of encoding absence of a located figure as zero." ∷
  portfolio-acquisition portfolioCompanyBoardInformationRights 97
    "Map Valar/GP board and information rights at portfolio companies separately from Southern Trust LP rights." ∷
  []
