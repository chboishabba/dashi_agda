module DASHI.Cognition.EpsteinValarInvestmentLifecycle20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinThielValarDirectSolicitation20261014Exact as Solicitation
import DASHI.Cognition.EpsteinValarCapitalLedgerClosure20261014Exact as Ledger
import DASHI.Cognition.EpsteinValarFundIVRenewedSolicitationBoundary20261014Exact as FundIV

------------------------------------------------------------------------
-- EPSTEIN / SOUTHERN TRUST / VALAR INVESTMENT LIFECYCLE — 2026-10-15
--
-- This owner binds already-paid solicitation, LP commitment, capital-account,
-- valuation and later solicitation states into one lifecycle without collapsing:
--   * commitment into paid capital;
--   * fund value into realised cash;
--   * renewed solicitation into a completed later-fund investment;
--   * LP economic exposure into portfolio-company control.
------------------------------------------------------------------------

data LifecycleStage : Set where
  directSolicitation : LifecycleStage
  lpCommitment : LifecycleStage
  paidCapital : LifecycleStage
  interimValuation : LifecycleStage
  performanceCommunication : LifecycleStage
  laterFundSolicitation : LifecycleStage
  estateUnrealisedEstimate : LifecycleStage

record LifecycleReceipt : Set where
  constructor lifecycle-receipt
  field
    stage : LifecycleStage
    date : String
    source : String
    boundedFinding : String
    amountUSD : Nat
    paid : Bool
    realisedCash : Bool
open LifecycleReceipt public

thielSolicitation2014 : LifecycleReceipt
thielSolicitation2014 = lifecycle-receipt
  directSolicitation "2014-11-15" "EFTA02594707 / EFTA01001339"
  "Peter Thiel directly introduced Andrew McCormack and James Fitzgerald to Epstein, described Valar as his early-stage venture platform, recommended that Epstein allocate USD10-20m, and offered to discuss it further in person."
  0 true false

fundIICommitment : LifecycleReceipt
fundIICommitment = lifecycle-receipt
  lpCommitment "2015" "EFTA00597489; Valar Fund II Southern Trust LP statement"
  "Southern Trust Company is named as limited partner in Valar Global Fund II with a USD15m commitment."
  15000000 true false

fundIIICommitment : LifecycleReceipt
fundIIICommitment = lifecycle-receipt
  lpCommitment "2016-2019" "EFTA00591792; EFTA00811797; Deutsche Bank transaction records"
  "Southern Trust Company is named as limited partner in Valar Global Fund III with a USD25m commitment. The complete commitment was ultimately funded through capital calls, but commitment date, payment date and carrying value remain distinct coordinates."
  25000000 true false

fundIISeptember2015State : LifecycleReceipt
fundIISeptember2015State = lifecycle-receipt
  paidCapital "2015-09-30" "EFTA00597489"
  "The unaudited Fund II LP statement records USD4.35m paid in, USD10.65m remaining and ending partner capital of USD4,147,529. A selected Deutsche Bank chart contains USD6.3m of Fund II rows through September 2015; that chart therefore cannot be treated as the authoritative exhaustive paid-in ledger for the statement date without reconciliation."
  4350000 true false

fundIIJune2018Value : LifecycleReceipt
fundIIJune2018Value = lifecycle-receipt
  interimValuation "2018-06-30" "EFTA00811795/96"
  "Fund II records USD14.55m paid in against the USD15m commitment and ending Southern Trust partner capital of USD21,000,471; distributions are recorded as zero on this statement."
  21000471 true false

fundIIIJune2018Value : LifecycleReceipt
fundIIIJune2018Value = lifecycle-receipt
  interimValuation "2018-06-30" "EFTA00811797 and Southern Trust valuation schedule"
  "Fund III records USD21m paid in against the USD25m commitment and ending Southern Trust partner capital of USD33,345,270. This is an LP accounting value, not cash proceeds."
  33345270 true false

september2018CarryingValues : LifecycleReceipt
september2018CarryingValues = lifecycle-receipt
  interimValuation "2018-09-30" "EFTA00811897..902 Southern Trust valuation report"
  "Southern Trust's September 2018 valuation report carries Valar Fund II at approximately USD21.000m and Fund III at approximately USD33.345m while separately recording funded cost of USD14.25m and USD21m. This pays cost-versus-carrying-value separation, not realised profit."
  54345740 true false

fundVResolicitation2018 : LifecycleReceipt
fundVResolicitation2018 = lifecycle-receipt
  laterFundSolicitation "2018-11-20" "EFTA01016101 / duplicate thread EFTA01029050"
  "Andrew McCormack solicited Epstein for the forthcoming Valar Fund V and described Funds II and III as Epstein's investments, quoting USD15m and USD25m invested respectively plus manager-reported gross MOIC/IRR figures. The same correspondence offered an N26 co-investment discussion. This pays continuing manager-investor solicitation; it does not establish a Fund V subscription."
  0 true false

fundPerformanceCommunication2019 : LifecycleReceipt
fundPerformanceCommunication2019 = lifecycle-receipt
  performanceCommunication "2019-02-06" "EFTA01029050"
  "McCormack sent Epstein estimated year-end capital-account balances of approximately USD40.75m for Fund II and USD49.69m for Fund III after Epstein asked for year-end numbers and how Fund V was progressing. These are manager-supplied unaudited estimates, not realised distributions."
  90440000 true false

estateEstimate2026 : LifecycleReceipt
estateEstimate2026 = lifecycle-receipt
  estateUnrealisedEstimate "2026-03-19" "House Oversight Darren Indyke deposition release"
  "Co-executor Darren Indyke described the two Valar interests as worth roughly USD172m and expected to expire or mature around 2026, while also indicating the estate accounting already included a Valar value. The estimate is unrealised and must not be added blindly to estate totals."
  172000000 true false

record LifecycleBoundary : Set where
  constructor lifecycle-boundary
  field
    directThielSolicitationPaid : Bool
    fundIIAndIIILPStatusPaid : Bool
    continuingValarManagerRelationshipPaid : Bool
    fundVCompletedInvestmentPaid : Bool
    accountingValueEqualsRealisedCash : Bool
    managerPerformanceFigureEqualsAuditedReturn : Bool
    lpExposureImpliesPortfolioControl : Bool
    lifecycleImpliesWrongdoing : Bool
open LifecycleBoundary public

canonicalLifecycleBoundary : LifecycleBoundary
canonicalLifecycleBoundary = lifecycle-boundary
  true true true false false false false false

data LaterSolicitationImpliesCompletedInvestment : Set where
data AccountingValueImpliesRealisedCash : Set where
data ManagerPerformanceImpliesAuditedReturn : Set where
data LPExposureImpliesPortfolioControl : Set where
data InvestmentLifecycleImpliesWrongdoing : Set where

laterSolicitationDoesNotCreateInvestment : LaterSolicitationImpliesCompletedInvestment → ⊥
laterSolicitationDoesNotCreateInvestment ()

accountingValueDoesNotCreateCash : AccountingValueImpliesRealisedCash → ⊥
accountingValueDoesNotCreateCash ()

managerPerformanceDoesNotCreateAuditedReturn : ManagerPerformanceImpliesAuditedReturn → ⊥
managerPerformanceDoesNotCreateAuditedReturn ()

lpExposureDoesNotCreatePortfolioControl : LPExposureImpliesPortfolioControl → ⊥
lpExposureDoesNotCreatePortfolioControl ()

lifecycleDoesNotCreateWrongdoing : InvestmentLifecycleImpliesWrongdoing → ⊥
lifecycleDoesNotCreateWrongdoing ()

------------------------------------------------------------------------
-- Remaining max-cut moves to realised economics and special rights.
------------------------------------------------------------------------

data LifecycleDebt : Set where
  realisedDistributionLedger : LifecycleDebt
  fundIIFinalCallReconciliation : LifecycleDebt
  executedSideLetters : LifecycleDebt
  fundIVFinalDisposition : LifecycleDebt
  fundVFinalDisposition : LifecycleDebt
  estateFinalValarDisposition : LifecycleDebt
  completeFundIIIPortfolioSchedule : LifecycleDebt

record LifecycleAcquisition : Set where
  constructor lifecycle-acquisition
  field
    debt : LifecycleDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open LifecycleAcquisition public

canonicalLifecycleAcquisition : List LifecycleAcquisition
canonicalLifecycleAcquisition =
  lifecycle-acquisition realisedDistributionLedger 100 true
    "Acquire Southern Trust/estate distributions and redemptions from Funds II/III so gross carrying-value growth is separated from realised net cash return, fees and carry."
  ∷ lifecycle-acquisition executedSideLetters 100 true
    "Acquire any executed side letters, co-investment rights, advisory-committee rights or fee concessions; absence of a located side letter must not be turned into proof none existed."
  ∷ lifecycle-acquisition estateFinalValarDisposition 100 true
    "Resolve the final 2026 disposition, extension, liquidation or distribution of the Valar interests and reconcile realised proceeds to estate accounting."
  ∷ lifecycle-acquisition fundVFinalDisposition 99 true
    "Resolve the late-2018/2019 Fund V solicitation to either signed/accepted/funded participation or an explicit non-close."
  ∷ lifecycle-acquisition fundIVFinalDisposition 98 true
    "Resolve the renewed Fund IV subscription-document process to a terminal accepted/funded or declined state."
  ∷ lifecycle-acquisition fundIIFinalCallReconciliation 98 true
    "Reconcile the Fund II selected bank-chart rows against dated LP statements and the final USD15m commitment without treating the selected chart as exhaustive."
  ∷ lifecycle-acquisition completeFundIIIPortfolioSchedule 97 true
    "Acquire the complete Fund III schedule and join Southern Trust's indirect economic exposure by date while preserving fund ownership versus LP control."
  ∷ []
