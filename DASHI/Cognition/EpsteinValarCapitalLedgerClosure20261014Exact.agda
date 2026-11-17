module DASHI.Cognition.EpsteinValarCapitalLedgerClosure20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinSouthernTrustInvestmentFlowAtlas20261014Exact as Flow

------------------------------------------------------------------------
-- VALAR CAPITAL LEDGER CLOSURE — 2026-10-14
--
-- This owner repairs the mismatch between the selected Deutsche Bank chart and
-- the actual Fund III commitment. The selected chart omitted an April 4 2017
-- USD2.5m capital-call wire. Direct bank-record indexing plus the LP-state
-- carrier lets Fund III be reconciled to the full USD25m commitment without
-- pretending the selected legal chart was exhaustive.
------------------------------------------------------------------------

record CapitalLedgerReceipt : Set where
  constructor capital-ledger-receipt
  field
    label : String
    source : String
    boundedFinding : String
    amountUSD : Nat
    sameObjectPaid : Bool
    realisedValuePaid : Bool
open CapitalLedgerReceipt public

missingFundIIIWire : CapitalLedgerReceipt
missingFundIIIWire = capital-ledger-receipt
  "Fund III omitted capital-call wire"
  "DOJ Dataset 10 EFTA01299550 / Deutsche Bank account record"
  "The bank record contains an outgoing USD2.5m Southern Trust payment to Silicon Valley Bank for Valar Global Fund III, described as a capital call, dated 4 April 2017. This row is absent from the later selected/highlighted transaction chart."
  2500000 true false

fundIII2018LPStatement : CapitalLedgerReceipt
fundIII2018LPStatement = capital-ledger-receipt
  "Valar Fund III LP state at 30 June 2018"
  "DOJ Dataset 9 EFTA00811797, identified Southern Trust limited-partner statement"
  "The Fund III Southern Trust LP statement records a USD25m commitment, USD21m paid-in, USD4m unfunded and ending partner capital of USD33,345,270 as of 30 June 2018. The statement is an LP accounting value, not a realised sale price."
  33345270 true false

fundIIIJanuary2019Call : CapitalLedgerReceipt
fundIIIJanuary2019Call = capital-ledger-receipt
  "Fund III January 2019 call"
  "DOJ/Deutsche Bank transaction record and January 2019 Southern Trust monthly report"
  "Southern Trust funded a further USD2.5m Valar III capital call in January 2019, taking cumulative paid capital from USD21m to USD23.5m."
  2500000 true false

fundII2018LPState : CapitalLedgerReceipt
fundII2018LPState = capital-ledger-receipt
  "Valar Fund II LP state at 30 June 2018"
  "DOJ Dataset 9 EFTA00811795/96"
  "Fund II records a USD15m commitment, USD14.55m paid-in, USD450k unfunded and ending partner capital of USD21,000,471."
  21000471 true false

record FundIIIClosure : Set where
  constructor fundIII-closure
  field
    commitmentUSD : Nat
    paidBy20180630USD : Nat
    unfunded20180630USD : Nat
    january2019CallUSD : Nat
    april2019FinalCallUSD : Nat
    finalPaidUSD : Nat
    commitmentReconciled : Bool
    selectedChartWasExhaustive : Bool
open FundIIIClosure public

canonicalFundIIIClosure : FundIIIClosure
canonicalFundIIIClosure = fundIII-closure
  25000000 21000000 4000000 2500000 1500000 25000000 true false

record CombinedValarState : Set where
  constructor combined-valar-state
  field
    fundIICommitmentUSD : Nat
    fundIIICommitmentUSD : Nat
    combinedCommitmentUSD : Nat
    combinedPaid20180630USD : Nat
    combinedLPValue20180630USD : Nat
    laterOralEstimateUSD : Nat
    oralEstimateIsRealisedProceeds : Bool
    oralEstimateCanBeAddedToEstateAccounting : Bool
open CombinedValarState public

canonicalCombinedValarState : CombinedValarState
canonicalCombinedValarState = combined-valar-state
  15000000 25000000 40000000 35550000 54345741 172000000 false false

record IndykeValuationReceipt : Set where
  constructor indyke-valuation-receipt
  field
    source : String
    depositionDate : String
    statedApproximateValueUSD : Nat
    boundedFinding : String
    officialVideoReleasePaid : Bool
    realisedExitPaid : Bool
open IndykeValuationReceipt public

indykeValarEstimate2026 : IndykeValuationReceipt
indykeValarEstimate2026 = indyke-valuation-receipt
  "House Oversight official 24 March 2026 release of Darren Indyke deposition video; transcript mirror"
  "2026-03-19"
  172000000
  "During his House Oversight deposition, co-executor Darren Indyke discussed a rough approximately USD172m value for the two Valar interests and clarified that the estate accounting already included some Valar value. This is oral/unrealised valuation testimony, not sale proceeds, and must not be double-counted with estate assets."
  true false

------------------------------------------------------------------------
-- Non-collapse boundaries.
------------------------------------------------------------------------

data SelectedChartEqualsCompleteLedger : Set where
data LPValueEqualsCashDistribution : Set where
data OralEstimateEqualsRealisedExit : Set where
data EstateValuePlusValarEstimateIsAdditive : Set where
data ValarInvestmentImpliesPalantirInvestment : Set where

selectedChartDoesNotCreateCompleteLedger : SelectedChartEqualsCompleteLedger → ⊥
selectedChartDoesNotCreateCompleteLedger ()

lpValueDoesNotCreateCashDistribution : LPValueEqualsCashDistribution → ⊥
lpValueDoesNotCreateCashDistribution ()

oralEstimateDoesNotCreateRealisedExit : OralEstimateEqualsRealisedExit → ⊥
oralEstimateDoesNotCreateRealisedExit ()

estateAndValarCannotBeBlindlyAdded : EstateValuePlusValarEstimateIsAdditive → ⊥
estateAndValarCannotBeBlindlyAdded ()

valarDoesNotCreatePalantirInvestment : ValarInvestmentImpliesPalantirInvestment → ⊥
valarDoesNotCreatePalantirInvestment ()

------------------------------------------------------------------------
-- Remaining Valar acquisition moves from existence/amount to rights,
-- underlying portfolio, distributions, ultimate disposition and fungible
-- capital capacity. Source-specific tracing is not needed for the systemic
-- balance-sheet claim unless a stronger earmarking proposition is sought.
------------------------------------------------------------------------

data ValarClosureDebt : Set where
  fundIIFullCallLedger : ValarClosureDebt
  subscriptionAgreements : ValarClosureDebt
  sideLettersAndLPPrivileges : ValarClosureDebt
  portfolioLookThrough : ValarClosureDebt
  distributionsAndFees : ValarClosureDebt
  estateExitDisposition : ValarClosureDebt
  capitalPoolCapacityChronology : ValarClosureDebt

record ValarClosureAcquisition : Set where
  constructor valar-closure-acquisition
  field
    debt : ValarClosureDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open ValarClosureAcquisition public

canonicalValarClosureAcquisition : List ValarClosureAcquisition
canonicalValarClosureAcquisition =
  valar-closure-acquisition sideLettersAndLPPrivileges 100 true
    "Acquire Southern Trust's Valar II/III side letters and special terms, if any; distinguish ordinary LP economics from preferential rights."
  ∷ valar-closure-acquisition portfolioLookThrough 100 true
    "Resolve Valar II/III underlying portfolio companies and Southern Trust's indirect economic exposure by fund/date without turning LP exposure into operational control."
  ∷ valar-closure-acquisition distributionsAndFees 99 true
    "Acquire distributions, management fees, carried-interest effects and net cash-return history so valuation growth is not confused with realised profit."
  ∷ valar-closure-acquisition estateExitDisposition 99 true
    "Trace the Valar interests through Epstein's estate, extensions/expiry and any final sale/distribution; reconcile against estate accounting to prevent double counting."
  ∷ valar-closure-acquisition subscriptionAgreements 98 true
    "Acquire executed subscription agreements and complete LP rights/governance terms for both funds."
  ∷ valar-closure-acquisition fundIIFullCallLedger 97 true
    "Reconstruct Fund II calls 6 onward to reconcile the entire USD15m commitment rather than relying on aggregate LP-statement totals."
  ∷ valar-closure-acquisition capitalPoolCapacityChronology 96 true
    "Reconstruct Southern Trust's aggregate liquidity/capital-capacity timeline around the Valar calls. Major Black/Rothschild inflows can contribute to a fungible pool without being treated as earmarked for Valar."
  ∷ []
