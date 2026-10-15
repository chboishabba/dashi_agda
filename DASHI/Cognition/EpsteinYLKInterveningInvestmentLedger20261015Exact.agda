module DASHI.Cognition.EpsteinYLKInterveningInvestmentLedger20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinYLKAssetReturnLifecycle20261015Exact as Lifecycle
import DASHI.Cognition.EpsteinCOUQYLKAssetTransfer20261015Exact as Transfer

------------------------------------------------------------------------
-- YLK INTERVENING INVESTMENT / REALISATION LEDGER — 2008
--
-- Initial contributed value and later dissolution transfers are separated by
-- intervening sales, option positions, liquidating distributions, grants,
-- expenses and market movements.  Initial minus final is not an economic-loss
-- estimator without this ledger.
------------------------------------------------------------------------

data YLKAssetSurface : Set where
  donatedAppleShares : YLKAssetSurface
  appleOption : YLKAssetSurface
  bearABSLiquidatingDistribution : YLKAssetSurface
  investmentGainLoss : YLKAssetSurface
  qualifyingDistribution : YLKAssetSurface

record YLKRealisationReceipt : Set where
  constructor ylk-realisation-receipt
  field
    label : String
    dateOrYear : String
    source : String
    surface : YLKAssetSurface
    grossProceedsUSD : Nat
    basisUSD : Nat
    boundedFinding : String
    paid : Bool
open YLKRealisationReceipt public

apple4000Sale : YLKRealisationReceipt
apple4000Sale = ylk-realisation-receipt
  "Sale of donated 4,000 Apple shares"
  "2008-03-27"
  "YLK 2008 Form 990-PF Part IV"
  donatedAppleShares 0 0
  "The filed return lists 4,000 AAPL shares acquired by donation on 2 January 2008 and sold on 27 March 2008. This pays active disposition of donated Apple stock; exact proceeds/basis should be read from the complete row schedule before being encoded as numeric values."
  true

apple1000SaleMarch : YLKRealisationReceipt
apple1000SaleMarch = ylk-realisation-receipt
  "Sale of donated 1,000 Apple shares"
  "2008-03-31"
  "YLK 2008 Form 990-PF Part IV"
  donatedAppleShares 0 0
  "The return separately lists 1,000 donated AAPL shares acquired 3 January 2008 and sold 31 March 2008."
  true

apple1000SaleApril : YLKRealisationReceipt
apple1000SaleApril = ylk-realisation-receipt
  "Sale of donated 1,000 Apple shares"
  "2008-04-08"
  "YLK 2008 Form 990-PF Part IV"
  donatedAppleShares 0 0
  "The return separately lists another 1,000 donated AAPL shares acquired 3 January 2008 and sold 8 April 2008."
  true

appleCall2008 : YLKRealisationReceipt
appleCall2008 = ylk-realisation-receipt
  "Apple call-option position"
  "2008-11-04 to 2008-12-08"
  "YLK 2008 Form 990-PF Part IV"
  appleOption 0 0
  "The return records a purchased December 2008 AAPL call position, establishing active portfolio management beyond passive receipt of contributed securities."
  true

bearLiquidatingDistribution2008 : YLKRealisationReceipt
bearLiquidatingDistribution2008 = ylk-realisation-receipt
  "Bear Stearns ABS Overseas liquidating distribution"
  "2008"
  "YLK 2008 Form 990-PF Part IV"
  bearABSLiquidatingDistribution 2795849 3824029
  "YLK reports USD2,795,849 gross proceeds from a liquidating distribution of Bear Stearns ABS Overseas against USD3,824,029 basis, a realised tax loss of USD1,028,180 on that reported line. This is an intervening recovery/disposition after the COUQ assignment and must not be attributed back to COUQ after assignment."
  true

record InterveningLedgerBoundary : Set where
  constructor intervening-ledger-boundary
  field
    donatedAppleSalesPaid : Bool
    activeOptionTradingPaid : Bool
    bearLiquidatingDistributionPaid : Bool
    initialCapitalizationWasStaticEscrow : Bool
    initialMinusDissolutionEqualsLoss : Bool
    bearDistributionBelongsToCOUQ : Bool
    fullLifecycleNetReturnPaid : Bool
open InterveningLedgerBoundary public

canonicalInterveningLedgerBoundary : InterveningLedgerBoundary
canonicalInterveningLedgerBoundary = intervening-ledger-boundary
  true true true false false false false

data InitialMinusFinalImpliesLoss : Set where
data PostAssignmentDistributionImpliesAssignorRecovery : Set where
data SomeRealisationRowsImpliesCompleteLedger : Set where

initialMinusFinalDoesNotCreateLoss : InitialMinusFinalImpliesLoss → ⊥
initialMinusFinalDoesNotCreateLoss ()

postAssignmentDoesNotCreateAssignorRecovery : PostAssignmentDistributionImpliesAssignorRecovery → ⊥
postAssignmentDoesNotCreateAssignorRecovery ()

someRowsDoNotCreateCompleteLedger : SomeRealisationRowsImpliesCompleteLedger → ⊥
someRowsDoNotCreateCompleteLedger ()

------------------------------------------------------------------------
-- Max-cut: complete intervening economics.
------------------------------------------------------------------------

data YLKLedgerDebt : Set where
  complete2008CapitalGainSchedule : YLKLedgerDebt
  completeAppleShareDisposition : YLKLedgerDebt
  completeBearDistributionLedger : YLKLedgerDebt
  grantsAndExpenses2008to2011 : YLKLedgerDebt
  investmentIncome2008to2011 : YLKLedgerDebt
  finalDissolutionBalanceSheet : YLKLedgerDebt

record YLKLedgerAcquisition : Set where
  constructor ylk-ledger-acquisition
  field
    debt : YLKLedgerDebt
    priority : Nat
    question : String
open YLKLedgerAcquisition public

canonicalYLKLedgerAcquisition : List YLKLedgerAcquisition
canonicalYLKLedgerAcquisition =
  ylk-ledger-acquisition grantsAndExpenses2008to2011 100
    "Reconstruct every grant, operating expense and charitable distribution between initial capitalization and dissolution so the asset-return chain has a complete use-of-funds side." ∷
  ylk-ledger-acquisition investmentIncome2008to2011 100
    "Reconstruct dividends, interest, gains/losses and investment-management activity across YLK's lifetime; initial and terminal balances alone are insufficient." ∷
  ylk-ledger-acquisition completeAppleShareDisposition 99
    "Trace the full 201,939-share Apple contribution through sales, options, remaining holdings and realised/unrealised gains." ∷
  ylk-ledger-acquisition completeBearDistributionLedger 99
    "Trace all post-assignment Bear ABS cash/in-kind liquidating distributions after the 2008 return's USD2.796m line." ∷
  ylk-ledger-acquisition complete2008CapitalGainSchedule 98
    "Extract every Part IV row with proceeds, basis and gain/loss to produce a complete 2008 realised-investment ledger." ∷
  ylk-ledger-acquisition finalDissolutionBalanceSheet 98
    "Reconcile the final YLK balance sheet and dissolution transfers to the Wexner Family Charitable Fund without converting book-value changes into unexplained loss."
  ∷ []
