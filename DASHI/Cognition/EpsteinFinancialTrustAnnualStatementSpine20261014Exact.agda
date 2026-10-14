module DASHI.Cognition.EpsteinFinancialTrustAnnualStatementSpine20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

data AccountingView : Set where
  filedYearEndStatement : AccountingView
  internalCashBasis : AccountingView

record AnnualStatement : Set where
  constructor annual-statement
  field
    year : Nat
    view : AccountingView
    cashUSD : Nat
    investmentsUSD : Nat
    totalAssetsUSD : Nat
    totalLiabilitiesUSD : Nat
    feeIncomeUSD : Nat
    investmentIncomeUSD : Nat
    netIncomeUSD : Nat
    distributionsUSD : Nat
    source : String
    primaryCourtOrReleasedCarrier : Bool
open AnnualStatement public

ftc1999 : AnnualStatement
ftc1999 = annual-statement 1999 filedYearEndStatement 0 0 24472690 898779 0 0 43701190 20427279
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013541; statement reports aggregate revenues USD43,965,458 rather than fee/investment split" true

ftc2000 : AnnualStatement
ftc2000 = annual-statement 2000 filedYearEndStatement 83682149 101643311 186971432 2952662 44296405 30746043 72465381 0
  "USVI v JPMorgan Document 268-52, Financial Trust 2000 statement" true

ftc2001 : AnnualStatement
ftc2001 = annual-statement 2001 filedYearEndStatement 46968234 179004937 226524334 1554467 46842367 20995777 62402963 0
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013533" true

ftc2002 : AnnualStatement
ftc2002 = annual-statement 2002 filedYearEndStatement 106082128 280140608 386707529 55075842 77680429 44720327 118191544 0
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013554" true

ftc2003 : AnnualStatement
ftc2003 = annual-statement 2003 filedYearEndStatement 60042683 335070706 395646418 563395 58954853 34282912 89951336 0
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013542" true

ftc2004Filed : AnnualStatement
ftc2004Filed = annual-statement 2004 filedYearEndStatement 157181657 405285955 563214706 87714150 53104052 73581555 108450613 0
  "USVI v JPMorgan Document 268-52, VI-JPM-000013518" true

ftc2004CashBasis : AnnualStatement
ftc2004CashBasis = annual-statement 2004 internalCashBasis 157192023 0 537033867 87714163 0 0 82499149 0
  "EFTA01304421 / EFTA01720157..163 — Financial Trust cash-basis books dated March 2005; investment-partnership subtotal USD202,189,381 and other securities/repo positions separately classified" true

ftc2005 : AnnualStatement
ftc2005 = annual-statement 2005 filedYearEndStatement 24682395 473416997 509564590 33832781 30879815 56854920 43481252 43250000
  "USVI v JPMorgan Document 194-22, VI-JPM-000013527" true

ftc2006 : AnnualStatement
ftc2006 = annual-statement 2006 filedYearEndStatement 55700201 303000394 487207276 11231303 65984969 8051002 70744165 70500000
  "USVI v JPMorgan Document 268-52, VI-JPM-000013514" true

ftc2007 : AnnualStatement
ftc2007 = annual-statement 2007 filedYearEndStatement 4732504 278443231 476580206 79 3965864 47053611 49333154 48729000
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013506" true

primaryPositiveFiledSpine : List AnnualStatement
primaryPositiveFiledSpine =
  ftc1999 ∷ ftc2000 ∷ ftc2001 ∷ ftc2002 ∷ ftc2003 ∷ ftc2004Filed ∷ ftc2005 ∷ ftc2006 ∷ ftc2007 ∷ []

data SignedResultClass : Set where
  positiveResult : SignedResultClass
  negativeResult : SignedResultClass
  zeroResult : SignedResultClass

record LossYearStatement : Set where
  constructor loss-year-statement
  field
    year : Nat
    cashUSD : Nat
    investmentsUSD : Nat
    totalAssetsUSD : Nat
    totalLiabilitiesUSD : Nat
    feeIncomeUSD : Nat
    investmentResultMagnitudeUSD : Nat
    investmentResultClass : SignedResultClass
    netResultMagnitudeUSD : Nat
    netResultClass : SignedResultClass
    distributionsUSD : Nat
    source : String
    primaryCourtCarrier : Bool
open LossYearStatement public

ftc2008 : LossYearStatement
ftc2008 = loss-year-statement 2008 145493041 57717468 364220131 8972 500000 95546771 negativeResult 100868968 negativeResult 11500000
  "USVI v JPMorgan Document 268-52, VI-JPM-000013509; total revenue includes USD9,680,688 related investment income and USD105,227,459 other related losses, net negative USD95,546,771" true

ftc2009 : LossYearStatement
ftc2009 = loss-year-statement 2009 134328728 53631852 334234043 23400 500000 11014238 negativeResult 12688515 negativeResult 17312000
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013550" true

ftc2010 : LossYearStatement
ftc2010 = loss-year-statement 2010 28173322 126843024 275155539 920845 100000 18008043 negativeResult 25397830 negativeResult 34578120
  "USVI v JPMorgan Document 268-52, VI-JPM-000013498" true

ftc2011 : LossYearStatement
ftc2011 = loss-year-statement 2011 29608037 109811863 244674225 459626 100000 9228140 negativeResult 12570094 negativeResult 17450000
  "USVI v JPMorgan Document 268-52, VI-JPM-000013497" true

ftc2012 : LossYearStatement
ftc2012 = loss-year-statement 2012 29428408 105787562 211789480 1264456 0 12277257 negativeResult 13994055 negativeResult 19695520
  "USVI v JPMorgan Document 268-52, VI-JPM-000013496" true

primaryLossYearSpine : List LossYearStatement
primaryLossYearSpine = ftc2008 ∷ ftc2009 ∷ ftc2010 ∷ ftc2011 ∷ ftc2012 ∷ []

record AnnualSpineClosure : Set where
  constructor annual-spine-closure
  field
    years1999to2012PrimaryPaid : Bool
    crisisLossSignsPreserved : Bool
    annualStatementsEqualClientLedger : Bool
    annualStatementsEqualCashflowLedger : Bool
open AnnualSpineClosure public

canonicalAnnualSpineClosure : AnnualSpineClosure
canonicalAnnualSpineClosure = annual-spine-closure true true false false

record AccountingBasisBoundary : Set where
  constructor accounting-basis-boundary
  field
    filed2004AssetsUSD : Nat
    cashBasis2004AssetsUSD : Nat
    viewsDiffer : Bool
    differenceImpliesOneCarrierFraudulent : Bool
    figuresMayBeAveragedWithoutReconciliation : Bool
    personalBalanceSheetMayBeAddedToFTCBalanceSheet : Bool
open AccountingBasisBoundary public

canonicalAccountingBasisBoundary : AccountingBasisBoundary
canonicalAccountingBasisBoundary = accounting-basis-boundary 563214706 537033867 true false false false

data DifferentAccountingViewsImpliesFraud : Set where
data AccountingViewsMayBeAveraged : Set where
data EpsteinPersonalPlusFTCMayBeAdded : Set where
data AnnualRevenueImpliesNamedClient : Set where

differentViewsDoNotCreateFraud : DifferentAccountingViewsImpliesFraud → ⊥
differentViewsDoNotCreateFraud ()
viewsCannotBeBlindlyAveraged : AccountingViewsMayBeAveraged → ⊥
viewsCannotBeBlindlyAveraged ()
personalAndCompanyCannotBeBlindlyAdded : EpsteinPersonalPlusFTCMayBeAdded → ⊥
personalAndCompanyCannotBeBlindlyAdded ()
annualRevenueDoesNotCreateNamedClient : AnnualRevenueImpliesNamedClient → ⊥
annualRevenueDoesNotCreateNamedClient ()

data AnnualSpineDebt : Set where
  accountingBasisReconciliation2004 : AnnualSpineDebt
  annualFeePayerAllocation : AnnualSpineDebt
  crisisLossRealisedUnrealisedSplit : AnnualSpineDebt
  annualCashflowReconciliation : AnnualSpineDebt

record AnnualSpineAcquisition : Set where
  constructor annual-spine-acquisition
  field
    debt : AnnualSpineDebt
    priority : Nat
    question : String
open AnnualSpineAcquisition public

canonicalAnnualSpineAcquisition : List AnnualSpineAcquisition
canonicalAnnualSpineAcquisition =
  annual-spine-acquisition annualFeePayerAllocation 100
    "Resolve fee income payer-by-payer for each filed year; annual fee totals are not a client list." ∷
  annual-spine-acquisition crisisLossRealisedUnrealisedSplit 100
    "Decompose 2008-2012 related-investment losses into realised loss, unrealised mark, write-down, subsidiary result and cash-flow effects before using them in crisis-incidence analysis." ∷
  annual-spine-acquisition accountingBasisReconciliation2004 99
    "Reconcile the filed 2004 USD563.215m asset statement against the internal cash-basis USD537.034m books by line item, consolidation and accounting basis." ∷
  annual-spine-acquisition annualCashflowReconciliation 99
    "Join annual income/distributions to bank, portfolio and inter-entity flows; year-end statements are snapshots, not complete cashflow ledgers." ∷
  []
