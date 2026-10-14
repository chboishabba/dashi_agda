module DASHI.Cognition.EpsteinFinancialTrustAnnualStatementSpine20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- FINANCIAL TRUST ANNUAL STATEMENT SPINE
--
-- Filed/year-end statements and internal cash-basis ledgers can legitimately
-- differ because of accounting basis, timing, consolidation and classification.
-- The discrepancy is an acquisition target; figures are not averaged or silently
-- selected to fit a preferred narrative.
------------------------------------------------------------------------

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
ftc1999 = annual-statement
  1999 filedYearEndStatement 0 0 24472690 898779 0 0 43701190 20427279
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013541; statement reports aggregate revenues USD43,965,458 rather than fee/investment split"
  true

ftc2000 : AnnualStatement
ftc2000 = annual-statement
  2000 filedYearEndStatement 83682149 101643311 186971432 2952662
  44296405 30746043 72465381 0
  "USVI v JPMorgan Document 268-52, VI-JPM filed Financial Trust 2000 statement"
  true

ftc2001 : AnnualStatement
ftc2001 = annual-statement
  2001 filedYearEndStatement 46968234 179004937 226524334 1554467
  46842367 20995777 62402963 0
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013533"
  true

ftc2003 : AnnualStatement
ftc2003 = annual-statement
  2003 filedYearEndStatement 60042683 335070706 395646418 563395
  58954853 34282912 89951336 0
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013542"
  true

ftc2004Filed : AnnualStatement
ftc2004Filed = annual-statement
  2004 filedYearEndStatement 157181657 405285955 563214706 87714150
  53104052 73581555 108450613 0
  "USVI v JPMorgan Document 268-52, VI-JPM-000013518"
  true

ftc2004CashBasis : AnnualStatement
ftc2004CashBasis = annual-statement
  2004 internalCashBasis 157192023 0 537033867 87714163
  0 0 82499149 0
  "EFTA01304421 / EFTA01720157..163 — Financial Trust cash-basis books dated March 2005; investment-partnership subtotal USD202,189,381 and other securities/repo positions are separately classified"
  true

ftc2005 : AnnualStatement
ftc2005 = annual-statement
  2005 filedYearEndStatement 24682395 473416997 509564590 33832781
  30879815 56854920 43481252 43250000
  "USVI v JPMorgan Document 194-22, VI-JPM-000013527"
  true

ftc2006 : AnnualStatement
ftc2006 = annual-statement
  2006 filedYearEndStatement 55700201 303000394 487207276 11231303
  65984969 8051002 70744165 70500000
  "USVI v JPMorgan Document 268-52, VI-JPM-000013514"
  true

primaryFiledSpine : List AnnualStatement
primaryFiledSpine =
  ftc1999 ∷ ftc2000 ∷ ftc2001 ∷ ftc2003 ∷ ftc2004Filed ∷ ftc2005 ∷ ftc2006 ∷ []

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
canonicalAccountingBasisBoundary = accounting-basis-boundary
  563214706 537033867 true false false false

data DifferentAccountingViewsImpliesFraud : Set where
data AccountingViewsMayBeAveraged : Set where
data EpsteinPersonalPlusFTCMayBeAdded : Set where

differentViewsDoNotCreateFraud : DifferentAccountingViewsImpliesFraud → ⊥
differentViewsDoNotCreateFraud ()

viewsCannotBeBlindlyAveraged : AccountingViewsMayBeAveraged → ⊥
viewsCannotBeBlindlyAveraged ()

personalAndCompanyCannotBeBlindlyAdded : EpsteinPersonalPlusFTCMayBeAdded → ⊥
personalAndCompanyCannotBeBlindlyAdded ()

------------------------------------------------------------------------
-- Max-cut after filling most of the early filed-statement spine.
------------------------------------------------------------------------

data AnnualSpineDebt : Set where
  primary2002Statement : AnnualSpineDebt
  primary2007Statement : AnnualSpineDebt
  primary2008Statement : AnnualSpineDebt
  primary2009Statement : AnnualSpineDebt
  primary2010Statement : AnnualSpineDebt
  primary2011Statement : AnnualSpineDebt
  primary2012Statement : AnnualSpineDebt
  accountingBasisReconciliation2004 : AnnualSpineDebt
  annualFeePayerAllocation : AnnualSpineDebt

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
  annual-spine-acquisition primary2002Statement 100
    "Acquire the primary 2002 FTC balance sheet/income statement and reconcile the approximately USD88m capital locator." ∷
  annual-spine-acquisition accountingBasisReconciliation2004 99
    "Reconcile the filed 2004 USD563.215m asset statement against the internal cash-basis USD537.034m books by line item, consolidation and accounting basis." ∷
  annual-spine-acquisition primary2007Statement 99 "Acquire primary 2007 filed/cash-basis statements." ∷
  annual-spine-acquisition primary2008Statement 99 "Acquire primary 2008 filed/cash-basis statements and isolate crisis-period realised/unrealised losses." ∷
  annual-spine-acquisition primary2009Statement 98 "Acquire primary 2009 statements." ∷
  annual-spine-acquisition primary2010Statement 98 "Acquire primary 2010 statements." ∷
  annual-spine-acquisition primary2011Statement 97 "Acquire primary 2011 statements." ∷
  annual-spine-acquisition primary2012Statement 97 "Acquire primary 2012 wind-down/termination statements before Southern Trust becomes the main operating vehicle." ∷
  []
