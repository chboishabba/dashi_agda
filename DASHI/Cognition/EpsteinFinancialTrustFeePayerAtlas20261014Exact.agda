module DASHI.Cognition.EpsteinFinancialTrustFeePayerAtlas20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialTrustAnnualStatementSpine20261014Exact as Annual

------------------------------------------------------------------------
-- FINANCIAL TRUST FEE-PAYER ATLAS
--
-- Annual fee-income totals are accounting facts, not client identities. A
-- payer is promoted only by invoice, wire, contract, admission/testimony or an
-- equivalently same-object receipt. Revenue collapse after a relationship ends
-- is an allocation lead, not proof that the relationship supplied every dollar.
------------------------------------------------------------------------

data FeePayer : Set where
  highbridgeDubinSwieca : FeePayer
  wexnerFamilyOfficeOrRelated : FeePayer
  unidentifiedPayer : FeePayer

record FeePayerReceipt : Set where
  constructor fee-payer-receipt
  field
    year : Nat
    payer : FeePayer
    amountUSD : Nat
    source : String
    statedPurpose : String
    paymentPaid : Bool
    executedContinuingAgreementPaid : Bool
    wrongdoingPaid : Bool
open FeePayerReceipt public

highbridge2004MAndA : FeePayerReceipt
highbridge2004MAndA = fee-payer-receipt
  2004 highbridgeDubinSwieca 15000000
  "USVI v JPMorgan court filing paragraph 172 / JPMC Exhibits 194-195; EFTA02816421 invoice-wire lineage"
  "Financial Trust invoice and payment for merger-and-acquisition advice in connection with JPMorgan's acquisition of a majority interest in Highbridge. Court filing identifies Dubin & Swieca Holdings as payer and states JPMorgan itself did not pay Epstein the fee."
  true false false

record DraftConsultingReceipt : Set where
  constructor draft-consulting-receipt
  field
    effectiveDatePrinted : String
    parties : String
    totalFeeUSD : Nat
    annualInstallmentUSD : Nat
    numberOfInstallments : Nat
    source : String
    signaturesPresent : Bool
    executedAgreementPaid : Bool
    paymentsUnderAgreementPaid : Bool
open DraftConsultingReceipt public

highbridge2005Draft : DraftConsultingReceipt
highbridge2005Draft = draft-consulting-receipt
  "2005-06-01"
  "Highbridge Capital Management LLC and Financial Trust Company Inc.; Jeffrey Epstein designated to perform the services"
  2250000 450000 5
  "EFTA00589969..977 — revised consulting agreement sent by Ron Resnick to Darren Indyke, cc Glenn Dubin and others"
  false false false

record FeeEra : Set where
  constructor fee-era
  field
    period : String
    aggregateFeeIncomeUSD : Nat
    source : String
    exactPayerAllocationPaid : Bool
open FeeEra public

wexnerEraAccounting : FeeEra
wexnerEraAccounting = fee-era
  "2000-2006"
  377742890
  "sum of primary filed Financial Trust annual statements in EpsteinFinancialTrustAnnualStatementSpine20261014Exact"
  false

post2006Accounting : FeeEra
post2006Accounting = fee-era
  "2007-2012"
  5165864
  "sum of primary filed Financial Trust annual statements in EpsteinFinancialTrustAnnualStatementSpine20261014Exact"
  false

record AllocationSignal : Set where
  constructor allocation-signal
  field
    label : String
    source : String
    boundedFinding : String
    relationshipPaid : Bool
    revenueCollapsePaid : Bool
    solePayerPaid : Bool
    exactAmountPaid : Bool
open AllocationSignal public

wexnerAllocationSignal : AllocationSignal
wexnerAllocationSignal = allocation-signal
  "Wexner relationship / FTC fee-income collapse"
  "primary FTC annual statements plus public reporting/review of the Wexner-Epstein relationship ending in the mid-2000s"
  "Financial Trust's annual fee income drops sharply after 2006 while the long-running Wexner relationship ended in the same broad period. This is a high-value payer-allocation lead, but chronology/correlation does not establish that Wexner or Wexner-related entities supplied all or any particular unexplained annual fee amount without payer-level records."
  true true false false

record FeePayerBoundary : Set where
  constructor fee-payer-boundary
  field
    annualFeeTotalsPaid : Bool
    highbridge2004PaymentPaid : Bool
    highbridge2005DraftPaidAsDraft : Bool
    highbridge2005ExecutedPaid : Bool
    wexnerRelationshipPaid : Bool
    feeCollapsePaid : Bool
    revenueCollapseImpliesWexnerWasSolePayer : Bool
    clientRelationshipImpliesAllFees : Bool
    draftAgreementImpliesPayment : Bool
    annualFeeTotalImpliesNamedClient : Bool
open FeePayerBoundary public

canonicalFeePayerBoundary : FeePayerBoundary
canonicalFeePayerBoundary = fee-payer-boundary
  true true true false true true false false false false

data RevenueCollapseImpliesSolePayer : Set where
data ClientRelationshipImpliesAllFees : Set where
data DraftAgreementImpliesPayment : Set where
data AnnualFeeTotalImpliesNamedClient : Set where

revenueCollapseDoesNotCreateSolePayer : RevenueCollapseImpliesSolePayer → ⊥
revenueCollapseDoesNotCreateSolePayer ()

clientRelationshipDoesNotCreateAllFees : ClientRelationshipImpliesAllFees → ⊥
clientRelationshipDoesNotCreateAllFees ()

draftAgreementDoesNotCreatePayment : DraftAgreementImpliesPayment → ⊥
draftAgreementDoesNotCreatePayment ()

annualFeeTotalDoesNotCreateNamedClient : AnnualFeeTotalImpliesNamedClient → ⊥
annualFeeTotalDoesNotCreateNamedClient ()

------------------------------------------------------------------------
-- Pareto after first payer-level closure.
------------------------------------------------------------------------

data FeeDebt : Set where
  wexnerFamilyInterestInvoicesAndWires : FeeDebt
  remaining2004FeeAllocation : FeeDebt
  feeAllocation2005_2006 : FeeDebt
  highbridge2005ExecutionAndPayments : FeeDebt
  feeAllocation2000_2003 : FeeDebt
  post2006SmallFeeAllocation : FeeDebt

record FeeAcquisition : Set where
  constructor fee-acquisition
  field
    debt : FeeDebt
    priority : Nat
    question : String
open FeeAcquisition public

canonicalFeeAcquisition : List FeeAcquisition
canonicalFeeAcquisition =
  fee-acquisition wexnerFamilyInterestInvoicesAndWires 100
    "Acquire Financial Trust invoices, bank credits, Family Interest records and Wexner-family-office accounting sufficient to allocate annual fee income to Wexner-related counterparties without using chronology as payment proof." ∷
  fee-acquisition remaining2004FeeAllocation 100
    "Allocate the remaining USD38,104,052 of 2004 fee income after the paid USD15m Highbridge transaction using invoices/wires/contracts." ∷
  fee-acquisition feeAllocation2005_2006 99
    "Resolve the USD30,879,815 2005 and USD65,984,969 2006 fee totals payer-by-payer, including any Highbridge, Wexner/family-office or other counterparties." ∷
  fee-acquisition highbridge2005ExecutionAndPayments 99
    "Determine whether the June 2005 Highbridge consulting agreement was executed and whether any USD450k installments were invoiced/paid; the released copy is unsigned." ∷
  fee-acquisition feeAllocation2000_2003 98
    "Resolve payer-level support for the 2000-2003 fee totals, prioritising same-object Wexner/Family Interest records and large transaction counterparties." ∷
  fee-acquisition post2006SmallFeeAllocation 97
    "Identify the counterparties behind USD5,165,864 total fee income recorded across 2007-2012; low absolute amount may still clarify continuity after the Wexner relationship ended." ∷
  []
