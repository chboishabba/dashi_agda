module DASHI.Cognition.EpsteinBlackPaymentScopeReconciliation20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBlackApolloSameObjectReceiptRound20261014Exact as BlackApollo
import DASHI.Cognition.EpsteinBlack2012ApolloRelatedAssetSaleExact as Sale2012

------------------------------------------------------------------------
-- BLACK PAYMENT-SCOPE RECONCILIATION — 2026-10-14
--
-- Two commonly repeated totals use different scopes:
--   * Dechert: USD158m in professional-service payments, 2013-2017;
--   * Senate/Treasury/Bank of America: USD169.8m in 18 wires from Black
--     accounts to Epstein-controlled accounts, 2012-2017.
--
-- The banking total is not safely relabelled "fees" transaction-by-transaction.
-- The 2012 USD5.5m-class transfer is strongly tied to an asset purchase. The
-- 2016 USD6.3m annual amount remains a high-priority classification residual.
------------------------------------------------------------------------

record AnnualBankWireTotal : Set where
  constructor annual-bank-wire-total
  field
    year : Nat
    amountUSD : Nat
    source : String
    officialAnnualTotalPaid : Bool
    allUnderlyingWireObjectsPubliclyResolved : Bool
open AnnualBankWireTotal public

black2012 : AnnualBankWireTotal
black2012 = annual-bank-wire-total 2012 5500000
  "Senate Finance 2026 Looking the Other Way report, Bank of America/Treasury SAR review"
  true true

black2013 : AnnualBankWireTotal
black2013 = annual-bank-wire-total 2013 50000000
  "Senate Finance 2026 Looking the Other Way report"
  true true

black2014 : AnnualBankWireTotal
black2014 = annual-bank-wire-total 2014 70000000
  "Senate Finance 2026 Looking the Other Way report"
  true true

black2015 : AnnualBankWireTotal
black2015 = annual-bank-wire-total 2015 30000000
  "Senate Finance 2026 Looking the Other Way report"
  true true

black2016 : AnnualBankWireTotal
black2016 = annual-bank-wire-total 2016 6300000
  "Senate Finance 2026 Looking the Other Way report"
  true false

black2017 : AnnualBankWireTotal
black2017 = annual-bank-wire-total 2017 8000000
  "Senate Finance 2026 Looking the Other Way report"
  true true

annualBankWireTotals : List AnnualBankWireTotal
annualBankWireTotals = black2012 ∷ black2013 ∷ black2014 ∷ black2015 ∷ black2016 ∷ black2017 ∷ []

record ScopeReconciliation : Set where
  constructor scope-reconciliation
  field
    dechertServiceFeesUSD : Nat
    senateBankWireTotalUSD : Nat
    arithmeticDifferenceUSD : Nat
    wireCount : Nat
    year2012AmountUSD : Nat
    year2016AmountUSD : Nat
    year2012AssetSaleClassPaid : Bool
    year2016ClassPaid : Bool
    senateTotalEqualsProfessionalFees : Bool
    differenceMeansHiddenFeeByDefinition : Bool
open ScopeReconciliation public

canonicalScopeReconciliation : ScopeReconciliation
canonicalScopeReconciliation = scope-reconciliation
  158000000 169800000 11800000 18 5500000 6300000 true false false false

record SARScopeReceipt : Set where
  constructor sar-scope-receipt
  field
    source : String
    firstSARFlaggedUSD : Nat
    secondSARAdded2012USD : Nat
    secondSARAdded2017USD : Nat
    bankSaidVerifiableBusinessPurposeAbsent : Bool
    bankStatementEqualsAdjudicatedIllegality : Bool
open SARScopeReceipt public

canonicalSARScopeReceipt : SARScopeReceipt
canonicalSARScopeReceipt = sar-scope-receipt
  "Senate Finance 2026 report summarising Bank of America February and October 2020 SARs"
  156000000 5500000 8000000 true false

------------------------------------------------------------------------
-- The Senate report itself contains another scope distinction:
-- Southern Trust tax returns reported ~USD184m revenue in 2013-2017; the
-- forensic accountant attributed USD158m to Black, while Senate SAR review
-- describes approximately USD166m of Black-account wires to Southern Trust in
-- the same broad period. These are different accounting/evidence surfaces.
------------------------------------------------------------------------

record SouthernTrustRevenueScope : Set where
  constructor southern-trust-revenue-scope
  field
    reportedRevenueUSD : Nat
    amadorBlackRevenueUSD : Nat
    senateBlackWireApproxUSD : Nat
    taxRevenueEqualsWireFlow : Bool
open SouthernTrustRevenueScope public

canonicalSouthernTrustRevenueScope : SouthernTrustRevenueScope
canonicalSouthernTrustRevenueScope = southern-trust-revenue-scope
  184000000 158000000 166000000 false

------------------------------------------------------------------------
-- Non-collapse boundaries.
------------------------------------------------------------------------

data BankWireEqualsServiceFee : Set where
data SARSuspicionEqualsConviction : Set where
data ArithmeticDifferenceEqualsConcealedFee : Set where
data RevenueEqualsWireFlow : Set where
data AnnualTotalCreatesUnknownWirePurpose : Set where

bankWireDoesNotAutoBecomeServiceFee : BankWireEqualsServiceFee → ⊥
bankWireDoesNotAutoBecomeServiceFee ()

sarSuspicionDoesNotCreateConviction : SARSuspicionEqualsConviction → ⊥
sarSuspicionDoesNotCreateConviction ()

arithmeticDifferenceDoesNotCreateConcealedFee : ArithmeticDifferenceEqualsConcealedFee → ⊥
arithmeticDifferenceDoesNotCreateConcealedFee ()

revenueDoesNotEqualWireFlow : RevenueEqualsWireFlow → ⊥
revenueDoesNotEqualWireFlow ()

annualTotalDoesNotCreateUnknownPurpose : AnnualTotalCreatesUnknownWirePurpose → ⊥
annualTotalDoesNotCreateUnknownWirePurpose ()

------------------------------------------------------------------------
-- Remaining reconciliation cut.
------------------------------------------------------------------------

data ReconciliationDebt : Set where
  classify2016SixPointThree : ReconciliationDebt
  reconstructAll18Wires : ReconciliationDebt
  reconcile156mFirstSAR : ReconciliationDebt
  reconcile166mSouthernTrustApproximation : ReconciliationDebt
  exact2012SaleClosingAllocation : ReconciliationDebt
  serviceFeeToInvoiceLedger : ReconciliationDebt

record ReconciliationAcquisition : Set where
  constructor reconciliation-acquisition
  field
    debt : ReconciliationDebt
    priority : Nat
    question : String
open ReconciliationAcquisition public

canonicalReconciliationAcquisition : List ReconciliationAcquisition
canonicalReconciliationAcquisition =
  reconciliation-acquisition classify2016SixPointThree 100
    "Resolve the individual 2016 Bank-of-America-originating wire(s) totaling USD6.3m, recipient account/entity and economic purpose; this is the largest remaining classification component of the USD11.8m difference."
  ∷ reconciliation-acquisition reconstructAll18Wires 100
    "Build the exact 18-wire Treasury/SAR ledger and classify each row as service fee, asset purchase, reimbursement, loan/gift/other or unresolved rather than assigning one aggregate narrative."
  ∷ reconciliation-acquisition reconcile156mFirstSAR 99
    "Reconstruct which wires Bank of America's February 2020 SAR counted in its USD156m subtotal and why the later SAR added the 2012 and 2017 wires."
  ∷ reconciliation-acquisition reconcile166mSouthernTrustApproximation 99
    "Reconcile Senate's approximately USD166m Southern Trust wire figure against tax-return revenue attribution and annual bank-wire totals without treating revenue and cash flow as identical."
  ∷ reconciliation-acquisition exact2012SaleClosingAllocation 98
    "Close the signed 2012 ESWW/AP SHL/AP Technology allocation and transfer mechanics so the USD5.5m component has final asset classification."
  ∷ reconciliation-acquisition serviceFeeToInvoiceLedger 98
    "Bind each Dechert professional-service payment to an invoice/agreement/work-product object and keep expense reimbursements or other transactions outside the fee ledger."
  ∷ []
