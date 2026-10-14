module DASHI.Economics.AICoreWeaveAggregateCustomerCashRealisation20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primarySECFiling : Source.SourceKind
primarySECFiling = Source.namedSourceKind "primary SEC filing"

coreWeaveQ22026Source : Source.AttributedSource
coreWeaveQ22026Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Form 10-Q for quarter ended June 30 2026"
  "SEC quarterly filing"
  "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  primarySECFiling
  "reports H1-2026 operating cash flow of USD 3.663B; states the increase was primarily driven by increased cash received from customers and timing of operating-expense payments; net accounts receivable declined from USD 3.169B at 2025 year-end to USD 2.541B at June 30 2026"
  Source.publicAttribution

record AggregateCustomerCashRealisation : Set where
  constructor aggregate-customer-cash-realisation
  field
    operatingCashFlowMillionUSD : Nat
    accountsReceivableStartMillionUSD : Nat
    accountsReceivableEndMillionUSD : Nat
    accountsReceivableDecreaseMillionUSD : Nat
    filingAttributesOCFIncreasePrimarilyToCustomerCash : Bool
    aggregateCustomerCashReceiptPaid : Bool
    namedPayerCashAttributionPaid : Bool
    exhaustiveTerminalIndependencePaid : Bool

open AggregateCustomerCashRealisation public

coreWeaveAggregateCustomerCash : AggregateCustomerCashRealisation
coreWeaveAggregateCustomerCash = aggregate-customer-cash-realisation
  3663 3169 2541 628 true true false false

operatingCashFlowMillionUSDIs3663 :
  operatingCashFlowMillionUSD coreWeaveAggregateCustomerCash ≡ 3663
operatingCashFlowMillionUSDIs3663 = refl

accountsReceivableDecreaseMillionUSDIs628 :
  accountsReceivableDecreaseMillionUSD coreWeaveAggregateCustomerCash ≡ 628
accountsReceivableDecreaseMillionUSDIs628 = refl

accountsReceivableReconciliation : 2541 + 628 ≡ 3169
accountsReceivableReconciliation = refl

aggregateCustomerCashReceiptObserved :
  aggregateCustomerCashReceiptPaid coreWeaveAggregateCustomerCash ≡ true
aggregateCustomerCashReceiptObserved = refl

namedPayerCashAttributionStillOpen :
  namedPayerCashAttributionPaid coreWeaveAggregateCustomerCash ≡ false
namedPayerCashAttributionStillOpen = refl

data AggregateCashIdentifiesNamedPayerPermission : Set where
data AggregateCashCreatesTerminalIndependencePermission : Set where

aggregateCashDoesNotIdentifyNamedPayer : AggregateCashIdentifiesNamedPayerPermission → ⊥
aggregateCashDoesNotIdentifyNamedPayer ()

aggregateCashDoesNotCreateTerminalIndependence : AggregateCashCreatesTerminalIndependencePermission → ⊥
aggregateCashDoesNotCreateTerminalIndependence ()

boundary : String
boundary =
  "CoreWeave's Q2-2026 filing pays aggregate customer-cash realisation: H1 operating cash flow was USD 3.663B, management attributes the increase primarily to increased cash received from customers plus expense-payment timing, and net accounts receivable declined by USD 628M from year-end. This answers the consumer 'is customer cash actually being collected in aggregate?' positively. It does not identify Microsoft, Meta, OpenAI or any other named payer as the source of a particular cash dollar and does not establish exhaustive terminal-payer independence."
