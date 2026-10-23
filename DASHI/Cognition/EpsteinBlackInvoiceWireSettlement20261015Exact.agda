module DASHI.Cognition.EpsteinBlackInvoiceWireSettlement20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBlackAgreementInvoiceWorkJoin20261015Exact as Work

------------------------------------------------------------------------
-- BLACK / SOUTHERN TRUST INVOICE -> SETTLED-WIRE RECEIPTS — 2026-10-15
------------------------------------------------------------------------

record WireReceipt : Set where
  constructor wire-receipt
  field
    date : String
    source : String
    payerDescription : String
    recipient : String
    amountUSD : Nat
    boundedFinding : String
    settledReceiptPaid : Bool
    exactDeliverableAllocationPaid : Bool
open WireReceipt public

wire20140715 : WireReceipt
wire20140715 = wire-receipt
  "2014-07-15"
  "Senate Finance letter 20 Mar 2026 citing EFTA01915809; paired invoice EFTA00585292"
  "Leon Black payment stream / underlying bank record"
  "Southern Trust Company"
  20000000
  "Senate Finance cites a same-day email from Richard Kahn to Epstein stating that the USD20m wire was received in Southern Trust. EFTA00585292 separately invoices Leon Black USD20m on 15 July 2014 for algorithms for estate-planning and related purposes. Date, amount, recipient and invoice purpose therefore align at transaction level; this does not allocate the payment among individual algorithms/checklist items or prove tax savings."
  true false

wireInstruction20130131 : WireReceipt
wireInstruction20130131 = wire-receipt
  "2013-01-31"
  "Senate Finance letter 20 Mar 2026 citing EFTA00396545"
  "Leon Black"
  "Southern Trust / instructed destination"
  15000000
  "The Senate letter cites Epstein instructing Indyke and Kahn to send Leon wire instructions for USD15m. This pays a payment-instruction surface; settlement should be joined to the corresponding bank receipt before labeling this row itself a settled wire."
  false false

wire2015BlackFamilyPartners : WireReceipt
wire2015BlackFamilyPartners = wire-receipt
  "2015"
  "Senate Finance letter 20 Mar 2026 citing EFTA01376741"
  "Black Family Partners LP c/o Apollo Global Management / Leon Black"
  "Epstein account / Southern Trust payment stream"
  20000000
  "The Senate letter cites Deutsche Bank employees noting that USD20m had arrived and that the wires came from Black Family Partners LP c/o Apollo Global Management, Leon Black. This pays bank-observed receipt and payer-description coordinates, not an Apollo corporate client relationship with Epstein."
  true false

record WireBoundary : Set where
  constructor wire-boundary
  field
    july2014InvoiceAndReceiptJoinPaid : Bool
    july2014InvoicePurposePaid : Bool
    july2014SpecificChecklistAllocationPaid : Bool
    january2013InstructionEqualsSettlement : Bool
    blackFamilyPartnersAddressImpliesApolloRetainedEpstein : Bool
    settledWireImpliesMeasuredTaxBenefit : Bool
open WireBoundary public

canonicalWireBoundary : WireBoundary
canonicalWireBoundary = wire-boundary
  true true false false false false

data SameDayInvoiceWireImpliesItemAllocation : Set where
data C_OAddressImpliesCorporateClient : Set where
data WireImpliesTaxBenefit : Set where

invoiceWireDoesNotCreateItemAllocation : SameDayInvoiceWireImpliesItemAllocation → ⊥
invoiceWireDoesNotCreateItemAllocation ()

careOfAddressDoesNotCreateCorporateClient : C_OAddressImpliesCorporateClient → ⊥
careOfAddressDoesNotCreateCorporateClient ()

wireDoesNotCreateTaxBenefit : WireImpliesTaxBenefit → ⊥
wireDoesNotCreateTaxBenefit ()

------------------------------------------------------------------------
-- Remaining max-cut is implementation/allocation, not July-2014 settlement.
------------------------------------------------------------------------

data WireDebt : Set where
  controllingAgreementVersion : WireDebt
  fullInvoiceWireLedger : WireDebt
  executedDeliverableJoin : WireDebt
  measuredTaxEstateOutcome : WireDebt

record WireAcquisition : Set where
  constructor wire-acquisition
  field
    debt : WireDebt
    priority : Nat
    question : String
open WireAcquisition public

canonicalWireAcquisition : List WireAcquisition
canonicalWireAcquisition =
  wire-acquisition executedDeliverableJoin 100
    "Join the paid July-2014 algorithms service and other payment tranches to executed trust/tax transactions and identifiable deliverables without inventing per-item allocation." ∷
  wire-acquisition controllingAgreementVersion 100
    "Resolve signed/operative agreement versions and amendments governing each paid tranche." ∷
  wire-acquisition fullInvoiceWireLedger 99
    "Pair every Black invoice/payment instruction with bank settlement and exact legal payer, extending the now-paid July 2014 join." ∷
  wire-acquisition measuredTaxEstateOutcome 98
    "Measure realised tax/estate consequences from executed instruments/returns, not invoice language alone." ∷
  []
