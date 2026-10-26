module DASHI.Cognition.EpsteinBlackAgreementInvoiceWorkJoin20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBlackEstatePlanningTransmission20261015Exact as Work
import DASHI.Cognition.EpsteinBlackPaymentScopeReconciliation20261014Exact as Payments

------------------------------------------------------------------------
-- BLACK / SOUTHERN TRUST AGREEMENT -> INVOICE -> WORK-SURFACE JOIN
-- 2026-10-15
--
-- The join is deliberately period/service scoped.  A contract covering estate
-- planning and a contemporaneous invoice/work product do not allocate an exact
-- dollar amount to an individual checklist item unless an invoice/deliverable
-- cross-reference says so.
------------------------------------------------------------------------

data JoinSurface : Set where
  serviceAgreement : JoinSurface
  invoice : JoinSurface
  transmittedChecklist : JoinSurface
  outsideCounselReview : JoinSurface
  paymentSchedule : JoinSurface

record AgreementInvoiceReceipt : Set where
  constructor agreement-invoice-receipt
  field
    label : String
    dateOrTerm : String
    source : String
    amountUSD : Nat
    surfaces : List JoinSurface
    boundedFinding : String
    paid : Bool
    exactChecklistItemAllocationPaid : Bool
open AgreementInvoiceReceipt public

serviceAgreement2013 : AgreementInvoiceReceipt
serviceAgreement2013 = agreement-invoice-receipt
  "Southern Trust / Black estate-planning service agreement"
  "2013-2014 service term"
  "EFTA00585599 / related agreement versions EFTA00589520, EFTA01114428, EFTA00585954, EFTA00691917"
  0
  (serviceAgreement ∷ paymentSchedule ∷ [])
  "Released agreement versions expressly describe Epstein, on behalf of Southern Trust, providing proprietary analyzing/evaluating/structuring services for Leon Black's estate planning and affiliated family/trust/entity structures. Versions contain different fee/term formulations; they must be version-reconciled before treating any one draft as controlling."
  true false

invoiceAlgorithms20140715 : AgreementInvoiceReceipt
invoiceAlgorithms20140715 = agreement-invoice-receipt
  "USD20m algorithms invoice"
  "2014-07-15"
  "EFTA00585292"
  20000000
  (invoice ∷ serviceAgreement ∷ [])
  "Southern Trust invoiced Leon Black USD20m for provision of algorithms for use in estate planning and related purposes. This directly pays invoice purpose and amount, not which checklist transaction or tax result consumed the algorithms."
  true false

checklistDuringAgreement : AgreementInvoiceReceipt
checklistDuringAgreement = agreement-invoice-receipt
  "Transmitted Black estate-planning checklist during paid service period"
  "2014-01-21"
  "EFTA00982173 plus attached EFTA00583490 checklist"
  0
  (transmittedChecklist ∷ serviceAgreement ∷ [])
  "Black Family Partners sent Epstein an updated Leon Black estate-planning/restructuring checklist during the period covered by the released Southern Trust service agreements. This pays contemporaneous operational workstream access, not a dollar allocation to the checklist."
  true false

outsideCounselReview2017 : AgreementInvoiceReceipt
outsideCounselReview2017 = agreement-invoice-receipt
  "Sullivan & Cromwell memorandum review request"
  "2017-07-24"
  "EFTA00702518"
  0
  (outsideCounselReview ∷ [])
  "A recipient forwarded Epstein a Sullivan & Cromwell Leon Black estate-planning memorandum and asked him to identify issues. It pays continuing review involvement in 2017 but does not identify the fee or agreement provision governing that review."
  true false

record WorkJoinBoundary : Set where
  constructor work-join-boundary
  field
    paidServiceAgreementSurface : Bool
    paidEstatePlanningInvoiceSurface : Bool
    paidContemporaneousChecklistTransmission : Bool
    paidLaterOutsideCounselReview : Bool
    exactInvoiceToChecklistItemPaid : Bool
    exactPaymentToTaxSavingsPaid : Bool
    agreementVersionControllingTextFullyReconciled : Bool
    contemporaneousWorkImpliesEpsteinSoleAuthor : Bool
open WorkJoinBoundary public

canonicalWorkJoinBoundary : WorkJoinBoundary
canonicalWorkJoinBoundary = work-join-boundary
  true true true true false false false false

data PeriodJoinImpliesItemAllocation : Set where
data WorkstreamAccessImpliesSoleAuthorship : Set where
data InvoicePurposeImpliesMeasuredTaxSavings : Set where

periodJoinDoesNotCreateItemAllocation : PeriodJoinImpliesItemAllocation → ⊥
periodJoinDoesNotCreateItemAllocation ()

workstreamAccessDoesNotCreateSoleAuthorship : WorkstreamAccessImpliesSoleAuthorship → ⊥
workstreamAccessDoesNotCreateSoleAuthorship ()

invoiceDoesNotCreateMeasuredTaxSavings : InvoicePurposeImpliesMeasuredTaxSavings → ⊥
invoiceDoesNotCreateMeasuredTaxSavings ()

------------------------------------------------------------------------
-- Remaining work-payment cut.
------------------------------------------------------------------------

data WorkJoinDebt : Set where
  controllingAgreementVersion : WorkJoinDebt
  invoiceToWireReconciliation : WorkJoinDebt
  executedChecklistTransactions : WorkJoinDebt
  deliverableMetadataAndAuthorship : WorkJoinDebt
  acceptedRejectedAdvice : WorkJoinDebt
  taxOutcomeMeasurement : WorkJoinDebt

record WorkJoinAcquisition : Set where
  constructor work-join-acquisition
  field
    debt : WorkJoinDebt
    priority : Nat
    question : String
open WorkJoinAcquisition public

canonicalWorkJoinAcquisition : List WorkJoinAcquisition
canonicalWorkJoinAcquisition =
  work-join-acquisition controllingAgreementVersion 100
    "Reconcile signed versus draft Southern Trust/Black agreement versions and amendments so fee/term language is tied to the operative instrument." ∷
  work-join-acquisition invoiceToWireReconciliation 100
    "Join each dated invoice to the corresponding settled wire and legal payer entity; invoice amount is not bank-settlement proof by itself." ∷
  work-join-acquisition executedChecklistTransactions 100
    "Join checklist items to executed trust releases, decantings, assignments, notes and tax instruments, distinguishing planned/reviewed from implemented advice." ∷
  work-join-acquisition deliverableMetadataAndAuthorship 99
    "Recover file metadata/version history and communications showing who drafted, revised and approved each material work product." ∷
  work-join-acquisition acceptedRejectedAdvice 99
    "Map Epstein proposals to accepted, modified or rejected implementation decisions by Black and professional advisers." ∷
  work-join-acquisition taxOutcomeMeasurement 98
    "Quantify realised tax/estate consequences only from executed transactions and returns, not from invoice descriptions or projected savings." ∷
  []
