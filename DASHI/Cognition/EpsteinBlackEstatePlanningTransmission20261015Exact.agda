module DASHI.Cognition.EpsteinBlackEstatePlanningTransmission20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBlackApolloOperationalTrustChecklist20261014Exact as Operational
import DASHI.Cognition.EpsteinBlackPaymentScopeReconciliation20261014Exact as Payments

------------------------------------------------------------------------
-- BLACK ESTATE-PLANNING WORK-PRODUCT TRANSMISSION — 2026-10-15
--
-- The repo already pays the Black->Epstein payment stream and operational
-- Apollo/trust interfaces.  This owner closes a different question: were
-- concrete estate-planning work objects transmitted to Epstein during the
-- paid advisory relationship?  Yes.  Receipt/review is still not authorship.
------------------------------------------------------------------------

data WorkSurface : Set where
  estatePlanningChecklist : WorkSurface
  trustAccounting : WorkSurface
  trustDecanting : WorkSurface
  taxReceivableAgreementWorkbook : WorkSurface
  outsideCounselMemorandum : WorkSurface
  paymentStream : WorkSurface

record WorkTransmissionReceipt : Set where
  constructor work-transmission-receipt
  field
    label : String
    date : String
    source : String
    surfaces : List WorkSurface
    boundedFinding : String
    directlyTransmittedToEpstein : Bool
    epsteinAuthorshipPaid : Bool
open WorkTransmissionReceipt public

blackChecklist20140121 : WorkTransmissionReceipt
blackChecklist20140121 = work-transmission-receipt
  "Black Family Partners sends updated estate-planning checklist to Epstein"
  "2014-01-21"
  "EFTA00982173"
  (estatePlanningChecklist ∷ trustAccounting ∷ trustDecanting ∷ [])
  "Ada Clapp of Black Family Partners emailed Jeffrey Epstein an updated nine-page Leon Black estate-planning and restructuring checklist and said she had updated it to show progress. The attached January 14 checklist assigns completed trust-accounting tasks to Family Office/Apollo and Apollo and tracks trust decanting, releases, cash-flow and entity restructuring. Direct transmission pays Epstein's operational access to the workstream, not authorship of every checklist item."
  true false

blackChecklist20131002 : WorkTransmissionReceipt
blackChecklist20131002 = work-transmission-receipt
  "Earlier Black estate-planning checklist"
  "2013-10-02"
  "EFTA01071282"
  (estatePlanningChecklist ∷ trustDecanting ∷ [])
  "An earlier seven-page Leon Black estate-planning and restructuring checklist records the workstream before the January 2014 progress update. Its presence in the released Epstein corpus supplies version lineage; the document alone does not establish who drafted each item."
  false false

apolloTRAPaymentWorkbook2014 : WorkTransmissionReceipt
apolloTRAPaymentWorkbook2014 = work-transmission-receipt
  "Apollo / Leon Black TRA payment workbook"
  "2014-03-26"
  "EFTA00616944"
  (taxReceivableAgreementWorkbook ∷ [])
  "A workbook titled Apollo / Leon Black / Tax Receivable Agreement (TRA) Payment Workbook / Tax Year 2013 is present in the released Epstein corpus. The workbook is a same-domain Black/Apollo financial work object, but its text does not itself name Epstein; corpus possession is not direct transmission or authorship."
  false false

outsideCounselMemo2017 : WorkTransmissionReceipt
outsideCounselMemo2017 = work-transmission-receipt
  "Sullivan & Cromwell Leon Black estate-planning memorandum forwarded to Epstein"
  "2017-07-24"
  "EFTA00702518"
  (outsideCounselMemorandum ∷ estatePlanningChecklist ∷ [])
  "A recipient forwarded Jeffrey Epstein a privileged-and-confidential July 12 Sullivan & Cromwell memorandum on Leon Black estate planning and asked him to identify issues. This pays continuing direct review access to Black estate-planning work product in 2017; it does not make Epstein the memorandum's author or Sullivan & Cromwell's client."
  true false

record WorkPaymentBridge : Set where
  constructor work-payment-bridge
  field
    largeBlackPaymentStreamPaidElsewhere : Bool
    concreteWorkObjectsPaid : Bool
    directWorkTransmissionPaid : Bool
    workContinuesInto2017Paid : Bool
    exactPaymentToSpecificWorkObjectPaid : Bool
    transmissionImpliesEpsteinAuthorship : Bool
    workObjectImpliesApolloRetainedEpstein : Bool
open WorkPaymentBridge public

canonicalWorkPaymentBridge : WorkPaymentBridge
canonicalWorkPaymentBridge = work-payment-bridge
  true true true true false false false

data TransmissionImpliesAuthorship : Set where
data WorkObjectImpliesPaymentAllocation : Set where
data ApolloInterfaceImpliesApolloRetention : Set where

transmissionDoesNotCreateAuthorship : TransmissionImpliesAuthorship → ⊥
transmissionDoesNotCreateAuthorship ()

workObjectDoesNotCreatePaymentAllocation : WorkObjectImpliesPaymentAllocation → ⊥
workObjectDoesNotCreatePaymentAllocation ()

apolloInterfaceDoesNotCreateRetention : ApolloInterfaceImpliesApolloRetention → ⊥
apolloInterfaceDoesNotCreateRetention ()

------------------------------------------------------------------------
-- Acquisition is now version/authorship/implementation/payment joining.
------------------------------------------------------------------------

data WorkDebt : Set where
  checklistAuthorshipHistory : WorkDebt
  checklistEmailThread : WorkDebt
  implementedTrustInstruments : WorkDebt
  traWorkbookTransmission : WorkDebt
  paymentInvoiceWorkJoin : WorkDebt
  acceptedRejectedAdviceMap : WorkDebt

record WorkAcquisition : Set where
  constructor work-acquisition
  field
    debt : WorkDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open WorkAcquisition public

canonicalWorkAcquisition : List WorkAcquisition
canonicalWorkAcquisition =
  work-acquisition implementedTrustInstruments 100 true
    "Join checklist tasks to executed trust, decanting, release, assignment and tax instruments so proposed/reviewed advice is separated from implemented transactions."
  ∷ work-acquisition paymentInvoiceWorkJoin 100 true
    "Join dated Black payment tranches/invoices to identifiable work periods or deliverables without allocating undifferentiated fees by assumption."
  ∷ work-acquisition checklistAuthorshipHistory 99 true
    "Recover metadata/version history showing who originated and edited each checklist item; direct transmission to Epstein is already paid but authorship is not."
  ∷ work-acquisition checklistEmailThread 99 true
    "Recover the surrounding Clapp/Epstein/family-office thread to resolve comments, requested changes and resulting decisions."
  ∷ work-acquisition acceptedRejectedAdviceMap 99 true
    "Map Epstein proposals to accepted, modified or rejected outcomes, preserving professional review as a distinct causal layer."
  ∷ work-acquisition traWorkbookTransmission 97 true
    "Resolve who sent EFTA00616944 to whom and how it was used; corpus presence alone remains below direct-transmission status."
  ∷ []
