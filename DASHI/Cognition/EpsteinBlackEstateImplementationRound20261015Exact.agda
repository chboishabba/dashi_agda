module DASHI.Cognition.EpsteinBlackEstateImplementationRound20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBlackAgreementInvoiceWorkJoin20261015Exact as Agreement
import DASHI.Cognition.EpsteinBlackEstatePlanningTransmission20261015Exact as Work

------------------------------------------------------------------------
-- BLACK ESTATE-PLANNING IMPLEMENTATION ROUND — 2026-10-15
--
-- Direct workstream access/routing, executed instruments and implementation
-- status are distinct from authorship, professional responsibility and sole
-- causation. This owner pays what the primary records actually show.
------------------------------------------------------------------------

data ImplementationSurface : Set where
  jBlackTrustExecution : ImplementationSurface
  epsteinRoutingInstruction : ImplementationSurface
  initialFundingInstruction : ImplementationSurface
  apo2TrustCreation : ImplementationSurface
  trust97Decanting : ImplementationSurface
  gratFunding : ImplementationSurface
  gratAnnuityPayment : ImplementationSurface
  llcRestructuring : ImplementationSurface
  documentReview : ImplementationSurface

record ImplementationReceipt : Set where
  constructor implementation-receipt
  field
    label : String
    date : String
    source : String
    surfaces : List ImplementationSurface
    boundedFinding : String
    amountUSD : Nat
    implementedOrExecutedPaid : Bool
    epsteinSoleAuthorshipPaid : Bool
open ImplementationReceipt public

jBlackTrustExecuted : ImplementationReceipt
jBlackTrustExecuted = implementation-receipt
  "Executed J. Black Trust"
  "2014-04-29"
  "EFTA00292681 / EFTA00292702"
  (jBlackTrustExecution ∷ [])
  "The complete J. Black Trust agreement is dated 29 April 2014, names Leon David Black as grantor and Leon Black plus Melanie Spinella as trustees, and records USD2m initial funding. The instrument pays legal creation/execution and terms, not Epstein authorship of the trust text."
  2000000 true false

jBlackRoutingChain : ImplementationReceipt
jBlackRoutingChain = implementation-receipt
  "Epstein-requested J. Black Trust execution routing"
  "2014-04-29"
  "EFTA00370268 / EFTA00370270 / EFTA00370275 / EFTA00370276"
  (epsteinRoutingInstruction ∷ initialFundingInstruction ∷ jBlackTrustExecution ∷ [])
  "The email chain records Darren Indyke and Lesley Groff processing Epstein's request to send the J. Black Trust agreement to Melanie at Leon's office for execution/notarisation, with instructions concerning the USD2m transfer and document changes. This pays direct routing/instruction in the execution chain, but not sole legal authorship or proof that Black lacked independent decision authority."
  2000000 true false

apo2And97Decanting : ImplementationReceipt
apo2And97Decanting = implementation-receipt
  "APO2 creation and 1997 Trust decanting"
  "2014-04-02"
  "EFTA00987334"
  (apo2TrustCreation ∷ trust97Decanting ∷ [])
  "Ada Clapp's estate-planning update, forwarded to Epstein, states that the APO2 Declaration had been signed and was in existence, and that the 1997 Trust trustees had exercised discretion to decant non-GST-exempt principal to APO2. Notice had been given and most transfer documentation was complete, subject to two collateral/guaranty issues. This pays creation and trustee decanting action, while final asset transfer completion at that date remained conditional."
  0 true false

gratNo2Implementation : ImplementationReceipt
gratNo2Implementation = implementation-receipt
  "APO1 GRAT No. 2 funding and annuity"
  "2013-12-04 to 2014-03-03"
  "EFTA00987334"
  (gratFunding ∷ gratAnnuityPayment ∷ [])
  "The update states GRAT No. 2 was created 4 December 2013 and funded with a 34.53% LP interest in Black Family Partners. Leon Black received the first quarterly annuity on 3 March 2014, partly as USD27.5m cash and partly as BFP LP interests."
  27500000 true false

gratNo3Implementation : ImplementationReceipt
gratNo3Implementation = implementation-receipt
  "APO1 GRAT No. 3 creation and funding"
  "2014-03-04"
  "EFTA00987334"
  (gratFunding ∷ [])
  "The update states GRAT No. 3 was created 4 March 2014 and funded with BFP LP interests received from prior APO1/GRAT No. 2 annuity payments; valuation work for exact percentages/fair value was ongoing."
  0 true false

mayDocumentReview : ImplementationReceipt
mayDocumentReview = implementation-receipt
  "Clapp sends implementation-document review list to Epstein"
  "2014-05-27"
  "EFTA00989766"
  (documentReview ∷ llcRestructuring ∷ trust97Decanting ∷ [])
  "Ada Clapp asked Epstein to review/comment on roughly fourteen LDB 2011 LLC restructuring documents and roughly fifteen 1997 Trust decanting documents, plus related guaranty/65 Bleecker Street matters. This pays direct review involvement in implementation documentation, not authorship or final approval of each instrument."
  0 false false

juneAlmostComplete : ImplementationReceipt
juneAlmostComplete = implementation-receipt
  "2011 LLC restructuring and 97 Trust decanting document completion status"
  "2014-06-04"
  "EFTA00990280"
  (llcRestructuring ∷ trust97Decanting ∷ documentReview ∷ [])
  "Clapp reported that documents for the LDB 2011 LLC restructuring and 97 Trust decanting were almost complete, describing approximately thirty restructuring documents and twenty decanting documents and offering Epstein additional sale documents for review. This pays implementation-stage progress, not proof every contemplated transaction had closed by that date."
  0 false false

record ImplementationBoundary : Set where
  constructor implementation-boundary
  field
    jBlackTrustExecutedPaid : Bool
    epsteinExecutionRoutingPaid : Bool
    apo2CreationPaid : Bool
    trust97DecantingActionPaid : Bool
    gratImplementationPaid : Bool
    epsteinDocumentReviewPaid : Bool
    epsteinSoleDraftingPaid : Bool
    epsteinSoleCausationPaid : Bool
    blackIndependentDecisionAuthorityNegated : Bool
    everyChecklistItemImplemented : Bool
open ImplementationBoundary public

canonicalImplementationBoundary : ImplementationBoundary
canonicalImplementationBoundary = implementation-boundary
  true true true true true true false false false false

data RoutingImpliesSoleAuthorship : Set where
data ReviewImpliesSoleCausation : Set where
data ExecutedTransactionImpliesNoIndependentDecision : Set where
data SomeImplementationImpliesAllChecklistItemsImplemented : Set where

routingDoesNotCreateSoleAuthorship : RoutingImpliesSoleAuthorship → ⊥
routingDoesNotCreateSoleAuthorship ()

reviewDoesNotCreateSoleCausation : ReviewImpliesSoleCausation → ⊥
reviewDoesNotCreateSoleCausation ()

executionDoesNotEraseIndependentDecision : ExecutedTransactionImpliesNoIndependentDecision → ⊥
executionDoesNotEraseIndependentDecision ()

someImplementationDoesNotCreateAllImplementation : SomeImplementationImpliesAllChecklistItemsImplemented → ⊥
someImplementationDoesNotCreateAllImplementation ()

------------------------------------------------------------------------
-- Max-cut moves from implementation existence to provenance/economic effect.
------------------------------------------------------------------------

data ImplementationDebt : Set where
  completeChecklistExecutionMap : ImplementationDebt
  documentMetadataAuthorship : ImplementationDebt
  acceptedRejectedAdviceMap : ImplementationDebt
  operativeAgreementVersion : ImplementationDebt
  taxEstateOutcomeLedger : ImplementationDebt
  professionalAdvisorDecisionChain : ImplementationDebt

record ImplementationAcquisition : Set where
  constructor implementation-acquisition
  field
    debt : ImplementationDebt
    priority : Nat
    question : String
open ImplementationAcquisition public

canonicalImplementationAcquisition : List ImplementationAcquisition
canonicalImplementationAcquisition =
  implementation-acquisition completeChecklistExecutionMap 100
    "Map every material checklist item to executed, abandoned, superseded or still-pending instruments so partial implementation is not generalized to the whole plan." ∷
  implementation-acquisition documentMetadataAuthorship 100
    "Recover metadata/version history and drafting communications for executed trusts, decantings, GRATs and LLC restructurings to allocate authorship and professional responsibility." ∷
  implementation-acquisition acceptedRejectedAdviceMap 99
    "Separate Epstein-origin proposals from professional-adviser recommendations and Black/family-office acceptance, modification or rejection decisions." ∷
  implementation-acquisition taxEstateOutcomeLedger 99
    "Measure realised tax, estate, cash-flow and asset-allocation consequences from returns/executed instruments instead of projected or invoiced purposes." ∷
  implementation-acquisition operativeAgreementVersion 98
    "Resolve which Southern Trust/Black service-agreement version controlled each implementation period and payment tranche." ∷
  implementation-acquisition professionalAdvisorDecisionChain 98
    "Map Paul Weiss, Sullivan & Cromwell, accountants, valuation firms and family-office roles in review/approval so operational participation is not collapsed into Epstein-only causation."
  ∷ []
