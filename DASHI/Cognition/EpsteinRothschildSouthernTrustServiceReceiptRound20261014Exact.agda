module DASHI.Cognition.EpsteinRothschildSouthernTrustServiceReceiptRound20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBlackRothschildTransactionAtlas20261014Exact as Wires

------------------------------------------------------------------------
-- ROTHSCHILD / SOUTHERN TRUST SERVICE-AGREEMENT RECEIPTS — 2026-10-14
--
-- Agreement -> invoice -> near-matching payment chronology supplies contractual
-- context, but payer/version mismatches are preserved.  Downstream use is read
-- through a fungible capital-pool model: paid inflows increase Southern Trust's
-- deployment capacity; they need not be source-traced dollar-by-dollar unless
-- a stronger earmarking or payer-instruction claim is made.
------------------------------------------------------------------------

data RothschildServiceSurface : Set where
  riskAnalysis : RothschildServiceSurface
  estatePlanning : RothschildServiceSurface
  algorithmicWork : RothschildServiceSurface
  usDOJMatter : RothschildServiceSurface
  strategicBusinessMatter : RothschildServiceSurface
  invoice : RothschildServiceSurface
  bankWire : RothschildServiceSurface

record ServiceReceipt : Set where
  constructor service-receipt
  field
    label : String
    date : String
    source : String
    contractingSide : String
    counterparty : String
    statedFeeUSD : Nat
    surfaces : List RothschildServiceSurface
    boundedFinding : String
    instrumentExecutedBothSides : Bool
    paymentPerformancePaidByThisReceipt : Bool
    wrongdoingPaid : Bool
open ServiceReceipt public

septemberDraft : ServiceReceipt
septemberDraft = service-receipt
  "September 2015 Rothschild/STC draft"
  "2015-09"
  "EFTA00310331"
  "Ariane de Rothschild for herself/family/Edmond de Rothschild Holding S.A."
  "Southern Trust Company / Jeffrey Epstein"
  0
  (riskAnalysis ∷ estatePlanning ∷ algorithmicWork ∷ usDOJMatter ∷ [])
  "Released draft says Southern Trust/Epstein had been collaborating with Ariane de Rothschild/Rothschild Group on risk analysis, estate planning and algorithms, with a contingent fee ladder for DOJ matters. Fee/date fields for the base estate-planning work are blank in this draft."
  false false false

octoberHolding25m : ServiceReceipt
octoberHolding25m = service-receipt
  "5 October 2015 EDRH/STC USD25m agreement version"
  "2015-10-05"
  "EFTA00584881 and duplicate lineage"
  "Ariane de Rothschild on behalf of Edmond de Rothschild Holding S.A."
  "Southern Trust Company / Jeffrey Epstein"
  25000000
  (riskAnalysis ∷ algorithmicWork ∷ usDOJMatter ∷ [])
  "Agreement version states USD25m consideration for work specifically relating to outstanding matters between EDRH and the United States, payable shortly after EDRH pays the United States. Released copies must be evaluated by signature state rather than assuming every draft/version was operative."
  false false false

novemberAriane15m : ServiceReceipt
novemberAriane15m = service-receipt
  "3 November 2015 Ariane/STC USD15m agreement"
  "2015-11-03"
  "EFTA01125101"
  "Ariane de Rothschild personally"
  "Southern Trust Company / Darren Indyke vice-president addressee"
  15000000
  (strategicBusinessMatter ∷ estatePlanning ∷ [])
  "The November instrument says Southern Trust had been working with Ariane de Rothschild on strategic business matters and family estate planning and states a USD15m fee due by 30 November. The released image carries Ariane's manuscript signature while Southern Trust's signature line is unmarked."
  false false false

arianeInvoice15m : ServiceReceipt
arianeInvoice15m = service-receipt
  "15 December 2015 STC invoice to Ariane"
  "2015-12-15"
  "EFTA00586695 / duplicate EFTA01119622"
  "Southern Trust Company"
  "Ariane de Rothschild"
  15000000
  (invoice ∷ [])
  "Southern Trust invoiced Ariane de Rothschild USD15m pursuant to the 3 November 2015 agreement with Deutsche Bank Trust Company Americas wire instructions. Invoice establishes demand for payment, not payment itself."
  true false false

edmondSuisse10mWire : ServiceReceipt
edmondSuisse10mWire = service-receipt
  "17 December 2015 Edmond de Rothschild Suisse wire"
  "2015-12-17"
  "EFTA00080250 / DB-SDNY-0005122"
  "Edmond de Rothschild (Suisse) SA, Geneva"
  "Southern Trust Company"
  10000000
  (bankWire ∷ [])
  "Deutsche Bank transaction exhibit records a USD10m payment from Edmond de Rothschild (Suisse) SA to Southern Trust. Separate released instruments include bank-side strategic-business agreements in the USD10m/25m range, but this row itself states no purpose."
  true true false

benjamin15mWire : ServiceReceipt
benjamin15mWire = service-receipt
  "21 December 2015 Benjamin Edmond de Rothschild wire"
  "2015-12-21"
  "EFTA00080250 / DB-SDNY-0005122"
  "Benjamin Edmond de Rothschild"
  "Southern Trust Company"
  14999980
  (bankWire ∷ [])
  "Deutsche Bank exhibit records USD14,999,980 from Benjamin Edmond de Rothschild to Southern Trust. It is chronologically and numerically close to the USD15m Ariane invoice, but the payer differs and the amount is USD20 lower; no located primary document in this round explicitly says this wire satisfied Ariane's invoice."
  true true false

record ServiceJoinBoundary : Set where
  constructor service-join-boundary
  field
    consultingRelationshipPaid : Bool
    riskAnalysisPaidAsStatedScope : Bool
    estatePlanningPaidAsStatedScope : Bool
    algorithmicWorkPaidAsStatedScope : Bool
    usDOJMatterPaidAsStatedScope : Bool
    invoicePaid : Bool
    decemberWiresPaid : Bool
    fungibleCapitalContributionPaid : Bool
    benjaminWireEqualsArianeInvoicePayment : Bool
    edmondWireEqualsSpecificOctoberAgreementPayment : Bool
    statedScopeProvesQualityOrValueOfWork : Bool
    consultingRelationshipImpliesWrongdoing : Bool
open ServiceJoinBoundary public

canonicalServiceJoinBoundary : ServiceJoinBoundary
canonicalServiceJoinBoundary = service-join-boundary
  true true true true true true true true false false false false

data NearAmountImpliesInvoiceSatisfaction : Set where
data TemporalSequenceImpliesContractPerformance : Set where
data ConsultingImpliesImproperInfluence : Set where
data ScopeDescriptionImpliesDeliveredWorkProduct : Set where
data CapitalContributionImpliesEarmarking : Set where

nearAmountDoesNotCreateInvoiceSatisfaction : NearAmountImpliesInvoiceSatisfaction → ⊥
nearAmountDoesNotCreateInvoiceSatisfaction ()

temporalSequenceDoesNotCreatePerformance : TemporalSequenceImpliesContractPerformance → ⊥
temporalSequenceDoesNotCreatePerformance ()

consultingDoesNotCreateImproperInfluence : ConsultingImpliesImproperInfluence → ⊥
consultingDoesNotCreateImproperInfluence ()

scopeDoesNotCreateDeliveredWorkProduct : ScopeDescriptionImpliesDeliveredWorkProduct → ⊥
scopeDoesNotCreateDeliveredWorkProduct ()

capitalContributionDoesNotCreateEarmarking : CapitalContributionImpliesEarmarking → ⊥
capitalContributionDoesNotCreateEarmarking ()

------------------------------------------------------------------------
-- Pareto after consulting-relationship closure.
------------------------------------------------------------------------

data RothschildDebt : Set where
  exact10mContractToWireJoin : RothschildDebt
  exact15mInvoiceToWireJoin : RothschildDebt
  workProductAndDeliverables : RothschildDebt
  dojSettlementInterventionChain : RothschildDebt
  algorithmicWorkObject : RothschildDebt
  upstreamPaymentInstructions : RothschildDebt
  southernTrustCapitalPoolDeployment : RothschildDebt

record RothschildAcquisition : Set where
  constructor rothschild-acquisition
  field
    debt : RothschildDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open RothschildAcquisition public

canonicalRothschildAcquisition : List RothschildAcquisition
canonicalRothschildAcquisition =
  rothschild-acquisition exact10mContractToWireJoin 100 true
    "Acquire the executed bank-side USD10m agreement/payment instruction and join it to the 17 Dec Edmond de Rothschild Suisse -> Southern Trust USD10m wire."
  ∷ rothschild-acquisition exact15mInvoiceToWireJoin 100 true
    "Acquire remittance/payment instruction or correspondence proving whether Benjamin de Rothschild's USD14,999,980 wire discharged Ariane's USD15m 3-Nov agreement/invoice, and explain the USD20 difference rather than normalising it away."
  ∷ rothschild-acquisition dojSettlementInterventionChain 100 true
    "Resolve Epstein/STC's actual acts, communications and counterparties concerning Edmond de Rothschild's US DOJ matter and distinguish advice from decision authority or causation of the settlement."
  ∷ rothschild-acquisition algorithmicWorkObject 99 true
    "Acquire any algorithm/model/work product covered by the risk-analysis agreements; the contractual phrase alone does not identify a system, method or delivered result."
  ∷ rothschild-acquisition workProductAndDeliverables 99 true
    "Recover memoranda, models, estate structures, drafts, correspondence and professional counterparties showing what Southern Trust actually delivered."
  ∷ rothschild-acquisition southernTrustCapitalPoolDeployment 98 true
    "Place the December inflows into Southern Trust's aggregate capitalization/deployment chronology and measure subsequent investment capacity. Do not require source-specific tracing unless making an earmarking claim."
  ∷ rothschild-acquisition upstreamPaymentInstructions 97 true
    "Resolve originating accounts, signatories and payment instructions for the December wires without expanding named entities into family-wide agency."
  ∷ []
