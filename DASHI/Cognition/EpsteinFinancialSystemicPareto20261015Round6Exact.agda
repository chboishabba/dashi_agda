module DASHI.Cognition.EpsteinFinancialSystemicPareto20261015Round6Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialSystemicPareto20261015Round5Exact as Prior
import DASHI.Cognition.EpsteinPalantirInvestmentInterest20261015Exact as PalantirInterest
import DASHI.Cognition.EpsteinHoneycombPalantirOpportunityBridge20261015Exact as HoneycombPalantir
import DASHI.Cognition.PalantirTIAFinanceStateCapacityCrossPollination20261015Exact as TIAState

------------------------------------------------------------------------
-- FINANCIAL / SYSTEMIC PARETO — ROUND 6, 2026-10-15
--
-- This round pays a previously open edge class: Epstein-side Palantir-specific
-- investment interest/opportunity/diligence.  It does not promote interest to
-- ownership.  The max-cut therefore moves to execution/custody and to the
-- transaction mechanics of the independently paid Thiel and Fiszel routes.
--
-- It also cross-pollinates today's Palantir/TIA genealogy sibling PR as a
-- provenance-bearing donor while keeping historical programme identity and
-- modern state-capacity continuity as separate promotion obligations.
------------------------------------------------------------------------

data Lane6 : Set where
  epsteinPalantirExecutionCustody : Lane6
  palantirEarlyIntelligenceCapitalProductObject : Lane6
  honeycombFiszelPalantirShareSource : Lane6
  palantirInstalledBaseRevenueExit : Lane6
  palantirHistoricalStateCapacityGenealogy : Lane6
  thielValarPalantirOutcomeComparator : Lane6
  priorRound5FinanceFront : Lane6

record Profile6 : Set where
  constructor profile6
  field
    lane : Lane6
    priority : Nat
    relationshipOrInterestPaid : Bool
    transactionExecutionPaid : Bool
    governanceOrIncidenceResidualHigh : Bool
    reading : String
open Profile6 public

canonicalFront6 : List Profile6
canonicalFront6 =
  profile6 epsteinPalantirExecutionCustody 100 true false true
    "Direct 2014 Thiel/Epstein Palantir investment advice, a 2016 Palantir secondary-share opportunity routed via Fiszel/Kahn to Epstein, and 2018 Palantir valuation/IPO diligence are paid. The decisive remaining object is an executed trade/subscription, custody statement, cap-table entry, explicit rejection, or later disposition. Interest/opportunity does not equal ownership." ∷
  profile6 palantirEarlyIntelligenceCapitalProductObject 100 true false true
    "Today's Palantir/TIA sibling genealogy pays bounded In-Q-Tel/CIA capital-customer-access and early development context. Exact original investment terms, customer/product objects, feedback scope and contemporaneous contract/development records remain the high-value same-object cut; none is TIA succession by itself." ∷
  profile6 honeycombFiszelPalantirShareSource 100 true false true
    "Southern Trust was already a large Honeycomb investor when David Fiszel offered access to Palantir secondary shares. Same counterparty/opportunity routing is paid. The seller, transfer vehicle, Honeycomb relation and execution remain open; same manager does not identify the investment vehicle." ∷
  profile6 palantirInstalledBaseRevenueExit 99 true false true
    "Modern ICE/ImmigrationOS/ERO and Maven procurements plus generic Palantir ontology/action/permission/audit capabilities are paid at bounded levels. Renewal, limited-source continuity, revenue, schema/configuration ownership, export/migration rights and switching-cost evidence are required before lock-in or durable vendor-position claims are promoted." ∷
  profile6 palantirHistoricalStateCapacityGenealogy 99 true false true
    "TIA programme/disposition, Poindexter-Karp-Thiel contact, early intelligence-community capital/customer access and modern operational procurements can be arranged as a stage-preserving genealogy. Same-program identity, code/asset transfer, personnel authority continuity, procurement-scope continuity and institutional decision-authority continuity remain false/unpaid." ∷
  profile6 thielValarPalantirOutcomeComparator 98 true false true
    "The same Thiel investment-advice network produced a completed Southern Trust Valar II/III LP relationship, while the Palantir lane currently stops at advice/opportunity/diligence. This contrast is itself informative: common adviser and opportunity access do not imply common transaction outcome." ∷
  profile6 priorRound5FinanceFront 100 true true true
    "Round 5 remains live in parallel: Wexner settlement/trust termination, Valar realised returns/rights, Black implementation outcomes, Bear final recovery/net loss, YLK lifecycle and Family Interest economics are not displaced by the Palantir promotion."
  ∷ []

record Boundary6 : Set where
  constructor boundary6
  field
    investmentInquiryImpliesOwnership : Bool
    secondaryShareOpportunityImpliesExecution : Bool
    diligenceImpliesCustody : Bool
    sharedThielImpliesSharedCapital : Bool
    honeycombManagerImpliesHoneycombVehicle : Bool
    historicalTIAContextImpliesPalantirProgrammeSuccession : Bool
    genericCapabilityImpliesDeploymentAsymmetry : Bool
    repeatedProcurementImpliesLockIn : Bool
    policyCapabilityIntersectionImpliesVendorSelection : Bool
open Boundary6 public

canonicalBoundary6 : Boundary6
canonicalBoundary6 = boundary6 false false false false false false false false false

data InterestImpliesOwnership : Set where
data OpportunityImpliesExecution : Set where
data SharedAdviserImpliesSharedCapital : Set where
data GenealogyImpliesSuccession : Set where
data RepeatedProcurementImpliesLockIn : Set where

interestDoesNotCreateOwnership : InterestImpliesOwnership → ⊥
interestDoesNotCreateOwnership ()

opportunityDoesNotCreateExecution : OpportunityImpliesExecution → ⊥
opportunityDoesNotCreateExecution ()

sharedAdviserDoesNotCreateSharedCapital : SharedAdviserImpliesSharedCapital → ⊥
sharedAdviserDoesNotCreateSharedCapital ()

genealogyDoesNotCreateSuccession : GenealogyImpliesSuccession → ⊥
genealogyDoesNotCreateSuccession ()

repeatedProcurementDoesNotCreateLockIn : RepeatedProcurementImpliesLockIn → ⊥
repeatedProcurementDoesNotCreateLockIn ()

------------------------------------------------------------------------
-- Current acquisition cut after today's PR/commit cross-pollination.
------------------------------------------------------------------------

data Debt6 : Set where
  palantirExecutedTradeOrExplicitRejection : Debt6
  palantirCustodyCapTablePosition : Debt6
  fiszelSellerAndTransferVehicle : Debt6
  earlyIQTInvestmentAndCIADevelopmentObject : Debt6
  tiaSuccessorComponentIdentityAndTransfer : Debt6
  palantirRenewalSchemaMigrationLedger : Debt6
  palantirSubjectContestabilitySameDeployment : Debt6
  barakPalantirBoardProposalResolution : Debt6

record Acquisition6 : Set where
  constructor acquisition6
  field
    debt : Debt6
    priority : Nat
    likelyPublicCorpusClosable : Bool
    instruction : String
open Acquisition6 public

canonicalAcquisition6 : List Acquisition6
canonicalAcquisition6 =
  acquisition6 palantirExecutedTradeOrExplicitRejection 100 true
    "Search released bank/brokerage/email/cap-table records for an executed Palantir purchase after the 2014 Thiel advice or 2016 Fiszel offer, or an explicit decline/expiry that closes the opportunity without investment." ∷
  acquisition6 palantirCustodyCapTablePosition 100 true
    "Search Southern Trust, HBRK, Financial Trust and related custody/portfolio statements for a Palantir position; company research and valuation attachments are not holdings evidence." ∷
  acquisition6 fiszelSellerAndTransferVehicle 100 true
    "Resolve the December 2016 secondary-share seller/source, transfer vehicle and whether Fiszel acted personally, through Honeycomb, or through another vehicle." ∷
  acquisition6 earlyIQTInvestmentAndCIADevelopmentObject 100 true
    "Acquire contemporaneous In-Q-Tel investment terms and named early CIA development/customer objects, including product/version and feedback scope." ∷
  acquisition6 tiaSuccessorComponentIdentityAndTransfer 99 true
    "Follow the 2003 statutory disposition into named/declassified successor or transferred TIA components; separately test personnel, requirement, code/asset and contract continuity into Palantir-linked work." ∷
  acquisition6 palantirRenewalSchemaMigrationLedger 99 true
    "Join ICE/Maven and other deployments to renewals, limited-source justifications, data/schema/configuration ownership, export rights, migration attempts and switching costs before promoting installed-base lock-in." ∷
  acquisition6 palantirSubjectContestabilitySameDeployment 98 true
    "Pair one concrete deployment with subject data categories, decision use, notice, inspection/correction/appeal, audit and remedy records on the same object." ∷
  acquisition6 barakPalantirBoardProposalResolution 97 true
    "Resolve any Epstein-mediated Ehud Barak/Palantir board proposal or discussion from primary audio/correspondence; distinguish proposal, Thiel response, appointment and actual governance role."
  ∷ []
