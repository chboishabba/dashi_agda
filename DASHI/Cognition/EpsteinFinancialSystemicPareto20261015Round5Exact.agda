module DASHI.Cognition.EpsteinFinancialSystemicPareto20261015Round5Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialSystemicPareto20261015Round4Exact as Prior
import DASHI.Cognition.EpsteinBlackEstateImplementationRound20261015Exact as BlackImpl
import DASHI.Cognition.EpsteinBlackInvoiceWireSettlement20261015Exact as BlackWire
import DASHI.Cognition.EpsteinYLKInterveningInvestmentLedger20261015Exact as YLKLedger
import DASHI.Cognition.EpsteinWexnerRecoveryScopeReconciliation20261015Exact as WexnerRecovery
import DASHI.Cognition.EpsteinWexnerTrusteeTenureBoundary20261015Exact as WexnerTenure
import DASHI.Cognition.EpsteinValarInvestmentLifecycle20261015Exact as Valar
import DASHI.Cognition.EpsteinBearStructuredFundRecoveryRound20261015Exact as BearRecovery

------------------------------------------------------------------------
-- FINANCIAL / SYSTEMIC PARETO — ROUND 5, 2026-10-15
--
-- Round 5 removes two stale existence debts:
--   * Black estate-plan implementation is now directly paid across executed
--     trust/decanting/GRAT/routing/review surfaces;
--   * YLK has an intervening investment/recovery ledger, so it cannot be treated
--     as a static escrow between initial capitalization and dissolution.
------------------------------------------------------------------------

data Lane5 : Set where
  wexnerSettlementComponentReconciliation : Lane5
  wexnerTrustTerminationNeutralTransactions : Lane5
  valarRealisedCashRightsFinalDisposition : Lane5
  blackImplementationProvenanceOutcome : Lane5
  bearFinalRecoveryNetLoss : Lane5
  ylkFullLifecycleUseOfFunds : Lane5
  familyInterestPartnershipEconomics : Lane5
  southernTrustPortfolioReturnsGovernance : Lane5

record Profile5 : Set where
  constructor profile5
  field
    lane : Lane5
    priority : Nat
    relationshipExistenceClosed : Bool
    transactionExistenceClosed : Bool
    governanceOrIncidenceResidualHigh : Bool
    reading : String
open Profile5 public

canonicalFront5 : List Profile5
canonicalFront5 =
  profile5 wexnerSettlementComponentReconciliation 100 true true true
    "The official-source USD100m return account, USD46.658m YLK capitalization and USD35.142m onward dissolution transfers are paid at bounded levels. The remaining same-object problem is the executed settlement and component/overlap ledger; none of those figures are automatically additive." ∷
  profile5 wexnerTrustTerminationNeutralTransactions 100 true false true
    "Primary trust/SEC records pay Epstein trustee authority through August 2003; Bear respondents attribute trustee-capacity trades in 2006/07 and removal in 2008. The exact removal/successor instrument and neutral Bear subscriptions/wires remain the useful evidentiary upgrade." ∷
  profile5 valarRealisedCashRightsFinalDisposition 100 true true true
    "Thiel solicitation, Southern Trust LP commitments/calls, manager reports and carrying-value growth are paid. The frontier is realised distributions/net returns, Southern Trust-specific side letters/co-investment rights and final estate disposition." ∷
  profile5 blackImplementationProvenanceOutcome 100 true true true
    "Black service agreements, a same-day USD20m algorithms invoice/received-wire join, direct checklist transmission, executed J. Black Trust, APO2 creation, 97 Trust decanting action, GRAT funding/annuity flows and Epstein routing/review are paid. The live cut is item-level authorship/professional responsibility, accepted-vs-rejected advice and realised tax/estate outcomes, not implementation existence." ∷
  profile5 bearFinalRecoveryNetLoss 100 true true true
    "Bear contributions/rollover, COUQ->YLK assignment, FTC in-kind ABS Trust recovery, interim wind-down proceeds and collective settlement are paid at their source levels. Final administrator distributions and settlement allocation are required before net realised loss can be computed." ∷
  profile5 ylkFullLifecycleUseOfFunds 99 true true true
    "YLK's filed initial capitalization, Apple dispositions/options, Bear liquidating distribution and later dissolution transfers show an active investment/charitable vehicle rather than static escrow. The remaining object is the complete gains/losses/grants/expenses ledger through dissolution." ∷
  profile5 familyInterestPartnershipEconomics 99 true true true
    "FTC-as-GP, Wexner-family-trust-as-LP and large partnership-capital movement are paid. Partnership agreement, capital accounts, allocation/fee rules and exact LP trust identity remain document-bound." ∷
  profile5 southernTrustPortfolioReturnsGovernance 98 true true true
    "Fungible capital-pool inflows and Valar/Honeycomb/Boothbay deployments are paid. The remaining object is realised return/distribution and investor-right reconstruction rather than source-specific dollar tracing."
  ∷ []

record Boundary5 : Set where
  constructor boundary5
  field
    implementationImpliesSoleAuthorship : Bool
    implementationImpliesSoleCausation : Bool
    initialMinusFinalYLKMeansLoss : Bool
    trusteeAuthorityMeansBeneficialOwnership : Bool
    carryingValueMeansRealisedCash : Bool
    grossBearContributionMeansNetLoss : Bool
    fungibleCapitalNeedsDollarTracing : Bool
open Boundary5 public

canonicalBoundary5 : Boundary5
canonicalBoundary5 = boundary5 false false false false false false false

data ImplementationImpliesSoleAuthorship : Set where
data StaticEscrowDifferenceImpliesLoss : Set where
data CarryingValueImpliesCash : Set where
data FungiblePoolRequiresDollarTracing : Set where

implementationDoesNotCreateSoleAuthorship : ImplementationImpliesSoleAuthorship → ⊥
implementationDoesNotCreateSoleAuthorship ()

initialFinalDifferenceDoesNotCreateLoss : StaticEscrowDifferenceImpliesLoss → ⊥
initialFinalDifferenceDoesNotCreateLoss ()

carryingValueDoesNotCreateCash : CarryingValueImpliesCash → ⊥
carryingValueDoesNotCreateCash ()

fungiblePoolDoesNotRequireDollarTracing : FungiblePoolRequiresDollarTracing → ⊥
fungiblePoolDoesNotRequireDollarTracing ()

------------------------------------------------------------------------
-- Current terminal public-acquisition cut.
------------------------------------------------------------------------

data Debt5 : Set where
  wexnerExecutedSettlementSchedules : Debt5
  wexnerTrustRemovalAndBearSubscriptions : Debt5
  valarDistributionSideLetterExitLedger : Debt5
  blackAuthorshipDecisionOutcomeMap : Debt5
  bearFinalAdministratorSettlementAllocation : Debt5
  ylkCompleteInvestmentGrantExpenseLedger : Debt5
  familyInterestAgreementCapitalAccounts : Debt5

record Acquisition5 : Set where
  constructor acquisition5
  field
    debt : Debt5
    priority : Nat
    instruction : String
open Acquisition5 public

canonicalAcquisition5 : List Acquisition5
canonicalAcquisition5 =
  acquisition5 wexnerExecutedSettlementSchedules 100
    "Acquire the executed 2007/08 settlement/recovery agreement and asset schedules and reconcile every component against YLK/property/securities transfers without double counting." ∷
  acquisition5 wexnerTrustRemovalAndBearSubscriptions 100
    "Acquire signed trustee transition/amendment instruments plus neutral Bear subscription/wire/account records for the 2006/07 trust investments." ∷
  acquisition5 valarDistributionSideLetterExitLedger 100
    "Acquire Southern Trust-specific Valar distributions, side letters/co-investment rights and terminal estate disposition." ∷
  acquisition5 blackAuthorshipDecisionOutcomeMap 100
    "Map executed Black transactions to document authors, professional advisers, decision-makers, accepted/rejected Epstein advice and realised tax/estate outcomes." ∷
  acquisition5 bearFinalAdministratorSettlementAllocation 100
    "Acquire final ABS/EL administrator recovery records and allocate the USD9.2m settlement before calculating claimant-specific net economic loss." ∷
  acquisition5 ylkCompleteInvestmentGrantExpenseLedger 99
    "Complete YLK's 2008-11 investment income/gains/losses, grants and expenses ledger before comparing capitalization and dissolution values." ∷
  acquisition5 familyInterestAgreementCapitalAccounts 99
    "Acquire Family Interest LP governing agreement and partner capital accounts; GP operational authority is not beneficial ownership."
  ∷ []
