module DASHI.Cognition.EpsteinFinancialSystemicPareto20261015Round4Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialSystemicPareto20261015Round3Exact as Prior
import DASHI.Cognition.EpsteinWexnerTrustInstrumentAuthority20261015Exact as TrustInstrument
import DASHI.Cognition.EpsteinWexnerTrusteeTenureBoundary20261015Exact as Tenure
import DASHI.Cognition.EpsteinWexnerTrustPersistenceAuthorityBoundary20261015Exact as Persistence
import DASHI.Cognition.EpsteinYLKAssetReturnLifecycle20261015Exact as YLK
import DASHI.Cognition.EpsteinWexnerRecoveryScopeReconciliation20261015Exact as RecoveryScope
import DASHI.Cognition.EpsteinCOUQYLKAssetTransfer20261015Exact as COUQYLK
import DASHI.Cognition.EpsteinBlackInvoiceWireSettlement20261015Exact as BlackWire
import DASHI.Cognition.EpsteinBlackAgreementInvoiceWorkJoin20261015Exact as BlackWork
import DASHI.Cognition.EpsteinValarInvestmentLifecycle20261015Exact as Valar
import DASHI.Cognition.EpsteinBearStructuredFundRecoveryRound20261015Exact as BearRecovery

------------------------------------------------------------------------
-- FINANCIAL / SYSTEMIC PARETO — ROUND 4, 2026-10-15
--
-- Round 4 follows direct payment of several former frontier questions:
--   * primary Wexner Trust II governing authority;
--   * primary/SEC trustee-status lower bounds and attributed 2008 removal;
--   * filed COUQ+FTC -> YLK -> Wexner Family Charitable Fund transfer chain;
--   * official-memo account of a USD100m Wexner recovery, with overlap unresolved;
--   * July-2014 Black USD20m invoice -> same-day received-wire join;
--   * Bear interim recovery and COUQ->YLK assignment surfaces.
------------------------------------------------------------------------

data FinanceLane4 : Set where
  wexnerRecoveryAndAssetReturnReconciliation : FinanceLane4
  wexnerTrustAuthorityTerminationIncidence : FinanceLane4
  valarRealisedEconomicsSpecialRights : FinanceLane4
  blackImplementedAdviceAndPaymentAllocation : FinanceLane4
  bearNetLossRecoveryAllocation : FinanceLane4
  ylkSuccessorFoundationAssetLifecycle : FinanceLane4
  financialTrustFamilyInterestCapitalArchitecture : FinanceLane4
  southernTrustFungibleDeploymentReturns : FinanceLane4
  rothschildDeliveredWorkImplementation : FinanceLane4
  modernPrivateCapitalAssetisation : FinanceLane4

record FinanceProfile4 : Set where
  constructor finance-profile4
  field
    lane : FinanceLane4
    priority : Nat
    directReceiptDensityHigh : Bool
    sameObjectResidualHigh : Bool
    realisedIncidenceDebtHigh : Bool
    governanceAuthorityDebtHigh : Bool
    reading : String
open FinanceProfile4 public

canonicalFinanceFront4 : List FinanceProfile4
canonicalFinanceFront4 =
  finance-profile4 wexnerRecoveryAndAssetReturnReconciliation 100 true true true true
    "A federal prosecution memorandum records Wexner counsel's account that Epstein returned USD100m in January 2008. Filed YLK returns independently pay USD46.657998m of COUQ+FTC noncash capitalization, and recipient-foundation returns pay USD35.141684m of later YLK dissolution transfers. The live cut is the private settlement/component ledger and overlap: none of these amounts may be blindly added, and the Wexner/review misappropriation-restoration characterization is not an adjudicated tracing result." ∷
  finance-profile4 wexnerTrustAuthorityTerminationIncidence 100 true true true true
    "The 1998 primary trust instrument pays Wexner grantor/Epstein trustee identity and broad discretionary authority; 2002 and August-2003 SEC signatures independently pay continued trustee status. Bear respondents assert trustee-capacity investments in 2006/07 and state Epstein was removed in 2008, but the removal footnote cites Reuters rather than a transition deed. The max-cut is exact removal/successor instrument, amendments, neutral Bear account authority and beneficiary incidence." ∷
  finance-profile4 valarRealisedEconomicsSpecialRights 100 true true true true
    "Valar relationship existence and lifecycle are substantially paid: direct Thiel solicitation, Southern Trust II/III LP commitments/calls, carrying-value appreciation, later manager re-solicitation and 2026 estate value. The frontier is realised cash distributions/net returns, Southern Trust-specific side letters/co-investment rights and final estate disposition; carrying value is not realised cash." ∷
  finance-profile4 blackImplementedAdviceAndPaymentAllocation 100 true true true true
    "Southern Trust/Black estate-planning agreements, transmitted Black work product, the July-2014 USD20m algorithms invoice and a same-day USD20m received-wire receipt are paid. The remaining cut is operative agreement version, executed trust/tax implementation, per-deliverable authorship/allocation and realised tax/estate outcome; Black/Apollo interfaces do not create an Apollo corporate retainer." ∷
  finance-profile4 bearNetLossRecoveryAllocation 100 true true true false
    "Structured-credit contributions/rollover, partial common-share sale, COUQ->YLK asset assignment, interim wind-down recovery assertions and the USD9.2m collective settlement are paid at their proper source levels. Gross invested amounts cannot stand in for net loss. The max-cut is final administrator distributions/in-kind recoveries, settlement allocation and tax-basis realised-loss reconciliation." ∷
  finance-profile4 ylkSuccessorFoundationAssetLifecycle 99 true true true true
    "Primary tax records pay USD46.657998m initial noncash capitalization of YLK and USD35.141684m onward dissolution transfers to the Wexner Family Charitable Fund. Assignment instruments pay named COUQ investment transfers, and YLK tax records show intervening investment/liquidating activity. The live object is YLK's complete 2008-11 asset/grant/investment ledger, not a simple initial-minus-final loss calculation." ∷
  finance-profile4 financialTrustFamilyInterestCapitalArchitecture 99 true true true true
    "FTC GP / Wexner-family LP relationship, large Family Interest capital movement, Trust II note financing and primary trust authority create a dense capital-management architecture. Governing partnership agreements, capital accounts and economic incidence remain more valuable than further broad relationship discovery." ∷
  finance-profile4 southernTrustFungibleDeploymentReturns 99 true true true false
    "Southern Trust capital-pool inflows and downstream Valar/Honeycomb/Boothbay deployments are paid. Earmarking is not required for pool-level incidence. The frontier is aggregate return/distribution and governance-right reconstruction, not dollar-by-dollar payer tracing." ∷
  finance-profile4 rothschildDeliveredWorkImplementation 98 true true true true
    "Rothschild-Southern Trust consulting agreements/invoices/wires and capital inflows are paid. Delivered algorithm/risk/estate work products and downstream implementation/authority remain the useful same-object residuals." ∷
  finance-profile4 modernPrivateCapitalAssetisation 97 true true true true
    "Modern housing/AI/power assetisation remains a structural consumer of the historical finance machinery but ranks below the now-document-rich same-object Wexner/Black/Valar/Bear cuts. Same manager, same fund and historical causation remain distinct."
  ∷ []

record Round4Boundary : Set where
  constructor round4-boundary
  field
    hundredMillionPlusYLKMayBeAdded : Bool
    ylkDissolutionIsNewRecovery : Bool
    reviewRestitutionIsAdjudication : Bool
    trustAuthorityIsBeneficialOwnership : Bool
    removalAssertionIsRemovalInstrument : Bool
    invoiceWireJoinAllocatesSpecificChecklistItems : Bool
    valarCarryingValueIsRealisedCash : Bool
    grossBearContributionIsNetLoss : Bool
    fungiblePoolRequiresEarmarking : Bool
    sourceTypedAssetReturnAndAuthorityWorthInvestigating : Bool
open Round4Boundary public

canonicalRound4Boundary : Round4Boundary
canonicalRound4Boundary = round4-boundary
  false false false false false false false false false true

data AdditiveRecoveryWithoutScope : Set where
data RemovalClaimEqualsInstrument : Set where
data SameDayPaymentImpliesItemAllocation : Set where
data CarryingValueImpliesCash : Set where
data GrossInvestmentImpliesNetLoss : Set where

recoveryAmountsCannotBeBlindlyAdded : AdditiveRecoveryWithoutScope → ⊥
recoveryAmountsCannotBeBlindlyAdded ()

removalClaimDoesNotCreateInstrument : RemovalClaimEqualsInstrument → ⊥
removalClaimDoesNotCreateInstrument ()

paymentDoesNotCreateItemAllocation : SameDayPaymentImpliesItemAllocation → ⊥
paymentDoesNotCreateItemAllocation ()

carryingValueDoesNotCreateCash : CarryingValueImpliesCash → ⊥
carryingValueDoesNotCreateCash ()

grossInvestmentDoesNotCreateNetLoss : GrossInvestmentImpliesNetLoss → ⊥
grossInvestmentDoesNotCreateNetLoss ()

------------------------------------------------------------------------
-- Terminal public-acquisition max-cut after Round 4.
------------------------------------------------------------------------

data Round4Debt : Set where
  wexnerExecutedSettlementAndComponentLedger : Round4Debt
  wexnerTrustRemovalSuccessorAmendments : Round4Debt
  neutralWexnerTrustBearSubscriptions : Round4Debt
  valarRealisedDistributionsSideLettersExit : Round4Debt
  blackExecutedImplementationAndAllocation : Round4Debt
  bearFinalAdministratorAndSettlementAllocation : Round4Debt
  ylkCompleteLifecycleLedger : Round4Debt
  familyInterestAgreementCapitalAccounts : Round4Debt

record Round4Acquisition : Set where
  constructor round4-acquisition
  field
    debt : Round4Debt
    priority : Nat
    publicSearchYield : Nat
    instruction : String
open Round4Acquisition public

canonicalRound4Acquisition : List Round4Acquisition
canonicalRound4Acquisition =
  round4-acquisition wexnerExecutedSettlementAndComponentLedger 100 100
    "Acquire the executed private settlement/recovery schedules and reconcile the reported USD100m with YLK, property, securities, loans and other returned assets without double counting." ∷
  round4-acquisition wexnerTrustRemovalSuccessorAmendments 100 98
    "Acquire the signed 2008 trustee resignation/removal/successor instrument and amendment chain; the Bear/Reuters removal statement is an attributed endpoint, not the legal instrument." ∷
  round4-acquisition neutralWexnerTrustBearSubscriptions 100 97
    "Acquire neutral Bear subscription/wire/capital-account records for the pleaded USD20m ABS and USD10m Europe Long/Short trust investments." ∷
  round4-acquisition valarRealisedDistributionsSideLettersExit 100 96
    "Acquire Southern Trust-specific Valar distributions, side letters/co-investment rights and final estate disposition; public carrying-value and call records already pay the investment lifecycle." ∷
  round4-acquisition blackExecutedImplementationAndAllocation 100 95
    "Join paid agreements/invoices/wires and transmitted work products to executed trust/tax transactions, authorship and accepted/rejected advice." ∷
  round4-acquisition bearFinalAdministratorAndSettlementAllocation 100 94
    "Acquire final ABS administrator distribution/in-kind records plus the USD9.2m settlement allocation to calculate net realised recovery/loss." ∷
  round4-acquisition ylkCompleteLifecycleLedger 99 95
    "Reconstruct YLK investment gains/losses, grants, expenses and asset dispositions between the filed initial capitalization and dissolution transfers." ∷
  round4-acquisition familyInterestAgreementCapitalAccounts 99 90
    "Acquire Family Interest LP governing agreement and partner capital accounts to resolve GP/LP authority and economic incidence."
  ∷ []
