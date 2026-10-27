module DASHI.Unified.RescueFinancePalantirTOENonPromotionExact where

-- TOE integration. Original source authors remain attributed in their owners.
-- DASHI owns only this adapter and its exact non-promotion compositions.
-- External sibling PR #1161 is an observed source donor, not Agda authority.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PalantirTIAFinanceStateCapacityCrossPollination20261015Exact as TIA
import DASHI.Cognition.Project2025PalantirImmigrationDataIntersectionExact as ICE
import DASHI.Cognition.EpsteinSouthernTrustInvestmentFlowAtlas20261014Exact as Pool
import DASHI.Cognition.EpsteinValarCapitalLedgerClosure20261014Exact as Valar
import DASHI.Cognition.EpsteinFinancialTrustBearCrisisAwarenessSettlement20261014Exact as Bear
import DASHI.Governance.PalantirPlatformCapabilityEvidenceExact as Capability
import DASHI.Governance.PalantirProcurementLegibilityAdapterExact as Procurement

-- Preconditions: the existing source-typed receipts and their owner modules.
-- Invariant: each edge has its own source, object, authority, and proof status.
-- Postcondition: TOE can reuse the exact blockers without claiming final QG.

poolDoesNotProveDirection : Pool.FungiblePoolContributionImpliesEarmarking → ⊥
poolDoesNotProveDirection = Pool.fungibleContributionDoesNotCreateEarmarking

valarDoesNotProvePalantir : Valar.ValarInvestmentImpliesPalantirInvestment → ⊥
valarDoesNotProvePalantir = Valar.valarDoesNotCreatePalantirInvestment

thielContactDoesNotProveSharedCapital : TIA.SharedPersonImpliesSharedCapital → ⊥
thielContactDoesNotProveSharedCapital = TIA.sharedPersonDoesNotCreateSharedCapital

thielValarDoesNotProvePalantir : TIA.ValarInvestmentImpliesPalantirInvestment → ⊥
thielValarDoesNotProvePalantir = TIA.valarDoesNotCreatePalantirInvestment

policyDemandDoesNotChooseVendor : ICE.PolicyDemandImpliesVendorSelection → ⊥
policyDemandDoesNotChooseVendor = ICE.policyDemandDoesNotCreateVendorSelection

procurementDoesNotProveAbuse : Procurement.ProcurementAloneEstablishesAbuse → ⊥
procurementDoesNotProveAbuse = Procurement.procurementDoesNotEstablishAbuse

capabilityDoesNotProveAbuse : Capability.ObjectGraphPromotesAbuse → ⊥
capabilityDoesNotProveAbuse = Capability.objectGraphDoesNotPromoteAbuse

auditLogDoesNotProveRemedy : Capability.AuditLoggingPromotesPublicContestability → ⊥
auditLogDoesNotProveRemedy = Capability.auditLoggingDoesNotPromotePublicContestability

bearSettlementDoesNotProveAdmission : Bear.SettlementImpliesAdmission → ⊥
bearSettlementDoesNotProveAdmission = Bear.settlementDoesNotCreateAdmission

-- Exact selected-owner observations. These are not assertions of causation.
policyVendorSelectionUnpaid :
  ICE.Project2025PalantirBoundary.project2025SelectedPalantir
    ICE.canonicalProject2025PalantirBoundary ≡ false
policyVendorSelectionUnpaid = refl

historicalTIAIdentityUnpaid :
  TIA.StateCapacityChain.sameProgrammeIdentityPaid
    TIA.canonicalStateCapacityChain ≡ false
historicalTIAIdentityUnpaid = refl

palantirLockInUnpaid :
  TIA.StateCapacityChain.lockInAlreadyProved
    TIA.canonicalStateCapacityChain ≡ false
palantirLockInUnpaid = refl

subjectRemedyUnpaid :
  Capability.PalantirCapabilityBoundary.subjectInspectionCorrectionAppealInstalled
    Capability.canonicalPalantirCapabilityBoundary ≡ false
subjectRemedyUnpaid = refl

-- O/R/C/S/L/P/G/F: owner, receipt, claim, scope, lineage, promotion,
-- governance, failure. No unverified control or causal edge is promoted.
record TOEFinanceGovernanceCut : Set where
  constructor toe-finance-governance-cut
  field
    owner : Bool
    receipt : Bool
    claimScoped : Bool
    sourceLineagePreserved : Bool
    promotionRequiresExactObject : Bool
    governanceAuthoritySeparate : Bool
    failureOfEarmarkingInference : Bool
    firstOrderRescueContract : Bool
    secondOrderAccessMeasured : Bool
    thirdOrderInstitutionalControlMeasured : Bool
    terminalTOEPhysicsProved : Bool

canonicalTOEFinanceGovernanceCut : TOEFinanceGovernanceCut
canonicalTOEFinanceGovernanceCut = toe-finance-governance-cut
  true true true true true true true
  true false false false

-- First-order contracts are separate from possible later capital advantages.
-- Source: Federal Reserve Bank of New York, Maiden Lane transaction records.
-- Source: US GAO, GAO-11-696, table 17 (2008-2010 fees).
-- Source: US GAO, GAO-10-24SP (2008 TARP Capital Purchase Program).
-- Source: FRBNY 2020 PMCCF investment management agreement, exhibit G.
-- These sources retain authorship and statutory/reporting scope.
record RescueSourceReceipt : Set where
  constructor rescue-source-receipt
  field
    source : String
    boundedFinding : String
    firstOrderPaid : Bool
    secondOrderInstitutionalAccessPaid : Bool
    thirdOrderPolicyControlPaid : Bool

maidenLane2008 : RescueSourceReceipt
maidenLane2008 = rescue-source-receipt
  "Federal Reserve Bank of New York, Maiden Lane Transactions; GAO-11-696 table 17"
  "BlackRock Financial Management was retained as investment manager; GAO records USD 107648136 fees to BlackRock for Maiden Lane LLC during 2008-2010. This is firm revenue, not Larry Fink personal income."
  true false false

tarpNineBanks2008 : RescueSourceReceipt
tarpNineBanks2008 = rescue-source-receipt
  "US GAO, GAO-10-24SP, Treasury Capital Purchase Program"
  "Treasury and federal banking regulators identified nine large institutions for USD125bn approved preferred capital purchases under the larger USD700bn TARP authority. Individual BlackRock advice, beneficial ownership and decision control are not paid by this source."
  true false false

corporateCredit2020 : RescueSourceReceipt
corporateCredit2020 = rescue-source-receipt
  "FRBNY, 2020 PMCCF Investment Management Agreement, Exhibit G"
  "BlackRock Financial Management served as investment manager and transaction agent, subject to written conflict and information-barrier requirements. Policy decision control and asset-holder inflation gains are not paid."
  true false false

-- Incident/benefit order never upgrades an evidentiary grade.
data BenefitOrder : Set where
  immediateContract : BenefitOrder
  futureAccessOption : BenefitOrder
  durableInstitutionalInfluence : BenefitOrder

record BenefitOrderAssessment : Set where
  constructor benefit-order-assessment
  field
    order : BenefitOrder
    sameObjectEvidencePaid : Bool
    benefitQuestion : String

directRescueFee : BenefitOrderAssessment
directRescueFee = benefit-order-assessment immediateContract true
  "Contracted manager fees and services paid by the federal rescue vehicles."

futureAccess : BenefitOrderAssessment
futureAccess = benefit-order-assessment futureAccessOption false
  "Did rescue appointments improve future government access or mandate award probability? Acquire same-client contract chronology and selection records."

institutionalInfluence : BenefitOrderAssessment
institutionalInfluence = benefit-order-assessment durableInstitutionalInfluence false
  "Did sustained client dependence change procurement rules, public policy, asset prices or household incidence? Require attributable decision, causal comparator and distribution records."

