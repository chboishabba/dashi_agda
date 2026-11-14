module DASHI.Governance.AIOffBalanceCapitalRecovery20261101Exact where

------------------------------------------------------------------------
-- AI OFF-BALANCE CAPITAL COMMITMENTS / ROLLOVER / GUARANTEE MAX-CUT
--
-- Bounded original-issuer observations, not accounting consolidation.
-- Primary issuer authors retain all first-party financial authorship.
-- Analytical prior owners are imported; this thin synthesis adds finite
-- arithmetic and counterexamples, not source text claimed as kernel proof.
--
-- Existing DASHI owners:
-- SoftBankOpenAIValuationLeverage2026Exact,
-- CoreWeaveGPUBackedStructuredFinance2026Exact,
-- AIEnergyInfrastructureFundingStress2026Exact,
-- ReflexiveFlowValidationExact and KnowledgeProcessingCaptureSourceAtlas.
--
-- Values use USD millions unless otherwise specified.
-- No double count of uncommenced leases vs purchase commitments or
-- repaid bridge facility vs its takeout notes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.SoftBankOpenAIValuationLeverage2026Exact as SoftBank
import DASHI.Economics.CoreWeaveGPUBackedStructuredFinance2026Exact as CoreWeave
import DASHI.Economics.AIEnergyInfrastructureFundingStress2026Exact as Funding
import DASHI.Economics.ReflexiveFlowValidationExact as Econ
import DASHI.Economics.AIStructuredInfrastructureCommonFactorRiskExact as Shared
import DASHI.Economics.CommonFactorStructuredFinanceExact as Structured
import DASHI.Economics.AITerminalPayerEconomicValidationExact as Terminal
import DASHI.Governance.KnowledgeProcessingCaptureSourceAtlas20261101Exact as Atlas

data AccountingRole : Set where
  recognisedBorrowing recognisedOperatingLeaseLiability
    uncommencedLeaseFutureUndiscountedRent
    noncancelPurchaseOrServiceCommitment
    contingentCloudPurchase
    projectSPVLoan
    conditionalResidualValueGuarantee
    customerFutureBacklog
    undrawnSecuredBorrowingCapacity
    companyCashEquivalent
    fundingTakeoutBond : AccountingRole

-- Different accounting roles are NOT interchangeable; the source may
-- still need to reconcile overlap between TWO numerically distinct roles.
data MetaObservedRole : Set where
  metaNotes metaUnstartedRent metaOtherContracts metaContingent : MetaObservedRole

record RoleBoundReceipt : Set where
  constructor roleBoundReceipt
  field
    accountingRole : AccountingRole
    amountUSDmillion : Nat
    observedDate : String
    source : Atlas.SourceReceipt
    presentLiabilityEstablishedFromAmountAlone : Bool
open RoleBoundReceipt public

metaSeniorNotes : RoleBoundReceipt
metaSeniorNotes = roleBoundReceipt
  recognisedBorrowing 84000 "2026-09-30"
  Atlas.metaSept30LeaseAndCommitments true

metaUncommencedLeaseRent : RoleBoundReceipt
metaUncommencedLeaseRent = roleBoundReceipt
  uncommencedLeaseFutureUndiscountedRent 355730 "2026-09-30"
  Atlas.metaSept30LeaseAndCommitments false

metaNoncancelCommitments : RoleBoundReceipt
metaNoncancelCommitments = roleBoundReceipt
  noncancelPurchaseOrServiceCommitment 454520 "2026-09-30"
  Atlas.metaSept30LeaseAndCommitments false

metaConditionalExtraCloud : RoleBoundReceipt
metaConditionalExtraCloud = roleBoundReceipt
  contingentCloudPurchase 14720 "2026-09-30"
  Atlas.metaSept30LeaseAndCommitments false

coreWeaveRecognisedDebt : RoleBoundReceipt
coreWeaveRecognisedDebt = roleBoundReceipt
  recognisedBorrowing 35600 "2026-06-30"
  Atlas.coreWeaveH1SecCashClock true

coreWeaveOperatingRent : RoleBoundReceipt
coreWeaveOperatingRent = roleBoundReceipt
  recognisedOperatingLeaseLiability 16300 "2026-06-30"
  Atlas.coreWeaveH1SecCashClock true

coreWeaveDrawCapacity : RoleBoundReceipt
coreWeaveDrawCapacity = roleBoundReceipt
  undrawnSecuredBorrowingCapacity 10014 "2026-06-30"
  Atlas.coreWeaveH1SecCashClock false

coreWeaveCash : RoleBoundReceipt
coreWeaveCash = roleBoundReceipt
  companyCashEquivalent 5524 "2026-06-30"
  Atlas.coreWeaveH1SecCashClock true

------------------------------------------------------------------------
-- Exact first-party numbers. These are arithmetic identities, not
-- assertions of economic viability or identical project cash timing.
------------------------------------------------------------------------

coreH1OperatingCash : Nat
coreH1OperatingCash = 3663

coreH1InvestingOutflow : Nat
coreH1InvestingOutflow = 14874

coreH1CashFundingGap : Nat
coreH1CashFundingGap = 11211

coreFundingIdentity :
  coreH1OperatingCash + coreH1CashFundingGap
  ≡ coreH1InvestingOutflow
coreFundingIdentity = refl

coreLiquidityIncludingDraws :
  5524 + 15 + 10014 ≡ 15553
coreLiquidityIncludingDraws = refl

metaQ2Uncommenced : Nat
metaQ2Uncommenced = 278990

metaQ3Uncommenced : Nat
metaQ3Uncommenced = 355730

metaQuarterGrowth : Nat
metaQuarterGrowth = 76740

metaUncommencedQuarterBridge :
  metaQ2Uncommenced + metaQuarterGrowth ≡ metaQ3Uncommenced
metaUncommencedQuarterBridge = refl

-- USD 10,000 units; actual coupon for Sep24 USD 10bn notes:
-- 1bn*8.625% = 86.25m; 4.5bn*9.25% = 416.25m;
-- 4.5bn*9.75% = 438.75m; total 941.25m USD per year.
softBank2030CouponUnits : Nat
softBank2030CouponUnits = 8625

softBank2032CouponUnits : Nat
softBank2032CouponUnits = 41625

softBank2034CouponUnits : Nat
softBank2034CouponUnits = 43875

softBankAnnualUSDCouponUnits : Nat
softBankAnnualUSDCouponUnits = 94125

softBankBondCouponIdentity :
  softBank2030CouponUnits + softBank2032CouponUnits +
  softBank2034CouponUnits ≡ softBankAnnualUSDCouponUnits
softBankBondCouponIdentity = refl

------------------------------------------------------------------------
-- Maturity wall and continuing investment are distinct time coordinates.
-- A company can pay its immediate maturities yet still need new external
-- cash for the next wave of buildout. This is a synthetic possibility.
------------------------------------------------------------------------

data FundingCondition : Set where
  scheduledDebtPaidNoNewBuild
    scheduledDebtPaidWithGrowingBuild : FundingCondition

data FinancingOutcome : Set where
  canSelfFundModeledCycle
    needsAdditionalCapitalForNewBuild : FinancingOutcome

immediateMaturitiesMet : FundingCondition → Bool
immediateMaturitiesMet _ = true

nextCycleFinancing : FundingCondition → FinancingOutcome
nextCycleFinancing scheduledDebtPaidNoNewBuild =
  canSelfFundModeledCycle
nextCycleFinancing scheduledDebtPaidWithGrowingBuild =
  needsAdditionalCapitalForNewBuild

sameMaturitiesMet :
  immediateMaturitiesMet scheduledDebtPaidNoNewBuild
  ≡ immediateMaturitiesMet scheduledDebtPaidWithGrowingBuild
sameMaturitiesMet = refl

differentCapitalNeed :
  nextCycleFinancing scheduledDebtPaidNoNewBuild
  ≡ nextCycleFinancing scheduledDebtPaidWithGrowingBuild → ⊥
differentCapitalNeed ()

data MaturityPaymentProvesFullExpansionFinanced : Set where
maturityOnlyCannotPayNewCapex :
  MaturityPaymentProvesFullExpansionFinanced → ⊥
maturityOnlyCannotPayNewCapex ()

data NonRecourseExcludesAllEconomicExposure : Set where
noRecourseDoesNotEraseContractualDemandRisk :
  NonRecourseExcludesAllEconomicExposure → ⊥
noRecourseDoesNotEraseContractualDemandRisk ()

data ProjectCapitalEqualsCustomerIndependentCash : Set where
vendorFundingDoesNotPayTerminalDemand :
  ProjectCapitalEqualsCustomerIndependentCash → ⊥
vendorFundingDoesNotPayTerminalDemand ()

sharedDriverPrior : Structured.ProjectMultiplicityImpliesRiskIndependencePermission → ⊥
sharedDriverPrior = Shared.projectMultiplicityDoesNotCloseRiskIndependence

terminalRevenueNotValidation :
  Terminal.SurroundingSignalsImplyEconomicValidationPermission → ⊥
terminalRevenueNotValidation =
  Terminal.surroundingSignalsDoNotAutoPromoteToEconomicValidation

data SharedProjectLenderImpliesIndependentRisks : Set where
distinctSPVsDoNotEstablishRiskIndependence :
  SharedProjectLenderImpliesIndependentRisks → ⊥
distinctSPVsDoNotEstablishRiskIndependence ()

data UnstartedRentEqualsCurrentRecognisedDebt : Set where
accountingPresentationRetainsLeaseTiming :
  UnstartedRentEqualsCurrentRecognisedDebt → ⊥
accountingPresentationRetainsLeaseTiming ()

------------------------------------------------------------------------
-- Existing application owners retained and attribution not moved.
------------------------------------------------------------------------

softBankOriginalOwner : SoftBank.SoftBankOpenAIValuationLeverageCalibration
softBankOriginalOwner =
  SoftBank.canonicalSoftBankOpenAIValuationLeverageCalibration

coreWeaveOriginalOwner : CoreWeave.CoreWeaveStructuredFinanceCalibration
coreWeaveOriginalOwner =
  CoreWeave.canonicalCoreWeaveStructuredFinanceCalibration

existingFundingClock : Funding.FundingClock
existingFundingClock = Funding.candidateBurryStyleFundingClock

externalCashIsNotMarkToMarket :
  Econ.MarkedGainImpliesExternalCashPermission → ⊥
externalCashIsNotMarkToMarket =
  Econ.markedGainDoesNotAutoPromoteToExternalCash

-- Contingent contract effect requires named facility/JV accounting and
-- operational restrictions, not a categorical assertion of hidden fraud.
record SourceSpecificProjectFinance : Set where
  constructor sourceSpecificProjectFinance
  field
    spvEntityID : String
    counterpartyTenantID : String
    securedBondOrLeaseInstrumentID : String
    consolidationAndRecourseRule : String
    guaranteeTriggerAndCap : String
    noteSpecificCollateralPriority : String
    leaseCommencementAndDiscount : String
    overlapReconciliation : String
    futureBuildAndRefreshCapitalNeed : String

metaHyperionOriginal : Atlas.SourceReceipt
metaHyperionOriginal = Atlas.metaHyperionBlueOwlOriginal

softBankSepNotesOriginal : Atlas.SourceReceipt
softBankSepNotesOriginal = Atlas.softBankSep24SecuredNoneNotes

edZitronOriginalPosition : Atlas.SourceReceipt
edZitronOriginalPosition = Atlas.edZitronCreditCrunch2026

offBalanceAnalysis : String
offBalanceAnalysis =
  "H1 cash-before-financing vs growth capex, lease commitments not yet recognized, conditional residual value guarantees and long-lived project debt require separate issuer-specific accounting; obligations cannot be summed across overlapping categories or claimed as actual consolidated debt. A long debt maturity does not finance future GPU refresh or guarantee terminal customer demand."
