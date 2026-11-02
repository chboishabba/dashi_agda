module DASHI.Governance.AIContinuingCapitalFundingMaxCut20261102Exact where

------------------------------------------------------------------------
-- FUTURE-BUILD CASH, FINANCING SUPPLY AND EPISTEMIC INCIDENCE
--
-- Dated original issuer datum (not forward guidance):
-- CoreWeave Inc., 2026-06-30 Form 10-Q, SEC 000176962826000366:
-- https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm
-- H1 OCF USD3663m, investing use USD14874m; operating cash
-- includes USD1365m change in deferred revenue in cash-flow reconciliation.
-- Cash USD5524m, securities USD15m, undrawn secured facilities USD10014m.
--
-- Existing canonical authors and theorem owners:
-- DASHI.Governance.AIOffBalanceCapitalRecovery20261101Exact
-- DASHI.Economics.AIInfrastructureConsumerIndexedFibreAdequacyExact
-- DASHI.Economics.AIInfrastructureConsumerFibreRefinementSchedulerExact
-- DASHI.Economics.AIStructuredInfrastructureCommonFactorRiskExact
-- DASHI.Economics.GlobalFundingLiquidityRealisationExact
-- DASHI.Core.IntersectionalNonFactorability
--
-- This is NEW repo-native finite synthesis, not an economic theorem from
-- CoreWeave, nor an assertion that all modelling scenarios will materialise.
-- Exact numbers from the Python harness are scenario outputs requiring
-- a separate executed same-program/Agda bridge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Economics.AIInfrastructureConsumerIndexedFibreAdequacyExact as Consumer
import DASHI.Economics.AIInfrastructureConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Economics.AIStructuredInfrastructureCommonFactorRiskExact as Shared
import DASHI.Economics.CommonFactorStructuredFinanceExact as Structured
import DASHI.Economics.GlobalFundingLiquidityRealisationExact as Liquidity
import DASHI.Governance.AIOffBalanceCapitalRecovery20261101Exact as Base
import DASHI.Governance.KnowledgeProcessingCaptureSourceAtlas20261101Exact as Atlas
import DASHI.Governance.KnowledgeCaptureSecondThirdOrder20261101Exact as Third

-- Observed CoreWeave six-month quantities, USD millions: source arithmetic.
observedOperatingH1 : Nat
observedOperatingH1 = 3663

observedInvestingH1 : Nat
observedInvestingH1 = 14874

deferredRevenueMovementH1 : Nat
deferredRevenueMovementH1 = 1365

ocfNetOfOneDeferredRevenueMovement : Nat
ocfNetOfOneDeferredRevenueMovement = 2298

h1OperatingCashWorkingCapitalIdentity :
  ocfNetOfOneDeferredRevenueMovement + deferredRevenueMovementH1
    ≡ observedOperatingH1
h1OperatingCashWorkingCapitalIdentity = refl

-- NOT a claim that USD2298m is independently verified recurring OCF:
-- all other working-capital entries, interest, cash receipts and payments
-- remain in the original cash-flow statement and its note.
priorCashIdentity :
  Base.coreH1OperatingCash + Base.coreH1CashFundingGap
    ≡ Base.coreH1InvestingOutflow
priorCashIdentity = Base.coreFundingIdentity

-- The same current debt maturity/operating-asset snapshot admits different
-- next-generation financing outcomes. Current debt paid is insufficient.
data FutureFinancingWorld : Set where
  nextGenerationFundingOpen
    nextGenerationFundingConstrained : FutureFinancingWorld

data CurrentMaturityObservation : Set where
  currentMaturityCovered : CurrentMaturityObservation

data ContinuationStatus : Set where
  gpuReplacementAndBuildFinanceable
    additionalFundingMissing : ContinuationStatus

currentMaturityView : FutureFinancingWorld → CurrentMaturityObservation
currentMaturityView _ = currentMaturityCovered

continuationView : FutureFinancingWorld → ContinuationStatus
continuationView nextGenerationFundingOpen =
  gpuReplacementAndBuildFinanceable
continuationView nextGenerationFundingConstrained =
  additionalFundingMissing

sameCurrentMaturityView :
  currentMaturityView nextGenerationFundingOpen
  ≡ currentMaturityView nextGenerationFundingConstrained
sameCurrentMaturityView = refl

differentContinuationView :
  continuationView nextGenerationFundingOpen
  ≡ continuationView nextGenerationFundingConstrained → ⊥
differentContinuationView ()

forwardFinancingNonFactorability :
  NF.NonFactorabilityWitness currentMaturityView continuationView
forwardFinancingNonFactorability =
  NF.nonFactorabilityWitness
    nextGenerationFundingOpen nextGenerationFundingConstrained
    sameCurrentMaturityView differentContinuationView

currentMaturityCannotDetermineFutureBuild :
  NF.FactorsThrough currentMaturityView continuationView → ⊥
currentMaturityCannotDetermineFutureBuild =
  NF.witnessRulesOutEveryFlatFactorisation
    forwardFinancingNonFactorability

-- The original consumer-indexed economics owner already proves that the
-- apparently equal current headline cannot answer a financing question.
reusedConsumerRefinancingDefect :
  Consumer.AIFibreMissingCoordinate
reusedConsumerRefinancingDefect =
  Consumer.refinancingContextCoordinate

reusedRequiredEmpiricalPanel :
  Scheduler.EmpiricalProducerSurface
reusedRequiredEmpiricalPanel =
  Scheduler.empiricalProducerFor
    Scheduler.refinancingContextProducer

originalCommonFactorIndependenceBoundary :
  Structured.ProjectMultiplicityImpliesRiskIndependencePermission → ⊥
originalCommonFactorIndependenceBoundary =
  Shared.projectMultiplicityDoesNotCloseRiskIndependence

originalLatentVsRealisedBoundary :
  Liquidity.LatentLossImpliesRealisedLossPermission → ⊥
originalLatentVsRealisedBoundary =
  Liquidity.latentLossDoesNotAutoRealise

-- Explicit three-way non-additive financing streams:
-- project borrowings and customer commitments can be alternative views of
-- the SAME underlying future revenue. Gross receivable sum is not unique
-- external household/enterprise demand.
data CashFlowCoordinate : Set where
  terminalIndependentCustomerPayment
    platformVendorInvestment
    spvLoanAdvance
    tenantPayAsYouGoOrTakeOrPay
    gpuSupplierAdvance
    collateralLiquidationReceipt : CashFlowCoordinate

data MoneyMetric : Set where
  companyOperatingCash
    unrestrictedCompanyCash
    undrawnConditionalDebtCapacity
    newProjectCapital
    newFundedExternalPayerCash
    disclosedLeaseRent
    futureServiceCommitment
    conditionalGuarantee : MoneyMetric

data DoubleCountingEquivalence : Set where
  exactSameCashFlowInstrument
    possibleAccountingOverlap
    distinctSettledExternalCash : DoubleCountingEquivalence

-- Classifying a receipt is necessary but insufficient. The actual
-- instrument, entity, due date and settlement amount are still absent.
record IndependentCashAndCapitalProducer : Set where
  constructor independentCashAndCapitalProducer
  field
    originalIssuerOrBankDocument : String
    instrumentAndEntityID : String
    effectiveAndMaturityDates : String
    nettingOverlapAndElimination : String
    externalTerminalPayerIdentity : String
    rawCashSettlementOrTrusteeStatement : String
    gpuCohortAndReplacementLife : String
    collateralPriorityAndRealisation : String
    committedVsAvailableCapital : String
    cashConversionAndBacklogDelivery : String
    applicableLawAndJurisdiction : String
    measuredIndependentComputeExit : String

data RolloverPaymentClosesEntireCapexCycle : Set where
data BacklogIsDistributableFreeCash : Set where
data UndrawnLoanIsUnrestrictedCash : Set where
data MultipleDebtVehiclesAreIndependentDemand : Set where
data SPVNonRecourseMeansNoSponsorContingentLoss : Set where

maturityPaidStillNeedsNewBuildFinance :
  RolloverPaymentClosesEntireCapexCycle → ⊥
maturityPaidStillNeedsNewBuildFinance ()

backlogDoesNotPayFreeCash : BacklogIsDistributableFreeCash → ⊥
backlogDoesNotPayFreeCash ()

undrawnCapacityNeedsConditions : UndrawnLoanIsUnrestrictedCash → ⊥
undrawnCapacityNeedsConditions ()

sharedDriverSurvivesMultipleSPVs :
  MultipleDebtVehiclesAreIndependentDemand → ⊥
sharedDriverSurvivesMultipleSPVs ()

nonRecourseDoesNotEraseOtherObligations :
  SPVNonRecourseMeansNoSponsorContingentLoss → ⊥
nonRecourseDoesNotEraseOtherObligations ()

source : Atlas.SourceReceipt
source = Atlas.coreWeaveCashPrepaymentsOriginal2026

escrowOriginal : Atlas.SourceReceipt
escrowOriginal = Atlas.metaEscrowRestricted2026

-- Third-order selection is governed by a distinct existing hypothetical
-- policy path and needs its own real instrument and observed access effect.
-- No automatic private-credit-stress -> sovereign knowledge-control rule.
financialStressCannotProveExecutedBailout :
  Third.SupplierFinanceProvesPublicRescue → ⊥
financialStressCannotProveExecutedBailout =
  Third.circularFinancingDoesNotForceRescue

existingContestableCounterfactual :
  Third.ThreeHop
    Third.protectivePolicyIntervention Third.contestablePublicOversight
existingContestableCounterfactual = Third.resilientResponsePath

existingConcentrationCounterfactual :
  Third.ThreeHop
    Third.protectivePolicyIntervention Third.entrenchedPrivateStandardsPower
existingConcentrationCounterfactual = Third.concentratingResponsePath

-- Scope: real forward debt availability, contractual GPU refresh, one-party
-- exposure and any public/private intervention remain empirical obligations.
