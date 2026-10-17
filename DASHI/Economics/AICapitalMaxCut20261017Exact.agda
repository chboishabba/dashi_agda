module DASHI.Economics.AICapitalMaxCut20261017Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIFinancingCohortMatchedOutcomeExperiment20261017Exact as Cohort
import DASHI.Economics.AIFinancingCohortCompanyOutcomeCoordinates20261017Exact as Company
import DASHI.Economics.AIFinancingCustomerCreditPriceDifferential20261017Exact as Price
import DASHI.Economics.AIHardwareLeaseResidualStructure20261017Exact as Lease
import DASHI.Economics.AIIRENCloudDirectCostBoundary20261017Exact as DirectCost
import DASHI.Economics.AICapitalOutcomeCompatibility20261016Exact as Outcome
import DASHI.Economics.AIAustraliaDataCentrePolicyShift20261016Exact as Policy

record MaxCutState : Set where
  constructor max-cut-state
  field
    financingCohortStructurePaid : Bool
    crossLayerFinancingReplicationPaid : Bool
    companyOutcomeCoordinatesPaid : Bool
    sameCompanyFinancingPriceDifferencePaid : Bool
    leaseResidualStructurePaid : Bool
    providerDirectCostCoordinatePaid : Bool
    namedPayerCashPaid : Bool
    publicContractRealisationRatioPaid : Bool
    publicGPUSerialCohortPaid : Bool
    matchedProjectReturnPaid : Bool
    matchedRefinancingOutcomePaid : Bool
    pureInferenceMarginalCostPaid : Bool
    realisedHardwareResidualPaid : Bool
    enactedInfrastructureDutyPaid : Bool
    realisedPolicyCostPaid : Bool
    terminalRegimeSelected : Bool

open MaxCutState public

currentMaxCut : MaxCutState
currentMaxCut = max-cut-state
  true true true true true true
  false false false false false false false false false false

financingCohortPaid : financingCohortStructurePaid currentMaxCut ≡ true
financingCohortPaid = refl

companyOutcomeCoordinatesPaidProof : companyOutcomeCoordinatesPaid currentMaxCut ≡ true
companyOutcomeCoordinatesPaidProof = refl

providerDirectCostPaid : providerDirectCostCoordinatePaid currentMaxCut ≡ true
providerDirectCostPaid = refl

namedCashStillOpen : namedPayerCashPaid currentMaxCut ≡ false
namedCashStillOpen = refl

marginalCostStillOpen : pureInferenceMarginalCostPaid currentMaxCut ≡ false
marginalCostStillOpen = refl

terminalRegimeStillOpen : terminalRegimeSelected currentMaxCut ≡ false
terminalRegimeStillOpen = refl

cohortValidatorNotOutcome : Cohort.mechanismSimilaritySelectsOutcome Cohort.currentCohortExperiment ≡ false
cohortValidatorNotOutcome = Cohort.mechanismSimilarityDoesNotSelectOutcome

positiveOCFNotProjectReturn : Company.positiveOCFSelectsProjectReturn Company.currentCompanyOutcomeBoundary ≡ false
positiveOCFNotProjectReturn = Company.positiveOCFDoesNotSelectProjectReturn

selected300bpNotCausal : Price.pureCustomerCreditCausalEffectPaid Price.irenSelectedFinancingDifferential ≡ false
selected300bpNotCausal = Price.causalEffectStillOpen

leaseOptionNotSalvage : Lease.optionPriceEqualsMarketResidual Lease.currentLeaseResidualBoundary ≡ false
leaseOptionNotSalvage = Lease.optionDoesNotEqualMarketResidual

directCostNotMarginalCost : DirectCost.marginalInferenceCostPaid DirectCost.irenFY2026CloudCost ≡ false
directCostNotMarginalCost = DirectCost.marginalInferenceCostStillOpen

policyEnactmentStillOpen : Policy.newMandatoryDataCentreDutyEnacted Policy.currentPolicyShift ≡ false
policyEnactmentStillOpen = Policy.enactmentStillOpen

outcomeStillUnselected : Outcome.anyTerminalRegimeSelected ≡ false
outcomeStillUnselected = Outcome.terminalPromotionStillClosed

boundary : String
boundary =
  "The October-17 max-cut is empirical rather than architectural. Public sources now pay a five-subject financing-mechanism cohort across provider/neocloud/developer layers, first company-level outcome coordinates for Nebius and IREN, a same-company selected 300bp IREN financing-price difference, explicit GPU lease terminal-value structures and an audited IREN cloud direct-cost coordinate. None of these closes the decisive consumers by proxy. Positive operating cash can be advance/prepayment-driven and is not project return; the selected financing-rate difference is not a pure customer-credit effect because instrument/project/maturity/collateral matching is unpaid; contractual buyout options are not realised salvage; direct cloud cost excluding depreciation is not marginal inference cost. The genuine remaining public wall is named payer cash and realised CRR, public GPU cohort/serial data, matched project return/refinancing outcomes, workload-normalised marginal provider cost, realised hardware residual/refresh economics, actually enacted infrastructure duties and realised compliance costs. Predeclared outcome regimes remain unselected."
