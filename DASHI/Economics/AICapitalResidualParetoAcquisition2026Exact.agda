module DASHI.Economics.AICapitalResidualParetoAcquisition2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ExpectedFibreReductionCostExact as Reduction
import DASHI.Core.ResidualConditionedExperimentPortfolioExact as Portfolio
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Interop.StateIndexedLiveCutParetoCrossPollinationExact as StateIndexed
import DASHI.Economics.AICapitalObservedStateTimeSeries2026Exact as Time

------------------------------------------------------------------------
-- AI-CAPITAL RESIDUAL -> SOURCE-ACQUISITION PARETO ADAPTER
------------------------------------------------------------------------

data CapitalAcquisitionRoute : Set where
  terminalPayerVectorRoute : CapitalAcquisitionRoute
  capitalSpreadFilingsRoute : CapitalAcquisitionRoute
  inferenceQualityServingRoute : CapitalAcquisitionRoute
  scarcityOpenClosedRoute : CapitalAcquisitionRoute
  gpuReplacementRoute : CapitalAcquisitionRoute
  rolloverFinanceRoute : CapitalAcquisitionRoute
  policyGridRoute : CapitalAcquisitionRoute
  marketSeriesRoute : CapitalAcquisitionRoute
  reportedProposalShortcut : CapitalAcquisitionRoute

data CapitalAcquisitionConsumer : Set where
  capitalRecoveryConsumer : CapitalAcquisitionConsumer

data CapitalSourceAuthority : Set where
  publicSourceAcquisitionAuthority : CapitalSourceAuthority

routeMove : CapitalAcquisitionRoute → Choice.InformationMove
routeMove terminalPayerVectorRoute = Choice.informationMove Choice.takeMeasurement 2
  "complete same-horizon terminal payer / revenue vector" "filing and source acquisition" "public source evidence required"
routeMove capitalSpreadFilingsRoute = Choice.informationMove Choice.takeMeasurement 5
  "realised ROIC-WACC producer" "company filings and debt instruments" "same-entity same-horizon accounting authority required"
routeMove inferenceQualityServingRoute = Choice.informationMove Choice.takeMeasurement 3
  "quality-adjusted inference spread" "serving-price, quality and provider-cost join" "platform telemetry alone is insufficient"
routeMove scarcityOpenClosedRoute = Choice.informationMove Choice.takeMeasurement 3
  "open/closed quality-price scarcity spread" "platform telemetry plus declared capability chart" "platform-local evidence only"
routeMove gpuReplacementRoute = Choice.informationMove Choice.takeMeasurement 1
  "GPU replacement/depreciation route" "lender collateral/depreciation evidence" "replacement evidence is not capital recovery"
routeMove rolloverFinanceRoute = Choice.informationMove Choice.takeMeasurement 2
  "same-borrower refinancing/rollover schedule" "debt maturity and refinancing evidence" "funding spread alone is insufficient"
routeMove policyGridRoute = Choice.informationMove Choice.takeMeasurement 2
  "policy/grid backstop salience route" "regulator and permitting evidence" "policy salience is not capture probability"
routeMove marketSeriesRoute = Choice.informationMove Choice.takeMeasurement 1
  "fixed-window AI-linked market flip/volatility series" "declared basket plus broad benchmark" "market state remains separate from fundamentals"
routeMove reportedProposalShortcut = Choice.informationMove Choice.takeMeasurement 0
  "reported proposal shortcut" "proposal/report only" "not admitted"

routeReduction : CapitalAcquisitionRoute → Reduction.ReductionEnvelope
routeReduction terminalPayerVectorRoute = Reduction.reductionEnvelope 1 2 "may close terminal-payer and revenue-vector residuals"
routeReduction capitalSpreadFilingsRoute = Reduction.reductionEnvelope 1 1 "targets capital-spread residual"
routeReduction inferenceQualityServingRoute = Reduction.reductionEnvelope 0 1 "requires quality and serving-cost join"
routeReduction scarcityOpenClosedRoute = Reduction.reductionEnvelope 0 2 "may narrow scarcity and capability residuals"
routeReduction gpuReplacementRoute = Reduction.reductionEnvelope 0 1 "directly informs replacement/depreciation and obsolescence rung"
routeReduction rolloverFinanceRoute = Reduction.reductionEnvelope 0 1 "requires maturity/refinancing closure"
routeReduction policyGridRoute = Reduction.reductionEnvelope 0 1 "policy salience route remains noncausal"
routeReduction marketSeriesRoute = Reduction.reductionEnvelope 1 2 "fixed series can close flip/volatility producers"
routeReduction reportedProposalShortcut = Reduction.reductionEnvelope 0 2 "nominal shortcut excluded by admission"

routeRelevant : Time.MissingCapitalProducer → CapitalAcquisitionConsumer → CapitalAcquisitionRoute → Bool
routeRelevant Time.capitalSpreadProducerOpen capitalRecoveryConsumer capitalSpreadFilingsRoute = true
routeRelevant Time.inferenceSpreadProducerOpen capitalRecoveryConsumer inferenceQualityServingRoute = true
routeRelevant Time.scarcitySpreadProducerOpen capitalRecoveryConsumer scarcityOpenClosedRoute = true
routeRelevant Time.capabilityCompressionProducerOpen capitalRecoveryConsumer scarcityOpenClosedRoute = true
routeRelevant Time.capabilityCompressionProducerOpen capitalRecoveryConsumer gpuReplacementRoute = true
routeRelevant Time.replacementDepreciationProducerOpen capitalRecoveryConsumer gpuReplacementRoute = true
routeRelevant Time.rolloverProducerOpen capitalRecoveryConsumer rolloverFinanceRoute = true
routeRelevant Time.policyBackstopProducerOpen capitalRecoveryConsumer policyGridRoute = true
routeRelevant Time.marketFlipProducerOpen capitalRecoveryConsumer marketSeriesRoute = true
routeRelevant Time.marketVolProducerOpen capitalRecoveryConsumer marketSeriesRoute = true
routeRelevant Time.terminalPayerCoverageOpen capitalRecoveryConsumer terminalPayerVectorRoute = true
routeRelevant Time.revenueVectorCoverageOpen capitalRecoveryConsumer terminalPayerVectorRoute = true
routeRelevant _ _ _ = false

routeAdmitted : CapitalSourceAuthority → CapitalAcquisitionRoute → Bool
routeAdmitted publicSourceAcquisitionAuthority reportedProposalShortcut = false
routeAdmitted publicSourceAcquisitionAuthority _ = true

routeReference : CapitalAcquisitionRoute → String
routeReference terminalPayerVectorRoute = "Anthropic filing/revenue-routing route; complete payer vector still open"
routeReference capitalSpreadFilingsRoute = "same-entity filings/debt route for realised ROIC-WACC"
routeReference inferenceQualityServingRoute = "quality-adjusted serving economics route"
routeReference scarcityOpenClosedRoute = "open/closed quality-price substitution route"
routeReference gpuReplacementRoute = "Reuters lender GPU depreciation/replacement evidence, 2026-10-01"
routeReference rolloverFinanceRoute = "Reuters AI leveraged-finance route plus same-borrower maturities"
routeReference policyGridRoute = "FERC/PJM and permitting policy-support route"
routeReference marketSeriesRoute = "fixed-window AI-linked basket / benchmark series"
routeReference reportedProposalShortcut = "negative fixture: proposal cannot win by zero declared cost"

aiCapitalAcquisitionPortfolio : Portfolio.ExperimentPortfolio
aiCapitalAcquisitionPortfolio = Portfolio.experimentPortfolio
  CapitalAcquisitionRoute Time.MissingCapitalProducer CapitalAcquisitionConsumer CapitalSourceAuthority
  routeMove routeReduction routeRelevant routeAdmitted routeReference

terminalPayerCandidate : Portfolio.PortfolioCandidate aiCapitalAcquisitionPortfolio Time.terminalPayerCoverageOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority terminalPayerVectorRoute
terminalPayerCandidate = Portfolio.portfolioCandidate refl refl "directly attacks the first terminal coverage residual" "declared source-acquisition cost 2; reduction envelope 1-2"

capitalSpreadCandidate : Portfolio.PortfolioCandidate aiCapitalAcquisitionPortfolio Time.capitalSpreadProducerOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority capitalSpreadFilingsRoute
capitalSpreadCandidate = Portfolio.portfolioCandidate refl refl "same-entity realised return and funding cost close the capital-spread producer" "higher acquisition cost retained rather than replaced by revenue/gross-margin proxies"

replacementCandidate : Portfolio.PortfolioCandidate aiCapitalAcquisitionPortfolio Time.replacementDepreciationProducerOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority gpuReplacementRoute
replacementCandidate = Portfolio.portfolioCandidate refl refl "lender depreciation evidence attacks the explicit replacement/depreciation residual" "interval evidence narrows the residual but does not itself close company replacement capex"

marketSeriesCandidate : Portfolio.PortfolioCandidate aiCapitalAcquisitionPortfolio Time.marketFlipProducerOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority marketSeriesRoute
marketSeriesCandidate = Portfolio.portfolioCandidate refl refl "fixed-window market series directly closes a current market-dynamics producer" "cheap route remains separate from terminal economic authority"

proposalShortcutNotAdmitted : Portfolio.admissibleNow aiCapitalAcquisitionPortfolio publicSourceAcquisitionAuthority reportedProposalShortcut ≡ false
proposalShortcutNotAdmitted = refl

terminalRouteBecomesIrrelevantToCapitalSpread : Portfolio.relevantNow aiCapitalAcquisitionPortfolio Time.capitalSpreadProducerOpen capitalRecoveryConsumer terminalPayerVectorRoute ≡ false
terminalRouteBecomesIrrelevantToCapitalSpread = refl

replacementRouteIsRelevantWhenReplacementResidualLive : Portfolio.relevantNow aiCapitalAcquisitionPortfolio Time.replacementDepreciationProducerOpen capitalRecoveryConsumer gpuReplacementRoute ≡ true
replacementRouteIsRelevantWhenReplacementResidualLive = refl

terminalPayerParetoProblem : Pareto.ConsumerMDLProblem
terminalPayerParetoProblem = StateIndexed.asStateIndexedMDLProblem aiCapitalAcquisitionPortfolio Time.terminalPayerCoverageOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority

terminalPayerRouteEligible : Pareto.Eligible terminalPayerParetoProblem terminalPayerVectorRoute
terminalPayerRouteEligible = StateIndexed.portfolioCandidateIsEligible terminalPayerCandidate

replacementParetoProblem : Pareto.ConsumerMDLProblem
replacementParetoProblem = StateIndexed.asStateIndexedMDLProblem aiCapitalAcquisitionPortfolio Time.replacementDepreciationProducerOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority

replacementRouteEligible : Pareto.Eligible replacementParetoProblem gpuReplacementRoute
replacementRouteEligible = StateIndexed.portfolioCandidateIsEligible replacementCandidate

data CapitalAcquisitionAxis : Set where
  acquisitionCostAxis : CapitalAcquisitionAxis
  residualSurvivalAxis : CapitalAcquisitionAxis
  horizonPenaltyAxis : CapitalAcquisitionAxis
  dependencyDepthAxis : CapitalAcquisitionAxis
  authorityBurdenAxis : CapitalAcquisitionAxis

routeAxisCost : CapitalAcquisitionAxis → CapitalAcquisitionRoute → Nat
routeAxisCost acquisitionCostAxis terminalPayerVectorRoute = 2
routeAxisCost acquisitionCostAxis capitalSpreadFilingsRoute = 5
routeAxisCost acquisitionCostAxis inferenceQualityServingRoute = 3
routeAxisCost acquisitionCostAxis scarcityOpenClosedRoute = 3
routeAxisCost acquisitionCostAxis gpuReplacementRoute = 1
routeAxisCost acquisitionCostAxis rolloverFinanceRoute = 2
routeAxisCost acquisitionCostAxis policyGridRoute = 2
routeAxisCost acquisitionCostAxis marketSeriesRoute = 1
routeAxisCost acquisitionCostAxis reportedProposalShortcut = 0
routeAxisCost residualSurvivalAxis terminalPayerVectorRoute = 1
routeAxisCost residualSurvivalAxis capitalSpreadFilingsRoute = 0
routeAxisCost residualSurvivalAxis inferenceQualityServingRoute = 1
routeAxisCost residualSurvivalAxis scarcityOpenClosedRoute = 1
routeAxisCost residualSurvivalAxis gpuReplacementRoute = 1
routeAxisCost residualSurvivalAxis rolloverFinanceRoute = 1
routeAxisCost residualSurvivalAxis policyGridRoute = 1
routeAxisCost residualSurvivalAxis marketSeriesRoute = 0
routeAxisCost residualSurvivalAxis reportedProposalShortcut = 0
routeAxisCost horizonPenaltyAxis terminalPayerVectorRoute = 2
routeAxisCost horizonPenaltyAxis capitalSpreadFilingsRoute = 1
routeAxisCost horizonPenaltyAxis inferenceQualityServingRoute = 1
routeAxisCost horizonPenaltyAxis scarcityOpenClosedRoute = 1
routeAxisCost horizonPenaltyAxis gpuReplacementRoute = 1
routeAxisCost horizonPenaltyAxis rolloverFinanceRoute = 1
routeAxisCost horizonPenaltyAxis policyGridRoute = 0
routeAxisCost horizonPenaltyAxis marketSeriesRoute = 0
routeAxisCost horizonPenaltyAxis reportedProposalShortcut = 0
routeAxisCost dependencyDepthAxis terminalPayerVectorRoute = 1
routeAxisCost dependencyDepthAxis capitalSpreadFilingsRoute = 3
routeAxisCost dependencyDepthAxis inferenceQualityServingRoute = 3
routeAxisCost dependencyDepthAxis scarcityOpenClosedRoute = 2
routeAxisCost dependencyDepthAxis gpuReplacementRoute = 1
routeAxisCost dependencyDepthAxis rolloverFinanceRoute = 2
routeAxisCost dependencyDepthAxis policyGridRoute = 2
routeAxisCost dependencyDepthAxis marketSeriesRoute = 1
routeAxisCost dependencyDepthAxis reportedProposalShortcut = 0
routeAxisCost authorityBurdenAxis terminalPayerVectorRoute = 2
routeAxisCost authorityBurdenAxis capitalSpreadFilingsRoute = 1
routeAxisCost authorityBurdenAxis inferenceQualityServingRoute = 2
routeAxisCost authorityBurdenAxis scarcityOpenClosedRoute = 2
routeAxisCost authorityBurdenAxis gpuReplacementRoute = 1
routeAxisCost authorityBurdenAxis rolloverFinanceRoute = 1
routeAxisCost authorityBurdenAxis policyGridRoute = 1
routeAxisCost authorityBurdenAxis marketSeriesRoute = 1
routeAxisCost authorityBurdenAxis reportedProposalShortcut = 0

axisReference : CapitalAcquisitionAxis → String
axisReference acquisitionCostAxis = "declared acquisition effort; lower is better"
axisReference residualSurvivalAxis = "declared target residual survival after route; lower is better"
axisReference horizonPenaltyAxis = "same-horizon reconciliation burden; lower is better"
axisReference dependencyDepthAxis = "prerequisite join/transform depth; lower is better"
axisReference authorityBurdenAxis = "source/admission authority burden; lower is better"

capitalAcquisitionCosts : Pareto.CostHyperfabric terminalPayerParetoProblem
capitalAcquisitionCosts = Pareto.costHyperfabric CapitalAcquisitionAxis routeAxisCost axisReference

record AICapitalParetoAcquisitionBoundary : Set where
  constructor aiCapitalParetoAcquisitionBoundary
  field
    hardAdmissionPrecedesPareto : Bool
    hardAdmissionPrecedesParetoIsTrue : hardAdmissionPrecedesPareto ≡ true
    residualUpdateMayChangeRouteSalience : Bool
    residualUpdateMayChangeRouteSalienceIsTrue : residualUpdateMayChangeRouteSalience ≡ true
    replacementResidualIsExplicitlySchedulable : Bool
    replacementResidualIsExplicitlySchedulableIsTrue : replacementResidualIsExplicitlySchedulable ≡ true
    weightedScalarWinnerRequired : Bool
    weightedScalarWinnerRequiredIsFalse : weightedScalarWinnerRequired ≡ false
    paretoFrontierCreatesEmpiricalAuthority : Bool
    paretoFrontierCreatesEmpiricalAuthorityIsFalse : paretoFrontierCreatesEmpiricalAuthority ≡ false
    cheapProposalMayBypassSourceAdmission : Bool
    cheapProposalMayBypassSourceAdmissionIsFalse : cheapProposalMayBypassSourceAdmission ≡ false

canonicalAICapitalParetoAcquisitionBoundary : AICapitalParetoAcquisitionBoundary
canonicalAICapitalParetoAcquisitionBoundary = aiCapitalParetoAcquisitionBoundary true refl true refl true refl false refl false refl false refl
