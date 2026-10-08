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

data CapitalAcquisitionRoute : Set where
  terminalPayerVectorRoute capitalSpreadFilingsRoute inferenceQualityServingRoute
  scarcityOpenClosedRoute gpuReplacementRoute rolloverFinanceRoute policyGridRoute
  marketSeriesRoute persistenceReplicationRoute reportedProposalShortcut : CapitalAcquisitionRoute

data CapitalAcquisitionConsumer : Set where capitalRecoveryConsumer : CapitalAcquisitionConsumer
data CapitalSourceAuthority : Set where publicSourceAcquisitionAuthority : CapitalSourceAuthority

routeMove : CapitalAcquisitionRoute → Choice.InformationMove
routeMove terminalPayerVectorRoute = Choice.informationMove Choice.takeMeasurement 2 "complete same-horizon terminal payer / revenue vector" "filing and source acquisition" "public source evidence required"
routeMove capitalSpreadFilingsRoute = Choice.informationMove Choice.takeMeasurement 5 "realised ROIC-WACC producer" "company filings and debt instruments" "same-entity same-horizon accounting authority required"
routeMove inferenceQualityServingRoute = Choice.informationMove Choice.takeMeasurement 3 "quality-adjusted inference spread" "serving-price, quality and provider-cost join" "platform telemetry alone is insufficient"
routeMove scarcityOpenClosedRoute = Choice.informationMove Choice.takeMeasurement 3 "open/closed quality-price scarcity spread" "platform telemetry plus declared capability chart" "platform-local evidence only"
routeMove gpuReplacementRoute = Choice.informationMove Choice.takeMeasurement 1 "GPU replacement/depreciation route" "lender collateral/depreciation evidence" "replacement evidence is not capital recovery"
routeMove rolloverFinanceRoute = Choice.informationMove Choice.takeMeasurement 2 "same-borrower refinancing/rollover schedule" "debt maturity and refinancing evidence" "funding spread alone is insufficient"
routeMove policyGridRoute = Choice.informationMove Choice.takeMeasurement 2 "policy/grid backstop salience route" "regulator and permitting evidence" "policy salience is not capture probability"
routeMove marketSeriesRoute = Choice.informationMove Choice.takeMeasurement 1 "fixed-window AI-linked market flip/volatility series" "declared basket plus broad benchmark" "market state remains separate from fundamentals"
routeMove persistenceReplicationRoute = Choice.informationMove Choice.replicateMeasurement 2 "second comparable AI-capital state point" "same producer/coverage/horizon protocol" "replication does not create authority unless comparison gates close"
routeMove reportedProposalShortcut = Choice.informationMove Choice.takeMeasurement 0 "reported proposal shortcut" "proposal/report only" "not admitted"

routeReduction : CapitalAcquisitionRoute → Reduction.ReductionEnvelope
routeReduction terminalPayerVectorRoute = Reduction.reductionEnvelope 1 2 "may close terminal-payer and revenue-vector residuals"
routeReduction capitalSpreadFilingsRoute = Reduction.reductionEnvelope 1 1 "targets capital-spread residual"
routeReduction inferenceQualityServingRoute = Reduction.reductionEnvelope 0 1 "requires quality and serving-cost join"
routeReduction scarcityOpenClosedRoute = Reduction.reductionEnvelope 0 2 "may narrow scarcity and capability residuals"
routeReduction gpuReplacementRoute = Reduction.reductionEnvelope 0 1 "directly informs replacement/depreciation and obsolescence rung"
routeReduction rolloverFinanceRoute = Reduction.reductionEnvelope 0 1 "requires maturity/refinancing closure"
routeReduction policyGridRoute = Reduction.reductionEnvelope 0 1 "policy salience route remains noncausal"
routeReduction marketSeriesRoute = Reduction.reductionEnvelope 1 2 "fixed series can close flip/volatility producers"
routeReduction persistenceReplicationRoute = Reduction.reductionEnvelope 0 1 "one further comparable state may discharge only the first persistence comparison obligation"
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
routeRelevant Time.persistenceTrajectoryOpen capitalRecoveryConsumer persistenceReplicationRoute = true
routeRelevant _ _ _ = false

routeAdmitted : CapitalSourceAuthority → CapitalAcquisitionRoute → Bool
routeAdmitted publicSourceAcquisitionAuthority reportedProposalShortcut = false
routeAdmitted publicSourceAcquisitionAuthority _ = true

routeReference : CapitalAcquisitionRoute → String
routeReference terminalPayerVectorRoute = "complete payer/revenue vector"
routeReference capitalSpreadFilingsRoute = "same-entity realised ROIC-WACC"
routeReference inferenceQualityServingRoute = "quality-adjusted serving economics"
routeReference scarcityOpenClosedRoute = "open/closed quality-price substitution"
routeReference gpuReplacementRoute = "GPU replacement/depreciation"
routeReference rolloverFinanceRoute = "same-borrower refinancing schedule"
routeReference policyGridRoute = "grid/permitting policy support"
routeReference marketSeriesRoute = "fixed AI-linked market series"
routeReference persistenceReplicationRoute = "replicate comparable X_t under same comparison key"
routeReference reportedProposalShortcut = "inadmissible zero-cost negative fixture"

aiCapitalAcquisitionPortfolio : Portfolio.ExperimentPortfolio
aiCapitalAcquisitionPortfolio = Portfolio.experimentPortfolio CapitalAcquisitionRoute Time.MissingCapitalProducer CapitalAcquisitionConsumer CapitalSourceAuthority routeMove routeReduction routeRelevant routeAdmitted routeReference

terminalPayerCandidate : Portfolio.PortfolioCandidate aiCapitalAcquisitionPortfolio Time.terminalPayerCoverageOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority terminalPayerVectorRoute
terminalPayerCandidate = Portfolio.portfolioCandidate refl refl "terminal residual live" "cost 2"
replacementCandidate : Portfolio.PortfolioCandidate aiCapitalAcquisitionPortfolio Time.replacementDepreciationProducerOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority gpuReplacementRoute
replacementCandidate = Portfolio.portfolioCandidate refl refl "replacement residual live" "interval evidence narrows only"
persistenceCandidate : Portfolio.PortfolioCandidate aiCapitalAcquisitionPortfolio Time.persistenceTrajectoryOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority persistenceReplicationRoute
persistenceCandidate = Portfolio.portfolioCandidate refl refl "single current X_t leaves persistence live" "replicate under identical comparison definitions"

proposalShortcutNotAdmitted : Portfolio.admissibleNow aiCapitalAcquisitionPortfolio publicSourceAcquisitionAuthority reportedProposalShortcut ≡ false
proposalShortcutNotAdmitted = refl
persistenceRouteRelevant : Portfolio.relevantNow aiCapitalAcquisitionPortfolio Time.persistenceTrajectoryOpen capitalRecoveryConsumer persistenceReplicationRoute ≡ true
persistenceRouteRelevant = refl

data CapitalAcquisitionAxis : Set where acquisitionCostAxis residualSurvivalAxis horizonPenaltyAxis dependencyDepthAxis authorityBurdenAxis : CapitalAcquisitionAxis

routeAxisCost : CapitalAcquisitionAxis → CapitalAcquisitionRoute → Nat
routeAxisCost acquisitionCostAxis terminalPayerVectorRoute = 2
routeAxisCost acquisitionCostAxis capitalSpreadFilingsRoute = 5
routeAxisCost acquisitionCostAxis inferenceQualityServingRoute = 3
routeAxisCost acquisitionCostAxis scarcityOpenClosedRoute = 3
routeAxisCost acquisitionCostAxis gpuReplacementRoute = 1
routeAxisCost acquisitionCostAxis rolloverFinanceRoute = 2
routeAxisCost acquisitionCostAxis policyGridRoute = 2
routeAxisCost acquisitionCostAxis marketSeriesRoute = 1
routeAxisCost acquisitionCostAxis persistenceReplicationRoute = 2
routeAxisCost acquisitionCostAxis reportedProposalShortcut = 0
routeAxisCost residualSurvivalAxis persistenceReplicationRoute = 1
routeAxisCost residualSurvivalAxis marketSeriesRoute = 0
routeAxisCost residualSurvivalAxis capitalSpreadFilingsRoute = 0
routeAxisCost residualSurvivalAxis reportedProposalShortcut = 0
routeAxisCost residualSurvivalAxis _ = 1
routeAxisCost horizonPenaltyAxis terminalPayerVectorRoute = 2
routeAxisCost horizonPenaltyAxis _ = 0
routeAxisCost dependencyDepthAxis capitalSpreadFilingsRoute = 3
routeAxisCost dependencyDepthAxis inferenceQualityServingRoute = 3
routeAxisCost dependencyDepthAxis persistenceReplicationRoute = 2
routeAxisCost dependencyDepthAxis scarcityOpenClosedRoute = 2
routeAxisCost dependencyDepthAxis rolloverFinanceRoute = 2
routeAxisCost dependencyDepthAxis policyGridRoute = 2
routeAxisCost dependencyDepthAxis _ = 1
routeAxisCost authorityBurdenAxis terminalPayerVectorRoute = 2
routeAxisCost authorityBurdenAxis inferenceQualityServingRoute = 2
routeAxisCost authorityBurdenAxis scarcityOpenClosedRoute = 2
routeAxisCost authorityBurdenAxis reportedProposalShortcut = 0
routeAxisCost authorityBurdenAxis _ = 1

axisReference : CapitalAcquisitionAxis → String
axisReference acquisitionCostAxis = "declared acquisition effort"
axisReference residualSurvivalAxis = "declared residual survival"
axisReference horizonPenaltyAxis = "same-horizon reconciliation burden"
axisReference dependencyDepthAxis = "prerequisite join depth"
axisReference authorityBurdenAxis = "source/admission burden"

terminalPayerParetoProblem : Pareto.ConsumerMDLProblem
terminalPayerParetoProblem = StateIndexed.asStateIndexedMDLProblem aiCapitalAcquisitionPortfolio Time.terminalPayerCoverageOpen capitalRecoveryConsumer publicSourceAcquisitionAuthority
capitalAcquisitionCosts : Pareto.CostHyperfabric terminalPayerParetoProblem
capitalAcquisitionCosts = Pareto.costHyperfabric CapitalAcquisitionAxis routeAxisCost axisReference

record AICapitalParetoAcquisitionBoundary : Set where
  constructor aiCapitalParetoAcquisitionBoundary
  field
    hardAdmissionPrecedesPareto : Bool
    residualUpdateMayChangeRouteSalience : Bool
    replacementResidualIsExplicitlySchedulable : Bool
    persistenceResidualIsExplicitlySchedulable : Bool
    weightedScalarWinnerRequired : Bool
    paretoFrontierCreatesEmpiricalAuthority : Bool
    cheapProposalMayBypassSourceAdmission : Bool

open AICapitalParetoAcquisitionBoundary public
canonicalAICapitalParetoAcquisitionBoundary : AICapitalParetoAcquisitionBoundary
canonicalAICapitalParetoAcquisitionBoundary = aiCapitalParetoAcquisitionBoundary true true true true false false false
