{-# OPTIONS --safe #-}
module DASHI.Unified.ForecastComparativeNonPromotionTOEBridgeExact where

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F
--
-- O. Objective.
-- Connect existing forecast and comparative non-promotion theorems to the
-- focused DASHI TOE graph.
--
-- R. Reuse.
-- Reuse the exact forecast kernel, forecast lifecycle/time-cut boundary,
-- provider-neutral query boundary, WorldMonitor comparative boundary,
-- dashiTRADE comparative boundary, and dashiTRADE typed explanation boundary.
--
-- C. Construction.
-- Expose only theorem-bearing projections from existing owners.
-- Add no new forecast, market, world, or causal theorem.
--
-- S. Safety invariants.
-- Probability is not world state.
-- Score is not forecast truth.
-- Hindsight evidence does not enter the forecast-time cut silently.
-- Controlled score recomputation is not causal attribution.
-- A search hit does not pay a residual.
-- A forecast change does not automatically change the world.
-- A signal does not create claim truth.
-- A trading justification chain does not prove market causation.
-- Realised profit does not create global theory truth.
-- A typed explanation does not predict a market outcome.
--
-- L. Lane.
-- This module owns only forecast/comparative TOE normalization.
-- It does not edit ESD or digital_esd modules.
-- It does not copy code from meta-introspector repositories.
--
-- P. Postconditions.
-- TOE consumers reach one normalized exact non-promotion surface for forecast,
-- research, WorldMonitor, and dashiTRADE comparative semantics.
--
-- G. Governance.
-- Original theorem owners retain proof ownership.
-- Prototype repository history remains attribution context only.
-- External meta-introspector repositories remain process/tooling donors only.
--
-- F. Verification.
-- Source read-back must find every import and theorem below.
-- Kernel certification requires an exact-head Agda or CI receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Statistics.ForecastVerificationKernelExact as Kernel
import DASHI.Statistics.ForecastResolutionSelectionExact as Lifecycle
import DASHI.Core.ProviderNeutralWorldQueryAlgebraExact as Query
import DASHI.Law.SensibLawWorldMonitorComparativeAdapterExact as WorldMonitor
import DASHI.Law.SensibLawDashiTradeComparativeAdapterExact as Trade
import DASHI.Law.SensibLawDashiTradeTypedExplanationExact as TradeExplain

forecastKernelBoundary : Kernel.ForecastVerificationKernelBoundary
forecastKernelBoundary =
  Kernel.canonicalForecastVerificationKernelBoundary

forecastLifecycleBoundary : Lifecycle.ForecastResolutionSelectionBoundary
forecastLifecycleBoundary =
  Lifecycle.canonicalForecastResolutionSelectionBoundary

worldQueryBoundary : Query.ProviderNeutralWorldQueryBoundary
worldQueryBoundary =
  Query.canonicalProviderNeutralWorldQueryBoundary

worldMonitorBoundary : WorldMonitor.WorldMonitorComparativeBoundary
worldMonitorBoundary =
  WorldMonitor.canonicalWorldMonitorComparativeBoundary

tradeBoundary : Trade.DashiTradeComparativeBoundary
tradeBoundary =
  Trade.canonicalDashiTradeComparativeBoundary

tradeExplanationBoundary : TradeExplain.DashiTradeTypedExplanationBoundary
tradeExplanationBoundary =
  TradeExplain.canonicalDashiTradeTypedExplanationBoundary

toeProbabilityIsNotWorldState :
  Kernel.ForecastVerificationKernelBoundary.probabilityIsWorldState
    forecastKernelBoundary
  ≡ false
toeProbabilityIsNotWorldState =
  Kernel.ForecastVerificationKernelBoundary.probabilityIsWorldStateIsFalse
    forecastKernelBoundary

toeScoreIsNotForecastTruth :
  Kernel.ForecastVerificationKernelBoundary.scoreIsForecastTruth
    forecastKernelBoundary
  ≡ false
toeScoreIsNotForecastTruth =
  Kernel.ForecastVerificationKernelBoundary.scoreIsForecastTruthIsFalse
    forecastKernelBoundary

toeHindsightDoesNotLeakIntoForecastCut :
  Lifecycle.ForecastResolutionSelectionBoundary.hindsightEvidenceMayEnterForecastTimeCutSilently
    forecastLifecycleBoundary
  ≡ false
toeHindsightDoesNotLeakIntoForecastCut =
  Lifecycle.ForecastResolutionSelectionBoundary.hindsightEvidenceMayEnterForecastTimeCutSilentlyIsFalse
    forecastLifecycleBoundary

toeControlledRecomputationIsNotCausalAttribution :
  Lifecycle.ForecastResolutionSelectionBoundary.controlledRecomputationIsCausalAttribution
    forecastLifecycleBoundary
  ≡ false
toeControlledRecomputationIsNotCausalAttribution =
  Lifecycle.ForecastResolutionSelectionBoundary.controlledRecomputationIsCausalAttributionIsFalse
    forecastLifecycleBoundary

toeSearchHitDoesNotPayResidual :
  Query.ProviderNeutralWorldQueryBoundary.searchHitEqualsPayment
    worldQueryBoundary
  ≡ false
toeSearchHitDoesNotPayResidual =
  Query.ProviderNeutralWorldQueryBoundary.searchHitEqualsPaymentIsFalse
    worldQueryBoundary

toeExternalOntologyNavigationDoesNotCreateInternalTruth :
  Query.ProviderNeutralWorldQueryBoundary.wikidataNavigationCreatesCanonicalOntology
    worldQueryBoundary
  ≡ false
toeExternalOntologyNavigationDoesNotCreateInternalTruth =
  Query.ProviderNeutralWorldQueryBoundary.wikidataNavigationCreatesCanonicalOntologyIsFalse
    worldQueryBoundary

toeForecastChangeDoesNotAutomaticallyChangeWorld :
  WorldMonitor.WorldMonitorComparativeBoundary.forecastChangeAutomaticallyChangesWorld
    worldMonitorBoundary
  ≡ false
toeForecastChangeDoesNotAutomaticallyChangeWorld =
  WorldMonitor.WorldMonitorComparativeBoundary.forecastChangeAutomaticallyChangesWorldIsFalse
    worldMonitorBoundary

toeRiskScoreDoesNotAutomaticallyChangeWorld :
  WorldMonitor.WorldMonitorComparativeBoundary.riskScoreAutomaticallyChangesWorld
    worldMonitorBoundary
  ≡ false
toeRiskScoreDoesNotAutomaticallyChangeWorld =
  WorldMonitor.WorldMonitorComparativeBoundary.riskScoreAutomaticallyChangesWorldIsFalse
    worldMonitorBoundary

toeSignalAppearanceDoesNotCreateClaimTruth :
  WorldMonitor.WorldMonitorComparativeBoundary.signalAppearanceCreatesClaimTruth
    worldMonitorBoundary
  ≡ false
toeSignalAppearanceDoesNotCreateClaimTruth =
  WorldMonitor.WorldMonitorComparativeBoundary.signalAppearanceCreatesClaimTruthIsFalse
    worldMonitorBoundary

toeTradeJustificationDoesNotCreateCausalProof :
  Trade.DashiTradeComparativeBoundary.justificationChainCreatesCausalProof
    tradeBoundary
  ≡ false
toeTradeJustificationDoesNotCreateCausalProof =
  Trade.DashiTradeComparativeBoundary.justificationChainCreatesCausalProofIsFalse
    tradeBoundary

toeRealisedProfitDoesNotCreateGlobalTheoryTruth :
  Trade.DashiTradeComparativeBoundary.realisedProfitCreatesGlobalTheoryTruth
    tradeBoundary
  ≡ false
toeRealisedProfitDoesNotCreateGlobalTheoryTruth =
  Trade.DashiTradeComparativeBoundary.realisedProfitCreatesGlobalTheoryTruthIsFalse
    tradeBoundary

toeTypedTradeExplanationDoesNotPredictOutcome :
  TradeExplain.DashiTradeTypedExplanationBoundary.explanationPredictsMarketOutcome
    tradeExplanationBoundary
  ≡ false
toeTypedTradeExplanationDoesNotPredictOutcome =
  TradeExplain.DashiTradeTypedExplanationBoundary.explanationPredictsMarketOutcomeIsFalse
    tradeExplanationBoundary

toeTypedTradeExplanationDoesNotCreateClaimTruth :
  TradeExplain.DashiTradeTypedExplanationBoundary.explanationCreatesClaimTruth
    tradeExplanationBoundary
  ≡ false
toeTypedTradeExplanationDoesNotCreateClaimTruth =
  TradeExplain.DashiTradeTypedExplanationBoundary.explanationCreatesClaimTruthIsFalse
    tradeExplanationBoundary
