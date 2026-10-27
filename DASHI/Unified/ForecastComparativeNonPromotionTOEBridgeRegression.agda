{-# OPTIONS --safe #-}
module DASHI.Unified.ForecastComparativeNonPromotionTOEBridgeRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Unified.ForecastComparativeNonPromotionTOEBridgeExact as TOE

probabilityStillNotWorldState :
  TOE.Kernel.ForecastVerificationKernelBoundary.probabilityIsWorldState
    TOE.forecastKernelBoundary
  ≡ false
probabilityStillNotWorldState =
  TOE.toeProbabilityIsNotWorldState

scoreStillNotForecastTruth :
  TOE.Kernel.ForecastVerificationKernelBoundary.scoreIsForecastTruth
    TOE.forecastKernelBoundary
  ≡ false
scoreStillNotForecastTruth =
  TOE.toeScoreIsNotForecastTruth

hindsightStillBlockedFromForecastCut :
  TOE.Lifecycle.ForecastResolutionSelectionBoundary.hindsightEvidenceMayEnterForecastTimeCutSilently
    TOE.forecastLifecycleBoundary
  ≡ false
hindsightStillBlockedFromForecastCut =
  TOE.toeHindsightDoesNotLeakIntoForecastCut

controlledRecomputationStillNotCausal :
  TOE.Lifecycle.ForecastResolutionSelectionBoundary.controlledRecomputationIsCausalAttribution
    TOE.forecastLifecycleBoundary
  ≡ false
controlledRecomputationStillNotCausal =
  TOE.toeControlledRecomputationIsNotCausalAttribution

searchHitStillDoesNotPayResidual :
  TOE.Query.ProviderNeutralWorldQueryBoundary.searchHitEqualsPayment
    TOE.worldQueryBoundary
  ≡ false
searchHitStillDoesNotPayResidual =
  TOE.toeSearchHitDoesNotPayResidual

forecastChangeStillDoesNotChangeWorldAutomatically :
  TOE.WorldMonitor.WorldMonitorComparativeBoundary.forecastChangeAutomaticallyChangesWorld
    TOE.worldMonitorBoundary
  ≡ false
forecastChangeStillDoesNotChangeWorldAutomatically =
  TOE.toeForecastChangeDoesNotAutomaticallyChangeWorld

signalStillDoesNotCreateClaimTruth :
  TOE.WorldMonitor.WorldMonitorComparativeBoundary.signalAppearanceCreatesClaimTruth
    TOE.worldMonitorBoundary
  ≡ false
signalStillDoesNotCreateClaimTruth =
  TOE.toeSignalAppearanceDoesNotCreateClaimTruth

tradeJustificationStillDoesNotCreateCausalProof :
  TOE.Trade.DashiTradeComparativeBoundary.justificationChainCreatesCausalProof
    TOE.tradeBoundary
  ≡ false
tradeJustificationStillDoesNotCreateCausalProof =
  TOE.toeTradeJustificationDoesNotCreateCausalProof

realisedProfitStillDoesNotCreateTheoryTruth :
  TOE.Trade.DashiTradeComparativeBoundary.realisedProfitCreatesGlobalTheoryTruth
    TOE.tradeBoundary
  ≡ false
realisedProfitStillDoesNotCreateTheoryTruth =
  TOE.toeRealisedProfitDoesNotCreateGlobalTheoryTruth

typedTradeExplanationStillDoesNotPredictOutcome :
  TOE.TradeExplain.DashiTradeTypedExplanationBoundary.explanationPredictsMarketOutcome
    TOE.tradeExplanationBoundary
  ≡ false
typedTradeExplanationStillDoesNotPredictOutcome =
  TOE.toeTypedTradeExplanationDoesNotPredictOutcome
