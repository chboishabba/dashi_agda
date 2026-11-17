{-# OPTIONS --safe #-}
module DASHI.Unified.ForecastComparativeNonPromotionTOEBridgeRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.ForecastComparativeNonPromotionTOEBridgeExact as TOE
import DASHI.Statistics.ForecastVerificationKernelExact as Kernel
import DASHI.Statistics.ForecastResolutionSelectionExact as Lifecycle
import DASHI.Core.ProviderNeutralWorldQueryAlgebraExact as Query
import DASHI.Law.SensibLawWorldMonitorComparativeAdapterExact as WorldMonitor
import DASHI.Law.SensibLawDashiTradeComparativeAdapterExact as Trade
import DASHI.Law.SensibLawDashiTradeTypedExplanationExact as TradeExplain
import DASHI.Unifier as LegacyUnifier

probabilityStillNotWorldState :
  Kernel.ForecastVerificationKernelBoundary.probabilityIsWorldState
    TOE.forecastKernelBoundary
  ≡ false
probabilityStillNotWorldState =
  TOE.toeProbabilityIsNotWorldState

scoreStillNotForecastTruth :
  Kernel.ForecastVerificationKernelBoundary.scoreIsForecastTruth
    TOE.forecastKernelBoundary
  ≡ false
scoreStillNotForecastTruth =
  TOE.toeScoreIsNotForecastTruth

hindsightStillBlockedFromForecastCut :
  Lifecycle.ForecastResolutionSelectionBoundary.hindsightEvidenceMayEnterForecastTimeCutSilently
    TOE.forecastLifecycleBoundary
  ≡ false
hindsightStillBlockedFromForecastCut =
  TOE.toeHindsightDoesNotLeakIntoForecastCut

controlledRecomputationStillNotCausal :
  Lifecycle.ForecastResolutionSelectionBoundary.controlledRecomputationIsCausalAttribution
    TOE.forecastLifecycleBoundary
  ≡ false
controlledRecomputationStillNotCausal =
  TOE.toeControlledRecomputationIsNotCausalAttribution

searchHitStillDoesNotPayResidual :
  Query.ProviderNeutralWorldQueryBoundary.searchHitEqualsPayment
    TOE.worldQueryBoundary
  ≡ false
searchHitStillDoesNotPayResidual =
  TOE.toeSearchHitDoesNotPayResidual

forecastChangeStillDoesNotChangeWorldAutomatically :
  WorldMonitor.WorldMonitorComparativeBoundary.forecastChangeAutomaticallyChangesWorld
    TOE.worldMonitorBoundary
  ≡ false
forecastChangeStillDoesNotChangeWorldAutomatically =
  TOE.toeForecastChangeDoesNotAutomaticallyChangeWorld

signalStillDoesNotCreateClaimTruth :
  WorldMonitor.WorldMonitorComparativeBoundary.signalAppearanceCreatesClaimTruth
    TOE.worldMonitorBoundary
  ≡ false
signalStillDoesNotCreateClaimTruth =
  TOE.toeSignalAppearanceDoesNotCreateClaimTruth

tradeJustificationStillDoesNotCreateCausalProof :
  Trade.DashiTradeComparativeBoundary.justificationChainCreatesCausalProof
    TOE.tradeBoundary
  ≡ false
tradeJustificationStillDoesNotCreateCausalProof =
  TOE.toeTradeJustificationDoesNotCreateCausalProof

realisedProfitStillDoesNotCreateTheoryTruth :
  Trade.DashiTradeComparativeBoundary.realisedProfitCreatesGlobalTheoryTruth
    TOE.tradeBoundary
  ≡ false
realisedProfitStillDoesNotCreateTheoryTruth =
  TOE.toeRealisedProfitDoesNotCreateGlobalTheoryTruth

typedTradeExplanationStillDoesNotPredictOutcome :
  TradeExplain.DashiTradeTypedExplanationBoundary.explanationPredictsMarketOutcome
    TOE.tradeExplanationBoundary
  ≡ false
typedTradeExplanationStillDoesNotPredictOutcome =
  TOE.toeTypedTradeExplanationDoesNotPredictOutcome


unifierProbabilityAliasUsesExactOwner :
  LegacyUnifier.toeForecastProbabilityIsNotWorldState
  ≡ TOE.toeProbabilityIsNotWorldState
unifierProbabilityAliasUsesExactOwner = refl

unifierScoreAliasUsesExactOwner :
  LegacyUnifier.toeForecastScoreIsNotTruth
  ≡ TOE.toeScoreIsNotForecastTruth
unifierScoreAliasUsesExactOwner = refl

unifierSearchPaymentAliasUsesExactOwner :
  LegacyUnifier.toeForecastSearchHitDoesNotPayResidual
  ≡ TOE.toeSearchHitDoesNotPayResidual
unifierSearchPaymentAliasUsesExactOwner = refl

unifierTradeCausationAliasUsesExactOwner :
  LegacyUnifier.toeTradeJustificationDoesNotCreateCausalProof
  ≡ TOE.toeTradeJustificationDoesNotCreateCausalProof
unifierTradeCausationAliasUsesExactOwner = refl
