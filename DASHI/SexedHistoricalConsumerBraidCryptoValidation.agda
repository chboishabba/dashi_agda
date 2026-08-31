module DASHI.SexedHistoricalConsumerBraidCryptoValidation where

open import DASHI.Core.Prelude

import DASHI.Control.LearnedAbstentionBoundary as Market
import DASHI.Crypto.AttackerObservationLanguageRefinementExact as CryptoObs
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Governance.SexedHistoricalConsumerIndexedBraidCryptoDivergenceExact as Consumer
import DASHI.Governance.SexedHistoricalBraidedStratifiedConsumerKernelExact as Kernel
import DASHI.Governance.SexedHistoricalBraidRiskAbstentionControlExact as Control
import DASHI.Governance.SexedHistoricalStratifiedFutureConeQuotientExact as Future

immediateConsumerNoDivergenceRegression :
  Consumer.consumerDivergence Consumer.immediateActionConsumer
  ≡ Consumer.noDivergenceWithinDeclaredScope
immediateConsumerNoDivergenceRegression = refl

longConsumerFirstDivergenceRegression :
  Consumer.consumerDivergence Consumer.longForecastConsumer
  ≡ Consumer.firstVisibleAtLongHorizon
longConsumerFirstDivergenceRegression = refl

braidConsumerAlreadySeparatesRegression :
  Consumer.consumerDivergence Consumer.braidProvenanceConsumer
  ≡ Consumer.braidTraceAlreadySeparates
braidConsumerAlreadySeparatesRegression = refl

cryptoStyleBaseObservationStillCollidesRegression :
  CryptoObs.BaseEquivalent
    Consumer.historicalBraidObservationLanguage
    Future.repairedThenPluralised
    Future.repairedThenInstitutionalised
cryptoStyleBaseObservationStillCollidesRegression =
  Consumer.immediateActionBaseEquivalent

cryptoStyleExtendedObservationSeparatesRegression :
  CryptoObs.ExtendedEquivalent
    Consumer.historicalBraidObservationLanguage
    Future.repairedThenPluralised
    Future.repairedThenInstitutionalised → ⊥
cryptoStyleExtendedObservationSeparatesRegression =
  Consumer.braidProvenanceRefinesImmediateActionLanguage

evidenceFidelityImmediateSwapSafeRegression :
  Kernel.SwapSafeImmediate Kernel.evidenceFidelityWord
evidenceFidelityImmediateSwapSafeRegression =
  Kernel.evidenceFidelitySwapImmediateSafe

evidenceFidelityProvenanceSwapUnsafeRegression :
  Kernel.SwapSafeProvenance Kernel.evidenceFidelityWord → ⊥
evidenceFidelityProvenanceSwapUnsafeRegression =
  Kernel.evidenceFidelitySwapNotProvenanceSafe

supportInstitutionFutureSwapUnsafeRegression :
  Kernel.SwapSafeFuture Kernel.supportInstitutionWord → ⊥
supportInstitutionFutureSwapUnsafeRegression =
  Kernel.supportInstitutionSwapNotFutureSafe

longConsumerCornerStratumRegression :
  Kernel.consumerKernelStratum Consumer.longForecastConsumer
  ≡ Strata.cornerStratum
longConsumerCornerStratumRegression = refl

historicalLongDivergenceSuspendsRegression :
  Control.controlForConsumer Consumer.longForecastConsumer
  ≡ Control.suspendLongForecast
historicalLongDivergenceSuspendsRegression = refl

historicalSuspensionRetainsBranchRegression :
  Control.applyHistoricalControl
    Control.suspendLongForecast Control.branchRetained
  ≡ Control.branchRetained
historicalSuspensionRetainsBranchRegression = Control.suspensionRetainsBranch

marketNeutralHoldRegression :
  Market.compileDecision (Market.decision Market.neutral false)
  ≡ Market.hold
marketNeutralHoldRegression = Control.marketNeutralIsHoldNotFlatten

marketExplicitRiskCloseRegression :
  Market.compileRisk Market.closeExposure Market.hold
  ≡ Market.flatten
marketExplicitRiskCloseRegression = Control.marketExplicitRiskCloseFlattens

consumerBraidCryptoBoundaryRegression :
  Consumer.ConsumerIndexedBraidCryptoDivergenceBoundary
consumerBraidCryptoBoundaryRegression =
  Consumer.canonicalConsumerIndexedBraidCryptoDivergenceBoundary

braidedConsumerKernelBoundaryRegression :
  Kernel.BraidedStratifiedConsumerKernelBoundary
braidedConsumerKernelBoundaryRegression =
  Kernel.canonicalBraidedStratifiedConsumerKernelBoundary

braidRiskControlBoundaryRegression :
  Control.BraidRiskAbstentionControlBoundary
braidRiskControlBoundaryRegression =
  Control.canonicalBraidRiskAbstentionControlBoundary
