module DASHI.Economics.AIMaxCutReconciliation20261012FinalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIMaxCutReconciliation20261012Exact as Prior
import DASHI.Economics.AIFixedBasketMarketSeries20261012Exact as Basket
import DASHI.Economics.AIOpenWeightTrajectory20261012Exact as OpenTrajectory
import DASHI.Economics.AIQualityNormalizedPriceSpread20261012Exact as QualityPrice
import DASHI.Economics.AITwoSidedConcentrationPropagation20261012Exact as Concentration

------------------------------------------------------------------------
-- FINAL OCTOBER-12 RECONCILIATION
--
-- This owner records only the incremental max-cut beyond the prior October-12
-- reconciliation. All payments are scoped; none is allowed to manufacture the
-- genuinely missing terminal/fundamental producers.
------------------------------------------------------------------------

data FinalState : Set where
  open partial paid : FinalState

record FinalProducer : Set where
  constructor finalProducer
  field
    producer : String
    state : FinalState
    scope : String
    receipt : String
    promotesGlobalCapitalRecovery : Bool

open FinalProducer public

selectedPublicEquityDynamicsPaid : FinalProducer
selectedPublicEquityDynamicsPaid = finalProducer
  "fixed-composition public-equity flip/volatility"
  paid
  "equal-weight CRWV/ORCL/AVGO; seven sessions 2026-10-01..2026-10-09"
  "4 flips over 6 transitions; 66.67 percent flip rate; 2.8644 percent population daily realised volatility"
  false

vercelOpenWeightTrajectoryPaid : FinalProducer
vercelOpenWeightTrajectoryPaid = finalProducer
  "same-platform open-weight token-share trajectory"
  paid
  "Vercel AI Gateway"
  "open-weight token share rises from 56.0 percent in August to 61.3 percent on 2026-10-10, +5.3 percentage points"
  false

selectedBenchmarkPricePairPaid : FinalProducer
selectedBenchmarkPricePairPaid = finalProducer
  "selected benchmark-normalised open/closed API-price pair"
  paid
  "Artificial Analysis Intelligence Index: MiMo-V2.6-Pro vs Claude Opus 5.5 Max"
  "reported cost per index task and score imply approximately 36.483x closed/open cost-per-index-point ratio for this selected pair"
  false

coreWeaveTwoSidedConcentrationPaid : FinalProducer
coreWeaveTwoSidedConcentrationPaid = finalProducer
  "CoreWeave two-sided concentration topology"
  paid
  "CoreWeave Q2-2026 customer side + Core Scientific H1-2026 provider side"
  "CoreWeave top-three customers account for 72 percent with HHI bounds 0.2072..0.2856; CoreWeave is approximately 77 percent of Core Scientific H1 revenue"
  false

wholeComplexMarketDynamicsStillPartial : FinalProducer
wholeComplexMarketDynamicsStillPartial = finalProducer
  "whole-complex market dynamics"
  partial
  "public equities + broad market/IPO/credit evidence"
  "private labs, credit, SPVs and non-public infrastructure positions are not one harmonised fixed market basket"
  false

globalOpenWeightTrajectoryStillOpen : FinalProducer
globalOpenWeightTrajectoryStillOpen = finalProducer
  "global open-weight usage trajectory"
  open
  "global market"
  "Vercel trajectory is platform-local and cannot establish global usage share"
  false

sameCapabilityScarcityRentStillOpen : FinalProducer
sameCapabilityScarcityRentStillOpen = finalProducer
  "same-capability open/closed scarcity rent"
  open
  "global model market"
  "benchmark-normalised selected-pair pricing does not establish equal capability or a global scarcity-rent spread"
  false

providerServingMarginStillOpen : FinalProducer
providerServingMarginStillOpen = finalProducer
  "quality-adjusted provider serving margin"
  open
  "provider economics"
  "API price is observed but same-object marginal serving cost remains absent"
  false

terminalPayerStillOpen : FinalProducer
terminalPayerStillOpen = finalProducer
  "independent terminal-payer provenance"
  open
  "global/entity"
  "two-sided concentration and role overlap refine dependency topology but do not identify complete independent terminal cash"
  false

realisedROICWACCStillOpen : FinalProducer
realisedROICWACCStillOpen = finalProducer
  "realised ROIC-WACC"
  open
  "global/entity"
  "operating trajectories and maturity schedules do not yet provide an admissible same-entity realised ROIC plus WACC join"
  false

------------------------------------------------------------------------
-- Proof receipts and non-promotion.
------------------------------------------------------------------------

selectedBasketFlipPaid : Basket.selectedBasketFlipRateClosed Basket.selectedAICapitalBasketResult ≡ true
selectedBasketFlipPaid = Basket.selectedFlipRateIsClosed

selectedBasketVolPaid : Basket.selectedBasketVolatilityClosed Basket.selectedAICapitalBasketResult ≡ true
selectedBasketVolPaid = Basket.selectedVolatilityIsClosed

openTrajectoryPaid : OpenTrajectory.platformLocalPersistenceObserved OpenTrajectory.vercelOpenWeightTrajectory ≡ true
openTrajectoryPaid = OpenTrajectory.platformPersistenceIsObserved

openTrajectoryStillNotGlobal : OpenTrajectory.globalMarketTrajectoryClosed OpenTrajectory.vercelOpenWeightTrajectory ≡ false
openTrajectoryStillNotGlobal = OpenTrajectory.globalTrajectoryStillOpen

qualityPricePairPaid : QualityPrice.selectedPairClosed QualityPrice.mimoVsOpusBenchmarkPricePair ≡ true
qualityPricePairPaid = QualityPrice.selectedPairIsPaid

qualityPricePairStillNotMargin : QualityPrice.providerMarginClosed QualityPrice.mimoVsOpusBenchmarkPricePair ≡ false
qualityPricePairStillNotMargin = QualityPrice.providerMarginStillOpen

coreWeaveTwoSidedObserved : Concentration.twoSidedConcentrationObserved Concentration.coreWeaveTwoSidedConcentration ≡ true
coreWeaveTwoSidedObserved = refl

coreWeaveTwoSidedStillNotTerminal : Concentration.terminalPayerIndependenceClosed Concentration.coreWeaveTwoSidedConcentration ≡ false
coreWeaveTwoSidedStillNotTerminal = Concentration.terminalIndependenceStillOpen

data ScopedPaymentImpliesGlobalClosurePermission : Set where

data PriceNormalizationImpliesMarginPermission : Set where

data ConcentrationTopologyImpliesTerminalPayerPermission : Set where

scopedPaymentDoesNotAutoCloseGlobal : ScopedPaymentImpliesGlobalClosurePermission → ⊥
scopedPaymentDoesNotAutoCloseGlobal ()

priceNormalizationDoesNotAutoCreateMargin : PriceNormalizationImpliesMarginPermission → ⊥
priceNormalizationDoesNotAutoCreateMargin ()

concentrationTopologyDoesNotAutoCreateTerminalPayer : ConcentrationTopologyImpliesTerminalPayerPermission → ⊥
concentrationTopologyDoesNotAutoCreateTerminalPayer ()

finalBoundary : String
finalBoundary =
  "After the October-12 max-cut, selected public-equity market dynamics, Vercel platform-local open-weight persistence, one benchmark-normalised open/closed API-price pair, and CoreWeave two-sided concentration are paid. The remaining substantive frontier is independent terminal-payer provenance, realised ROIC-WACC, same-object marginal serving cost/quality-adjusted inference margin, global same-capability scarcity rent, whole-complex comparable market/state dynamics, and measured regulatory burden/concentration response."
