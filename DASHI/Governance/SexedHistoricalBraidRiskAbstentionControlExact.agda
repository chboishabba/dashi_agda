module DASHI.Governance.SexedHistoricalBraidRiskAbstentionControlExact where

------------------------------------------------------------------------
-- BRAID / RISK / ABSTENTION CONTROL BOUNDARY
--
-- Cross-pollination from the market-control lane:
--
--   uncertainty / abstention -> HOLD
--   explicit risk directive -> FLAT
--
-- Historical analogue:
--
--   unresolved long-horizon braid divergence -> suspend long forecast while
--   retaining currently justified immediate action;
--   branch destruction/closure requires a separate explicit closure authority.
--
-- This is a structural control grammar only.  It does not identify social
-- action with trading, historical branches with positions, or political
-- authority with a market risk directive.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Control.LearnedAbstentionBoundary as Market
import DASHI.Governance.SexedHistoricalConsumerIndexedBraidCryptoDivergenceExact as Consumer
import DASHI.Governance.SexedHistoricalHorizonQualifiedSelectiveReopeningExact as HorizonReopen

------------------------------------------------------------------------
-- 1. Historical control states.
------------------------------------------------------------------------

data HistoricalControlDirective : Set where
  continueImmediateAction
  suspendLongForecast
  explicitlyCloseBranch
  : HistoricalControlDirective

data BranchStatus : Set where
  branchRetained
  branchClosed
  : BranchStatus

applyHistoricalControl : HistoricalControlDirective → BranchStatus → BranchStatus
applyHistoricalControl continueImmediateAction status = status
applyHistoricalControl suspendLongForecast status = status
applyHistoricalControl explicitlyCloseBranch _ = branchClosed

suspensionRetainsBranch :
  applyHistoricalControl suspendLongForecast branchRetained ≡ branchRetained
suspensionRetainsBranch = refl

explicitClosureClosesBranch :
  applyHistoricalControl explicitlyCloseBranch branchRetained ≡ branchClosed
explicitClosureClosesBranch = refl

------------------------------------------------------------------------
-- 2. Consumer divergence chooses suspension at long horizon, not branch close.
------------------------------------------------------------------------

controlForConsumer : Consumer.HistoricalConsumer → HistoricalControlDirective
controlForConsumer Consumer.immediateActionConsumer = continueImmediateAction
controlForConsumer Consumer.shortForecastConsumer = continueImmediateAction
controlForConsumer Consumer.mediumForecastConsumer = continueImmediateAction
controlForConsumer Consumer.longForecastConsumer = suspendLongForecast
controlForConsumer Consumer.braidProvenanceConsumer = suspendLongForecast
controlForConsumer Consumer.riskControlConsumer = explicitlyCloseBranch

longDivergenceSuspendsRatherThanCloses :
  controlForConsumer Consumer.longForecastConsumer ≡ suspendLongForecast
longDivergenceSuspendsRatherThanCloses = refl

immediateConsumerContinues :
  controlForConsumer Consumer.immediateActionConsumer ≡ continueImmediateAction
immediateConsumerContinues = refl

riskConsumerUsesSeparateExplicitClosure :
  controlForConsumer Consumer.riskControlConsumer ≡ explicitlyCloseBranch
riskConsumerUsesSeparateExplicitClosure = refl

------------------------------------------------------------------------
-- 3. Continuity with horizon-qualified retention/reopening.
------------------------------------------------------------------------

immediateCertificateStillRetained :
  HorizonReopen.RetainedBelowFirstDivergence
    HorizonReopen.immediateActionCertificate
immediateCertificateStillRetained = HorizonReopen.canonicalImmediateRetention

longForecastStillReopens :
  HorizonReopen.reopeningDisposition HorizonReopen.longForecastCertificate
  ≡ HorizonReopen.reopenCertificate
longForecastStillReopens = HorizonReopen.longDispositionReopens

------------------------------------------------------------------------
-- 4. Exact market-control precedents retained as separate-domain witnesses.
------------------------------------------------------------------------

marketAbstentionIsHold :
  Market.compileDecision (Market.decision Market.up true) ≡ Market.hold
marketAbstentionIsHold = Market.abstentionCompilesToHold Market.up

marketNeutralIsHoldNotFlatten :
  Market.compileDecision (Market.decision Market.neutral false) ≡ Market.hold
marketNeutralIsHoldNotFlatten = Market.neutralDoesNotFlatten

marketExplicitRiskCloseFlattens :
  Market.compileRisk Market.closeExposure Market.hold ≡ Market.flatten
marketExplicitRiskCloseFlattens = Market.onlyRiskClosesExposure Market.hold

------------------------------------------------------------------------
-- 5. No-promotion boundaries.
------------------------------------------------------------------------

data HistoricalSuspensionMeansBranchDeletion : Set where

data LongForecastReopeningMeansImmediateActionStop : Set where

data TradingRiskDirectiveCreatesPoliticalAuthority : Set where

data HistoricalBranchIsFinancialPosition : Set where

data HoldMeansEndorsement : Set where

data ExplicitClosureIsAutomaticallyLegitimate : Set where

historicalSuspensionDoesNotDeleteBranch :
  HistoricalSuspensionMeansBranchDeletion → ⊥
historicalSuspensionDoesNotDeleteBranch ()

longForecastReopeningDoesNotStopImmediateAction :
  LongForecastReopeningMeansImmediateActionStop → ⊥
longForecastReopeningDoesNotStopImmediateAction ()

tradingRiskDirectiveDoesNotCreatePoliticalAuthority :
  TradingRiskDirectiveCreatesPoliticalAuthority → ⊥
tradingRiskDirectiveDoesNotCreatePoliticalAuthority ()

historicalBranchIsNotFinancialPosition : HistoricalBranchIsFinancialPosition → ⊥
historicalBranchIsNotFinancialPosition ()

holdDoesNotMeanEndorsement : HoldMeansEndorsement → ⊥
holdDoesNotMeanEndorsement ()

explicitClosureIsNotAutomaticallyLegitimate :
  ExplicitClosureIsAutomaticallyLegitimate → ⊥
explicitClosureIsNotAutomaticallyLegitimate ()

record BraidRiskAbstentionControlBoundary : Set where
  constructor braid-risk-abstention-control-boundary
  field
    immediateActionCanRemainActive : Bool
    longForecastCanSuspendSeparately : Bool
    suspensionRetainsBranch : Bool
    explicitClosureSeparate : Bool
    marketHoldFlatBoundaryReusedStructurally : Bool
    historicalBranchEqualsFinancialPosition : Bool
    marketRiskDirectiveCreatesPoliticalAuthority : Bool
    explicitClosureAutomaticallyLegitimate : Bool

canonicalBraidRiskAbstentionControlBoundary : BraidRiskAbstentionControlBoundary
canonicalBraidRiskAbstentionControlBoundary =
  braid-risk-abstention-control-boundary
    true true true true true false false false
