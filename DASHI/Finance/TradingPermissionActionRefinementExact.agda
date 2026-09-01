module DASHI.Finance.TradingPermissionActionRefinementExact where

open import DASHI.Core.Prelude

import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream

------------------------------------------------------------------------
-- Permission is not action.
--
-- The legacy ternary Permission carrier ACT/HOLD/BAN is retained as a
-- historical authorization surface.  It does not by itself specify the
-- execution action to take.  In particular BAN is interpreted as
-- 'ban exposure-increasing action', not 'freeze the portfolio'.  If exposure
-- already exists, a blocked state may require an ACT-like risk-reduction move.
------------------------------------------------------------------------

data ExposureState : Set where
  flatExposure : ExposureState
  longExposure : ExposureState
  shortExposure : ExposureState

data ExecutionIntent : Set where
  increaseExposure : ExecutionIntent
  keepExposure : ExecutionIntent
  reduceExposure : ExecutionIntent
  flattenExposure : ExecutionIntent

data RefinedPermission : Set where
  mayIncreaseRisk : RefinedPermission
  holdOnly : RefinedPermission
  reduceRiskOnly : RefinedPermission

refinePermission : Legacy.Permission → RefinedPermission
refinePermission Legacy.ACT = mayIncreaseRisk
refinePermission Legacy.HOLD = holdOnly
refinePermission Legacy.BAN = reduceRiskOnly

permissionAllows : RefinedPermission → ExecutionIntent → Bool
permissionAllows mayIncreaseRisk increaseExposure = true
permissionAllows mayIncreaseRisk keepExposure = true
permissionAllows mayIncreaseRisk reduceExposure = true
permissionAllows mayIncreaseRisk flattenExposure = true
permissionAllows holdOnly increaseExposure = false
permissionAllows holdOnly keepExposure = true
permissionAllows holdOnly reduceExposure = false
permissionAllows holdOnly flattenExposure = false
permissionAllows reduceRiskOnly increaseExposure = false
permissionAllows reduceRiskOnly keepExposure = true
permissionAllows reduceRiskOnly reduceExposure = true
permissionAllows reduceRiskOnly flattenExposure = true

banBlocksIncrease :
  permissionAllows (refinePermission Legacy.BAN) increaseExposure ≡ false
banBlocksIncrease = refl

banAllowsReduction :
  permissionAllows (refinePermission Legacy.BAN) reduceExposure ≡ true
banAllowsReduction = refl

banAllowsFlatten :
  permissionAllows (refinePermission Legacy.BAN) flattenExposure ≡ true
banAllowsFlatten = refl

holdMeansNoChange :
  permissionAllows (refinePermission Legacy.HOLD) keepExposure ≡ true
holdMeansNoChange = refl

holdDoesNotAuthorizeIncrease :
  permissionAllows (refinePermission Legacy.HOLD) increaseExposure ≡ false
holdDoesNotAuthorizeIncrease = refl

------------------------------------------------------------------------
-- State-dependent execution compilation.
--
-- BAN over a flat book can result in no trade. BAN over a non-flat book can
-- legitimately compile to an active de-risk/flatten action. This is why BAN
-- can look ACT-like at the execution layer while remaining a negative
-- permission at the exposure-increase layer.
------------------------------------------------------------------------

compileIntent : Legacy.Permission → ExposureState → ExecutionIntent
compileIntent Legacy.ACT flatExposure = increaseExposure
compileIntent Legacy.ACT longExposure = keepExposure
compileIntent Legacy.ACT shortExposure = keepExposure
compileIntent Legacy.HOLD exposure = keepExposure
compileIntent Legacy.BAN flatExposure = keepExposure
compileIntent Legacy.BAN longExposure = reduceExposure
compileIntent Legacy.BAN shortExposure = reduceExposure

banFlatCompilesToHold :
  compileIntent Legacy.BAN flatExposure ≡ keepExposure
banFlatCompilesToHold = refl

banLongCompilesToActLikeReduction :
  compileIntent Legacy.BAN longExposure ≡ reduceExposure
banLongCompilesToActLikeReduction = refl

banShortCompilesToActLikeReduction :
  compileIntent Legacy.BAN shortExposure ≡ reduceExposure
banShortCompilesToActLikeReduction = refl

------------------------------------------------------------------------
-- Repair of the option-cone interpretation.
--
-- `riskBlocked` should block exposure-increasing BUY/SELL entries, but should
-- not be read as blocking risk-reducing exits. The old `TradeAction` carrier
-- is direction-only and cannot distinguish entry SELL from long-exit SELL.
-- We therefore expose this non-factorability rather than silently assigning
-- exit semantics to sellAction.
------------------------------------------------------------------------

data OrderRole : Set where
  entryOrder : OrderRole
  exitOrder : OrderRole
  reductionOrder : OrderRole

record SituatedOrder : Set where
  constructor situatedOrder
  field
    side : Dream.TradeAction
    role : OrderRole

open SituatedOrder public

riskBlockedOrderAvailable : SituatedOrder → Bool
riskBlockedOrderAvailable (situatedOrder Dream.holdAction role) = true
riskBlockedOrderAvailable (situatedOrder Dream.buyAction entryOrder) = false
riskBlockedOrderAvailable (situatedOrder Dream.sellAction entryOrder) = false
riskBlockedOrderAvailable (situatedOrder Dream.buyAction exitOrder) = true
riskBlockedOrderAvailable (situatedOrder Dream.sellAction exitOrder) = true
riskBlockedOrderAvailable (situatedOrder Dream.buyAction reductionOrder) = true
riskBlockedOrderAvailable (situatedOrder Dream.sellAction reductionOrder) = true

blockedLongExitSellAllowed :
  riskBlockedOrderAvailable
    (situatedOrder Dream.sellAction exitOrder) ≡ true
blockedLongExitSellAllowed = refl

blockedShortExitBuyAllowed :
  riskBlockedOrderAvailable
    (situatedOrder Dream.buyAction exitOrder) ≡ true
blockedShortExitBuyAllowed = refl

blockedNewBuyForbidden :
  riskBlockedOrderAvailable
    (situatedOrder Dream.buyAction entryOrder) ≡ false
blockedNewBuyForbidden = refl

blockedNewSellForbidden :
  riskBlockedOrderAvailable
    (situatedOrder Dream.sellAction entryOrder) ≡ false
blockedNewSellForbidden = refl

record PermissionActionBoundary : Set where
  constructor permissionActionBoundary
  field
    permissionIsExecutionAction : Bool
    permissionIsExecutionActionIsFalse : permissionIsExecutionAction ≡ false
    banMeansDoNothing : Bool
    banMeansDoNothingIsFalse : banMeansDoNothing ≡ false
    banMayCompileToActiveRiskReduction : Bool
    banMayCompileToActiveRiskReductionIsTrue :
      banMayCompileToActiveRiskReduction ≡ true
    holdMeansMaintainCurrentExposure : Bool
    holdMeansMaintainCurrentExposureIsTrue :
      holdMeansMaintainCurrentExposure ≡ true

canonicalPermissionActionBoundary : PermissionActionBoundary
canonicalPermissionActionBoundary =
  permissionActionBoundary false refl false refl true refl true refl

boundaryStatement : String
boundaryStatement =
  "ACT/HOLD/BAN is a permission layer, not an execution-action layer. BAN forbids increasing risk but may compile to an active reduce/flatten action when exposure exists; HOLD is the genuine maintain-current-exposure state."
