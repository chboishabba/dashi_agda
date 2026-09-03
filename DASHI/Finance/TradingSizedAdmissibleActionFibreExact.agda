module DASHI.Finance.TradingSizedAdmissibleActionFibreExact where

open import DASHI.Core.Prelude

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Finance.TradingAdmissibleOptionConeSupersessionExact as Cone

------------------------------------------------------------------------
-- Full trading admissibility includes size/exposure.
--
-- Direction/action and size are not separate stages where a coarse action is
-- first admitted and then an arbitrary quantity is attached. The actionable
-- object is a proof-bearing sized transition whose size/exposure is itself
-- constrained by the joint state-indexed preconditions.
------------------------------------------------------------------------

data SizeBand : Set where
  zeroSize smallSize mediumSize largeSize : SizeBand

data LiquidityState : Set where
  thinLiquidity normalLiquidity deepLiquidity : LiquidityState

data TurnoverState : Set where
  turnoverTight turnoverOpen : TurnoverState

data NeutralityState : Set where
  neutralityTight neutralityOpen : NeutralityState

data ExecutionState : Set where
  executionFragile executionNormal : ExecutionState

data TemporalState : Set where
  pitValid pitInvalid : TemporalState

record FullTradeState : Set where
  constructor fullTradeState
  field
    coarseState : Cone.TradeState
    liquidity : LiquidityState
    turnover : TurnoverState
    neutrality : NeutralityState
    execution : ExecutionState
    temporal : TemporalState

open FullTradeState public

record SizedAction : Set where
  constructor sizedAction
  field
    control : Cone.ControlAction
    size : SizeBand

open SizedAction public

------------------------------------------------------------------------
-- Joint proof-bearing precondition.
--
-- `baseAction` proves the coarse action is available. The remaining witnesses
-- prove that the requested size/exposure survives the other constraints.
------------------------------------------------------------------------

data LiquidityAllows : LiquidityState → SizeBand → Set where
  liquidityZero : {l : LiquidityState} → LiquidityAllows l zeroSize
  thinSmall : LiquidityAllows thinLiquidity smallSize
  normalSmall : LiquidityAllows normalLiquidity smallSize
  normalMedium : LiquidityAllows normalLiquidity mediumSize
  deepSmall : LiquidityAllows deepLiquidity smallSize
  deepMedium : LiquidityAllows deepLiquidity mediumSize
  deepLarge : LiquidityAllows deepLiquidity largeSize

data TurnoverAllows : TurnoverState → SizeBand → Set where
  turnoverZero : {t : TurnoverState} → TurnoverAllows t zeroSize
  tightSmall : TurnoverAllows turnoverTight smallSize
  openSmall : TurnoverAllows turnoverOpen smallSize
  openMedium : TurnoverAllows turnoverOpen mediumSize
  openLarge : TurnoverAllows turnoverOpen largeSize

data NeutralityAllows : NeutralityState → Cone.ControlAction → SizeBand → Set where
  neutralityHold : {n : NeutralityState} → NeutralityAllows n Cone.holdAction zeroSize
  tightReduceSmall : NeutralityAllows neutralityTight Cone.reduceAction smallSize
  openReduceSmall : NeutralityAllows neutralityOpen Cone.reduceAction smallSize
  openReduceMedium : NeutralityAllows neutralityOpen Cone.reduceAction mediumSize
  openReduceLarge : NeutralityAllows neutralityOpen Cone.reduceAction largeSize
  tightIncreaseSmall : NeutralityAllows neutralityTight Cone.increaseAction smallSize
  openIncreaseSmall : NeutralityAllows neutralityOpen Cone.increaseAction smallSize
  openIncreaseMedium : NeutralityAllows neutralityOpen Cone.increaseAction mediumSize
  openIncreaseLarge : NeutralityAllows neutralityOpen Cone.increaseAction largeSize

data ExecutionAllows : ExecutionState → SizeBand → Set where
  executionZero : {e : ExecutionState} → ExecutionAllows e zeroSize
  fragileSmall : ExecutionAllows executionFragile smallSize
  normalSmall : ExecutionAllows executionNormal smallSize
  normalMedium : ExecutionAllows executionNormal mediumSize
  normalLarge : ExecutionAllows executionNormal largeSize

data TemporalAllows : TemporalState → Set where
  pitWitness : TemporalAllows pitValid

record SizedTradePrecondition
    (state : FullTradeState)
    (action : SizedAction) : Set where
  constructor sizedTradePrecondition
  field
    baseAction : Cone.TradePrecondition (coarseState state) (control action)
    liquidityAllows : LiquidityAllows (liquidity state) (size action)
    turnoverAllows : TurnoverAllows (turnover state) (size action)
    neutralityAllows : NeutralityAllows (neutrality state) (control action) (size action)
    executionAllows : ExecutionAllows (execution state) (size action)
    temporalAllows : TemporalAllows (temporal state)

open SizedTradePrecondition public

------------------------------------------------------------------------
-- HOLD is represented as the zero-change sized action.
------------------------------------------------------------------------

holdSized : SizedAction
holdSized = sizedAction Cone.holdAction zeroSize

holdSizedAvailable :
  (state : FullTradeState) →
  TemporalAllows (temporal state) →
  SizedTradePrecondition state holdSized
holdSizedAvailable state temporalWitness =
  sizedTradePrecondition
    Cone.holdAvailable
    liquidityZero
    turnoverZero
    neutralityHold
    executionZero
    temporalWitness

------------------------------------------------------------------------
-- Same directional action can have different feasible sizes because the full
-- precondition family differs. Therefore size cannot factor through action
-- alone, nor through the learned signal alone.
------------------------------------------------------------------------

clearLong : Cone.TradeState
clearLong = Cone.tradeState Cone.longExposure Cone.riskClear

deepOpenState : FullTradeState
deepOpenState =
  fullTradeState clearLong deepLiquidity turnoverOpen neutralityOpen executionNormal pitValid

thinTightState : FullTradeState
thinTightState =
  fullTradeState clearLong thinLiquidity turnoverTight neutralityTight executionFragile pitValid

largeIncrease : SizedAction
largeIncrease = sizedAction Cone.increaseAction largeSize

smallIncrease : SizedAction
smallIncrease = sizedAction Cone.increaseAction smallSize

deepOpenAllowsLargeIncrease : SizedTradePrecondition deepOpenState largeIncrease
deepOpenAllowsLargeIncrease =
  sizedTradePrecondition
    Cone.increaseLongClear
    deepLarge
    openLarge
    openIncreaseLarge
    normalLarge
    pitWitness

thinTightAllowsSmallIncrease : SizedTradePrecondition thinTightState smallIncrease
thinTightAllowsSmallIncrease =
  sizedTradePrecondition
    Cone.increaseLongClear
    thinSmall
    tightSmall
    tightIncreaseSmall
    fragileSmall
    pitWitness

thinTightCannotLargeIncrease :
  SizedTradePrecondition thinTightState largeIncrease → ⊥
thinTightCannotLargeIncrease ()

------------------------------------------------------------------------
-- Temporal/PIT admissibility participates in sizing/admissibility itself.
-- A future-contaminated state supplies no admissible sized transition receipt.
------------------------------------------------------------------------

pitInvalidState : FullTradeState
pitInvalidState =
  fullTradeState clearLong deepLiquidity turnoverOpen neutralityOpen executionNormal pitInvalid

pitInvalidBlocksSmallIncrease :
  SizedTradePrecondition pitInvalidState smallIncrease → ⊥
pitInvalidBlocksSmallIncrease ()

------------------------------------------------------------------------
-- The canonical executable choice is the dependent pair of sized action and
-- its full precondition witness. No naked action and no naked scalar size has
-- execution authority.
------------------------------------------------------------------------

AdmissibleSizedAction : FullTradeState → Set
AdmissibleSizedAction state =
  Σ SizedAction (SizedTradePrecondition state)

canonicalLargeChoice : AdmissibleSizedAction deepOpenState
canonicalLargeChoice = largeIncrease , deepOpenAllowsLargeIncrease

canonicalSmallChoice : AdmissibleSizedAction thinTightState
canonicalSmallChoice = smallIncrease , thinTightAllowsSmallIncrease

record SizingAuthorityBoundary : Set where
  constructor sizingAuthorityBoundary
  field
    actionThenArbitrarySize : Bool
    actionThenArbitrarySizeIsFalse : actionThenArbitrarySize ≡ false
    signalAloneDeterminesExposure : Bool
    signalAloneDeterminesExposureIsFalse : signalAloneDeterminesExposure ≡ false
    sizeIsPartOfJointAdmissibility : Bool
    sizeIsPartOfJointAdmissibilityIsTrue : sizeIsPartOfJointAdmissibility ≡ true
    temporalValidityParticipatesInAdmissibility : Bool
    temporalValidityParticipatesInAdmissibilityIsTrue :
      temporalValidityParticipatesInAdmissibility ≡ true

canonicalSizingAuthorityBoundary : SizingAuthorityBoundary
canonicalSizingAuthorityBoundary =
  sizingAuthorityBoundary false refl false refl true refl true refl

boundaryStatement : String
boundaryStatement =
  "Exposure and trade size are not post-hoc parameters. The executable object is a dependent pair of sized action and the full joint precondition witness; liquidity, turnover, neutrality, execution feasibility, risk/action availability, and PIT temporal validity jointly determine which sizes exist in the admissible fibre."
