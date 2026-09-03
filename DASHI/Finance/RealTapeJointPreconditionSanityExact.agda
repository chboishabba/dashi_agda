module DASHI.Finance.RealTapeJointPreconditionSanityExact where

open import DASHI.Core.Prelude

import DASHI.Finance.TradingJointPreconditionFabricExact as Joint

------------------------------------------------------------------------
-- Published market-tape sanity cases.
--
-- These constructors encode only facts exposed by a public NASDAQ/LOBSTER
-- sample: ordinary live-book activity and an explicit trading-halt interval.
-- They deliberately do NOT manufacture factor, portfolio, authority, or
-- economic-admissibility facts that are absent from the tape.
------------------------------------------------------------------------

data TapePhase : Set where
  liveBookPhase : TapePhase
  haltedPhase : TapePhase
  quotingResumedPhase : TapePhase
  tradingResumedPhase : TapePhase

record TapeState : Set where
  constructor tapeState
  field
    phase : TapePhase
    displayedAskDepth : Nat
    tapeTimeNanosTag : Nat

open TapeState public

-- The public example records 9,484 displayed shares before a 100-share ask
-- deletion and 9,384 after it.  Times are represented only by stable local
-- tags here; the exact decimal timestamps remain provenance in the source.
normalBefore : TapeState
normalBefore = tapeState liveBookPhase 9484 1

normalAfter100Delete : TapeState
normalAfter100Delete = tapeState liveBookPhase 9384 2

haltedTape : TapeState
haltedTape = tapeState haltedPhase 0 3

quotingResumedTape : TapeState
quotingResumedTape = tapeState quotingResumedPhase 0 4

tradingResumedTape : TapeState
tradingResumedTape = tapeState tradingResumedPhase 0 5

askDepthDrop : Nat
askDepthDrop = displayedAskDepth normalBefore - displayedAskDepth normalAfter100Delete

askDepthDropIs100 : askDepthDrop ≡ 100
askDepthDropIs100 = refl

------------------------------------------------------------------------
-- Candidate transitions remain stable objects.  The tape can constrain some
-- of their preconditions but cannot supply the whole trading proof fabric.
------------------------------------------------------------------------

data TapeTransition : Set where
  passiveHold : TapeTransition
  displayedHundredShareTake : TapeTransition
  largerLiquidityTakingTransition : TapeTransition

tapeCarrier : Joint.TransitionCarrier
tapeCarrier = Joint.transitionCarrier TapeTransition gross turn label
  where
    gross : TapeTransition → Nat
    gross passiveHold = 0
    gross displayedHundredShareTake = 100
    gross largerLiquidityTakingTransition = 1000

    turn : TapeTransition → Nat
    turn passiveHold = 0
    turn displayedHundredShareTake = 100
    turn largerLiquidityTakingTransition = 1000

    label : TapeTransition → String
    label passiveHold = "passive hold"
    label displayedHundredShareTake = "100-share liquidity-taking candidate"
    label largerLiquidityTakingTransition = "larger liquidity-taking candidate"

------------------------------------------------------------------------
-- Evidence strata exposed by the tape itself.
------------------------------------------------------------------------

data TapePIT : TapeState → TapeTransition → Set where
  tapePIT : {state : TapeState} {delta : TapeTransition} → TapePIT state delta

data TapeLiquidity : TapeState → TapeTransition → Set where
  holdLiquidity : {state : TapeState} → TapeLiquidity state passiveHold
  hundredLiveLiquidity :
    TapeLiquidity normalBefore displayedHundredShareTake

data TapeExecution : TapeState → TapeTransition → Set where
  holdLiveExecution : TapeExecution normalBefore passiveHold
  hundredLiveExecution : TapeExecution normalBefore displayedHundredShareTake
  holdAfterDeleteExecution : TapeExecution normalAfter100Delete passiveHold
  hundredAfterDeleteExecution : TapeExecution normalAfter100Delete displayedHundredShareTake
  resumedHoldExecution : TapeExecution tradingResumedTape passiveHold

data NotObservedOnTape : TapeState → TapeTransition → Set where

data JointEconomicCompatibility : TapeState → TapeTransition → Set where

------------------------------------------------------------------------
-- Full fabric instantiated conservatively: PIT market-data observations are
-- available; liquidity/execution have only literal tape witnesses; factor,
-- inventory, risk, neutrality, turnover economics, impact economics,
-- authority and final joint compatibility remain uninhabited because the
-- public tape alone does not establish them.
------------------------------------------------------------------------

tapeFabric : Joint.TradingPreconditionFabric TapeState tapeCarrier
tapeFabric = record
  { UniversePIT = NotObservedOnTape
  ; MarketDataPIT = TapePIT
  ; FactorResidualValid = NotObservedOnTape
  ; InventoryCompatible = NotObservedOnTape
  ; LiquidityCapacity = TapeLiquidity
  ; RiskBudget = NotObservedOnTape
  ; Neutrality = NotObservedOnTape
  ; TurnoverBudget = NotObservedOnTape
  ; CostImpactViable = NotObservedOnTape
  ; ExecutionFeasible = TapeExecution
  ; AuthorityCurrent = NotObservedOnTape
  ; JointCompatibility = JointEconomicCompatibility
  }

------------------------------------------------------------------------
-- Sanity result 1: a normal live tape can support local market-data,
-- liquidity and execution observations, but it cannot by itself authorize a
-- portfolio transition.  Alpha/size are not inferred from visible depth.
------------------------------------------------------------------------

normalTapeShowsMarketDataPIT :
  Joint.MarketDataPIT tapeFabric normalBefore displayedHundredShareTake
normalTapeShowsMarketDataPIT = tapePIT

normalTapeShowsHundredLiquidity :
  Joint.LiquidityCapacity tapeFabric normalBefore displayedHundredShareTake
normalTapeShowsHundredLiquidity = hundredLiveLiquidity

normalTapeShowsHundredExecutionLocally :
  Joint.ExecutionFeasible tapeFabric normalBefore displayedHundredShareTake
normalTapeShowsHundredExecutionLocally = hundredLiveExecution

normalTapeDoesNotAuthorizeHundredShareTrade :
  Joint.JointlyAdmissible
    tapeFabric normalBefore displayedHundredShareTake → ⊥
normalTapeDoesNotAuthorizeHundredShareTrade receipt =
  noAuthority (Joint.authorityCurrent receipt)
  where
    noAuthority :
      NotObservedOnTape normalBefore displayedHundredShareTake → ⊥
    noAuthority ()

largerTradeNotLicensedByDisplayedDepth :
  Joint.LiquidityCapacity
    tapeFabric normalBefore largerLiquidityTakingTransition → ⊥
largerTradeNotLicensedByDisplayedDepth ()

------------------------------------------------------------------------
-- Sanity result 2: during a literal halt, execution feasibility is absent.
-- No learned score, nominal direction, or desired exposure can repair this
-- missing local execution witness.
------------------------------------------------------------------------

haltHasTapePIT :
  Joint.MarketDataPIT tapeFabric haltedTape displayedHundredShareTake
haltHasTapePIT = tapePIT

haltBlocksExecution :
  Joint.ExecutionFeasible tapeFabric haltedTape displayedHundredShareTake → ⊥
haltBlocksExecution ()

haltBlocksJointAdmissibility :
  Joint.JointlyAdmissible
    tapeFabric haltedTape displayedHundredShareTake → ⊥
haltBlocksJointAdmissibility receipt =
  haltBlocksExecution (Joint.executionFeasible receipt)

quotingResumeStillDoesNotInventExecution :
  Joint.ExecutionFeasible
    tapeFabric quotingResumedTape displayedHundredShareTake → ⊥
quotingResumeStillDoesNotInventExecution ()

tradingResumeCanRestoreLocalExecutionForHold :
  Joint.ExecutionFeasible tapeFabric tradingResumedTape passiveHold
tradingResumeCanRestoreLocalExecutionForHold = resumedHoldExecution

------------------------------------------------------------------------
-- Boundary: tape evidence is one stratum in the fabric, not the whole fabric.
------------------------------------------------------------------------

record RealTapeSanityBoundary : Set where
  constructor realTapeSanityBoundary
  field
    visibleDepthDeterminesPortfolioSize : Bool
    visibleDepthDeterminesPortfolioSizeIsFalse :
      visibleDepthDeterminesPortfolioSize ≡ false
    liveTapeAloneDeterminesJointAdmissibility : Bool
    liveTapeAloneDeterminesJointAdmissibilityIsFalse :
      liveTapeAloneDeterminesJointAdmissibility ≡ false
    haltRemovesExecutionWitness : Bool
    haltRemovesExecutionWitnessIsTrue :
      haltRemovesExecutionWitness ≡ true
    tradingResumeMayReopenExecutionStratum : Bool
    tradingResumeMayReopenExecutionStratumIsTrue :
      tradingResumeMayReopenExecutionStratum ≡ true

canonicalRealTapeSanityBoundary : RealTapeSanityBoundary
canonicalRealTapeSanityBoundary =
  realTapeSanityBoundary false refl false refl true refl true refl

boundaryStatement : String
boundaryStatement =
  "Published exchange-tape evidence constrains market-data, liquidity and execution strata but does not determine portfolio size or joint admissibility. During a recorded halt the execution stratum is empty; after trading resumes it may reopen, while all other required preconditions must still be independently inhabited for the same literal transition."
