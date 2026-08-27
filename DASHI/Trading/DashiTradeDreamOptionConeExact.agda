module DASHI.Trading.DashiTradeDreamOptionConeExact where

------------------------------------------------------------------------
-- DASHITRADE DREAM OPTION-CONE FORMALISM
--
-- Purpose
-- -------
-- Record the theorem-bearing target architecture suggested by the current
-- dashiTRADE audit without claiming that the Python runtime already inhabits
-- it.
--
-- Existing owners reused:
--
-- * DASHI.Trading.PermissionKernel is the historical trading predecessor.  It
--   already separates shape, energy, persistence, liquidity and risk before
--   producing ACT/HOLD/BAN.
-- * DASHI.Core.IntersectionalNonFactorability owns the generic theorem that a
--   downstream phenomenon cannot factor through an observer that identifies a
--   witness pair, and that arbitrary post-composition cannot repair an erased
--   distinction.
--
-- Cross-PR alignment, deliberately not imported here:
--
-- * PR #606 owns world/perceived/accessible/actionable branch separation,
--   history-deformed gates/barriers and history-valued action cost.
-- * PR #618 owns relational social-ecological action availability over a
--   product context.
-- * PR #620 owns the nonlinear intersection/recharting theorem imported below.
--
-- This file is stacked on #620 so it can reuse that generic theorem directly.
-- It does not copy #606/#618 draft owners across ancestry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Trading.PermissionKernel as Legacy

------------------------------------------------------------------------
-- Historical predecessor retained, not replaced.
------------------------------------------------------------------------

legacyPermission : Legacy.MarketWindowState → Legacy.Permission
legacyPermission state = Legacy.authorize (Legacy.quotient state)

------------------------------------------------------------------------
-- Candidate direction is only an observer/proposal coordinate.
------------------------------------------------------------------------

data Direction : Set where
  shortDirection flatDirection longDirection : Direction

data TradeAction : Set where
  sellAction holdAction buyAction : TradeAction

data InventoryRegime : Set where
  neutralInventory crowdedLongInventory : InventoryRegime

data LiquidityRegime : Set where
  liquidBook thinBook : LiquidityRegime

data UncertaintyRegime : Set where
  calibrated uncertain : UncertaintyRegime

data HistoryRegime : Set where
  stableHistory flipHeavyHistory : HistoryRegime

data RiskRegime : Set where
  riskClear riskCaution riskBlocked : RiskRegime

record TradingFabricState : Set where
  constructor tradingFabricState
  field
    proposal : Direction
    inventory : InventoryRegime
    liquidity : LiquidityRegime
    uncertainty : UncertaintyRegime
    history : HistoryRegime
    risk : RiskRegime

open TradingFabricState public

candidateObserver : TradingFabricState → Direction
candidateObserver = proposal

------------------------------------------------------------------------
-- Relational action availability.
--
-- HOLD is first-class and always available in this finite specimen.  BUY is
-- not determined by direction alone: inventory, liquidity, uncertainty,
-- history and risk jointly restrict the reachable action subfabric.
------------------------------------------------------------------------

actionAvailable : TradingFabricState → TradeAction → Bool
actionAvailable state holdAction = true
actionAvailable state sellAction with risk state
... | riskBlocked = false
... | _ = true
actionAvailable state buyAction with risk state
... | riskBlocked = false
... | riskCaution with liquidity state
...   | thinBook = false
...   | liquidBook with inventory state
...     | crowdedLongInventory = false
...     | neutralInventory with uncertainty state
...       | uncertain = false
...       | calibrated with history state
...         | flipHeavyHistory = false
...         | stableHistory = true
... | riskClear with liquidity state
...   | thinBook = false
...   | liquidBook with inventory state
...     | crowdedLongInventory = false
...     | neutralInventory with uncertainty state
...       | uncertain = false
...       | calibrated with history state
...         | flipHeavyHistory = false
...         | stableHistory = true

Available : TradingFabricState → TradeAction → Set
Available state action = actionAvailable state action ≡ true

holdAlwaysAvailable : (state : TradingFabricState) → Available state holdAction
holdAlwaysAvailable state = refl

------------------------------------------------------------------------
-- Canonical same-proposal / different-actionability witness.
------------------------------------------------------------------------

cleanLongState : TradingFabricState
cleanLongState =
  tradingFabricState
    longDirection neutralInventory liquidBook calibrated stableHistory riskClear

crowdedLongState : TradingFabricState
crowdedLongState =
  tradingFabricState
    longDirection crowdedLongInventory liquidBook calibrated stableHistory riskClear

sameLongProposal :
  candidateObserver cleanLongState ≡ candidateObserver crowdedLongState
sameLongProposal = refl

buyAvailabilityDiffers :
  actionAvailable cleanLongState buyAction
  ≡ actionAvailable crowdedLongState buyAction → ⊥
buyAvailabilityDiffers ()

buyViabilityDoesNotFactorThroughDirection :
  INF.NonFactorabilityWitness
    candidateObserver
    (λ state → actionAvailable state buyAction)
buyViabilityDoesNotFactorThroughDirection =
  INF.nonFactorabilityWitness
    cleanLongState
    crowdedLongState
    refl
    buyAvailabilityDiffers

noDirectionOnlyBuyClassifier :
  INF.FactorsThrough
    candidateObserver
    (λ state → actionAvailable state buyAction) → ⊥
noDirectionOnlyBuyClassifier =
  INF.witnessRulesOutEveryFlatFactorisation
    buyViabilityDoesNotFactorThroughDirection

postprocessedDirectionStillCannotRecoverBuyViability :
  ∀ {Chart : Set} →
  (rechart : Direction → Chart) →
  INF.FactorsThrough
    (λ state → rechart (candidateObserver state))
    (λ state → actionAvailable state buyAction) →
  ⊥
postprocessedDirectionStillCannotRecoverBuyViability rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart buyViabilityDoesNotFactorThroughDirection

------------------------------------------------------------------------
-- Branch coordinates remain independently typed.
--
-- This is an application-level trading profile aligned with #606's branch
-- separation.  It is not declared the generic owner; after draft ancestry is
-- reconciled it should become a thin adapter to that owner.
------------------------------------------------------------------------

record TradeBranchProfile : Set where
  constructor tradeBranchProfile
  field
    physicallyPossible : Bool
    predictedWeight : Nat
    accessible : Bool
    barrier : Nat
    actionable : Bool

open TradeBranchProfile public

sameWeightAccessible : TradeBranchProfile
sameWeightAccessible = tradeBranchProfile true 3 true 1 true

sameWeightInaccessible : TradeBranchProfile
sameWeightInaccessible = tradeBranchProfile true 3 false 1 false

samePredictedWeightDifferentAccessibility :
  predictedWeight sameWeightAccessible
  ≡ predictedWeight sameWeightInaccessible
samePredictedWeightDifferentAccessibility = refl

sameWeightDoesNotIdentifyBranchProfile :
  sameWeightAccessible ≡ sameWeightInaccessible → ⊥
sameWeightDoesNotIdentifyBranchProfile ()

accessibleButNonActionable : TradeBranchProfile
accessibleButNonActionable = tradeBranchProfile true 2 true 4 false

accessibilityDoesNotCollapseToActionability :
  accessible accessibleButNonActionable
  ≡ actionable accessibleButNonActionable → ⊥
accessibilityDoesNotCollapseToActionability ()

------------------------------------------------------------------------
-- Interaction witness.
--
-- Three independently favourable marginal readings do not force the joint BUY
-- decision to be favourable.  This mirrors the generic nonlinear lesson in
-- IntersectionalConstraintGeometryExact: marginal openness is not a theorem of
-- joint openness.
------------------------------------------------------------------------

marginalSignalGood : Bool
marginalSignalGood = true

marginalLiquidityGood : Bool
marginalLiquidityGood = true

marginalRiskGood : Bool
marginalRiskGood = true

jointCrowdedBuyAvailable : Bool
jointCrowdedBuyAvailable = actionAvailable crowdedLongState buyAction

allDeclaredMarginalsGood :
  marginalSignalGood ≡ true
allDeclaredMarginalsGood = refl

jointCanStillClose : jointCrowdedBuyAvailable ≡ false
jointCanStillClose = refl

------------------------------------------------------------------------
-- Trajectory cost is not endpoint-only.
------------------------------------------------------------------------

data TradeRoute : Set where
  lowTurnoverRoute churnRoute : TradeRoute

record TrajectoryCost : Set where
  constructor trajectoryCost
  field
    executionCost : Nat
    riskCost : Nat
    turnoverCost : Nat
    optionalityLoss : Nat

open TrajectoryCost public

costFor : TradeRoute → TrajectoryCost
costFor lowTurnoverRoute = trajectoryCost 1 1 1 0
costFor churnRoute = trajectoryCost 1 1 3 4

totalCost : TrajectoryCost → Nat
totalCost cost =
  executionCost cost
  + riskCost cost
  + turnoverCost cost
  + optionalityLoss cost

sameEndpointDifferentTrajectoryCost :
  totalCost (costFor lowTurnoverRoute)
  ≡ totalCost (costFor churnRoute) → ⊥
sameEndpointDifferentTrajectoryCost ()

------------------------------------------------------------------------
-- Roadmap / promotion boundary.
------------------------------------------------------------------------

record DashiTradeDreamBoundary : Set where
  constructor dashi-trade-dream-boundary
  field
    legacyPermissionKernelIsCompleteDreamArchitecture : Bool
    scalarConfidenceDeterminesAuthorizationSizeAndUrgency : Bool
    marginalGateSuccessImpliesJointTradeViability : Bool
    candidateProofAlreadyProvesRobustEconomicDominance : Bool
    currentPythonRuntimeConformanceSupplied : Bool
    holdNoTradeIsFirstClassSafeCandidate : Bool
    actionViabilityMayRequireRelationalState : Bool
    trajectoryCostMayIncludeFutureOptionalityLoss : Bool

canonicalDashiTradeDreamBoundary : DashiTradeDreamBoundary
canonicalDashiTradeDreamBoundary =
  dashi-trade-dream-boundary
    false
    false
    false
    false
    false
    true
    true
    true
