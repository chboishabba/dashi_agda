{-# OPTIONS --safe #-}
module DASHI.Trading.PermissionKernel where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _≤_)
open import Data.Nat.Properties using (≤-refl)

open import DASHI.Core.KernelSystem

record Unit : Set where
  constructor unit

data ShapeInvariant : Set where
  downward flat upward : ShapeInvariant

data EnergyInvariant : Set where
  calm ordinary stressed : EnergyInvariant

data PersistenceInvariant : Set where
  transient persistent unstable : PersistenceInvariant

data LiquidityInvariant : Set where
  thin adequate deep : LiquidityInvariant

data RiskGate : Set where
  clear caution blocked : RiskGate

data Permission : Set where
  ACT HOLD BAN : Permission

record MarketWindowState : Set where
  constructor marketState
  field
    shape : ShapeInvariant
    energy : EnergyInvariant
    persistence : PersistenceInvariant
    liquidity : LiquidityInvariant
    risk : RiskGate
    modelCost : Nat
    residualCost : Nat
    riskPenalty : Nat
    currentPermission : Permission
open MarketWindowState public

record MarketQuotient : Set where
  constructor marketQuotient
  field
    qShape : ShapeInvariant
    qEnergy : EnergyInvariant
    qPersistence : PersistenceInvariant
    qLiquidity : LiquidityInvariant
    qRisk : RiskGate
open MarketQuotient public

quotient : MarketWindowState → MarketQuotient
quotient s = marketQuotient
  (shape s)
  (energy s)
  (persistence s)
  (liquidity s)
  (risk s)

authorize : MarketQuotient → Permission
authorize (marketQuotient shape energy persistence liquidity blocked) = BAN
authorize (marketQuotient shape stressed persistence liquidity caution) = BAN
authorize (marketQuotient shape energy unstable liquidity caution) = HOLD
authorize (marketQuotient shape energy persistence thin caution) = HOLD
authorize (marketQuotient upward calm persistent adequate clear) = ACT
authorize (marketQuotient upward calm persistent deep clear) = ACT
authorize (marketQuotient upward ordinary persistent adequate clear) = ACT
authorize (marketQuotient upward ordinary persistent deep clear) = ACT
authorize (marketQuotient shape energy persistence liquidity clear) = HOLD
authorize (marketQuotient shape energy persistence liquidity caution) = HOLD

permissionKernel : MarketWindowState → MarketWindowState
permissionKernel s = marketState
  (shape s)
  (energy s)
  (persistence s)
  (liquidity s)
  (risk s)
  (modelCost s)
  (residualCost s)
  (riskPenalty s)
  (authorize (quotient s))

stateInvolution : MarketWindowState → MarketWindowState
stateInvolution s = s

tradingKernelSystem : KernelSystem
tradingKernelSystem = record
  { State = MarketWindowState
  ; Site = Unit
  ; Channel = MarketQuotient
  ; Geometry = Unit
  ; Neighbourhood = Unit
  ; WeightFamily = Unit
  ; geometry = unit
  ; neighbourhood = unit
  ; weights = unit
  ; involution = stateInvolution
  ; kernel = permissionKernel
  ; involution-involutive = λ s → refl
  ; kernel-involution-equivariant = λ s → refl
  }

data TradingSchedule : Set where
  synchronous snapshotSequential : TradingSchedule

scheduledPermissionKernel : TradingSchedule → MarketWindowState → MarketWindowState
scheduledPermissionKernel synchronous = permissionKernel
scheduledPermissionKernel snapshotSequential = permissionKernel

tradingScheduledKernel : ScheduledKernel tradingKernelSystem
tradingScheduledKernel = record
  { Schedule = TradingSchedule
  ; canonicalSchedule = synchronous
  ; scheduled = scheduledPermissionKernel
  ; canonical-is-synchronous = λ s → refl
  }

_≈market_ : MarketWindowState → MarketWindowState → Set
x ≈market y = quotient x ≡ quotient y

marketEquivalence : Equivalence _≈market_
marketEquivalence = record
  { reflexive = λ s → refl
  ; symmetric = λ related → sym related
  ; transitive = λ left right → trans left right
  }

permissionKernel-respects-quotient :
  ∀ {x y} → x ≈market y → permissionKernel x ≈market permissionKernel y
permissionKernel-respects-quotient related = related

tradingQuotientKernel : QuotientKernel tradingKernelSystem
tradingQuotientKernel = record
  { _≈_ = _≈market_
  ; equivalence = marketEquivalence
  ; respects-quotient = permissionKernel-respects-quotient
  }

tradingQuotientReadout : QuotientReadout tradingKernelSystem
tradingQuotientReadout = record
  { Quotient = MarketQuotient
  ; quotient = quotient
  }

tradingReadoutComplete :
  ReadoutCompleteForRelation
    tradingKernelSystem
    tradingQuotientKernel
    tradingQuotientReadout
tradingReadoutComplete = record
  { relation⇒same-readout = λ related → related }

tradingAction : MarketWindowState → Nat
tradingAction s = modelCost s + residualCost s + riskPenalty s

record TradingActionReceipt (s : MarketWindowState) : Set where
  field
    action-does-not-increase : tradingAction (permissionKernel s) ≤ tradingAction s
open TradingActionReceipt public

tradingActionReceipt : ∀ s → TradingActionReceipt s
tradingActionReceipt s = record
  { action-does-not-increase = ≤-refl }

record LearnerReadout : Set where
  constructor learnerReadout
  field
    invariantState : MarketQuotient
open LearnerReadout public

learnerObserve : MarketWindowState → LearnerReadout
learnerObserve s = learnerReadout (quotient s)

permissionFromLearner : LearnerReadout → Permission
permissionFromLearner observation = authorize (invariantState observation)
