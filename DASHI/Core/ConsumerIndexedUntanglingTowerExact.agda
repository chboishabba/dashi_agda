module DASHI.Core.ConsumerIndexedUntanglingTowerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre

------------------------------------------------------------------------
-- CONSUMER-INDEXED UNTANGLING TOWER
--
-- Repeated projection failure should not trigger unrelated scalar accumulation.
-- Each layer retains exactly the relative-fine coordinate needed to reopen the
-- previous state, then permits that residual itself to be decomposed again.
--
--   State_0  <->  Coarse_0 x Residual_0
--   Residual_0 <-> Coarse_1 x Residual_1
--   ...
--
-- The final code is therefore a heterogeneous nested product
--
--   Coarse_0 x Coarse_1 x ... x Residual_n
--
-- and exact reconstruction follows solely from the existing canonical
-- CoarseFineReopening law.  Consumer termination is intentionally distinct:
-- a particular consumer may factor through an earlier coarse observer and may
-- therefore ignore deeper residual coordinates even though exact reconstruction
-- still retains them.
------------------------------------------------------------------------

data UntanglingTower (State : Set) : Nat → Set₁ where
  terminal : UntanglingTower State zero
  layer :
    ∀ {n} →
    (geometry : Fibre.CoarseFineReopening State) →
    UntanglingTower (Fibre.RelativeFine geometry) n →
    UntanglingTower State (suc n)

TowerCode :
  ∀ {State n} →
  UntanglingTower State n → Set
TowerCode {State = State} terminal = State
TowerCode (layer geometry rest) =
  Fibre.Coarse geometry × TowerCode rest

encodeTower :
  ∀ {State n}
    (tower : UntanglingTower State n) →
  State → TowerCode tower
encodeTower terminal state = state
encodeTower (layer geometry rest) state =
  Fibre.coarse geometry state ,
  encodeTower rest (Fibre.relativeFine geometry state)

decodeTower :
  ∀ {State n}
    (tower : UntanglingTower State n) →
  TowerCode tower → State
decodeTower terminal state = state
decodeTower (layer geometry rest) (coarseCode , residualCode) =
  Fibre.reopen geometry coarseCode (decodeTower rest residualCode)

towerRoundTrip :
  ∀ {State n}
    (tower : UntanglingTower State n)
    (state : State) →
  decodeTower tower (encodeTower tower state) ≡ state
towerRoundTrip terminal state = refl
towerRoundTrip (layer geometry rest) state
  rewrite towerRoundTrip rest (Fibre.relativeFine geometry state)
        | Fibre.reopenExact geometry state
  = refl

------------------------------------------------------------------------
-- Consumer terminal versus exact terminal.
------------------------------------------------------------------------

record ConsumerTerminal
    {State Observation : Set}
    (geometry : Fibre.CoarseFineReopening State)
    (observe : State → Observation) : Set₁ where
  constructor consumer-terminal
  field
    factorisation : Fibre.CoarseConsumerFactorisation geometry observe
open ConsumerTerminal public

consumerTerminalFromFactorisation :
  ∀ {State Observation}
    {geometry : Fibre.CoarseFineReopening State}
    {observe : State → Observation} →
  Fibre.CoarseConsumerFactorisation geometry observe →
  ConsumerTerminal geometry observe
consumerTerminalFromFactorisation = consumer-terminal

record ExactTowerTerminal
    {State : Set}
    {n : Nat}
    (tower : UntanglingTower State n) : Set₁ where
  constructor exact-tower-terminal
  field
    exactReopening :
      (state : State) →
      decodeTower tower (encodeTower tower state) ≡ state
open ExactTowerTerminal public

exactTerminalForEveryTower :
  ∀ {State n}
    (tower : UntanglingTower State n) →
  ExactTowerTerminal tower
exactTerminalForEveryTower tower =
  exact-tower-terminal (towerRoundTrip tower)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ConsumerIndexedUntanglingTowerBoundary : Set where
  constructor consumer-indexed-untangling-tower-boundary
  field
    canonicalCoarseFineReopeningReused : Bool
    residualMayBeDecomposedAgain : Bool
    heterogeneousFiniteTowerSupported : Bool
    nestedTowerCodeReopensInitialStateExactly : Bool
    consumerTerminalDistinctFromExactTerminal : Bool
    deeperResidualRequiredAfterConsumerFactors : Bool
    towerClaimsGlobalMinimalEncoding : Bool
    towerClaimsKolmogorovOptimality : Bool
    towerCreatesDomainSpecificTruth : Bool
open ConsumerIndexedUntanglingTowerBoundary public

canonicalConsumerIndexedUntanglingTowerBoundary :
  ConsumerIndexedUntanglingTowerBoundary
canonicalConsumerIndexedUntanglingTowerBoundary =
  consumer-indexed-untangling-tower-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
